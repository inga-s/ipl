// SPDX-License-Identifier: LGPL-2.1-or-later
/*
 *
 *  BlueZ - Bluetooth protocol stack for Linux
 *
 *  Copyright (C) 2021  Intel Corporation. All rights reserved.
 *
 *
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#define _GNU_SOURCE
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>

#include <sys/stat.h>

#include <ell/ell.h>

#include "lib/bluetooth.h"
#include "lib/hci.h"
#include "lib/hci_lib.h"
#include "lib/mgmt.h"
#include "lib/l2cap.h"

#include "mesh/crypto.h"

#include "src/shared/shell.h"
#include "src/shared/mgmt.h"
#include "src/shared/util.h"

#define IPLINK_OP_FLAG (1 << 2)
#define IPLINK_AR_FLAG (1 << 4)
#define IPLINK_MD_FLAG (1 << 5)
#define IPLINK_KIP_FLAG (1 << 6)
#define IPLINK_SAZ_FLAG (1 << 7)

#define IPLINK_VERSION(x) ((x) & 0x3) /*Version field (shall equal 0) */
#define IPLINK_OP(x) ((x) & IPLINK_OP_FLAG) /* 0 - data, 1 - ACK */
#define IPLINK_AR(x) ((x) & IPLINK_AR_FLAG) /* Acknowledgement requested */
#define IPLINK_MD(x) ((x) & IPLINK_MD_FLAG) /* More data */
#define IPLINK_KIP(x) ((x) & IPLINK_KIP_FLAG) /* Is 8-bit KEYID8 present */
#define IPLINK_SAZ(x) ((x) & IPLINK_SAZ_FLAG) /* Is address 16 bit */

#define ADDR_TYPE_64 0
#define ADDR_TYPE_16 1
#define ADDR_TYPE_BROADCAST 2

#define IP_LINK_ATLEAST_MTU 1380
#define IP_LINK_ATLEAST_PAYLOAD 251

#define MAX_PEERS 8
#define MAX_KEYS 2

#define PROMPT_ON	COLOR_BLUE "[iplink]" COLOR_OFF "# "

#define print(fmt, arg...) do { \
		bt_shell_printf(fmt "\n", ## arg); \
} while (0)

struct hcidev {
	uint16_t id;

	bdaddr_t bdaddr;		/* controller Bluetooth address */
	uint8_t bdaddr_type;		/* address type */
	uint8_t version;
	uint8_t dev_class[3];		/* controller class of device */
	char *name;			/* controller device name */
	char *short_name;		/* controller short name */
	uint32_t supported_settings;	/* controller supported settings */
	uint32_t pending_settings;	/* pending controller settings */
	uint32_t current_settings;	/* current controller settings */
	uint16_t manufacturer;		/* manufacturer */
};

struct net_key {
	uint32_t id;
	uint32_t seq;
	uint8_t fid;
	uint8_t n_key[16];
	uint8_t enc_key[16];
	uint8_t priv_key[16];
};

struct peer_rpl {
	uint32_t key_id;
	uint32_t seq;
};

struct ipl_node {
	uint64_t addr_64;
	struct l_queue *rpl;
	bool connected;
	uint16_t addr_16;
	bdaddr_t irpa_long;
	bdaddr_t irpa_short;
	uint8_t ark_long[16];
	uint8_t ark_short[16];
};

struct local_state {
	bool is_server;
	struct l_io *io;
	struct ipl_node node;
};

struct ipl_pdu {
	uint8_t fctl;		/* Frame Control (FCTL) field */
	uint8_t keyid;		/* Key Identifier (KEYID8) field */
	uint8_t fid;		/* Frame Identifier (FID) field */
	uint32_t seq;		/* Sequence number */
	uint8_t *payload;	/* A 6LoWPAN-encoded frame (opaque) */
	uint8_t payload_len;	/* Payload length */
	uint64_t mic;		/* Check (MIC) for the network */
};

static bool is_addr64;

static struct l_io *conn_io;
static struct l_io *listen_io;

static uint8_t short_frame[] = {0xab, 0xcd};
static uint8_t send_buf[2048];
static uint8_t rx_buf[2048];

static const char *client_cfg_path = "/home/istotlan/.config/iplink/client.sample.txt";
static const char *server_cfg_path = "/home/istotlan/.config/iplink/server.sample.txt";

static struct local_state *local;
static bool privacy = true;
static bool direct_adv;

static struct ipl_node peers[MAX_PEERS];
static uint16_t num_peers;

static struct mgmt *mgmt;
static uint16_t mgmt_index = MGMT_INDEX_NONE;
static int pending_index = 0;

static bool is_powered;

static uint8_t address_key[16];
//static uint8_t prand[3] = {0x51, 0xf4, 0x2d};
static uint8_t prand[3] = {0x2d, 0xf4, 0x51};

static struct net_key keys[MAX_KEYS];
static uint16_t num_keys;
struct net_key *default_temp_key;

static uint16_t nid = 0x1234;

static uint16_t iplink_psm = 0x0080; //TODO: What is the correct value?
static int sec_level = BT_SECURITY_LOW;

static struct l_queue *hcidevs;

static uint16_t imtu = IP_LINK_ATLEAST_MTU;

static void set_index(const char *arg)
{
	if (!arg || !strcmp(arg, "none") || !strcmp(arg, "any") ||
						!strcmp(arg, "all"))
		mgmt_index = MGMT_INDEX_NONE;
	else if(strlen(arg) > 3 && !strncasecmp(arg, "hci", 3))
		mgmt_index = atoi(&arg[3]);
	else
		mgmt_index = atoi(arg);
}

static bool match_index(const void *a, const void *b)
{
	const struct hcidev *dev = a;
	uint32_t index = L_PTR_TO_UINT(b);

	return (dev->id == index);
}

static int find_key_by_keyid_32(uint32_t keyid)
{
	int i;

	for (i = 0; i< num_keys; i++)
		if (keys[i].id == keyid)
			return i;

	return -1;
}

static int find_key_by_keyid_8(uint8_t keyid, int start)
{
	int i;

	for (i = start; i< num_keys; i++)
		if ((keys[i].id & 0xff) == keyid)
			return i;

	return -1;
}

static void update_prompt(uint16_t index)
{
	char str[32];

	if (index == MGMT_INDEX_NONE)
		snprintf(str, sizeof(str), "%s# ",
					COLOR_BLUE "[iplink]" COLOR_OFF);
	else
		snprintf(str, sizeof(str),
				COLOR_BLUE "[hci%u]" COLOR_OFF "# ", index);

	bt_shell_set_prompt(str);
}

static void mgmt_debug(const char *str, void *user_data)
{
	const char *prefix = user_data;

	print("%s%s", prefix, str);
}

static void print_data(const char *label, unsigned int indent,
						const void *data, size_t size)
{
	char *str;

	str = l_util_hexstring(data, size);
	print("%-20s =%*c%s", label, 1 + (indent * 2), ' ', str);
	l_free(str);
}

static bool aes_cmac(void *checksum, const uint8_t *msg,
					size_t msg_len, uint8_t res[16])
{
	if (!l_checksum_update(checksum, msg, msg_len))
		return false;

	if (16 == l_checksum_get_digest(checksum, res, 16))
		return true;

	return false;
}

static bool aes_cmac_one(const uint8_t key[16], const void *msg,
					size_t msg_len, uint8_t res[16])
{
	void *checksum;
	bool result;

	checksum = l_checksum_new_cmac_aes(key, 16);
	if (!checksum)
		return false;

	result = l_checksum_update(checksum, msg, msg_len);

	if (result) {
		ssize_t len = l_checksum_get_digest(checksum, res, 16);
		result = !!(len == 16);
	}

	l_checksum_free(checksum);

	return result;
}

static bool generate_ark_long(uint64_t addr, uint8_t out[16])
{
	uint8_t buf[16];
	size_t len = 0;
	void *checksum;
	bool res;

	checksum = l_checksum_new_cmac_aes(address_key, 16);
	if (!checksum)
		return false;

	buf[0] = 0x01;
	len++;
	memcpy(&buf[len], &nid, 2);
	len += 2;
	memcpy(&buf[3], &addr, 8);
	len += 8;
	res = aes_cmac(checksum, buf, len, out);
	l_checksum_free(checksum);
	return res;
}

static bool generate_ark_short(uint16_t addr, uint8_t out[16])
{
	uint8_t buf[16];
	size_t len = 0;
	void *checksum;
	bool res;

	print_data("Address key", 0, address_key, 16);

	checksum = l_checksum_new_cmac_aes(address_key, 16);
	if (!checksum)
		return false;

	buf[0] = 0x00;

	len++;
	memcpy(&buf[len], &nid, 2);
	len += 2;
	memcpy(&buf[3], &addr, 2);
	len += 2;

	res = aes_cmac(checksum, buf, len, out);
	l_checksum_free(checksum);
	return res;
}

static bool aes_ecb_one(uint8_t key[16], const uint8_t *in, uint8_t *out,
								uint32_t sz)
{
	void *cipher;
	bool result = false;

	cipher = l_cipher_new(L_CIPHER_AES, key, 16);

	if (cipher) {
		result = l_cipher_encrypt(cipher, in, out, sz);
		print("l_cipher_encrypt %s", result ? "ok":"failed");
		l_cipher_free(cipher);
	}

	return result;
}

static void generate_irpa(uint8_t key[16], uint8_t prand[3], bdaddr_t *irpa)
{
	uint8_t prand_pad[16];
	uint8_t res[16];

	memset(prand_pad, 0, 13);
	memcpy(prand_pad + 13, prand, 3);
	aes_ecb_one(key, prand_pad, res,16);

	memcpy(&irpa->b[0], res + 13, 3);
	memcpy(&irpa->b[3], prand, 3);
	irpa->b[5] &=  0x3f;
	irpa->b[5] |= 0x40;

	print_data("IRPA bytes", 0, irpa->b, 6);

}

static void network_nonce(uint32_t seq, uint64_t src, uint8_t nonce[13])
{
	nonce[0] = 0x00;
	l_put_be32(seq, &nonce[1]);
	l_put_be64(src, &nonce[5]);
}

static bool aes_ccm_encrypt(const uint8_t nonce[13], const uint8_t key[16],
					const uint8_t *add, uint16_t add_len,
					const void *data, uint16_t data_len,
					void *enc_data)
{
	void *cipher;
	bool result;

	cipher = l_aead_cipher_new(L_AEAD_CIPHER_AES_CCM, key, 16, 8);

	result = l_aead_cipher_encrypt(cipher, data, data_len, add, add_len,
					nonce, 13, enc_data, data_len + 8);

	l_aead_cipher_free(cipher);

	return result;
}

static bool encrypt_payload(uint8_t *out, struct ipl_pdu *pdu,
				struct net_key *key, struct ipl_node *peer,
								bool is_short)
{
	uint8_t nonce[13];
	uint8_t add_data[13]; /* NID || DST || FCTL || [KEYID] || [FID] */
	uint8_t add_len;
	bool res;

	print_data("encrypt_payload: Clear text", 0, pdu->payload,
							pdu->payload_len);

	network_nonce(pdu->seq, local->node.addr_64, nonce);

	l_put_be16(nid, &add_data);
	add_len = 2;

	if(is_short) {
		l_put_be16(peer->addr_16, &add_data[add_len]);
		add_len += 2;
	} else {
		l_put_be16(peer->addr_64, &add_data[add_len]);
		add_len += 8;
	}

	add_data[add_len++] = pdu->fctl;

	if (IPLINK_KIP(pdu->fctl))
		add_data[add_len++] = pdu->keyid;

	if (IPLINK_AR(pdu->fctl) || IPLINK_OP(pdu->fctl))
		add_data[add_len++] = pdu->fid;

	if (IPLINK_AR(pdu->fctl))
		print("ACK required!");
	print("encrypt:");
	print_data("nonce", 0, nonce, 13);
	print_data("key", 0, key->n_key, 16);
	print_data("add", 0, add_data, add_len);
	print_data("data", 0, pdu->payload, pdu->payload_len);

	res = aes_ccm_encrypt(nonce, key->enc_key, add_data, add_len,
					pdu->payload, pdu->payload_len, out);

	if (res)
		print_data("encrypted payload: ", 0, out, pdu->payload_len);
	else
		print("Failed to encypt payload!");

	return res;
}

static bool crypto_k2(const uint8_t n[16], const uint8_t *p, size_t p_len,
							uint8_t net_id[1],
							uint8_t enc_key[16],
							uint8_t priv_key[16])
{
	void *checksum;
	uint8_t output[16];
	uint8_t t[16];
	uint8_t *stage;
	bool success = false;

	stage = l_malloc(sizeof(output) + p_len + 1);
	if (!stage)
		return false;

	if (!mesh_crypto_s1("smk2", 4, stage))
		goto fail;

	if (!aes_cmac_one(stage, n, 16, t))
		goto fail;

	checksum = l_checksum_new_cmac_aes(t, 16);
	if (!checksum)
		goto fail;

	memcpy(stage, p, p_len);
	stage[p_len] = 1;

	if (!aes_cmac(checksum, stage, p_len + 1, output))
		goto done;

	net_id[0] = output[15] & 0x7f;

	memcpy(stage, output, 16);
	memcpy(stage + 16, p, p_len);
	stage[p_len + 16] = 2;

	if (!aes_cmac(checksum, stage, p_len + 16 + 1, output))
		goto done;

	memcpy(enc_key, output, 16);

	memcpy(stage, output, 16);
	memcpy(stage + 16, p, p_len);
	stage[p_len + 16] = 3;

	if (!aes_cmac(checksum, stage, p_len + 16 + 1, output))
		goto done;

	memcpy(priv_key, output, 16);
	success = true;

done:
	l_checksum_free(checksum);
fail:
	l_free(stage);

	return success;
}

static void prepare_encoding(struct net_key *key)
{
	size_t p_len;
	uint8_t p[1];
	uint8_t n;

	p[0] = 0;
	p_len = 1;
	print_data("NetworkKey", 0, key->n_key, 16);
	crypto_k2(key->n_key, p, p_len, &n, key->enc_key, key->priv_key);

	//print("nid: %4.4x", nid);
	print_data("EncryptionKey", 0, key->enc_key, 16);
	print_data("PrivacyKey", 0, key->priv_key, 16);

}

static const char *settings_str[] = {
				"powered",
				"connectable",
				"fast-connectable",
				"discoverable",
				"bondable",
				"link-security",
				"ssp",
				"br/edr",
				"hs",
				"le",
				"advertising",
				"secure-conn",
				"debug-keys",
				"privacy",
				"configuration",
				"static-addr",
				"phy-configuration",
				"wide-band-speech",
};

static const char *settings2str(uint32_t settings)
{
	static char str[256];
	unsigned i;
	int off;

	off = 0;
	str[0] = '\0';

	for (i = 0; i < NELEM(settings_str); i++) {
		if ((settings & (1 << i)) != 0)
			off += snprintf(str + off, sizeof(str) - off, "%s ",
							settings_str[i]);
	}

	return str;
}

static void new_settings(uint16_t index, uint16_t len,
					const void *param, void *user_data)
{
	const uint32_t *ev = param;

	if (len < sizeof(*ev)) {
		print("Too short new_settings event (%u)", len);
		return;
	}

	print("hci%u new_settings: %s", index, settings2str(get_le32(ev)));
}

static const char *options_str[] = {
				"external",
				"public-address",
};

static const char *options2str(uint32_t options)
{
	static char str[256];
	unsigned i;
	int off;

	off = 0;
	str[0] = '\0';

	for (i = 0; i < NELEM(options_str); i++) {
		if ((options & (1 << i)) != 0)
			off += snprintf(str + off, sizeof(str) - off, "%s ",
							options_str[i]);
	}

	return str;
}

static void config_options_rsp(uint8_t status, uint16_t len, const void *param,
							void *user_data)
{
	const struct mgmt_rp_read_config_info *rp = param;
	uint16_t index = L_PTR_TO_UINT(user_data);
	uint32_t supported_options, missing_options;

	if (status != 0) {
		l_error("Reading hci%u config failed with status 0x%02x (%s)",
					index, status, mgmt_errstr(status));
		goto done;
	}

	if (len < sizeof(*rp)) {
		l_error("Info reply too short (%u bytes)", len);
		goto done;
	}

	print("hci%u:\tConfiguration options", index);

	supported_options = le32_to_cpu(rp->supported_options);
	print("\tsupported options: %s", options2str(supported_options));

	missing_options = le32_to_cpu(rp->missing_options);
	print("\tmissing options: %s", options2str(missing_options));

done:
	pending_index--;

	if (pending_index > 0)
		return;

	bt_shell_noninteractive_quit(EXIT_SUCCESS);
}

static void free_hcidev(void *data)
{
	struct hcidev *dev = data;

	l_free(dev->name);
	l_free(dev->short_name);
	l_free(dev);
}

static void print_hcidev_info(struct hcidev *dev)
{
	char addr[18];

	ba2str(&dev->bdaddr, addr);
	print("hci%u:\tPrimary controller", dev->id);
	print("\taddr %s version %u manufacturer %u class 0x%02x%02x%02x",
			addr, dev->version, dev->manufacturer,
		dev->dev_class[2], dev->dev_class[1], dev->dev_class[0]);
	print("\tsupported settings: %s",
					settings2str(dev->supported_settings));
	print("\tcurrent settings: %s", settings2str(dev->current_settings));
	print("\tname %s", dev->name);
	print("\tshort name %s", dev->short_name);
}

static void info_rsp(uint8_t status, uint16_t len, const void *param,
							void *user_data)
{
	const struct mgmt_rp_read_info *rp = param;
	uint16_t index = PTR_TO_UINT(user_data);
	struct hcidev *dev = NULL, *old_dev;
	bool res = false;

	if (status != 0) {
		l_error("Reading hci%u info failed with status 0x%02x (%s)",
					index, status, mgmt_errstr(status));
		goto done;
	}

	if (len < sizeof(*rp)) {
		l_error("Info reply too short(%u bytes)", len);
		goto done;
	}

	dev = l_new(struct hcidev, 1);
	dev->id = index;
	dev->manufacturer = le16_to_cpu(rp->manufacturer);
	dev->version = rp->version;

	dev->name = l_strdup((const char *) rp->name);
	dev->short_name = l_strdup((const char *) rp->short_name);
	memcpy(dev->dev_class, rp->dev_class, 3);

	bacpy(&dev->bdaddr, &rp->bdaddr);
	dev->supported_settings = le32_to_cpu(rp->supported_settings);
	dev->current_settings = le32_to_cpu(rp->current_settings);

	dev->name = l_strdup((const char *) rp->name);

	print_hcidev_info(dev);

	if (!(dev->supported_settings & MGMT_SETTING_LE)) {
		l_info("Controller hci%u does not support LE", index);
		free_hcidev(dev);
		goto done;
	}

	if (!(dev->supported_settings & MGMT_SETTING_PRIVACY)) {
		l_info("Controller hci%u does not support privacy", index);
		free_hcidev(dev);
		goto done;
	}

	old_dev = l_queue_remove_if(hcidevs, match_index,
						L_UINT_TO_PTR(mgmt_index));
	l_free(old_dev);

	l_queue_push_tail(hcidevs, dev);

	if (dev->supported_settings & MGMT_SETTING_CONFIGURATION) {
		if (!mgmt_send(mgmt, MGMT_OP_READ_CONFIG_INFO,
					index, 0, NULL, config_options_rsp,
					L_UINT_TO_PTR(index), NULL)) {
			l_error("Unable to send read_config cmd");
			goto done;
		}
		return;
	}

	res = true;

done:
	if (!res && dev && dev->id == mgmt_index)
		mgmt_index = MGMT_INDEX_NONE;

	pending_index--;

	if (pending_index > 0)
		return;

	bt_shell_noninteractive_quit(EXIT_SUCCESS);
}

static void index_rsp(uint8_t status, uint16_t len, const void *param,
							void *user_data)
{
	const struct mgmt_rp_read_index_list *rp = param;
	struct mgmt *mgmt = user_data;
	uint16_t count;
	unsigned int i;

	if (status != 0) {
		l_error("Reading index list failed with status 0x%02x (%s)",
						status, mgmt_errstr(status));
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (len < sizeof(*rp)) {
		l_error("Index list reply too short(%u bytes)", len);
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	count = le16_to_cpu(rp->num_controllers);

	if (len < sizeof(*rp) + count * sizeof(uint16_t)) {
		l_error("Index count (%u) doesn't match reply length (%u)",
								count, len);
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	print("Index list with %u item%s", count, count != 1 ? "s" : "");

	for (i = 0; i < count; i++) {
		uint16_t index = le16_to_cpu(rp->index[i]);

		if (!mgmt_send(mgmt, MGMT_OP_READ_INFO, index, 0, NULL,
					info_rsp, UINT_TO_PTR(index), NULL)) {
			l_error("Unable to send read_info cmd");
			return bt_shell_noninteractive_quit(EXIT_FAILURE);
		}

		pending_index++;
	}

	if (!count)
		bt_shell_noninteractive_quit(EXIT_SUCCESS);
}

static void set_mode(uint16_t opcode, uint8_t mode, mgmt_request_func_t cb)
{
	struct mgmt_mode cp;

	memset(&cp, 0, sizeof(cp));
	cp.val = mode;

	mgmt_send(mgmt, opcode, mgmt_index, sizeof(cp), &cp, cb, NULL, NULL);
}

static void user_confirm_request_callback(uint16_t index, uint16_t length,
							const void *param,
							void *user_data)
{
	const struct mgmt_ev_user_confirm_request *ev = param;
	struct mgmt_cp_user_confirm_reply cp;
	uint16_t opcode;

	memset(&cp, 0, sizeof(cp));
	memcpy(&cp.addr, &ev->addr, sizeof(cp.addr));

	opcode = MGMT_OP_USER_CONFIRM_REPLY;

	mgmt_reply(mgmt, opcode, index, sizeof(cp), &cp,
							NULL, NULL, NULL);
}

static bool check_mtu(int sk)
{
	struct l2cap_options l2o;
	socklen_t len;

	memset(&l2o, 0, sizeof(l2o));

	/* LE CoC enabled kernels should support BT_RCVMTU and
	 * BT_SNDMTU.
	 */
	len = sizeof(l2o.imtu);
	if (getsockopt(sk, SOL_BLUETOOTH, BT_RCVMTU, &l2o.imtu, &len) < 0) {
			bt_shell_printf("getsockopt(BT_RCVMTU): %s (%d)",
					strerror(errno), errno);
			return false;
	}

	l_info("RCV_MTU %d", l2o.imtu);

	len = sizeof(l2o.omtu);
	if (getsockopt(sk, SOL_BLUETOOTH, BT_SNDMTU, &l2o.omtu, &len) < 0) {
			bt_shell_printf("getsockopt(BT_SNDMTU): %s (%d)",
					strerror(errno), errno);
			return false;
	}

	l_info("SND_MTU %d", l2o.omtu);

	return true;
}

static void disconnect_cb(struct l_io *io, void *user_data)
{
	int err = 0;
	socklen_t len;

	len = sizeof(err);

	if (getsockopt(l_io_get_fd(io), SOL_SOCKET, SO_ERROR, &err, &len) < 0)
		print("(sk %d) Failed to obtain disconnect error %s",
					l_io_get_fd(io), strerror(errno));

	print("IO %p disconnected: %s", io, strerror(err));
}

static struct ipl_node *match_peer_by_short_addr(uint16_t addr_16)
{
	int i;

	for(i = 0; i < num_peers; i++) {
		if (addr_16 == peers[i].addr_16)
			return &peers[i];
	}

	return NULL;
}

static struct ipl_node *match_peer_by_long_addr(uint64_t addr_64)
{
	int i;

	for(i = 0; i < num_peers; i++) {
		if (addr_64 == peers[i].addr_64)
			return &peers[i];
	}

	return NULL;
}

static void send_data(void *user_data)
{
	struct iovec *iov = user_data;
	int err, sk_err, sk;
	socklen_t sk_len = sizeof(sk_err);
	size_t sent_len;

	if (local->io)
		sk = l_io_get_fd(local->io);
	else
		sk = l_io_get_fd(conn_io);

	if (getsockopt(sk, SOL_SOCKET, SO_ERROR, &sk_err, &sk_len) < 0)
		err = -errno;
	else
		err = -sk_err;

	if (err < 0) {
		print("%s (%d)", strerror(-err), -err);
		return;
	}

	sent_len = write(sk, iov->iov_base, iov->iov_len);

	if (sent_len != iov->iov_len) {
		print("Sent data  failed");
		return;
	}

	print_data("Sent:", 0, iov->iov_base, iov->iov_len);
}

static struct ipl_node* clarify_header(bool *decrypted, struct net_key *key,
					struct ipl_pdu *pdu, uint8_t *buf,
					uint8_t *mic, uint32_t *hdr_sz)
{
	uint8_t hdr[13];
	uint8_t seed[16];
	uint32_t len, i, fid_offset = 0;
	uint16_t src16;
	uint16_t src64;
	bool fid;

	/* Privacy seed */
	memset(seed, 0, 4);
	l_put_be32(key->id, &seed[4]);
	memcpy(&seed[8], mic, 8);

	if (!aes_ecb_one(key->priv_key, seed, seed, 16)) {
		print("Failed to clarify header");
		*decrypted = false;
		return NULL;;
	}

	*decrypted = true;

	print_data("priv key", 0, key->priv_key, 16);
	print_data("seed", 0, seed, 16);

	len = IPLINK_SAZ(pdu->fctl) ? 12 : 6;

	fid = IPLINK_OP(pdu->fctl) || IPLINK_AR(pdu->fctl);
	if (fid)
		len++;

	for (i = 0; i < len; i++)
		hdr[i] = seed[i] ^ buf[i];

	*hdr_sz = len;

	print_data("obfuscated", 0, buf, len);
	print_data("cl header", 0, hdr, len);

	if (fid) {
		pdu->fid = hdr[0];
		print("fid = %2.2x", pdu->fid);
		fid_offset = 1;
	}

	pdu->seq = l_get_be32(&hdr[fid_offset]);
	print("Seq # = %u", pdu->seq);

	if (len < 12) {
		src16 = l_get_be16(&hdr[4 + fid_offset]);
		print("Src16 %4.4x", src16);
		return match_peer_by_short_addr(src16);
	}

	src64 = l_get_be64(&hdr[4 + fid_offset]);
	print("Src64 %8.8x", src64);

	return match_peer_by_long_addr(src64);
}

static bool decrypt_payload(uint8_t *out, struct ipl_pdu *pdu,
				struct net_key *key, struct ipl_node *peer)
{
	uint8_t nonce[13];
	uint8_t add_data[13]; /* NID || DST || FCTL || [KEYID] || [FID] */
	uint8_t add_len;
	bool res;

	print_data("decrypt_payload: Clear text", 0, pdu->payload,
							pdu->payload_len);

	network_nonce(pdu->seq, peer->addr_64, nonce);
	print_data("nonce", 0, nonce, 13);

	l_put_be16(nid, &add_data);
	add_len = 2;

	if(IPLINK_SAZ(pdu->fctl)) {
		l_put_be16(local->node.addr_64, &add_data[add_len]);
		add_len += 8;
	} else {
		l_put_be16(local->node.addr_16, &add_data[add_len]);
		add_len += 2;
	}

	add_data[add_len++] = pdu->fctl;

	if (IPLINK_KIP(pdu->fctl))
		add_data[add_len++] = pdu->keyid;

	if (IPLINK_AR(pdu->fctl) || IPLINK_OP(pdu->fctl))
		add_data[add_len++] = pdu->fid;

	print("decrypt:");
	print_data("nonce", 0, nonce, 13);
	print_data("key", 0, key, 16);
	print_data("add", 0, add_data, add_len);
	print_data("data", 0, pdu->payload, pdu->payload_len);

	res = aes_ccm_encrypt(nonce, key->enc_key, add_data, add_len,
					pdu->payload, pdu->payload_len, out);

	if (!res) {
		print("Failed to decrypt payload!");
		return false;
	}

	print_data("decrypted payload: ", 0, out, pdu->payload_len);

	return res;
}

/*
PrivacySeed = 0x00 || KEYID32 || MIC
HeaderFields = (FID || SEQ || SRC),
where FID = 0 if elided.
ObfuscatedData = AES-CTR (PrivacyKey, PrivacySeed, HeaderFields)
*/
static bool obfuscate_header(uint8_t *out, struct net_key *key,
					struct ipl_pdu *pdu, uint8_t *mic)
{
	uint8_t hdr[13];
	uint8_t seed[16];
	uint32_t i, len = 0;

	/* Privacy seed */
	memset(seed, 0, 4);
	l_put_be32(key->id, &seed[4]);
	memcpy(&seed[8], mic, 8);

	print_data("mic", 0, mic, 8);
	print_data("privacy seed", 0, seed, 16);

	if (!aes_ecb_one(key->priv_key, seed, seed, 16))
		return false;

	print_data("priv key", 0, key->priv_key, 16);
	print_data("seed vector", 0, seed, 16);

	/* Header fields */
	if ((IPLINK_OP(pdu->fctl) || IPLINK_AR(pdu->fctl))) {
		hdr[0] = pdu->fid;
		len++;
	}

	l_put_be32(pdu->seq, &hdr[len]);
	len += 4;

	if (IPLINK_SAZ(pdu->fctl)) {
		l_put_be64(local->node.addr_64, &hdr[len]);
		len += 8;
	} else {
		l_put_be16(local->node.addr_16, &hdr[len]);
		len += 2;
	}

	for (i = 0; i < len; i++)
		out[i] = seed[i] ^ hdr[i];

	print_data("header", 0, hdr, len);
	print_data("obfuscated", 0, out, len);

	return true;
}

static bool generate_pdu(uint8_t *out, struct net_key *key,
				struct ipl_node *peer, uint8_t fid,
				bool is_short,
				struct ipl_pdu *pdu, uint32_t *total_len)
{
	uint32_t len, hdr_offset;
	uint8_t *mic;

	pdu->seq = key->seq;

	/* Visible header fields: FCTL, [KEYID8], [FID] */
	len = 1;
	if (IPLINK_KIP(pdu->fctl)) {
		out[len] = pdu->keyid;
		len++;
	}

	hdr_offset = len;

	/* Calculate total header length */
	/* FID */
	if (IPLINK_OP(pdu->fctl) || IPLINK_AR(pdu->fctl)) {
		len++;
		pdu->fid = fid;
	}

	/* Sequence number */
	len += 4;

	if (is_addr64) {
		pdu->fctl |= IPLINK_SAZ_FLAG;
		len += 8;
	} else {
		pdu->fctl &= ~IPLINK_SAZ_FLAG;
		len += 2;
	}

	out[0] = pdu->fctl;

	/* Encrypt payload and generate MIC */
	if (!encrypt_payload(out + len, pdu, key, peer, is_short))
		return false;

	mic = out + len + pdu->payload_len;

	/* Obfuscate header fields: Frame ID, sequence number, destination */
	if (!obfuscate_header(out + hdr_offset, key, pdu, mic))
		return false;

	*total_len = len + pdu->payload_len + 8;
	print_data("encrypted PDU", 0, out, *total_len);

	/* Increment local sequence number */
	//key->seq++;

	return true;
}

static bool ack_reply(uint8_t fctl, struct net_key *key, uint8_t fid,
					struct ipl_node *peer, bool is_short)
{
	struct ipl_pdu pdu;
	struct iovec *iov;
	uint32_t total_len, offset;

	memset(&pdu, 0, sizeof (pdu));
	pdu.fctl |= IPLINK_OP_FLAG;

	pdu.payload = NULL;
	pdu.payload_len = 0;

	/* TODO: differentiate between L2CAP & AEXT connection */

	/*If l2cap connection, include header */
	if (is_short)
		memcpy(send_buf, &peer->irpa_short.b, 6);
	else
		memcpy(send_buf, &peer->irpa_long.b, 6);

	offset = 6;

	if (!generate_pdu(send_buf + offset, key, peer, fid, is_short, &pdu,
								&total_len)) {
		print("Failed to generate ACK response");
		return false;
	}

	print("Sending ACK response");
	iov = l_new(struct iovec, 1);

	iov->iov_base = send_buf;
	iov->iov_len = total_len + offset;

	l_idle_oneshot(send_data, iov, l_free);

	return true;
}

static bool check_rpl(struct ipl_node *peer, uint32_t key_id, uint32_t seq)
{
	const struct l_queue_entry *entry;
	struct peer_rpl *rpl;

	entry = l_queue_get_entries(peers->rpl);

	for (; entry; entry = entry->next) {
		rpl = entry->data;

		if (rpl->key_id != key_id)
			continue;

		if (seq <= rpl->seq) {
			print("Fail RPL check: old %u, new %u", rpl->seq, seq);
			return false;
		}

		rpl->seq = seq;
		return true;
	}

	rpl = l_new(struct peer_rpl, 1);
	rpl->key_id = key_id;
	rpl->seq = seq;

	l_queue_push_tail(peer->rpl, rpl);

	return true;
}

static void parse_pdu(uint8_t *buf, uint32_t len)
{
	struct ipl_pdu pdu;
	struct ipl_node *peer;
	struct net_key *key;
	uint32_t hdr_len, sz;
	uint8_t *mic;
	int i = 0;
	bool res;

	memset(&pdu, 0, sizeof (pdu));

	hdr_len = 1;

	pdu.fctl = buf[0];

	print("FCTL %2.2x", pdu.fctl);

try_again:
	if (IPLINK_KIP(pdu.fctl)) {
		pdu.keyid = buf[hdr_len++];
		i = find_key_by_keyid_8(pdu.keyid, i);

		if (i < 0) {
			print("Key %2.2x does not exist", pdu.keyid);
			return;
		}

		key = &keys[i];
		print("Trying to use key %u", key->id);
	} else {
		i = -1;

		if (!default_temp_key) {
			print("Temp key does not exist");
			return;
		}

		print("Using default temp key");
		key = default_temp_key;
	}

	mic = buf + len - 8;
	print_data("mic", 0, mic, 8);

	peer = clarify_header(&res, key, &pdu, buf + hdr_len, mic, &sz);

	if (!peer) {

		if (!res && i >= 0) {
			print("Try another matching key to clarify header");
			goto try_again;
		}

		if (!res)
			print("Failed to clarify header");
		else
			print("Peer not found");

		return;
	}

	hdr_len += sz;

	if (pdu.seq && !check_rpl(peer, key->id, pdu.seq))
		return;

	pdu.payload = buf + hdr_len;
	pdu.payload_len = len - hdr_len - 8;

	if (!decrypt_payload(rx_buf, &pdu, key, peer))
		return;

	if (!IPLINK_AR(pdu.fctl))
		return;

	print("ACK reply fctl %2.2x", pdu.fctl);
	ack_reply(IPLINK_KIP(pdu.fctl) != 0, key, pdu.fid, peer,
					IPLINK_SAZ(pdu.fctl) == 0);
}

static bool read_cb(struct l_io *io, void *user_data)
{
	int err, sk_err, sk;
	socklen_t sk_len = sizeof(sk_err);
	char buf[IP_LINK_ATLEAST_MTU];
	size_t len;

	print("read cb: IO %p", io);
	sk = l_io_get_fd(io);

	l_info("Data read ready on sk %d", sk);

	if (getsockopt(sk, SOL_SOCKET, SO_ERROR, &sk_err, &sk_len) < 0)
		err = -errno;
	else
		err = -sk_err;

	if (err < 0) {
		print("%s (%d)", strerror(-err), -err);
		return false;
	}

	len = read(sk, buf, sizeof(buf));

	print_data("Received L2CAP data", 0, buf, len);

	if (len < 6) {
		print("Recvd data too short %lu", len);
		return false;
	}

	parse_pdu((uint8_t*) buf + 6, len - 6);

	return true;
}

static bool write_cb(struct l_io *io, void *user_data)
{
	l_info("write_cb: IO %p", io);
	return false;
}

static bool listen_cb(struct l_io *io, void *user_data)
{
	int sk, new_sk;

	l_info("listen_cb: IO %p", io);
	sk = l_io_get_fd(io);

	new_sk = accept(sk, NULL, NULL);
	if (new_sk < 0) {
		print("Accept failed: %s (%u)", strerror(errno), errno);
		return false;
	}

	if (!check_mtu(new_sk)) {
		print("Check mtu failed");
		return false;
	}

	l_info("listen_cb: new IPL IO %p", io);
	local->io = l_io_new(new_sk);
	l_io_set_close_on_destroy(local->io, true);

	l_io_set_read_handler(local->io, read_cb, NULL, NULL);
	l_io_set_write_handler(local->io, write_cb, NULL, NULL);
	l_io_set_disconnect_handler(local->io, disconnect_cb, NULL, NULL);

	print("Successfully connected\n");

	close(sk);

	return false;
}

static int create_l2cap_sock(uint16_t psm, uint16_t cid, int sec_level)
{
	struct hcidev *dev;
	struct sockaddr_l2 addr;
	int sk, err;

	dev = l_queue_find(hcidevs, match_index, L_UINT_TO_PTR(mgmt_index));
	if (!dev) {
		l_info("No HCI device found");
		return -ENODEV;
	}

	sk = socket(PF_BLUETOOTH, SOCK_SEQPACKET | SOCK_NONBLOCK,
							BTPROTO_L2CAP);
	if (sk < 0) {
		err = -errno;
		print("Can't create socket: %s (%d)", strerror(errno), errno);
		return err;
	}

	memset(&addr, 0, sizeof(addr));
	addr.l2_family = AF_BLUETOOTH;
	addr.l2_psm = htobs(psm);

	bacpy(&addr.l2_bdaddr, &dev->bdaddr);
	addr.l2_bdaddr_type = BDADDR_LE_PUBLIC;

	if (bind(sk, (struct sockaddr *) &addr, sizeof(addr)) < 0) {
		err = -errno;
		l_error("Can't bind socket: %s (%d)", strerror(errno), errno);
		close(sk);
		return err;
	}

	if (sec_level) {
		struct bt_security sec;

		memset(&sec, 0, sizeof(sec));
		sec.level = sec_level;

		if (setsockopt(sk, SOL_BLUETOOTH, BT_SECURITY, &sec,
							sizeof(sec)) < 0) {
			err = -errno;
			l_error("Can't set security level: %s (%d)",
						strerror(errno), errno);
			close(sk);
			return err;
		}
	}

	if (setsockopt(sk, SOL_BLUETOOTH, BT_RCVMTU, &imtu,
							sizeof(imtu)) < 0) {
		err = -errno;
		l_error("Can't set Recv MTU: %s (%d)",
						strerror(errno), errno);
		return err;
	}

	return sk;
}

#if 0
static void scan_complete(uint8_t status, uint16_t length,
					const void *param, void *user_data)
{
	const struct mgmt_cp_start_discovery *rp = param;

	if (status != MGMT_STATUS_SUCCESS) {
		print("Start Discovery failed wit status 0x%02x", status);
		return;
	}

	if (length < sizeof(*rp)) {
		print("Wrong size of start scanning return parameters");
		return;
	}
}

#define SCAN_TYPE_LE ((1 << BDADDR_LE_PUBLIC) | (1 << BDADDR_LE_RANDOM))
static void start_discovery(void)
{
	struct mgmt_cp_start_discovery cp;

	cp.type = SCAN_TYPE_LE;

	mgmt_send(mgmt, MGMT_OP_START_DISCOVERY, mgmt_index,
				sizeof(cp), &cp, scan_complete, NULL, NULL);

}
#endif
static void powered_off_cb(uint8_t status, uint16_t length,
					const void *param, void *user_data)
{
	if (status != MGMT_STATUS_SUCCESS) {
		print("Failed to power off the controller %s (0x%02x)",
						mgmt_errstr(status), status);
		return;
	}

	print("Controller powered off");
}

static void powered_on_cb(uint8_t status, uint16_t length,
					const void *param, void *user_data)
{
	int sk;

	if (status != MGMT_STATUS_SUCCESS) {
		print("Failed to power on the controller %s (0x%02x)",
						mgmt_errstr(status), status);
		mgmt_index = MGMT_INDEX_NONE;
		l_free(local);
		local = NULL;
		return;
	}

	print("Controller powered on");
	is_powered = true;

	if (!local->is_server || direct_adv)
		return;

	sk = create_l2cap_sock(iplink_psm, 0x43, sec_level);

	if (sk < 0) {
		bt_shell_printf("Failed to create server socket");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (listen(sk, 5) < 0) {
		bt_shell_printf("Listening on socket failed: %s (%u)",
					strerror(errno), errno);
		close(sk);
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	listen_io = l_io_new(sk);
	l_io_set_close_on_destroy(listen_io, true);

	l_io_set_read_handler(listen_io, listen_cb, NULL, NULL);
	l_io_set_write_handler(listen_io, write_cb, NULL, NULL);

	bt_shell_printf("Listening for connections");
	return bt_shell_noninteractive_quit(EXIT_SUCCESS);
}

static void load_empty_irks_callback(uint8_t status, uint16_t length,
					const void *param, void *user_data)
{
	bool power_on = L_PTR_TO_UINT(user_data);

	if (status != MGMT_STATUS_SUCCESS) {
		print("Load empty IRKs failed\n");
	}

	print("Loaded empty IRKs");

	if (power_on)
		set_mode(MGMT_OP_SET_POWERED, 0x01, powered_on_cb);
	else if (is_powered)
		set_mode(MGMT_OP_SET_POWERED, 0x00, powered_off_cb);
}

static void load_arks_complete(uint8_t status, uint16_t length,
					const void *param, void *user_data)
{
	if (status != MGMT_STATUS_SUCCESS) {
		print("Load ARKs failed %s (0x%02x)",
					mgmt_errstr(status), status);
		return;
	}

	print("Loaded ARKs");
}

static void load_arks(void)
{
	struct mgmt_cp_load_irks *cp;
	struct mgmt_irk_info *irk;
	size_t sz;
	int i, k;

	if (num_peers == 0)
		return;

	sz = sizeof(*cp) + (num_peers * 2 * sizeof(*irk));
	cp = l_malloc(sz);

	cp->irk_count = htobs(num_peers * 2);

	for (i = 0, k = 0; i < num_peers; i++, k += 2) {
		irk = &cp->irks[k];
		bacpy(&irk->addr.bdaddr, &peers[i].irpa_short);
		irk->addr.type = BDADDR_LE_PUBLIC;
		memcpy(irk->val, peers[i].ark_short, sizeof(irk->val));
		irk = &cp->irks[k + 1];
		bacpy(&irk->addr.bdaddr, &peers[i].irpa_long);
		irk->addr.type = BDADDR_LE_PUBLIC;
		memcpy(irk->val, peers[i].ark_long, sizeof(irk->val));
	}

	print_data("load irk data", 0, (uint8_t *)cp, sz);
	mgmt_send(mgmt, MGMT_OP_LOAD_IRKS, mgmt_index,
			sz, cp, load_arks_complete, NULL, NULL);

	l_free(cp);
}

static void set_privacy_complete(uint8_t status, uint16_t length,
					const void *param, void *user_data)
{
	const char irks_empty_list[] = { 0x00, 0x00 };

	if (status != MGMT_STATUS_SUCCESS) {
		l_error("Failed to set privacy for hci%u: %s (0x%02x)",
				mgmt_index, mgmt_errstr(status), status);
		return;
	}

	print("Successfuly %s %s privacy on hci%u",
					privacy ? "enabled" : "disabled",
			local->is_server ? "server's" : "client's", mgmt_index);

	mgmt_send(mgmt, MGMT_OP_LOAD_IRKS, mgmt_index,
				sizeof(irks_empty_list), irks_empty_list,
				load_empty_irks_callback, user_data, NULL);
}

static void set_privacy(bool privacy, uint8_t irk[16], bool power_on)
{
	struct mgmt_cp_set_privacy cp;

	set_mode(MGMT_OP_SET_POWERED, 0x00, powered_off_cb);

	cp.privacy = privacy ? 1 : 0;
	memcpy(cp.irk, irk, 16);

	if (mgmt_send(mgmt, MGMT_OP_SET_PRIVACY, mgmt_index, sizeof (cp), &cp,
		      set_privacy_complete, L_UINT_TO_PTR(power_on), NULL) > 0)
		return bt_shell_noninteractive_quit(EXIT_SUCCESS);

	print("Failed to set privacy");
	return bt_shell_noninteractive_quit(EXIT_FAILURE);
}

static struct ipl_node *match_peer_by_addr(char *str)
{
	uint64_t addr_64;
	uint16_t addr_16;
	size_t len = strlen(str);

	if (len != 4 && len != 16)
		return NULL;

	if (len == 4) {
		sscanf(str, "%04hx", &addr_16);
		return match_peer_by_short_addr(addr_16);
	}

	sscanf(str, "%16lx", &addr_64);
	return match_peer_by_long_addr(addr_64);
}

static void cmd_connect(int argc, char **argv)
{
	int sk, err;
	struct sockaddr_l2 addr;
	bdaddr_t dst;
	struct ipl_node *peer;
	char buf[18];

	if (argc <= 1) {
		l_error("Missing destination address");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	switch (strlen(argv[1])) {
	case 17:
		if (str2ba(argv[1], &dst))
			return bt_shell_noninteractive_quit(EXIT_FAILURE);
		break;
	case 4:
	case 16:
		peer = match_peer_by_addr(argv[1]);
		if (!peer) {
			print("Peer %s not found", argv[1]);
			return bt_shell_noninteractive_quit(EXIT_FAILURE);
		}

		if (strlen(argv[1]) == 4)
			memcpy(&dst, &peer->irpa_short, sizeof(dst));
		else
			memcpy(&dst, &peer->irpa_long, sizeof(dst));
		break;
	default:
		print("Bad address %s", argv[1]);
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	ba2str(&dst, buf);
	print("Connecting to %s", buf);

	if (!local->is_server && direct_adv) {
		unsigned char param[] = { 0x01 };
		mgmt_send(mgmt, MGMT_OP_SET_ADVERTISING, mgmt_index,
				sizeof(param), param, NULL, NULL, NULL);
	}

	if (!conn_io) {
		sk = create_l2cap_sock(iplink_psm, 0x41, sec_level);
		if (sk < 0) {
			l_error("Failed to create l2cap socket");
			return;
		}
	} else
		sk = l_io_get_fd(conn_io);

	memset(&addr, 0, sizeof(addr));
	addr.l2_family = AF_BLUETOOTH;
	addr.l2_psm = htobs(iplink_psm);
	addr.l2_bdaddr_type = BDADDR_LE_PUBLIC;
	bacpy(&addr.l2_bdaddr, &dst);

	err = connect(sk, (struct sockaddr *) &addr, sizeof(addr));
	if (err < 0 && !(errno == EAGAIN || errno == EINPROGRESS)) {
		err = -errno;
		l_error("Can't connect socket: %s (%d)", strerror(errno),
									errno);
		close(sk);
		return;
	}

	if (!conn_io) {
		conn_io = l_io_new(sk);
		print("Create new conn IO %p", conn_io);

		l_io_set_close_on_destroy(conn_io, true);

		l_io_set_read_handler(conn_io, read_cb, NULL, NULL);
		l_io_set_write_handler(conn_io, write_cb, NULL, NULL);
	}

	print("Connect in progress");
}

static void cmd_list_peers(int argc, char **argv)
{
	int i;
	char buf[18];

	for (i = 0; i< num_peers; i++) {
		print("* Peer %u", i);
		print("  Short address:\t%4.4x", peers[i].addr_16);
		print("  Long address:\t%lx", peers[i].addr_64);
		ba2str(&peers[i].irpa_short, buf);
		print("  IRPA short:\t%s", buf);
		ba2str(&peers[i].irpa_long, buf);
		print("  IRPA long:\t%s", buf);
		print_data("  ARK short",0, peers[i].ark_short, 16);
		print_data("  ARK long", 0, peers[i].ark_long, 16);
	}
}

static void cmd_send_data(int argc, char **argv)
{
	struct ipl_node *peer;
	struct ipl_pdu pdu = {.fid = 0,};
	struct net_key *key;
	struct iovec iov;
	uint32_t val, len, offset = 0;
	bool is_short;
	int next_arg;

	if (mgmt_index == MGMT_INDEX_NONE || !local) {
		l_error("Device not configured");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (argc <= 2) {
		print("Expected at least 2 args: address, fctl");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	peer = match_peer_by_addr(argv[1]);
	if (!peer) {
		print("Peer %s not found", argv[1]);
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	is_short = strlen(argv[1]) == 4;
	sscanf(argv[2], "%2x", &val);
	pdu.fctl = (uint8_t) val;

	next_arg = 3;

	if (IPLINK_KIP(pdu.fctl)) {
		int i;

		if (argc <= 3) {
			print("fctl requires key ID value to be present");
			return bt_shell_noninteractive_quit(EXIT_FAILURE);
		}

		sscanf(argv[3], "%x", &val);
		i = find_key_by_keyid_32(val);

		if (i < 0) {
			print("No KeyId32 matching %8.8x\n", val);
			return bt_shell_noninteractive_quit(EXIT_FAILURE);
		}

		key = &keys[i];
		pdu.keyid = key->id & 0xff;
		next_arg++;
	} else
		key = default_temp_key;

	if (!key) {
		print("No keys found");
		return;
	}

	if (IPLINK_AR(pdu.fctl) || IPLINK_OP(pdu.fctl)) {
		pdu.fid = (uint8_t) (key->seq & 0xff);
		print("Frame ID value set to %2.2x", pdu.fid);
	}

	/* Use canned data */
	pdu.payload = short_frame;
	pdu.payload_len = sizeof(short_frame);

	/* TODO: differentiate between L2CAP & AEXT connection */

	/*If l2cap connection, include header */
	if (is_short)
		memcpy(send_buf, &peer->irpa_short.b, 6);
	else
		memcpy(send_buf, &peer->irpa_long.b, 6);

	offset = 6;

	if (!generate_pdu(send_buf + offset, key, peer, key->fid, is_short,
								&pdu, &len))
		return bt_shell_noninteractive_quit(EXIT_FAILURE);

	/* Increment FID */
	if (IPLINK_OP(pdu.fctl) || IPLINK_AR(pdu.fctl))
		key->fid++;

	key->fid = (key->fid < 0xff) ? key->fid + 1 : 0;
	iov.iov_base = send_buf;
	iov.iov_len = len + offset;

	send_data(&iov);

	bt_shell_noninteractive_quit(EXIT_SUCCESS);
}

static void cmd_update_peers(int argc, char **argv)
{
	if (num_peers  <= 0) {
		print("No known peers");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	load_arks();
}

static void cmd_add_peer(int argc, char **argv)
{
	uint8_t *ark;
	size_t sz;

	if (mgmt_index == MGMT_INDEX_NONE) {
		l_error("Device not configured");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (!privacy) {
		l_error("Privacy not enabled");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (argc <= 6) {
		print("Expected 6 args: short address, IRPA short,\
				ARK short, long address, IRPA long, \
								ARK long");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (!str2ba(argv[1], &peers[num_peers].irpa_short))
		return bt_shell_noninteractive_quit(EXIT_FAILURE);

	if (!argv[2] || (strlen(argv[2]) != 32)) {
		bt_shell_printf(COLOR_RED "Requires ARK\n" COLOR_RED);
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	ark = l_util_from_hexstring(argv[2], &sz);
	if (!ark || sz != 16) {
		bt_shell_printf(COLOR_RED "Failed ro read ARK\n" COLOR_RED);
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	memcpy(peers[num_peers].ark_short, ark, 16);
	l_free(ark);

	peers[num_peers].rpl = l_queue_new();

	num_peers++;
	load_arks();
}

static void cmd_index(int argc, char **argv)
{
	uint32_t index;

	if (local) {
		print("cannot change index. Device already configured");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (argc <= 1) {
		print("Missing HCI index");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	} else if (sscanf(argv[1], "%u", &index) != 1) {
		print("Failed to parse  HCI index");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	mgmt_index = index;

	if (!mgmt_send(mgmt, MGMT_OP_READ_INFO, index, 0, NULL, info_rsp,
					UINT_TO_PTR(index), NULL)) {
		l_error("Unable to send read_info cmd");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}
}

static void cmd_info(int argc, char **argv)
{
	uint32_t index;

	if (argc <= 1) {
		index = MGMT_INDEX_NONE;
	} else if (sscanf(argv[1], "%u", &index) != 1)
		return;

	if (index == MGMT_INDEX_NONE) {
		if (!mgmt_send(mgmt, MGMT_OP_READ_INDEX_LIST,
					MGMT_INDEX_NONE, 0, NULL,
					index_rsp, mgmt, NULL)) {
			l_error("Unable to send index_list cmd");
			return bt_shell_noninteractive_quit(EXIT_FAILURE);
		}

		return;
	}

	if (!mgmt_send(mgmt, MGMT_OP_READ_INFO, index, 0, NULL, info_rsp,
					UINT_TO_PTR(index), NULL)) {
		l_error("Unable to send read_info cmd");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}
}

static void set_le_mode_callback(uint8_t status, uint16_t length,
					const void *param, void *user_data)
{
	struct mgmt_mode cp;

	memset(&cp, 0, sizeof(cp));
	cp.val = 0x01;

	if (status != MGMT_STATUS_SUCCESS) {
		print("Failed to set mode: %s (0x%02x)",
						mgmt_errstr(status), status);
		mgmt_index = MGMT_INDEX_NONE;
		l_free(local);
		local = NULL;
		return;
	} else
		print("Set LE mode");

	if (!privacy)
		set_mode(MGMT_OP_SET_POWERED, 0x01, powered_on_cb);
	else
		set_privacy(privacy, is_addr64 ?
				local->node.ark_long : local->node.ark_short,
									true);
}

static void cmd_power_off(int argc, char **argv)
{
	if (mgmt_index == MGMT_INDEX_NONE)
		return  bt_shell_noninteractive_quit(EXIT_FAILURE);

	privacy = false;

	if (!local)
		set_mode(MGMT_OP_SET_POWERED, 0x00, powered_off_cb);
	else
		set_privacy(privacy, is_addr64 ?
				local->node.ark_long : local->node.ark_short,
									false);
}

static void write2file(const void *buffer, size_t len, const char *path)
{
	char *tmp_path;
	ssize_t written;
	int fd;

	tmp_path = l_strdup_printf("%s.tmp.XXXXXX", path);

	fd = L_TFR(mkostemp(tmp_path, O_CLOEXEC));
	if (fd == -1) {
		print("Error creating temp file %s\n", tmp_path);
		goto done;
	}

	written = L_TFR(write(fd, buffer, len));
	L_TFR(close(fd));

	if (written != (ssize_t) len) {
		print("Error writing %lu bytes to temp file %s\n",
							len, tmp_path);
		goto done;
	}

	if (rename(tmp_path, path) == -1)
		print("Error renaming %s to %s", tmp_path, path);

done:
	l_free(tmp_path);
}

static void save_to_file(const char *path)
{
	struct l_settings *settings;
	char **groups = NULL;
	char *data;
	size_t length = 0;
	int i, k;

	print("Saving updated info to %s\n", path);

	settings = l_settings_new();
	if(!l_settings_load_from_file(settings, path)) {
		print("Failed to load configuration from %s\n", path);
		l_settings_free(settings);
		goto done;
	}

	groups = l_settings_get_groups(settings);

	for(i = 0; groups[i]; i++) {
		uint32_t id;

		if (strncmp(groups[i], "Network", 7))
			continue;

		sscanf(groups[i] + 7, "%d", &id);

		k = find_key_by_keyid_32(id);
		if (k < 0) {
			//TODO: add a new NetKey
			continue;
		}

		if (!l_settings_set_uint(settings, groups[i], "SeqNum",
								keys[k].seq))
			print("Failed to save local Seq # for %s", groups[i]);
	}


	for (i = 0; i < num_peers; i++) {
		char name[10];
		char buf[16];
		const struct l_queue_entry *entry;

		sprintf(name, "Peer%d", i);

		entry = l_queue_get_entries(peers[i].rpl);

		for (; entry; entry = entry->next) {
			struct peer_rpl *rpl = entry->data;

			sprintf(buf, "SeqNum%d", rpl->key_id);
			if (!l_settings_set_uint(settings, name, buf,
					rpl->seq)) {
				printf("Failed to save %s's Seq #\n", name);
				continue;
			}
		}
	}

done:
	data = l_settings_to_data(settings, &length);
	write2file(data, length, path);
	l_free(data);
	l_settings_free(settings);
}

static bool setup_from_file(const char *path)
{
	struct l_settings *settings;
	uint8_t *buf;
	uint32_t val;
	size_t n;
	int i, k;
	bool result = false;
	char **groups = NULL;

	settings = l_settings_new();
	if(!l_settings_load_from_file(settings, path)) {
		l_error("Failed to load configuration from %s\n", path);
		goto done;
	}


	groups = l_settings_get_groups(settings);

	for(i = 0, k = 0; groups[i] && k < MAX_KEYS; i++) {

		if (strncmp(groups[i], "Network", 7))
			continue;

		sscanf(groups[i] + 7, "%d", &keys[k].id);

		buf = l_settings_get_bytes(settings, groups[i], "Key", &n);
		if (!buf || n != 16) {
			l_error("Failed to read network key for %s\n",
								groups[i]);
			continue;
		}

		memcpy(&keys[k].n_key, buf, 16);
		l_free(buf);

		if (!l_settings_get_uint(settings, groups[i], "SeqNum",
							&keys[k].seq)) {
			print("Failed to read local sequence number for %s",
								groups[i]);
			print("Re-initializing to zero");
			keys[k].seq = 0;
		}

		keys[k].fid = 0x34;

		k++;
	}

	if (k <= 0) {
		print("No network keys loaded from %s", path);
		goto done;
	}

	num_keys = k;
	default_temp_key = &keys[0];

	/* Local Node */
	buf = l_settings_get_bytes(settings, "Local", "AddressKey", &n);
	if (!buf || n != sizeof(address_key)) {
		print("Failed to read address key from %s", path);
		goto done;
	}

	memcpy(address_key, buf, sizeof(address_key));
	l_free(buf);

	if (!l_settings_get_uint(settings, "Local", "ShortAddress", &val)) {
		print("Failed to read local short address from %s\n", path);
		goto done;
	}

	local->node.addr_16 = l_get_u16(&val);

	if (!l_settings_get_uint64(settings, "Local", "LongAddress",
							&local->node.addr_64)) {
		print("Failed to read local long address from %s", path);
		goto done;
	}

	/* Peers */

	for(i = 0, k = 0; groups[i] && k < MAX_PEERS; i++) {
		char *str;
		int res;

		if (strncmp(groups[i], "Peer", 4))
			continue;

		if (!l_settings_get_uint(settings, groups[i], "ShortAddress",
									&val)) {
			l_error("Failed to read %s's short addr\n", groups[i]);
			continue;
		}

		peers[k].addr_16 = (uint16_t) val;

		buf = l_settings_get_bytes(settings, groups[i], "ShortARK", &n);
		if (!buf || n != sizeof(peers[k].ark_short)) {
			l_error("Failed to read %s's short ARK\n", groups[i]);
			l_free(buf);
			continue;
		}

		memcpy(peers[k].ark_short, buf, n);
		l_free(buf);

		str = l_settings_get_string(settings, groups[i], "ShortIRPA");
		if (!str) {
			l_error("Failed to read %s's short IRPA\n", groups[i]);
			continue;
		}

		res = str2ba(str, &peers[k].irpa_short);
		l_free(str);

		if (res != 0) {
			l_error("Failed to parse %s's short IRPA\n", groups[i]);
			continue;
		}

		if (!l_settings_get_uint64(settings, groups[i], "LongAddress",
						&peers[k].addr_64)) {
			l_error("Failed to read %s's long addr\n", groups[i]);
			continue;
		}

		buf = l_settings_get_bytes(settings, groups[i], "LongARK", &n);
		if (!buf || n != sizeof(peers[k].ark_long)) {
			l_error("Failed to read %s's long ARK\n", groups[i]);
			l_free(buf);
			continue;
		}

		memcpy(peers[k].ark_long, buf, n);
		l_free(buf);

		str = l_settings_get_string(settings, groups[i], "LongIRPA");
		if (!str) {
			l_error("Failed to read %s's long IRPA\n", groups[i]);
			continue;
		}

		res = str2ba(str, &peers[k].irpa_long);
		l_free(str);

		if (res != 0) {
			l_error("Failed to parse %s's long IRPA\n", groups[i]);
			continue;
		}

		k++;
	}

	num_peers = k;
	result = true;

	for (k = 0; k < num_keys; k++)
		prepare_encoding(&keys[k]);

done:
	l_free(groups);
	l_settings_free(settings);
	return result;
}

static bool init_local_node(const char *path)
{
	char buf[18];

	if (!setup_from_file(path)) {
		print("Failed to parse config file");
		return false;
	}

	if (!generate_ark_long(local->node.addr_64, local->node.ark_long) ||
		!generate_ark_short(local->node.addr_16, local->node.ark_short))
		return false;

	generate_irpa(local->node.ark_long, prand, &local->node.irpa_long);
	generate_irpa(local->node.ark_short, prand, &local->node.irpa_short);

	print_data("ARK long", 0, local->node.ark_long, 16);
	ba2str(&local->node.irpa_long, buf);
	print("IRPA long %s\n", buf);
	print_data("ARK short", 0, local->node.ark_short, 16);
	ba2str(&local->node.irpa_short, buf);
	print("IRPA short %s\n", buf);

	return true;
}

static void cmd_client(int argc, char **argv)
{
	unsigned char param[] = { 0x00 };

	if (local) {
		print("Device already configured as %s\n",
				local->is_server ? "server" : "client");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (mgmt_index == MGMT_INDEX_NONE) {
		print("Controller is not set up. Run \"set-index\" command");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	local = l_new(struct local_state, 1);

	if (!init_local_node(client_cfg_path)) {
		l_free(local);
		local = NULL;
		print("Failed to initialize local node");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	set_mode(MGMT_OP_SET_POWERED, 0x00, NULL);

	mgmt_register(mgmt, MGMT_EV_USER_CONFIRM_REQUEST, mgmt_index,
				user_confirm_request_callback, NULL, NULL);

	mgmt_register(mgmt, MGMT_EV_NEW_SETTINGS, mgmt_index, new_settings,
								NULL, NULL);
	mgmt_send(mgmt, MGMT_OP_SET_ADVERTISING, mgmt_index,
				sizeof(param), param, NULL, NULL, NULL);

	if (direct_adv) {
		unsigned char conn_param[] = { 0x01 };

		mgmt_send(mgmt, MGMT_OP_SET_CONNECTABLE, mgmt_index,
				sizeof(conn_param), conn_param, NULL, NULL, NULL);
		mgmt_send(mgmt, MGMT_OP_SET_ADVERTISING, mgmt_index,
				sizeof(param), conn_param, NULL, NULL, NULL);
	}

	set_mode(MGMT_OP_SET_LE, 0x01, set_le_mode_callback);
}

static void cmd_server(int argc, char **argv)
{
	unsigned char adv_param[] = { 0x01 };
	unsigned char conn_param[] = { 0x01 };

	if (local) {
		print("Device already configured as %s\n",
				local->is_server ? "server" : "client");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	if (mgmt_index == MGMT_INDEX_NONE) {
		print("Controller is not set up. Run \"set-index\" command");
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	local = l_new(struct local_state, 1);

	if (!init_local_node(server_cfg_path)) {
		l_free(local);
		local = NULL;
		return bt_shell_noninteractive_quit(EXIT_FAILURE);
	}

	local->is_server = true;

	mgmt_register(mgmt, MGMT_EV_USER_CONFIRM_REQUEST, mgmt_index,
				user_confirm_request_callback, NULL, NULL);

	mgmt_register(mgmt, MGMT_EV_NEW_SETTINGS, mgmt_index, new_settings,
								NULL, NULL);

	mgmt_send(mgmt, MGMT_OP_SET_CONNECTABLE, mgmt_index,
			sizeof(conn_param), conn_param, NULL, NULL, NULL);

	if (direct_adv)
		adv_param[0] = 0;

	mgmt_send(mgmt, MGMT_OP_SET_ADVERTISING, mgmt_index,
				sizeof(adv_param), adv_param, NULL, NULL, NULL);

	set_mode(MGMT_OP_SET_LE, 0x01, set_le_mode_callback);
}

static void index_added(uint16_t index, uint16_t length, const void *param,
							void *user_data)
{
	l_info("Hci dev %4.4x added", index);

	mgmt_send(mgmt, MGMT_OP_READ_INFO, index, 0, NULL,
				info_rsp, L_UINT_TO_PTR(index), NULL);
}

static void index_removed(uint16_t index, uint16_t length, const void *param,
							void *user_data)
{
	struct hcidev *dev;

	l_warn("Hci dev %4.4x removed", index);

	dev = l_queue_remove_if(hcidevs, match_index, L_UINT_TO_PTR(index));

	if (dev)
		free_hcidev(dev);
}

static void register_mgmt_callbacks(void)
{
	mgmt_register(mgmt, MGMT_EV_INDEX_ADDED, mgmt_index, index_added,
								NULL, NULL);
	mgmt_register(mgmt, MGMT_EV_INDEX_REMOVED, mgmt_index, index_removed,
								NULL, NULL);
}

static const char *index_option;
static const char *addr_type_option;

static struct option main_options[] = {
	{ "index",	1, 0, 'i' },
	{ "addr",	1, 0, 'a' },
	{ 0, 0, 0, 0 }
};

static const char **optargs[] = {
	&index_option,
	&addr_type_option
};

static const char *help[] = {
	"Specify adapter index\n",
	"Specify address type: long (\"u64\") or short (\"u16\")\n"
};

static const struct bt_shell_opt opt = {
	.options = main_options,
	.optno = sizeof(main_options) / sizeof(struct option),
	.optstr = "",
	.optarg = optargs,
	.help = help,
};

static const struct bt_shell_menu main_menu = {
	.name = "main",
	.entries = {
	{ "info",		"[index]",
		cmd_info,	"Show controller info"},
	{ "set-index",		"<index>",
		cmd_index,	"Specify controller"},
	{ "client",		NULL,
		cmd_client,	"Setup client. Mutually exclusive with server"},
	{ "server",		NULL,
		cmd_server,	"Setup server. Mutually exclusive with client"},
	{ "list-peers",	NULL,
		cmd_list_peers, "Show peers' info"},
	{ "update-peers",	NULL,
		cmd_update_peers, "Load peers' addresses to resolvable list"},
	{ "add-peer",		"<addr16> <short ARK> <addr64> <long ARK>",
		cmd_add_peer,	"Add peer info"},
	{ "connect",		"<addr16|addr64>",
		cmd_connect,	"Connect to a remote device"},
	{ "send-data",		"<addr> <fctl> [keyid]",
		cmd_send_data,	"Send canned data"},
	{ "power-off",		NULL,
		cmd_power_off,	"Power off and disable privacy"},
	{ } },
};

int main(int argc, char *argv[])
{
	int status, i;

	l_log_set_stderr();

	bt_shell_init(argc, argv, &opt);
	bt_shell_set_menu(&main_menu);

	mgmt = mgmt_new_default();
	if (!mgmt) {
		fprintf(stderr, "Unable to open mgmt_socket\n");
		return EXIT_FAILURE;
	}

	if (getenv("MGMT_DEBUG"))
		mgmt_set_debug(mgmt, mgmt_debug, "mgmt: ", NULL);

	if (index_option)
		set_index(index_option);

	if (addr_type_option) {
		if (strlen(addr_type_option) != 3) {
			print("Invalid address type: expected u64 or u16\n");
			exit(1);
		}

		if (!strncasecmp(addr_type_option, "u64", 3))
			is_addr64 = true;
	}

	register_mgmt_callbacks();
	hcidevs = l_queue_new();

	bt_shell_attach(fileno(stdin));
	update_prompt(mgmt_index);

	if (mgmt_index != MGMT_INDEX_NONE) {
		if (!mgmt_send(mgmt, MGMT_OP_READ_INFO, mgmt_index, 0, NULL,
				info_rsp, UINT_TO_PTR(mgmt_index), NULL)) {
			print("Unable to send read_info cmd\n");
		}
	}

	status = bt_shell_run();

	mgmt_cancel_all(mgmt);
	mgmt_unregister_all(mgmt);
	mgmt_unref(mgmt);

	if (local) {
		if (0) save_to_file(local->is_server ?
					server_cfg_path : client_cfg_path);
		l_io_destroy(local->io);
		l_free(local);
	}

	l_io_destroy(conn_io);
	l_queue_destroy(hcidevs, free_hcidev);

	for (i = 0; i < num_peers; i++)
		l_queue_destroy(peers[i].rpl, l_free);

	return status;
}
