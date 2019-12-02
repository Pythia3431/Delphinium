#!/usr/bin/python
import random
import time
from struct import pack

S2N_STATE_SIZE_IN_BYTES = 60
S2N_SERIALIZED_FORMAT_VERSION = 1
TLS12_PROTOCOL_VERS = 33
UNKNOWN_VERS = 0
TLS_RSA_WITH_RC4_128_MD5 = 0x0004
TLS_RSA_WITH_AES_256_CBC_SHA256 =  0x006B 
TLS_RSA_WITH_AES_256_GCM_SHA384 = 0x009D
TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 = 0xC02C
CIPHER_DICT = {
    TLS_RSA_WITH_RC4_128_MD5: "rsa with rc4 128, hash function md5",
    TLS_RSA_WITH_AES_256_CBC_SHA256: "rsa with aes 256 cbc, hash function sha 256",
    TLS_RSA_WITH_AES_256_GCM_SHA384: "rsa with aes 256 gcm, hash function sha384",
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384: "ecdhe ecdsa with aes 256 gcm, hash function sha 384",
}

PROTO_DICT = {
    UNKNOWN_VERS: "unknown version",
    TLS12_PROTOCOL_VERS: "tls 1.2"
}
IANA_LIST = [TLS_RSA_WITH_RC4_128_MD5, TLS_RSA_WITH_AES_256_GCM_SHA384,
 TLS_RSA_WITH_AES_256_CBC_SHA256, TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384]
PROTO_VERSIONS = [TLS12_PROTOCOL_VERS, UNKNOWN_VERS]
TIME_FIELD = 8 #(field in bytes)
# this value differs based on connection but it is mostly standard
TICKET_LIFETIME =  54000000000000
TLS_SECRET_SIZE = 48 #(field in bytes)  

S2N_STATE_SIZE_IN_BYTES = TLS_SECRET_SIZE + 12
test_length = S2N_STATE_SIZE_IN_BYTES * 8
max_msg_size = test_length
length_field_size = test_length.bit_length()
bit_vec_length = test_length + length_field_size 

BYTE_MASK = (1<<8)-1

def initialize_state_from_ticket(ticket):
    msg = ticket >> length_field_size
    state_obj = {}
    state_obj["proto_version"] = grabByte(msg,1)
    state_obj["iana"] = grabNBytes(msg, 2, 2)
    state_obj["ticket_lifetime"] = TICKET_LIFETIME
    ticket_time = grabNBytes(msg, 8, 4)
    return state_obj, ticket_time

def shortFormPrint(ticket):
    format_len = int("".join(reversed(ticket[:length_field_size])),2)
    msg_ticket = ticket[length_field_size:]
    format_version = "".join(reversed(msg_ticket[0:8]))
    protocol_version = "".join(reversed(msg_ticket[8:16]))
    crypto_protocol_num = "".join(reversed(msg_ticket[16:32]))
    time_on_ticket = "".join(reversed(msg_ticket[32:32 + 64]))
    random_tls_secret = "".join(reversed(msg_ticket[32 + 64:]))
    return "TLS Random Secret: {} |Time Field: {} |Cipher Suite: {} | Protocol Number: {} | Format Number: {} | Length of Ticket: {}".format(random_tls_secret, time_on_ticket, crypto_protocol_num, protocol_version, format_version, format_len)

def prettyPrintTicket(ticket):
    msg = ticket >> length_field_size
    format_version = grabByte(msg, 0)
    protocol_version = grabByte(msg,1)
    crypto_protocol_num = grabNBytes(msg, 2, 2)
    time_on_ticket = grabNBytes(msg, 8, 4)
    random_tls_secret = msg >> (length_field_size + (12*8)) 
    list_tls = []
    for i in range(0, random_tls_secret.bit_length(), 8):
        rand_elt = (random_tls_secret >> i) & ((1 << 8) -1)
        list_tls.append(chr(rand_elt))
    tls_secret = "".join(list_tls)
    valid_time_range = time_on_ticket + TICKET_LIFETIME
    start_time = str(time.ctime(time_on_ticket / 10**9))
    end_time = str(time.ctime(valid_time_range / 10**9))
    print("TICKET\nFormat Version: {}\nTLS Protocol Version: {}\nCipher Suite: {}\nValid start time: {}\nValid end time: {}\nTLS Random Secret: {}".format(format_version, PROTO_DICT[protocol_version], CIPHER_DICT[crypto_protocol_num], start_time, end_time, tls_secret))

def isSymbolic(value):
    return not type(value) is int and not type(value) is long

def grabByte(msg, byte_idx):
    return (msg >> (8 * byte_idx)) & BYTE_MASK 

def grabNBytes(msg, num_bytes, byte_idx):
    return (msg >> (8 * byte_idx)) & ((1 << (8 * num_bytes))-1)

def grabSymbolicByte(msg, byte_idx, solver):
    return solver._rshift(msg, 8*byte_idx) & BYTE_MASK

def grabNSymbolicBytes(msg, num_bytes, byte_idx, solver):
    return solver._rshift(msg, 8*byte_idx) & ((1 << (8 * num_bytes))-1)

# code assumption for message is that the "beginning" of the message starts at the 0 index
def checkFormat(full_msg, time, state):
    #  message must be S2N_STATE_SIZE_IN_BYTES bytes long
    if full_msg & ((1 << length_field_size)-1) != test_length:
        return 0
    msg = full_msg >> length_field_size    
    # first byte must match S2N_SERIALIZED_FORMAT_VERSION
    if grabByte(msg,0) != S2N_SERIALIZED_FORMAT_VERSION:
        return 0
     
    # protocol version from earlier point in time
    # this is stateful information
    if grabByte(msg, 1) != state["proto_version"]:
        return 0

    # iana value of cipher suite negotiated, this is also stateful information
    if grabNBytes(msg, 2, 2) != state["iana"]:
        return 0
    
    # checking expiry of the session ticket, this is also stateful
    time_on_ticket = grabNBytes(msg, 8, 4)
    # this is going to change every time it's called...
    if time_on_ticket > time:
        return 0
    if (time - time_on_ticket) > TICKET_LIFETIME:
        return 0

    return 1


def checkFormatSMT(full_msg, solver, time, state):
    compound_expr = solver._eq(full_msg & (1 << length_field_size)-1, test_length)
    msg = solver.extract(full_msg, full_msg.size()-1, length_field_size)
    compound_expr = solver._and(compound_expr, solver._eq(solver.extract(msg, 8-1, 0), S2N_SERIALIZED_FORMAT_VERSION))
    compound_expr = solver._and(compound_expr, solver._eq(grabNSymbolicBytes(msg,2,2,solver), state["iana"]))
    compound_expr = solver._and(compound_expr, solver._eq(grabSymbolicByte(msg,1,solver), state["proto_version"]))
    
    time_on_ticket = solver.extract(msg, 8*4 + TIME_FIELD*8 - 1, 8*4)
    compound_expr = solver._and(compound_expr, solver._ule(time_on_ticket, time))
    compound_expr = solver._and(compound_expr, solver._ule(time - time_on_ticket, TICKET_LIFETIME))

    return solver._if(compound_expr, solver.bvconst(1,2), solver.bvconst(0,2))

def makePaddedMessage():
    """
        message = [Random Secret (highest value)] | [time stamp] | [cipher suite] | [protocol version] | [format_version] | [length field]

    Where lowest order bits are at the end of the bit vector, Random Secret is 48 bytes, time stamp is 8 bytes, cipher suite is 2 bytes, protocol and format version are 1 byte. The length field specifies how large the bit vector is
    """

    state_obj = {}
    random_tls_secret = random.randint(0, 2**(8*TLS_SECRET_SIZE)-1)
    
    s2n_padded_msg = S2N_SERIALIZED_FORMAT_VERSION
    # use protocol version number for tls 1.2
    proto_chosen = PROTO_VERSIONS[random.randint(0, len(PROTO_VERSIONS)-1)]
    s2n_padded_msg = s2n_padded_msg | (proto_chosen << 8)
    state_obj["proto_version"] = proto_chosen
    iana_chosen = IANA_LIST[random.randint(0,len(IANA_LIST)-1)]
    s2n_padded_msg = s2n_padded_msg | (iana_chosen << (8 * 2))
    state_obj["iana"] = iana_chosen
    # add current time as ticket, 8 bytes long
    tls_curr_time = long(time.time() * 10**9) # make sure precision on this value fits in 8 bytes
    if tls_curr_time.bit_length() > 64:
        raise ValueError("Time value is outside of allowable 8 byte range, cannot form a correctly padded message")
    state_obj["ticket_lifetime"] = TICKET_LIFETIME
    state_obj["time object"] = tls_curr_time
    s2n_padded_msg = (tls_curr_time << (8 * 4)) | s2n_padded_msg
    
    msg_len = test_length
    return ((random_tls_secret << ((8 * 12) + length_field_size)) | (s2n_padded_msg << length_field_size) | msg_len, state_obj)
