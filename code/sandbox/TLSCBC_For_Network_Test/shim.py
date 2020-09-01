import os
import sys
import socket
import struct
import hashlib
from multiprocessing import Process, Queue
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

# import a format concrete check function as format_check(msg) -> bool
IV_LEN = 16
DEBUG = True
from formats.PKCS7TLS import checkFormat as format_check_unwrapped
from formats.PKCS7TLS import max_msg_size

def format_check(msg):
    r = format_check_unwrapped(msg)
    if r == 0:
        return False
    elif r == 1:
        return True
    else:
        raise ValueError("format check returned error {}".format(r))

SERVER_ADDR = 'localhost'
SERVER_PORT = 8080
MAX_CT = 1024

def pack(i, size=None):
    b = []
    while i != 0:
        b.insert(0, i & ((1<<8)-1))
        i >>= 8
        if size is not None:
            size -= 1
    if size is not None:
        while size > 0:
            b.insert(0, 0)
            size -= 1
    return bytearray(b)

def unpack(b):
    i = 0
    for byte in b:
        i <<= 8
        i |= byte
    return i

class Server:
    def __init__(self, key):
        self.key = key
        self.ciphers = {}

    def check(self, ct, iv):
        backend = default_backend()
        cipher = Cipher(algorithms.AES(self.key), modes.CBC(iv), backend=backend)
        decryptor = cipher.decryptor()
        try:
            pt = decryptor.update(ct) + decryptor.finalize()
        except Exception as e:
            print("Error decrypting")
            print(len(ct))
            raise e
        check_int = unpack(bytearray(iv)+bytearray(pt))
        check_int = (check_int << 9) | (((len(pt)+IV_LEN)*8) & ((1<<9)-1))
        if DEBUG:
            print("message to check (server)")
            print(hex(check_int >> 9))
            print("length: {}".format(len(pt)+IV_LEN))
        return format_check(check_int)

    def encrypt(self, pt, iv):
        backend = default_backend()
        cipher = Cipher(algorithms.AES(self.key), modes.CBC(iv), backend=backend)
        encryptor = cipher.encryptor()
        return bytearray(encryptor.update(pt) + encryptor.finalize())

def server(srvr):
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
        try:
            s.bind((SERVER_ADDR, SERVER_PORT))
        except socket.error as e:
            print(e)
            return
        while True:
            data, addr = s.recvfrom(MAX_CT)
            if not data:
                break
            iv = data[:IV_LEN]
            ct = data[IV_LEN:]
            if DEBUG:
                print("IV {}".format(hex(unpack(bytearray(iv)))))
                print("ct {}".format(hex(unpack(bytearray(ct)))))
            resp = None
            try:
                res = srvr.check(ct, iv)
            except Exception as e:
                print(e)
                resp = bytearray(data)+bytearray([255])
            if resp is None:
                if res:
                    resp = bytearray(data)+bytearray(b'\xf0')
                else:
                    resp = bytearray(data)+bytearray(b'\x0f')
            s.sendto(resp, addr)

class Client:
    def __init__(self, ct, oracle_addr=SERVER_ADDR, oracle_port=SERVER_PORT):
        self.ct = ct
        self.oracle = (oracle_addr, oracle_port)
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.s = s

    def done(self):
        try:
            self.s.shutdown()
        except:
            pass
        try:
            self.s.close()
        except:
            pass

    def __del__(self):
        try:
            self.s.close()
        except:
            pass

    def maul(self, ct, mstr):
        # assumes IV is at top
        size = max_msg_size
        mstr & ((1 << (size+18))-1)
        low_trunc = mstr & ((1<<9)-1)
        mstr >>= 9
        high_trunc = mstr & ((1<<9)-1)
        mstr >>= 9
        ct = ct & ((1 << (size-high_trunc))-1)
        ct = ct >> low_trunc
        assert ((size-high_trunc-low_trunc) % 128) == 0
        assert mstr < 2**(size-low_trunc-high_trunc)
        ct = ct ^ mstr
        if DEBUG:
            print("ht: {}; lt: {}".format(high_trunc, low_trunc))
            print("ct: {}".format(ct.bit_length()))
            print("result size: {}".format(int((size-high_trunc-low_trunc)/8)))
        return ct, int((size-high_trunc-low_trunc)/8)

    def send(self, mall_str):
        ct_int = unpack(bytearray(self.ct))
        ct_mall_int, size = self.maul(ct_int, mall_str)
        ct_bytes = pack(ct_mall_int, size)
        if DEBUG:
            print("IV {}".format(hex(unpack(ct_bytes[:IV_LEN]))))
            print("CT {}".format(hex(unpack(ct_bytes[IV_LEN:]))))
        while True:
            self.s.sendto(ct_bytes, self.oracle)
            resp, _ = self.s.recvfrom(MAX_CT+1)
            resp_mall = resp[:-1]
            resp_res = resp[-1]
            if resp_mall != ct_bytes:
                continue
            if resp_res == b'\xf0':
                return True, mall_str
            elif resp_res == b'\x0f':
                return False, mall_str
            else:
                print("Server issued bad response")
                return None

if __name__ == '__main__':
    realM_int = 34235213454539002068883755547033564507831270130084104285391466877355590688709888 >> 9
    realM = pack(realM_int & ((1<< (16*8))-1))
    iv = pack(realM_int >> 16*8)
    #key = os.urandom(32)
    key = b'`\xbd\xfa\x05\xe5K_\xd8L_P\x81.\xb1\xce,\xd2\xa5X\xacY\x06\x1a\xaf\xee\x80,\xedC\xcby2'
    srvr = Server(key)
    print("iv = {}".format(iv))
    print("ct = {}".format(iv+srvr.encrypt(realM, iv)))
    server(srvr)
