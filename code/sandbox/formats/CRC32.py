import random
import math
POLYNOMIAL = 0x104C11DB7

CRC_SIZE = 32
test_length = 32
message_length = CRC_SIZE + test_length
length_field_size = int(math.log(test_length + CRC_SIZE,2)) + 1
bit_vec_length = test_length + CRC_SIZE + length_field_size
""" Validly formatted message looks like the following:
    [n bit message field] | [ x bit CRC field ] | [total_msg_length bit field]
    the total_msg_length field is always >= x and is up to x + n     Because CRC processes input in bytes, the total_msg input 
    field - x bits of CRC must be a multiple of 8
    Version of CRC used here supports bit vector inputs of length
    <= n bits long. It uses inversion to give different checksums
    for integers with the same numerical ending ie '0x01' vs '0x00 0x01' and also inverts the output at the end. Check www.sunshine2k.de/coding/javascript/crc/crc_js.html and associated resources for more details. The input and output here are NOT assumed to be reflected.  
"""

def calculateCRCNormal(msg, msg_len_bits):
    msg_len_bytes = (msg_len_bits - CRC_SIZE) / 8
    shift_reg = (1 << CRC_SIZE)-1
    # will be specified by the length field -- 
    # this will need to be unrolled in the solver
    for i in range((msg_len_bytes-1)*8, -8, -8):
        byte_msg = (msg >> i) & ((1 << 8)-1)
        shift_reg  = shift_reg ^ (byte_msg << 24)
        for j in range(8):
            if (shift_reg >> (CRC_SIZE-1)) & 1:
                shift_reg = (shift_reg << 1) ^ POLYNOMIAL
            else:
                shift_reg = shift_reg << 1
        
        #cannot be 33 bits long
        assert shift_reg < (1 << 33)
       
    shift_reg = shift_reg ^ ((1 << CRC_SIZE)-1)
    return shift_reg

def checkFormat(msg):
    # extract first n bits
    msg_length = msg & ((1 << length_field_size)-1)
    msg = msg >> length_field_size
    crc_value_from_msg = msg & ((1 << CRC_SIZE)-1)
    actual_msg = msg >> CRC_SIZE
    calc_crc_value = calculateCRCNormal(actual_msg, msg_length)
    # need to also ensure length is in bytes
    return (calc_crc_value == crc_value_from_msg) and ((msg_length - CRC_SIZE)%8 == 0)

# can this only be done for fixed length?? Potentially
def checkFormatSMT(full_msg, solver):
    # extract bits of the message
    length_msg = solver.extract(full_msg, length_field_size -1,0)
 
    msg = solver.extract(full_msg, full_msg.size()-1, length_field_size)

    actual_msg = solver.extract(msg, msg.size()-1, CRC_SIZE)
    crc_check = solver.extract(msg, CRC_SIZE-1,0)

    # need to unroll this actual_msg here for length_field_size
    or_chain = False
    # count up by 8's
    for l in range(8,actual_msg.size()+1,8):
        accumulator = (1 << CRC_SIZE) - 1
        byte_mask = 255

        for i in range(l-8, -1,-8):
            accumulator = accumulator ^ (((actual_msg >> i) & byte_mask) << 24)
            for j in range(8): 
                accumulator = solver._if(solver._eq((accumulator >> (CRC_SIZE - 1))&1, 1), solver._lshift(accumulator, 1) ^ POLYNOMIAL, solver._lshift(accumulator, 1))

        accumulator = accumulator ^ ((1 << CRC_SIZE)-1)
        accumulator = solver._and(solver._eq(accumulator, solver.extend(crc_check,test_length - CRC_SIZE)), solver._eq(length_msg, l + CRC_SIZE))
        or_chain = solver._or(or_chain, accumulator)
    return or_chain

def makePaddedMessage():
    """ Valid message contains a message followed by n bits of
        a crc 32 checksum and a field that expresses the length
       of the message + the checksum 
    """
    # making a message that is 64 bits long, w/o CRC and length field size
    random_msg = random.randint(0,(2**test_length)-1)
    next_highest_byte = (random_msg.bit_length() + 7)/ 8
    msg_length = random.randint(next_highest_byte*8 + CRC_SIZE, test_length + CRC_SIZE)
    random_crc = calculateCRCNormal(random_msg, msg_length)
    
    random_msg = (random_msg << CRC_SIZE) | random_crc
    
    return random_msg << length_field_size | msg_length
