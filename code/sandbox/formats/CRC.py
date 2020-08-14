import random
import math

POLYNOMIAL = 0x11D#0x104C11DB7 #0x13#0x18005#0x13#0x25#0x11D #0x104C11DB7
POLYNOMIAL_NO_LEADING = 0x1D #0x4C11DB7 #0x3 #0x8005#0x3#0x5#0x1D #0x4C11DB7 
CRC_SIZE = 8 #32 # 4
INPUT_SIZE = 8 if (CRC_SIZE % 8 == 0) else CRC_SIZE
INITIAL_VALUE = (1 << CRC_SIZE)-1
FINAL_VALUE = (1 << CRC_SIZE)-1 
plain_input = INPUT_SIZE*4
length_field_size = int(math.log(plain_input+CRC_SIZE,2)) + 1
test_length = plain_input + CRC_SIZE + length_field_size
hasIV = False
isStateful = False
""" Validly formatted message looks like the following:
    [n bit message field] | [ x bit CRC field ] | [total_msg_length bit field]
    the total_msg_length field is always equal to n (the number of bits in the message)
    Version of CRC used here supports bit vector inputs of length
    <= n bits long. Inversion is used to give different checksums
    for integers with the same numerical ending ie '0x01' vs '0x00 0x01'. The output is also inverted at the end. Check www.sunshine2k.de/coding/javascript/crc/crc_js.html and associated resources for more details. Support is offered for every functionality on the preceding website besides input/output reflection.  
"""

def parseCRC(msg):
    length_field = msg & ((1 << length_field_size)-1)
    crc_value = (msg >> length_field_size)& ((1 << CRC_SIZE)-1)
    msg_value = msg >> (length_field_size + CRC_SIZE)
    return {
        'length': length_field,
        'crc': crc_value,
        'msg': msg_value,
    }

def printMessage(msg):
    fields = parseCRC(msg)
    print_str = "Integer Message Representation: {}\nMessage: {}\nCRC:{}\nLength:{}\n".format(msg, hex(fields['msg']), hex(fields['crc']), fields['length'])
    print(print_str)

def calculateCRCNormal(msg, msg_len_input_size, init=INITIAL_VALUE, final=FINAL_VALUE):
    shift_reg = init
    for i in range((msg_len_input_size-1)*INPUT_SIZE, -INPUT_SIZE, -INPUT_SIZE):
        byte_msg = (msg >> i) & ((1 << INPUT_SIZE)-1)
        shift_reg  = shift_reg ^ (byte_msg << (CRC_SIZE - INPUT_SIZE))
        for j in range(INPUT_SIZE):
            if (shift_reg >> (CRC_SIZE-1)) & 1:
                shift_reg = (shift_reg << 1) ^ POLYNOMIAL
            else:
                shift_reg = (shift_reg << 1)
        
        assert shift_reg < (1 << CRC_SIZE)
    
    shift_reg = shift_reg ^ final
    return shift_reg

def checkFormat(msg):
    # extract first n bits
    msg_length = (msg & ((1 << length_field_size)-1)) - CRC_SIZE

    msg_length_input = (plain_input + (INPUT_SIZE - 1)) // INPUT_SIZE

    msg = msg >> length_field_size
    crc_value_from_msg = msg & ((1 << CRC_SIZE)-1)
    actual_msg = msg >> CRC_SIZE 
    or_sum = False 
    for i in range(1,msg_length_input+1):
        calc_crc_value = calculateCRCNormal(actual_msg, i)
        or_sum = or_sum or (calc_crc_value == crc_value_from_msg and msg_length == (INPUT_SIZE*i) and ((actual_msg >> (INPUT_SIZE*i))  == 0)) 
    return or_sum


def calculateCRCSymbolic(actual_msg, msg_len_input_size, solver): 
    accumulator = solver.bvconst(INITIAL_VALUE, CRC_SIZE)
    for i in range((msg_len_input_size-1)*INPUT_SIZE, -INPUT_SIZE, -INPUT_SIZE):
        select_input = solver.extract(actual_msg, i + INPUT_SIZE - 1, i)
        assert(select_input.size() == INPUT_SIZE)
        if select_input.size() < CRC_SIZE:
            select_input = solver.concat(select_input, solver.bvconst(0,CRC_SIZE - select_input.size()))
        
        assert(select_input.size() == CRC_SIZE)
        accumulator = accumulator ^ select_input
        for j in range(INPUT_SIZE): 
            accumulator = solver._if(solver._eq(solver._rshift(accumulator,(CRC_SIZE - 1))&1, 1), solver._lshift(accumulator, 1) ^ POLYNOMIAL, solver._lshift(accumulator, 1))

    accumulator = accumulator ^ FINAL_VALUE
    return accumulator

def checkFormatSMT(full_msg, solver):
    length_msg = solver.extract(full_msg, length_field_size -1,0) - CRC_SIZE
   
    msg = solver.extract(full_msg, full_msg.size()-1, length_field_size)

    actual_msg = solver.extract(msg, msg.size()-1, CRC_SIZE)
    crc_check = solver.extract(msg, CRC_SIZE-1,0)
    
    l = (plain_input + (INPUT_SIZE - 1)) // INPUT_SIZE
    or_sum = solver.false()
    for i in range(1,l + 1): 
        accumulator = calculateCRCSymbolic(actual_msg, i, solver)
        or_sum = solver._or(or_sum, solver._and(solver._and(solver._eq(length_msg, i*INPUT_SIZE), solver._eq(accumulator, crc_check)), solver._eq(solver._rshift(actual_msg, i*INPUT_SIZE),0)))
    return or_sum

def makePaddedMessage():
    """ Valid message contains a message followed by n bits of
        a crc checksum and a field that expresses the length
       of the message + the checksum 
    """
    number_bytes = random.randint(1, plain_input // INPUT_SIZE)
    random_msg = random.randint(0,(2**(number_bytes*INPUT_SIZE))-1)
    random_crc = calculateCRCNormal(random_msg, number_bytes)
    
    random_msg = (random_msg << CRC_SIZE) | random_crc

    return (random_msg << length_field_size) | ((number_bytes*INPUT_SIZE) + CRC_SIZE)
