import random
from math import ceil, log, floor
##### ALL GLOBAL CONSTANTS #######
unit_size = 8
block_size = 16
test_length = block_size * unit_size
num_blocks = 3
max_msg_size = test_length * num_blocks
length_field_size = max_msg_size.bit_length()
bit_vec_length = max_msg_size + length_field_size

def checkFormat(padded_msg_with_mask):
    if type(padded_msg_with_mask) is list or type(padded_msg_with_mask) is tuple:
        padded_and_field_msg = padded_msg_with_mask[0]
        mask = padded_msg_with_mask[1]
    else:
        padded_and_field_msg = padded_msg_with_mask
        mask = 0
    if mask & ((1 << test_length)-1) != 0:
        return 2
 
    # length of message  needs to be a multiple of the block size
    length = padded_and_field_msg & ((1 << length_field_size) - 1)
    if (padded_and_field_msg & ((1 << length_field_size) - 1)) % test_length != 0:
        return 0
    # this check is needed for the IV block --- we can't submit a query without at least two blocks. an error that occurs because of this is not format related but an error in the cryptographic software 
    if length <= test_length:
        return 2

    # message cannot be longer than the professed length
    padded_msg = padded_and_field_msg >> length_field_size
    if padded_msg > ((1 << length) - 1):
        return 0

    # PKCS7 padding check
    for i in range(1, block_size+1):
        correct_pad = True
        for num in range(i):
            added_val = padded_msg >> (num*unit_size)
            added_val = added_val & ((1 << unit_size) - 1)
            correct_pad = correct_pad and (i == added_val)
        if correct_pad:
            return 1
    return 0

def checkIfSymbolic(value):
    is_symb = not type(value) is long and not type(value) is int
    return is_symb
 
def checkFormatSMT(padded_msg_with_mask, solver):
    if type(padded_msg_with_mask) is list or type(padded_msg_with_mask) is tuple:
        padded_and_field_msg = padded_msg_with_mask[0]
        mask = padded_msg_with_mask[1]
    else:
        padded_and_field_msg = padded_msg_with_mask
        mask = 0
    compound_expr = solver.false()
    length_mask = (1 << length_field_size)-1
    # length must be multiple of the block size in bits
    length = padded_and_field_msg & length_mask
    length_check = solver._eq(solver._mod(length, test_length), 0)
    
    # length must be larger than one block because queries need an IV 
    iv_block_check = solver._and(length_check, solver._ugt(length, test_length))

    # message must be smaller than what is specified in the length field
    message_bits = solver._rshift(padded_and_field_msg, length_field_size)
    length_check = solver._and(length_check, solver._ule(message_bits, (1 << length)-1))
    length_check = solver._and(length_check, solver._ule(length, max_msg_size))
    # check for touching bits
    maul_check = mask & ((1 << test_length)-1)
    maul_check = solver._not(solver._eq(maul_check, 0))
 
    # PKCS7 paddng check
    padded_msg = solver.extract(padded_and_field_msg, (num_blocks*test_length) + length_field_size - 1, length_field_size)
    for i in range(1, block_size+1):
        correct_pad = solver.true()
        for num in range(i):
            added_val = solver.extract(padded_msg, (num + 1)*unit_size-1, num*unit_size)
            correct_pad = solver._and(correct_pad, solver._eq(solver.bvconst(i, unit_size), added_val))
        compound_expr = solver._or(compound_expr, correct_pad)
    compound_expr = solver._and(compound_expr, length_check)
    return solver._if(solver._or(maul_check, solver._not(iv_block_check)), solver.bvconst(2,2), solver._if(compound_expr, solver.bvconst(1,2), solver.bvconst(0,2)))


def makePaddedMessage(padding_length=None):
    """ A CBC padded message is formatted as follows:
        msg_cbc = [ actual message | field specifying number of bits in actual message ]
        actual message = [potentially 0 beginning | IV | extra blocks | padded message block]
        NOTE: messages are 0 indexed s.t. msg_cbc[0,length_field_size] refers to the length of the message
        and the "first" block i.e. msg_cbc[length_field_size, length_field_size + block_size]
        contains the message's padding
    """
    if padding_length is not None and (padding_length > block_size or padding_length <= 0):
        raise ValueError("Padding length must be in 1..{}".format(block_size))
    if padding_length is None:
        msg = random.randint(0, 2**(test_length - 1*unit_size)-1)
        msg_length = int(floor(log(msg, 2**unit_size)))+1
        padding_length = block_size - msg_length
    else:
        msg = random.randint(0, 2**(test_length-padding_length*unit_size)-1)
        msg_length = block_size - padding_length

    pad = padding_length
    padded_msg = msg
    for _ in range(padding_length):
        padded_msg <<= unit_size
        padded_msg |= pad    

    # add the beginning blocks
    add_blocks = random.randint(0, num_blocks-2)
    if num_blocks -2 < 0:
        raise ValueError("Number of blocks must at least be large enough for the IV and padding block")
    for i in range(add_blocks):
        adding_block = random.randint(0, 2**(test_length))
        padded_msg = padded_msg | (adding_block << (test_length * (1 + i)))

    # add the IV to be the highest order bits
    iv_block = random.randint(2**(test_length-1), (2**(test_length))-1)
    padded_msg = padded_msg | (iv_block << (test_length * (add_blocks + 1)))
    # add the length field size to the beginning
    return (padded_msg << length_field_size) | ((add_blocks + 2) * test_length)
