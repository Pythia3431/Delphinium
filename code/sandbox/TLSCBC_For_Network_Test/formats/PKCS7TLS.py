import random
from math import ceil
##### ALL GLOBAL CONSTANTS #######
unit_size = 8
block_size = 16
test_length = block_size * unit_size
num_blocks = 2
max_msg_size = test_length * num_blocks
bit_vec_length = max_msg_size

# note that the ordering here matters and we need to make the real 
# and symbolic interfaces match, this is why we need the malleation
# check first
def checkFormat(padded_msg_with_mask):
    if type(padded_msg_with_mask) is list or type(padded_msg_with_mask) is tuple:
        padded_and_field_msg = padded_msg_with_mask[0]
        mask = padded_msg_with_mask[1]
    else:
        padded_and_field_msg = padded_msg_with_mask
        mask = 0
    # this is equivalent to the taint check done in the symbolic function  
    if mask & ((1 << test_length)-1) != 0:
        return 2
 
    # length of message  needs to be a multiple of the block size
    length = 256

    # message cannot be more than the professed length
    padded_msg = padded_and_field_msg
    if padded_msg > ((1 << length) - 1):
        return 0

    # PKCS7 padding check
    for i in range(0, block_size):
        correct_pad = True
        for num in range(i+1):
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
    
    # message must be smaller than the length
    message_bits = padded_and_field_msg
    # check for touching bits
    taint_check = mask & ((1 << test_length)-1)
    taint_check = solver._not(solver._eq(taint_check, 0))
 
    # PKCS7 paddng check
    padded_msg = padded_and_field_msg
    for i in range(0, block_size):
        correct_pad = solver.true()
        for num in range(i+1):
            added_val = solver.extract(padded_msg, (num + 1)*unit_size-1, num*unit_size)
            correct_pad = solver._and(correct_pad, solver._eq(solver.bvconst(i, unit_size), added_val))
        compound_expr = solver._or(compound_expr, correct_pad)
    return solver._if(taint_check, solver._if(compound_expr, solver.bvconst(1,2), solver.bvconst(0,2)), solver.bvconst(2,2))

def makePaddedMessage(padding_length=None):
    """ A CBC padded message is formatted as follows:
        msg_cbc = [ actual message | field specifying number of bits in actual message ]
        actual message = [potentially 0 beginning | IV | extra blocks | padded message block]
        NOTE: messages are 0 indexed s.t. msg_cbc[0,length_field_size] refers to the length of the message
        and the "first" block i.e. msg_cbc[length_field_size, length_field_size + block_size]
        contains the message's padding
    """
    if padding_length is not None and (padding_length > block_size or padding_length <= 0):
        raise ValueError("Padding length is not in acceptable range")
    if padding_length is None:
        length_msg_bytes = block_size - random.randint(0,block_size-1)
        padd_out = block_size - (length_msg_bytes % block_size)
    else:
        padd_out = padding_length
        length_msg_bytes = block_size - padd_out

    expand_str_chr = random.randint(0,2**(length_msg_bytes * unit_size) - 1) << (padd_out * unit_size)
    
    # ending is x of x so do the following....
    for i in range(padd_out):
        #push out by 0, 8, 16, ... and so on
        expand_str_chr += ((padd_out-1) << (unit_size * i))

    # add the IV last
    iv_block = random.randint(2**(test_length-1), (2**(test_length))-1)
    expand_str_chr = expand_str_chr | (iv_block << (test_length))
    # add the length field size to the beginning
    return expand_str_chr

if __name__ == '__main__':
    print(makePaddedMessage())
