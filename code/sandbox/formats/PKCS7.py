import random
from math import log, floor
##### ALL GLOBAL CONSTANTS #######
unit_size = 8
block_size = 3

test_length = block_size * unit_size
hasIV = False
isStateful = False

def checkFormat(padded_msg):
    compound_expr = False
    for i in range(1, block_size+1):
        correct_pad = True
        for num in range(i):
            added_val = padded_msg >> (num*unit_size)
            added_val = added_val & ((1 << unit_size) - 1)
            correct_pad = correct_pad and (i == added_val)
        compound_expr = compound_expr or correct_pad
    return compound_expr

def checkFormatSMT(padded_msg, solver):
    compound_expr = solver.false()
    for i in range(1, block_size+1):
        correct_pad = solver.true()
        for num in range(i):
            added_val = solver.extract(padded_msg, (num + 1)*unit_size-1, num*unit_size)
            correct_pad = solver._and(correct_pad, solver._eq(solver.bvconst(i, unit_size), added_val))
        compound_expr = solver._or(compound_expr, correct_pad)
    return compound_expr

def makePaddedMessage(padding_length=None):
    if padding_length is None:
        msg = random.randint(0, 2**(test_length - 1*unit_size) - 1)
        msg_length = int(floor(log(msg, 2**unit_size)))+1
        padding_length = block_size - msg_length
    else:
        if padding_length > block_size or padding_length <= 0:
            raise ValueError("Padding length must be in 1..{}".format(block_size))
        msg = random.randint(0, 2**(test_length - padding_length*unit_size)-1)
        msg_length = block_size - padding_length
    pad = padding_length
    padded_msg = msg
    for _ in range(padding_length):
        padded_msg <<= unit_size
        padded_msg |= pad
    return padded_msg
