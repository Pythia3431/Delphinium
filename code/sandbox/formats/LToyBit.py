import random
from math import floor, log

test_length = 19
hasIV = False
isStateful = False

unit_size = 1
ciphertextBits = test_length
paddingSizeBits = 4
paddingSizeMask = 2**paddingSizeBits - 1
maxPaddingBits = ciphertextBits - paddingSizeBits

def checkFormat(m):
    numPaddingBits = m & paddingSizeMask
    pad = (1 << numPaddingBits) - 1
    return ((m >> paddingSizeBits) & pad) == pad

def checkFormatSMT(m, solver):
    padSize = solver.extract(m, paddingSizeBits-1, 0) # padding size field
    is_valid = solver.false()
    pad = 1
    for i in range(1, maxPaddingBits+1):
        candidate_pad = solver.extract(m, paddingSizeBits+i-1, paddingSizeBits)
        is_valid = solver._if(solver._eq(padSize, i), #if
                              solver._eq(candidate_pad, #then
                                         solver.bvconst(pad, i)),
                              is_valid) # else
        pad = (pad << 1) | 1 # increase test pad length
    padding_fits = solver._ule(padSize, maxPaddingBits)
    return solver._if(solver._and(is_valid, padding_fits), solver.true(), solver.false())

def makePaddedMessage():
    # we can't handle zero padding.... so never make a message like that
    plaintext = random.randint(0, 2**(ciphertextBits - paddingSizeBits - 1)-1)
    # this isn't good if plaintext bits is a multiple 
    plaintextBits = plaintext.bit_length()
    paddingSize = ciphertextBits-plaintextBits-paddingSizeBits
    pad = (1 << paddingSize) - 1
    plaintext = (plaintext << paddingSize) | pad
    plaintext = (plaintext << paddingSizeBits) | paddingSize
    return plaintext & ((1 << ciphertextBits)-1)
