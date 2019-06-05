import random

unit_size = 1
test_length = 128
ciphertextBits = 128
paddingSizeBits = 7
paddingSizeMask = 2**paddingSizeBits - 1

maxPaddingBits = (2**paddingSizeBits) - paddingSizeBits

totalPaddingBits = paddingSizeBits + maxPaddingBits

def checkFormat(term, solver=None):
    if type(term) is int or type(term) is long:
        numPaddingBits = term & paddingSizeMask
        commonTerm = (1 << numPaddingBits) - 1
        return (term >> paddingSizeBits) & commonTerm == commonTerm
    else:
        numBits = solver.extract(term,paddingSizeBits-1,0)
        oldTerm = solver.true()
        numVal = 1 # padding string
        # for each possible padding string size value (small to large)
        #   select the bits by index which should hold the padding string
        #   assert that if numBits is that size
        #       the selected range should be equal to numVal
        #   else
        #       this must have been true for some smaller pad size value
        for i in xrange(1,ciphertextBits-paddingSizeBits+1): # each pad string size
            ones = solver.extract(term,paddingSizeBits+i-1,paddingSizeBits)
            oldTerm = solver._if(solver._eq(numBits, i), solver._eq(ones, solver.bvconst(numVal,i)), oldTerm)
            numVal = (numVal << 1) | 1
        # ensure numbits doesn't exceed available space
        t1 = solver._ule(numBits,ciphertextBits-paddingSizeBits)
        return solver._and(t1,oldTerm)

def makePaddedMessage(numberPaddingBits=-1):
    if numberPaddingBits == -1:
    	realOneBits = random.randint(0, maxPaddingBits)
    else:
        if numberPaddingBits > maxPaddingBits:
            raise ValueError("Number of Padding Bits supplied is too high")
	realOneBits = numberPaddingBits
    realPaddingBits = realOneBits + paddingSizeBits
    realPlaintextBits = ciphertextBits - realPaddingBits
    # Make a random plaintext of size "realPlaintextBits"
    plaintext = random.randint(0, 2**(realPlaintextBits)-1)
    # Generate a padding string of size "realPaddingBits" consisting of
    # "realOneBits" 1 bits, followed by "paddingSizeBits" indicating length
    if realOneBits <= 0:
        paddingString = 0
    else:
        paddingString = (2**(realOneBits) - 1) << paddingSizeBits
        paddingString |= realOneBits
    # Add this to the plaintext
    plaintext = (plaintext << realPaddingBits) | paddingString
    return plaintext & ((1 << ciphertextBits) - 1)
