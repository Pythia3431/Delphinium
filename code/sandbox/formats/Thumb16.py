import random
from solver import Z3Solver as libsolver
test_length = 16

# http://infocenter.arm.com/help/topic/com.arm.doc.ddi0210c/DDI0210B.pdf
# register names are 3 bits

def checkFormat(instr):
    top8 = instr >> 8
    top7 = instr >> 9
    top6 = instr >> 10
    top5 = instr >> 11
    top4 = instr >> 12
    top3 = instr >> 13
    if top3 in (0b000, 0b001, 0b011):
        return True
    if top4 in (0b0101, 0b1000, 0b1001, 0b1010, 0b1100, 0b1101, 0b1111):
        return True
    if top5 in (0b01001, 0b11000):
        return True
    if top6 in (0b000111, 0b010000, 0b010001):
        return True
    if top7 in (0b1011010, 0b1011110):
        return True
    if top8 in (0b10110000, 0b11011111):
        return True
    return False

def checkFormatSMT(instr, solv):
    cons = solv.false()
    #msr 0 0 0 op2 offset5 Rs Rd                         000*************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 13), solv.bvconst(0b000, 16))
    )
    #add 0 0 0 1 1 1 op1 Rn/offset3 Rs Rd                000111**********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 10), solv.bvconst(0b000111, 16))
    )
    #imm 0 0 1 op2 Rd offset8                            001*************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 13), solv.bvconst(0b001, 16))
    )
    #alu 0 1 0 0 0 0 op4 Rs Rd                           010000**********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 10), solv.bvconst(0b010000, 16))
    )
    #bx+ 0 1 0 0 0 1 op2 h1 h1 Rs/Hs Rd/Hd               010001**********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 10), solv.bvconst(0b010001, 16))
    )
    #plr 0 1 0 0 1 Rd word8                              01001***********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 11), solv.bvconst(0b01001, 16))
    )
    #lsr 0 1 0 1 L B 0 Ro Rb Rd                          0101**0*********
    #lsb 0 1 0 1 H S 1 Ro Rb Rd                          0101**1*********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 12), solv.bvconst(0b0101, 16))
    )
    #lsi 0 1 1 B L offset5 Rb Rd                         011*************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 13), solv.bvconst(0b011, 16)) 
    )
    #lsh 1 0 0 0 L offset5 Rb Rd                         1000************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 12), solv.bvconst(0b1000, 16)) 
    )
    #slr 1 0 0 1 L Rd word8                              1001************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 12), solv.bvconst(0b1001, 16))
    )
    #lea 1 0 1 0 sp1 Rd word8                            1010************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 12), solv.bvconst(0b1010, 16)) 
    )
    #spa 1 0 1 1 0 0 0 0 s1 word7                        10110000********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr,  8), solv.bvconst(0b10110000, 16))
    )
    #p/p 1 0 1 1 L 1 0 R Rlist                           1011*10*********
    cons = solv._or(cons,
        solv._or(
          solv._eq(solv._rshift(instr,9), solv.bvconst(0b1011010, 16)),
          solv._eq(solv._rshift(instr,9), solv.bvconst(0b1011110, 16))
        )
    )
    #mls 1 1 0 0 L Rb Rlist                              1100************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 12), solv.bvconst(0b1100, 16)) 
    )
    #cbr 1 1 0 1 cond4 softset8                          1101************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 12), solv.bvconst(0b1101, 16)) 
    )
    #int 1 1 0 1 1 1 1 1 value8                          11011111********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr,  8), solv.bvconst(0b11011111, 16))
    )
    #ubr 1 1 1 0 0 offset11                              11100***********
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 11), solv.bvconst(0b11100, 16)) 
    )
    #lbl 1 1 1 1 H offset11                              1111************
    cons = solv._or(cons,
        solv._eq(solv._rshift(instr, 12), solv.bvconst(0b1111, 16))
    )
    #
    #Illegal instructions
    #                                                  1011001*********
    #                                                  1011101*********
    #                                                  10111000********
    #                                                  10110010********
    #                                                  10110001********
    #                                                  10111001********
    #                                                  10111010********
    #                                                  10111011********
    #                                                  ...
    return cons

def makePaddedMessage():
    if valid:
        return 0b1101111101010101
    else:
        return random.randrange(0, 2**16)
