#!/usr/bin/python
import oracle
import formats.PKCS7 as format
from malformations import xor as malform
import solver as solver_t
import time
import os

LOGFILE="humanPKCS7_"
DATFILE="humanPKCS7_"
CTR = 0 

realMessage = 105514930645558608415723679651132212742
ORACLE = oracle.Oracle(format.checkFormat, format.checkFormatSMT, malform)

try:
    bit_vec_length = format.test_length * format.num_blocks
except AttributeError:
    bit_vec_length = format.test_length


def addQueryAndApprox(solver, fm, malleation):
    start_t = time.time()
    result = ORACLE.do_query(realMessage,malleation)
    add_res = solver._bool(result)
     
    # cut set 
    solver.push()
    solver.add(solver._not(solver._eq(ORACLE.do_query_smt(fm, solver, malleation), add_res)))
    cut_set = solver.approxmc()[0]
    solver.pop()
    # updated set
    solver.add(
        solver._eq(ORACLE.do_query_smt(fm, solver, malleation), add_res)
    )
    updated_set = solver.approxmc()[0]
    knownbitsize = solver.knownbits("fm")
    duration = time.time() - start_t
    with open(LOGFILE, "a") as log_w:
        log_w.write("{} {}\n".format(malleation, result))
    with open(DATFILE, "a") as dat_w:
        dat_w.write("{} {} {} {}\n".format(2**knownbitsize.count("?"), updated_set, cut_set, duration))
    return result

def addQueryNoApprox(solver, fm, malleation):
    result = ORACLE.do_query(realMessage,malleation)
    add_res = solver._bool(result)

    solver.add(
        solver._eq(ORACLE.do_query_smt(fm, solver, malleation), add_res)
    )

# produce a sequence of malleation strings, mimic oracle access to a endpoint
def pkcs7attack(realM, m1, solver):    
    format_header = "Run of human attack on message {}\nKnown Solver Bits | Updated Set | Cut Set | Time for Size Checks\n".format(realM)
    with open(LOGFILE ,"w") as logfile:
        logfile.write(format_header)
    with open(DATFILE ,"w") as datfile:
        datfile.write(format_header)
    list_of_queries = []
    # first, figure out the length jumping ahead by bytes
    padding_length = -1
    for i in range(1,16):
        mall_string = 2**(8*i)
        # add query to solver
        res = addQueryAndApprox(solver, m1, mall_string) 
        # if result turns returns true then you've found the length -- unless you get unlucky which we'll talk about in a minute
        if res:
            # you passed the padding bit most likely so you can stop
            padding_length = i
            break
    # now from this point in, you can keep flipping one bit over 
    current_msg = ['?'] * (bit_vec_length // format.unit_size)
    
    for i in range(padding_length):
        current_msg[i] = padding_length 

    # fill in the padding 
    currentPaddString = padding_length + 1
    nonPaddCtr = 0
    malleation_str = 0 
    
    for i in range(currentPaddString-1):
        malleation_str += (current_msg[i] ^ currentPaddString) << (8 *i)

    while currentPaddString <= 16:
        # increment counter that flips a bit over wait until you receive a true to advance
        malleation_str += (nonPaddCtr << (8*(currentPaddString - 1)))
        if addQueryAndApprox(solver, m1, malleation_str):
            # if you found this you have the next byte in the string 
            current_msg[currentPaddString-1] = nonPaddCtr ^ currentPaddString
            currentPaddString += 1
            nonPaddCtr = 0
            # now you need to update the malleation string you are going to test
            malleation_str = 0
            for i in range(currentPaddString - 1):
                malleation_str += (int(current_msg[i]) ^ currentPaddString) << (8 *i)
        else:
            # take out what you added in and continue the attack
            malleation_str -= (nonPaddCtr << (8*(currentPaddString-1)))
            nonPaddCtr = nonPaddCtr + 1
    # query and make sure there is only one malleation string in the model of the solver
    if solver.check():
        finalmessage = solver.model("fm")
        print("{}".format(bin(finalmessage)))
        solver.add(m1 != finalmessage)
        if solver.check():
            print("Offending message: {}".format(solver.model("fm")))
            raise Error("Attack failed to reduce cut set down to one message")
        else:
            print("Attack was a success, finishing...")
    else:
        print("Even one message failed to pass checks! Error")
        raise Error("Attack failed :( ")

     
def main():
    global LOGFILE
    global DATFILE
    global CTR
    while os.path.exists(LOGFILE+str(CTR)+".log") or os.path.exists(DATFILE+str(CTR)+".dat"):
        CTR = CTR + 1
    LOGFILE = LOGFILE+str(CTR)+".log"
    DATFILE = DATFILE+str(CTR)+".dat"
    
    finalS = solver_t.Z3Solver()
    fm = finalS.bv('fm', bit_vec_length)
    if not realMessage:
        print("Message must not be none. Program exiting...")
        sys.exit(1)
    # add constraint to final solver
    finalS.add(format.checkFormatSMT(fm, finalS))
    pkcs7attack(realMessage, fm, finalS)
    return 


if __name__ == "__main__":
    main()
