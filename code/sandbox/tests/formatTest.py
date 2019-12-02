import formats.CRC as format
import solver as solver_t
import time
import malformations
import oracle

bit_vec_length = format.bit_vec_length 
ORACLE = None

def testWithMalform():
    solver = solver_t.Z3Solver()
    # keep pulling out valid malleations, applying them
    # to a message and 
    m1 = solver.bv("m1", format.bit_vec_length)
    mall = solver.bv("p", format.bit_vec_length)
    solver.add(solver._eq(format.checkFormatSMT(m1, solver), solver.true()))
    indicator = True
       
    symbolic_res = solver.bv('symb_res', format.bit_vec_length)
    some_valid_msg = format.makePaddedMessage()
    solver.add(solver._eq(m1, some_valid_msg)) 
    solver.add(solver._eq(format.checkFormatSMT(malformations.xor_SMT(m1, solver, mall), solver)),solver.true())
    tested = 0
    while indicator and tested < 20:
        tested += 1
        print("Starting another test")
        if solver.check():
            valid_fields = solver.model("m1", "p")
            print("Passed check with message {}, malleation {}, and modified message {}".format(valid_fields["m1"], valid_fields["p"], malformations.xor(valid_fields["m1"],valid_fields["p"])))
            if not format.checkFormat(malformations.xor(valid_fields["m1"], valid_fields["p"])):
                print("Found disagreeing fields, please debug")
                import pdb; pdb.set_trace()
            else:
                solver.add(
                    solver._not(solver._eq(mall, valid_fields["p"]))
                )
        else:
            print("Failed test")
            indicator = False

    tested = 0 
    while indicator and tested < 20:
        tested += 1
        if solver.check():
            mall_dict = solver.model("p", "m1")
            # check real xor and truncate result against smt
            print("Tested so far: {}\nMessage: {}\nMalleate: {}\n".format(tested, mall_dict["m1"], mall_dict["p"]))
            realRes = malformations.xor(mall_dict["m1"], mall_dict["p"])
            solver.push()
            solver.add(solver._eq(symbolic_res, malformations.xor_SMT(m1, solver, mall)))
            solver.add(
                solver._eq(m1, mall_dict["m1"]),
                solver._eq(mall, mall_dict["p"]),
            )
            if solver.check():
                symb_result = solver.model("symb_res")["symb_res"]
                if symb_result != realRes:
                    indicator = False
                    print("Found a value that the real and symbolic results disagree on for xor and truncate!!")
                else:
                    print("This check passed, results are the same -- doing quick symbolic function test....")
                    solver.push()
                    solver.add(solver._not(solver._eq(symb_result, symbolic_res)))
                    if solver.check():
                        print("Symbolic function is actually not a function and can go to multiple values --- need to debug")     
                        import pdb; pdb.set_trace()
                    print("Passed check on input values") 
                    solver.pop()
                    print("Try and check format check result")
                    actualFormatResult = format.checkFormat(realRes)
                    solver.add(solver._not(solver._eq(format.checkFormatSMT(symbolic_res, solver), actualFormatResult)))
                    if solver.check():
                        print("Symbolic and real format functions do NOT agree on input message")
                        import pdb; pdb.set_trace()
                    else:
                        solver.pop()
            else:
                print("Something weird happened, symbolic function could not calculate a valid range element") 
                import pdb; pdb.set_trace()
            # pull out a nuew value for everything by adding an iterative constraint
            solver.add(
                solver._not(solver._eq(mall, mall_dict["p"])),
            )
        else:
            print("Could not find any more valid malleation and message pairs")
            indicator = False
    checkMall = solver_t.Z3Solver()
    m1_msg = checkMall.bv("m1", format.bit_vec_length)
    m2_msg = checkMall.bv("m2", format.bit_vec_length)
    second_mall = checkMall.bv("p_mall", format.bit_vec_length)
    
    checkMall.add(
        checkMall._eq(ORACLE.do_query_smt(m1_msg, checkMall, second_mall), True),
        checkMall._eq(ORACLE.do_query_smt(m2_msg, checkMall, second_mall), False),
        solver._eq(format.checkFormatSMT(m1_msg, checkMall),solver.true()),
        solver._eq(format.checkFormatSMT(m2_msg, checkMall),solver.true()),
    )
    print("Checking if there is a malleation that splits the set of accepting messages")
    if checkMall.check():
        malleation = checkMall.model("p_mall", "m1", "m2")
    else:
        print("Failed to find a dividing malleation")

def main():
    global ORACLE
    ORACLE = oracle.MalleationOracle(format.checkFormat, format.checkFormatSMT, malformations.xor, malformations.xor_SMT, malformations.xor_SMT)
    # check that a generated padded message passes a format check
    generated_msg = format.makePaddedMessage()
    
    if not format.checkFormat(generated_msg):  
        print("Failed basic test - generated messages do not pass the format check")
        return
    else:
        print("Passed real format check with randomly generated message")
    # do a basic test that the smt version agrees with the non smt 
    # version
    solver = solver_t.Z3Solver()
    bv = solver.bv("test_bv", bit_vec_length)
    solver.add(solver._eq(format.checkFormatSMT(bv,solver), solver.true()))
    solver.push() 
    # you want to be able to specify the time you can make a query at -- assumes a very powerful adversary
    if not solver.check():
        print("Format function does not create any passing messages")
        return
    else:
        print("Format has at leat one satisfiable solution")
    bv_model = solver.model("test_bv")["test_bv"]
    if not format.checkFormat(bv_model):
        print("checkFormat and the smt version of checkFormat disagree")
        return 
    else:
        print("Model for passing message also passes real format check")
    solver.pop()
    solver.add(solver._eq(bv, generated_msg))
    
    if not solver.check():
        print("smt version of checkFormat disagrees with padded message")
        return
    else:
        print("Random generated message passes the smt solver format check")
    print("Passed 3 basic format file tests.")
    print("Testing battery with malformation....")
    testWithMalform()

if __name__ == "__main__":
    main()
