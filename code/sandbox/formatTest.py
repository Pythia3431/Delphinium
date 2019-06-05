import formats.SessionTicketAWSS2N as format
import solver as solver_t
import time

bit_vec_length = format.bit_vec_length 

def main():
    # check that a generated padded message passes a format check
    generated_msg, state_obj = format.makePaddedMessage()
    
    if not format.checkFormat(generated_msg, int(time.time()), state_obj):  
        print("Failed basic test - generated messages do not pass the format check")
        return
    else:
        print("Passed real format check with randomly generated message")
    # do a basic test that the smt version agrees with the non smt 
    # version
    solver = solver_t.Z3Solver()
    bv = solver.bv("test_bv", bit_vec_length)
    time_var = solver.bv("time_var", format.TIME_FIELD)
    SLACK = 50
    solver.add(solver._eq(format.checkFormatSMT(bv,solver, time_var, state_obj), solver.bvconst(1,2)))
    current_t = int(time.time())
    solver.push() 
    # you want to be able to specify the time you can make a query at -- assumes a very powerful adversary
    solver.add(
        solver._ugt(time_var, current_t + SLACK),
        solver._ule(time_var, current_t + 100)
    )
    if not solver.check():
        print("Format function does not create any passing messages")
        return
    else:
        print("Format has at leat one satisfiable solution")
    bv_model = solver.model("test_bv")["test_bv"]
    bv_time = solver.model("time_var")["time_var"]
    if bv_time < time.time():
        print("Could not make a query because modeled time was in the past... try and increase the slack factor")
        return
    if not format.checkFormat(bv_model, bv_time, state_obj):
        print("checkFormat and the smt version of checkFormat disagree")
        return 
    else:
        print("Model for passing message also passes real format check")
    solver.pop()
    solver.add(solver._eq(bv, generated_msg), solver._eq(time_var, current_t +50))
    
    if not solver.check():
        print("smt version of checkFormat disagrees with padded message")
        return
    else:
        print("Random generated message passes the smt solver format check")
    print("Passed 3 basic format file tests.")

if __name__ == "__main__":
    main()
