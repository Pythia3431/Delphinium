#!/usr/bin/python
import solver as solver_t
import formats.PKCS7 as format
import oracle
from multiprocessing import Process, Queue
from  malformations import xor as malform
import time
import sys

ORACLE = oracle.Oracle(format.checkFormat, format.checkFormatSMT, malform)
write_res = ""
try:
    bit_length = format.test_length
except:
    raise Error("Format does not provide bit vector length")


def addAndCheck(filename):
    solver = solver_t.Z3Solver()
    msg = solver.bv("msg", bit_length)
    with open(filename, "r") as file_r:
        lines = file_r.readlines()
        for line in lines:
            split_sections = line.split(" ")
            if len(split_sections) == 2:
                result = split_sections[1].startswith('T') if True else False
                malleation = int(split_sections[0])
                solver.add( 
                    solver._eq(ORACLE.do_query_smt(msg, solver, malleation),result)
                )    
    number_sols = 0         
    if solver.check():
        number_sols = number_sols + 1
        some_msg = solver.model("msg")["msg"]
        print("{}\n".format(bin(some_msg)))
        solver.add(solver._not(solver._eq(msg,some_msg)))
        if solver.check():
            number_sols = number_sols + 1
            print("Failed to get solver down to one message")
            offending_msg = solver.model("msg")["msg"]
            number_sols = solver.approxmc()
        print("Number of solutions total is {}".format(number_sols))
    else:
        print("Solver was not even satisfiable")

def oneCheck(list_of_malleations, idx, queue):
    assert len(list_of_malleations) == idx
    solver = solver_t.Z3Solver()
    fm = solver.bv("fm", format.test_length)
    range_check = len(list_of_malleations) - 1
    solver.add(solver._eq(format.checkFormatSMT(fm, solver), 1))
    for mall_pair in range(range_check):
        malleation = list_of_malleations[mall_pair][0]
        add_res = solver._bool(list_of_malleations[mall_pair][1])
        solver.add(
            solver._eq(ORACLE.do_query_smt(fm, solver, malleation), add_res) 
        )
    
    # add to solver and approxi
    actual_mall = list_of_malleations[range_check][0]
    actual_res = solver._bool(list_of_malleations[range_check][1])
    total_cnf = 0
    solver.push()
    solver.add(
        solver._not(solver._eq(ORACLE.do_query_smt(fm, solver, actual_mall),actual_res)) 
    )
    try:
        cut_time = time.time()
        cut_set, cnf_time = solver.approxAndTime()
        cut_time = time.time() - cut_time
    except:
        cut_set = 0
        cut_time = 0
        cnf_time = 0
    total_cnf += cnf_time
    solver.pop()
    solver.add(
        solver._eq(ORACLE.do_query_smt(fm, solver,actual_mall),actual_res)
    )
    update_time = time.time()
    updated_set, cnf_time = solver.approxAndTime()
    update_time = time.time() - update_time
    total_cnf += cnf_time
    solver_knows = solver.knownbits("fm")

    string_result = "{} {} {} {} {}\n".format(2**(solver_knows.count("?")), updated_set, cut_set, cnf_time, update_time + cut_time - total_cnf) 
    queue.put((string_result, idx))

def addAndApprox(filename, parallelize=True):
    WINDOW_MAX = 64
    write_res = filename.split(".")[0] + ".dat"
    all_malleations = []
    with open(filename, "r") as file_r:
        lines = file_r.readlines()
        for line in lines:
            split_sections = line.split(" ")
            if len(split_sections) == 2:
                malleation = int(split_sections[0])
                result = split_sections[1].startswith('T') if True else False
                all_malleations.append((malleation, result))
    print("Should go through {} checks\n".format(len(all_malleations)))
    num_malleations = len(all_malleations)
    for round_ctr in range(0, num_malleations, WINDOW_MAX):
        print("Starting round ctr .... {}".format(round_ctr))
        procs = []
        global_queue = Queue()
        stopping_pt = min(WINDOW_MAX, (num_malleations - round_ctr))
        for i in range(stopping_pt):
            total_mall = round_ctr + i
            print("Creating PID with {} malleations\n".format(total_mall + 1))
            necessary_malls = all_malleations[:total_mall+1]
            procs.append(Process(target=oneCheck, args=(necessary_malls,total_mall+1,global_queue,)))
        #run each process 
        for i in range(len(procs)):
            procs[i].start()
        # join on each
        results = []
        for i in range(len(procs)):
            procs[i].join()
            result_from_proc = global_queue.get()
            results.append(result_from_proc)
        # take each element off the queue and write to file
        results.sort(key=lambda tup: tup[1])
        stripped_res = [x[0] for x in results]
        write_to_file = "".join(stripped_res)
        with open(write_res, "a") as write_file:
            write_file.write(write_to_file)
    return

def main():
    if len(sys.argv) != 3:
        print("Python usage is: python {} [approx|check] [filename]".format(sys.argv[0]))
        sys.exit(1)
    elif sys.argv[1] == "approx":
        addAndApprox(sys.argv[2])
    elif sys.argv[1] == "check":
        addAndCheck(sys.argv[2])
    return


if __name__ == "__main__":
    main()
