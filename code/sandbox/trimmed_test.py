#!/usr/bin/env python
import os
import sys
import time
import math
import json
import random
import struct
import argparse
import importlib
import subprocess
import multiprocessing as mp
from datetime import datetime
from tempfile import NamedTemporaryFile, gettempdir

import oracle
import solver as libSolver
from malformations import xor as malform

DATE = '-'.join(
    [str(datetime.now().year),
     str(datetime.now().month),
     str(datetime.now().day)])

def MakeStructuralConstraint(solver, m1_arr, m2_arr,
                             fmt, *p):
    """ Add initial constraints to set up the attack
        require that m1 and m2 be validly formatted
        require that mall(m1, p) be validly formatted
        require that mall(m2, p) NOT be validly formatted
    """
    for t in range(TRIALS):
        solver.add(
            fmt(m1_arr[t], solver),
            fmt(m2_arr[t], solver),
            ORACLE.do_query_smt(m1_arr[t], solver, *p),
            solver._not(
                ORACLE.do_query_smt(m2_arr[t], solver, *p)
            ),
        )

"""
def MakeStructuralConstraintMultiOutput(solver, m1_arr, m2_arr, fmt, *p):
    ""\" Same as previous MakeStructuralConstraint except works for
        one specific format function's definition of true and false
        we could specify what true and false mean in the actual format
        file
    ""\"
    for i in range(TRIALS):
        solver.add(
            solver._eq(fmt(m1_arr[i], solver), 1),
            solver._eq(fmt(m2_arr[i], solver), 1),
            malleationIsValid(m1_arr[i], solver, *p),
            malleationIsValid(m2_arr[i], solver, *p),
            solver._eq(ORACLE.do_query_smt(m1_arr[i], solver, *p), 1),
            solver._eq(ORACLE.do_query_smt(m2_arr[i], solver, *p), 0),
        )

def AddAttackerKnowledge(final_solver, iterative_solver, m1_arr, m2_arr, fm, realM):
    ""\" Add extra constraints corresponding to knowledge an attacker would
        have about the real message, this is format and malleation dependent
    ""\"
    realMsgLength = realM & ((1 << format.length_field_size) - 1)
    final_solver.add(final_solver._eq(final_solver.extract(fm, format.length_field_size - 1, 0), realMsgLength))
    for i in range(TRIALS):
        iterative_solver.add(
            iterative_solver._eq(iterative_solver.extract(m1_arr[i], format.length_field_size-1,0), realMsgLength)
        )
        iterative_solver.add(
            iterative_solver._eq(iterative_solver.extract(m2_arr[i], format.length_field_size-1,0), realMsgLength)
        )
"""

def AddIterativeConstraint_IterativeSolver(solver, m1_arr, m2_arr,
                                           result, malleation):
    """ Step forward in the adaptive attack by inputting the malleation
        and the corresponding oracle result
    """
    add_res = solver._bool(result)
    for i in range(TRIALS):
        solver.add(
            solver._iff(
                ORACLE.do_query_smt(m1_arr[i], solver, *malleation), add_res
            ),
            solver._iff(
                ORACLE.do_query_smt(m2_arr[i], solver, *malleation), add_res
            ),
        )

def AddIterativeConstraint_CNFSolver(cnfS, cnf, m1c_arr, m2c_arr,
                                     result, malleation):
    """ Update the CNF to include the derived CNF constraints from
        an iterative constraint
    """
    add_res = cnfS._bool(result)
    cnfS.push()
    for i in range(TRIALS):
        cnfS.add(
            cnfS._iff(
                ORACLE.do_query_smt(m1c_arr[i], cnfS, *malleation), add_res
            ),
            cnfS._iff(
                ORACLE.do_query_smt(m2c_arr[i], cnfS, *malleation), add_res
            ),
        )
    new_cnf = cnfS.cnf(addTrue=False)
    cnfS.pop()
    # convert new_cnf to use variables from old cnf in order to extend old cnf
    new_cnf_map_inv = {}
    new_vars = {}
    for k,v in new_cnf.variables.iteritems():
        new_cnf_map_inv[v] = k
    for i in range(len(new_cnf.clauses)):
        for j in range(len(new_cnf.clauses[i])):
            tok = new_cnf.clauses[i][j]
            neg = False
            if tok.startswith('-'):
                neg = True
                tok = tok[1:]
            inv_mapped = new_cnf_map_inv[tok]
            if inv_mapped.startswith("k!"): # intermediate variable
                if inv_mapped in new_vars: # previously seen
                    v = new_vars[inv_mapped] # use same new mapping
                else:
                    v = cnf.newvar() # generate new mapping
                    while v in cnf.variables: # shouldn't happen, but must make sure
                        v = cnf.newvar()
                    cnf.variables[v] = v # intentional dead mapping, inverting is no-op
                    new_vars[inv_mapped] = v # save in case we see this intermediate again
            elif inv_mapped.startswith("p") or inv_mapped.startswith("m") or inv_mapped == "true":
                v = cnf.variables[inv_mapped]
            else:
                raise Exception("Invalid variable mapping lookup: {}".format(inv_mapped))
            new_cnf.clauses[i][j] = ("-" if neg else "") + v
    cnf.clauses.extend(new_cnf.clauses)

def AddIterativeConstraint_FinalSolver(finalS, fm, result, malleation):
    """ Update the final message solver to iteratively include the step in
        the adaptive attack
    """
    add_res = finalS._bool(result)
    finalS.add(
        finalS._iff(ORACLE.do_query_smt(fm, finalS, *malleation), add_res),
    )

def CreateParityConstraint(indices):
    """ Based on the remaining unconstrained indices and k,
        return a subset of indices which should be XOR'd over
        as a list of integers
        ISRANDOM determines whether to use a strategy which selects in
        expectation K indices but could select more or less
    """
    parity_indices = []
    if K > len(indices):
        raise ValueError("Number of variables in constraint is larger than actual size test")
    if ISRANDOM:
        prob_picking_var = min(K/float(len(indices)), 0.5)
        for idx in indices:
            if random.random() <= prob_picking_var:
                parity_indices.append(idx)
    else:
        random.shuffle(indices)
        parity_indices = list(indices[:K])
    return parity_indices

def SingleSizeExperimentXors(size, unknown_positions):
    """ Based on the size and unconstrained indices,
        return a list[2][TRIALS][size][K] of integers
        which represent the selection of XORs. In other words:
            for each message (m1, m2)
                for each trial
                    provide size # of K-sized XOR as a list of lists of integers
        additionally, provide a list[2][TRIALS][size] of integers (0 or 1)
        which represent the parity coin-flips for each XOR of size K
        finally, return the random seed used so that this set of XORs and coins
        can be exactly replicated
    """
    seed = struct.unpack("<L", os.urandom(4))[0]
    random.seed(seed)
    xors = []
    coins = []
    indices = list(unknown_positions)
    for _ in range(2):
        msg_xors = []
        msg_coins = []
        for _ in range(TRIALS):
            trial_xors = []
            trial_coins = []
            for _ in range(size):
                trial_xors.append(CreateParityConstraint(indices))
                trial_coins.append(random.randint(0,1))
            msg_xors.append(trial_xors)
            msg_coins.append(trial_coins)
        xors.append(msg_xors)
        coins.append(msg_coins)
    return xors, coins, seed

def ExtractModel(dimacs):
    """ Given the lines of output from CryptoMinisat (or any DIMACS-output
        solver) extract a model from the "v" lines of the output using the
        internal representation of the cnf to map integer DIMACS variables
        back to solver variables
        returns a map from cnf integer variable names
        to integer bit values {0, 1}
    """
    t_map = {}
    for line in dimacs:
        spl = line.split(' ')
        if not spl or spl[0].strip() != "v":
            continue
        for i_ in spl:
            i = i_.strip()
            if i == '0':
                break
            else:
                if i.startswith('-'):
                    t_map[i[1:]] = 0
                else:
                    t_map[i] = 1
    return t_map

def GetSizeResultCMS(q, cnf, size, unknown_positions):
    """ For a given size, collect the XORs for an MBound assertion
        and append them to a copy of the CNF
        then, write the CNFXOR out to a file and run CryptoMinisat
        if CMS returns SAT:
            extract a model and specifically extract a value for each bit of
            the malleation bitvector
        write to the output queue a 3-tuple:
            (
             size   : the MBound size which this result corresponds to
             mall   : the malleation extracted if SAT, else None
             time   : the runtime of CMS on this instance
            )
    """
    if DELTA != 0.5:
        raise Exception("FIX T/DELTA")
    xor_indices, coins, seed = SingleSizeExperimentXors(size, unknown_positions)
    procspersolver = max(int(NPROCS/WINDOW_SIZE), 1)
    for m in range(2): # m1 or m2
        for t in range(TRIALS):
            for i in range(size):
                xor = []
                for x in xor_indices[m][t][i]:
                    xor.append(cnf.variables["m{}_t{}_{}".format(m+1, t, x)])
                if coins[m][t][i] == 1:
                    xor.append(cnf.variables["true"])
                cnf.xors.append(xor)
    t0 = time.time()
    with NamedTemporaryFile(mode="w+", dir=TMPDIR) as out:
        with NamedTemporaryFile(mode="w+", dir=TMPDIR) as f:
            f.write(str(cnf))
            cnf.xors = []
            f.seek(0)
            ret = subprocess.call(["cryptominisat5",
                                   "--maxnummatrixes", "100",
                                   "--maxxorsize", "8",
                                   "--verb", "0", "-t", str(procspersolver),
                                   f.name], stdout=out)
            if ret not in [libSolver.CMS_SAT, libSolver.CMS_UNSAT]:
                f.seek(0)
                subprocess.call(["cp", f.name, "cms_error_{}.cnf".format(ret)])
                raise Exception("CMS returned bad status {}".format(ret))
        out.seek(0)
        dimacs = out.readlines()
    if ret == libSolver.CMS_SAT:
        targ_map = ExtractModel(dimacs)
        mall = long(0)
        for b in range(bit_vec_length):
            targ = cnf.variables["p_{}".format(b)]
            mall |= (targ_map[targ] << b)
    elif ret == libSolver.CMS_UNSAT:
        mall = None
    else:
        raise Exception("CMS returned bad status {}".format(ret))
    q.put((size, mall, time.time()-t0))

def PopulateSizeResultsCMS(solver, cnf, curr_size,
                           m1_arr, m2_arr, realM, unknown_positions):
    """ Call GetSizeResultCMS in parallel (WINDOW_SIZE at a time)
        to populate the size_results list with (malleation, execution time)
        tuples
        Starts at the highest sizes and works downward, ceasing when any
        check in a given window is satisfiable after processing the whole
        window
        the size which is associated with a given result is encoded as the
        index into the size_results array - the largest predicted MBound
        sizes are on the right side of the size_results list
        at each index of size_results:
            SAT results have a tuple (malleation, time)
            UNSAT results have a tuple (None, time)
            Unattempted results have a value None
    """
    size_results = [None]*(curr_size+1)
    q = mp.Queue()
    w = 0
    if DOPRINT:
        print("Running CMS window {}...{}".format(curr_size, max(curr_size-WINDOW_SIZE+1, 0)))
    done = False
    while not done and curr_size-WINDOW_SIZE*w > -1:
        procs = []
        if INVERT:
            window = range(WINDOW_SIZE*w,
                           min(WINDOW_SIZE*(w+1), curr_size+1),
                           1)
        else:
            window = range(curr_size-WINDOW_SIZE*w,
                           max(curr_size-WINDOW_SIZE*(w+1), -1),
                           -1)
        for i in window:
            p = mp.Process(target=GetSizeResultCMS,
                           args=(q, cnf, i, unknown_positions)
            )
            p.daemon = True
            procs.append(p)
        map(lambda p: p.start(), procs)
        map(lambda p: p.join(), procs)
        for _ in range(len(procs)):
            size, mall, time_run = q.get()
            if mall is not None:
                done = True
            size_results[size] = ((mall,), time_run)
        w += 1
    return size_results

def CreateBoolMapping(solver, m1_arr, m2_arr, p):
    """ The Z3 CNF conversion tactic will preserve names for boolean SMT
        variables over simplify, bit-blast, and tseitin-cnf
        in order to output useful CNF (CNF from which we can extract models or
        apply constraints) we must represent each relevant bit as a boolean
        to achieve this, we create a boolean for each index of each bitvector,
        then assert equivalence between that boolean and the bitvector bit
        however, this causes type issues in Z3, so we introduce the constant
        'one', so that we can express
            (b : boolean) == ((bit : bitvector) == (one : bitvector))
        we use a naming convention of <bitvector name>_<i> for each index i
        of the bitvector, e.g. p_0 for the least significant bit of p
    """
    one = solver.bvconst(1, 1)
    for t in range(TRIALS): # for each trial
        for i in range(bit_vec_length): # for each bit
            b1 = solver.bool('m1_t{}_{}'.format(t, i))
            b2 = solver.bool('m2_t{}_{}'.format(t, i))
            solver.add(
                solver._eq(b1, solver._eq(solver.extract(m1_arr[t], i, i), one)))
            solver.add(
                solver._eq(b2, solver._eq(solver.extract(m2_arr[t], i, i), one)))
    for i in range(bit_vec_length):
        pi = solver.bool("p_{}".format(i))
        solver.add(solver._eq(pi, solver._eq(solver.extract(p, i, i), one)))

def Trial(bootstrap, prevcnf=""):
    if bootstrap[0] == "":
        realM = format.makePaddedMessage()
        if not format.checkFormat(realM):
            raise ValueError("makePaddedMessage created an invalid message")
    else:
        realM = None # will get from bootstrap file
    overall_start = time.time()
    # Setup solvers
    libSolver.z3.set_param("parallel.enable", True)
    libSolver.z3.set_param("parallel.threads.max", NPROCS)
    solver = libSolver.Z3Solver(); cnfS = libSolver.Z3Solver()
    finalS = libSolver.Z3Solver()
    PopulateSizeResults = PopulateSizeResultsCMS
    m1_arr = []; m2_arr = []; m1c_arr = []; m2c_arr = []
    for t in range(TRIALS):
        m1_arr.append(solver.bv('m1_' + str(t), bit_vec_length))
        m2_arr.append(solver.bv('m2_' + str(t), bit_vec_length))
        m1c_arr.append(cnfS.bv('m1_' + str(t), bit_vec_length))
        m2c_arr.append(cnfS.bv('m2_' + str(t), bit_vec_length))
    p = solver.bv('p', bit_vec_length); pC = cnfS.bv('p', bit_vec_length)
    fm = finalS.bv('fm', bit_vec_length)
    MakeStructuralConstraint(solver, m1_arr, m2_arr, format.checkFormatSMT, p)
    MakeStructuralConstraint(cnfS, m1c_arr, m2c_arr, format.checkFormatSMT, pC)
    CreateBoolMapping(solver, m1_arr, m2_arr, p)
    CreateBoolMapping(cnfS, m1c_arr, m2c_arr, pC)
    if REALM_VALID:
        finalS.add(format.checkFormatSMT(fm, finalS))
    queryNum = 0
    if bootstrap[0] != "":
        bootstrap_file = bootstrap[0]
        approxmc_file = bootstrap[1]
        queryNum, realM = bootstrapPrevRun(bootstrap_file, finalS, fm,
                                           solver, m1_arr, m2_arr,
                                           approxmc_file)
        if approxmc_file != "":
            return
    InitTrialLogging(realM)
    t0 = time.time()
    if prevcnf is "" or bootstrap[0] != "":
        if DOPRINT:
            print("Generating CNF...")
        cnf = solver.cnf()
        out = DATE+"/"+TESTNAME+".cnf"
        if DOPRINT:
            print("Saving structural constraint CNF to file: {}".format(out))
        with open(out, 'w') as f:
            f.write("c map {}\n".format(json.dumps(cnf.variables)))
            f.write(str(cnf))
    else:
        if DOPRINT:
            print("Parsing previous CNF file {}...".format(prevcnf))
        cnf = bootstrapPrevCNF(prevcnf)
    if DOPRINT:
        print("Done ({}s)".format(time.time()-t0))
    curr_size = bit_vec_length
    unknown_positions = {i for i in range(bit_vec_length)}
    sol_vect = ['?' for _ in range(bit_vec_length)]
    rebuild = REBUILD
    while solver.check() and '?' in sol_vect:
        if DOPRINT:
            print "Starting query #", queryNum
        queryNum += 1
        t0 = time.time()
        if DOPRINT:
            print("Determining known bits...")
        sol_vect = finalS.knownbits("fm")
        if DOPRINT:
            print("Done ({}s)".format(time.time()-t0))
        if sol_vect.count('?') < curr_size: # did we learn some bits?
            curr_size = sol_vect.count('?')
            global K
            if ISRANDOM:
                K = int(curr_size/2)
            else:
                K = int(math.floor(math.log(curr_size, 2)))
            # the upper bound on how big the size of the set can be
            # is 2**(bit_vec_length - # of bits known)
            removed = set()
            for i, val in enumerate(sol_vect):
                if val != "?" and i in unknown_positions:
                    unknown_positions.remove(i)
                    removed.add(i)
            if DOPRINT:
                print("Removing indices {} from consideration".format(
                    sorted(list(removed)))
                )
            if curr_size == 0:
                break
            # compact iterative constraints back into the solver
            if rebuild == 0:
                t0 = time.time()
                if DOPRINT:
                    print("Re-extracting CNF")
                # re-extract CNF now encoding all iterative constraints thus far
                cnf = solver.cnf()
                if DOPRINT:
                    print("Done ({}s)".format(time.time()-t0))
                rebuild = REBUILD
            else:
                rebuild -= 1
        if DOPRINT:
            print "Solver knows ({} bits): {}".format(
                    bit_vec_length-curr_size, ''.join(list(reversed(sol_vect)))
            )
        t0 = time.time()
        size_results = PopulateSizeResults(solver, cnf, curr_size,
                                                m1_arr, m2_arr,
                                                realM, unknown_positions)
        if DOPRINT:
            print("Done ({}s)".format(time.time()-t0))
            print("Processing CMS results...")
        t1 = time.time()
        ProcessSizeResults(size_results, finalS, solver, cnfS, cnf,
                           fm, m1_arr, m2_arr, m1c_arr, m2c_arr, realM)
        if DOPRINT:
            print("Done ({}s)".format(time.time()-t1))
        size_results = []
        elap = time.time() - t0
        if DOPRINT:
            print "Elapsed: {}s in query {}".format(elap, queryNum)
            print "Elapsed: {}s so far".format(time.time() - overall_start)

    assert finalS.check()
    sol_vect = finalS.knownbits("fm")
    if DOPRINT:
        print "Fell through".format(curr_size)
        print "".join([str(s) for s in sol_vect])

    cardinality_satisfied = 0
    sawGood = False
    solns = []
    while finalS.check():
        finalResult = finalS.model('fm')['fm']
        solns.append(finalResult)
        if DOPRINT:
            if len(solns) <= 10:
                print "Solution %d for M: " % cardinality_satisfied, "\t", finalResult
            elif len(solns) == 11:
                print "Not printing remaining solutions"
        if (finalResult == realM):
            sawGood = True
        finalS.add(finalS._not(finalS._eq(fm, finalResult)))
        cardinality_satisfied += 1
    if DOPRINT:
        print "Saw {} solutions".format(len(solns))
    if sawGood and DOPRINT:
        print "Saw the correct solution"
    return {'sawGood': sawGood,
            'cardinality': cardinality_satisfied,
            'queries': queryNum,
            'realM': bin(realM),
            'time': (time.time() - overall_start),
            }

def ProcessSizeResults(size_results, finalS, solver, cnfS, cnf, fm,
                       m1_arr, m2_arr, m1c_arr, m2c_arr, realM):
    """ Given a populated size_results list, iterate down the tested sizes
        high to low to find the malleation representing the largest split
        Make the oracle query for this malleation, and add this iteration of
        the adaptive attack to the cnf via an additional solver (cnfS) which
        only briefly holds the iterative constraint before it is extracted as
        CNF and appended to the existing CNF
        in order to achieve this, we must resolve variables names from the new
        to the old CNFs, and then store the (malleation, result) pair on the
        original solver for later compacting
        this allows us to avoid the significant overhead of iteratively
        generating CNF from scratch using the slow Z3 tactic
    """
    actual_size_mbound = None
    total_time = 0.0
    for x in size_results:
        if x is not None:
            total_time = max(total_time, x[1]) # take longest of parallel window
    res = None
    for i in range(len(size_results)-1, -1, -1):
        if size_results[i] is not None and None not in size_results[i][0]:
            mall, _ = size_results[i]
            res = ORACLE.do_query(realM, *mall)
            actual_size_mbound = i
            if DOPRINT:
                print("Success at size {} (oracle: {})".format(i, res))
            break
    if res is not None:
        t0 = time.time()
        if DOPRINT:
            print("Adding iterative constraints...")
        AddIterativeConstraint_IterativeSolver(solver, m1_arr, m2_arr,
                                               res, mall)
        AddIterativeConstraint_CNFSolver(cnfS, cnf, m1c_arr, m2c_arr, res, mall)
        AddIterativeConstraint_FinalSolver(finalS, fm, res, mall)
        if DOPRINT:
            print("Done ({}s)".format(time.time()-t0))
        with open(GNU_LOG, "a") as log_w:
            log_w.write("{} {}\n".format(actual_size_mbound, total_time))
        with open(LOGNAME, "a") as log_w:
            log_w.write("{} {}\n".format(json.dumps(mall), res))
    else:
        if DOPRINT:
            print("No MBound-satisfiable malleations found")
        with open(GNU_LOG, "a") as log_w:
            log_w.write("{} {}\n".format(None, total_time))

def InitTrialLogging(realM):
    """ Write initial information to the first lines of the log files """
    if DOPRINT:
        print "Real Message: {}".format(bin(realM))
    if ISRANDOM:
        format_header = "Full run of attack with message {} at {} Bit with trials {}, delta {}, and expected constraint length {}. Threshold for success is {}/{}\n".format(realM, format.test_length, TRIALS, DELTA, K, math.floor((DELTA + 0.5) * TRIALS), TRIALS)
    else:
        format_header = "Full run of attack with message {} at {} Bit with trials {}, delta {}, and k is {}. Threshold for success is {}/{}\n".format(realM, format.test_length, TRIALS, DELTA, K, math.floor((DELTA + 0.5) * TRIALS), TRIALS)
    with open(GNU_LOG, "w") as dat_write:
        dat_write.write(format_header)
        dat_write.write("MBound size (log2) | Query time (longest in parallel)\n")
    with open(LOGNAME, "w") as write_log:
        write_log.write(format_header)

def main():
    global TESTNAME, LOGNAME, GNU_LOG, BOOTSTRAP, DOPRINT, TMPDIR, DOPRINT
    global WINDOW_SIZE, NPROCS, ISRANDOM, K, TRIALS, DELTA, REBUILD, INVERT
    global ORACLE, bit_vec_length, format, REALM_VALID
    try:
        TESTNAME = os.environ["NAME"]
    except KeyError as e:
        print "Must provide NAME in environment for log file name"
        raise e
    LOGNAME = DATE+"/"+TESTNAME
    GNU_LOG = DATE+"/"+TESTNAME
    if not os.path.exists(DATE):
        os.mkdir(DATE)
    ext = 0
    while (os.path.exists(LOGNAME + ('_' + str(ext) if ext > 0 else '')+".log")
           or
           os.path.exists(GNU_LOG + ('_' + str(ext) if ext > 0 else '')+".dat")):
        ext += 1
    LOGNAME = DATE+"/"+TESTNAME+('_'+str(ext) if ext > 0 else '')+".log"
    GNU_LOG = DATE+"/"+TESTNAME+('_'+str(ext) if ext > 0 else '')+".dat"
    parser = argparse.ArgumentParser(description="Run format oracle attack")
    parser.add_argument("--valid", action='store_true')
    parser.add_argument("-f", "--format", type=str, required=True)
    parser.add_argument("-k", type=int, default=0)
    parser.add_argument("-t", "--trials", type=int, default=2)
    parser.add_argument("-d", "--delta", type=float, default=0.5)
    parser.add_argument("-p", "--procs", type=int, default=mp.cpu_count())
    parser.add_argument("-w", "--window", type=int, default=mp.cpu_count())
    parser.add_argument("-i", "--invert", action='store_true')
    parser.add_argument("-r", "--random", action='store_true')
    parser.add_argument("-c", "--cnf", type=str, default="")
    parser.add_argument("--bootstrap", type=str, default="")
    parser.add_argument("--approxmc", type=str, default="")
    parser.add_argument("-b", "--rebuild", type=int, default=0)
    parser.add_argument("-q", "--quiet", action='store_true')
    parser.add_argument("-x", "--tmp", type=str, default=gettempdir())
    args = vars(parser.parse_args(sys.argv[1:]))
    format = importlib.import_module(args["format"])
    try:
        bit_vec_length = format.test_length * format.num_blocks
    except AttributeError:
        bit_vec_length = format.test_length
    REALM_VALID = args["valid"]
    BOOTSTRAP = (args["bootstrap"], args["approxmc"])
    ORACLE = oracle.Oracle(format.checkFormat, format.checkFormatSMT, malform)
    WINDOW_SIZE = args["window"]
    INVERT = args["invert"]
    NPROCS = args["procs"]
    ISRANDOM = args["random"]
    TRIALS = args["trials"]
    DELTA = args["delta"]
    if DELTA != 0.5:
        raise NotImplementedError("delta must be 0.5")
    PREVCNF = args["cnf"]
    REBUILD = args["rebuild"]
    DOPRINT = not args["quiet"]
    TMPDIR = args["tmp"]
    if args['k'] == 0:
        if ISRANDOM:
            K = int(bit_vec_length/2)
        else:
            K = int(math.floor(math.log(bit_vec_length, 2)))
    else:
        K = args["k"]
    if DOPRINT:
        print("Logging to {}".format(LOGNAME))
        print("Writing MBound results to {}".format(GNU_LOG))
    trial_res = Trial(bootstrap=BOOTSTRAP, prevcnf=PREVCNF)
    if BOOTSTRAP[1] != "":
        with open(LOGNAME, "a") as final_res:
            final_res.write(json.dumps(trial_res))
    return 0

def bootstrapPrevCNF(filename):
    """ Extract a cnf object from the cnf file denoted by filename
        must have been created with a c map line in order for variable
        mappings to be preserved
    """
    cnf = libSolver.CNF()
    def map_hook(obj):
        return {k.encode('utf-8') if isinstance(k,unicode) else k :
                v.encode('utf-8') if isinstance(v,unicode) else v
                for k,v in obj}
    with open(filename, 'r') as f:
        lines = f.readlines()
    for line in lines:
        if line.startswith("c"):
            if line.startswith("c map"):
                cnf.variables = json.loads(line[len("c map "):],
                                           object_pairs_hook=map_hook)
                cnf.var = len(cnf.variables)+1
            elif line.startswith("c ind"):
                continue
        elif line.startswith("p ind"):
            continue
        else:
            clause = []
            for tok_ in line.split(" "):
                tok = tok_.strip()
                if tok == "0":
                    break
                clause.append(tok)
            cnf.clauses.append(clause)
    return cnf

def bootstrapQueries(finalS, fm, solver, m1_arr, m2_arr, lines):
    for line in lines:
        tokens = line.split(" ")
        if len(tokens) != 2: # malleation iterable and oracle result boolean
            continue
        try:
            mall = json.loads(tokens[0])
            res = tokens[1].strip() == "True"
        except ValueError as e:
            print("Malformed bootstrap file line: {}".format(line))
            raise e
        AddIterativeConstraint_IterativeSolver(solver, m1_arr, m2_arr,
                                               res, mall)
        AddIterativeConstraint_FinalSolver(finalS, fm, res, mall)

def bootstrapAndApproxQueries(q, lines, approxmc_range):
    counts = {}
    finalS = libSolver.Z3Solver()
    fm = finalS.bv('fm', bit_vec_length)
    if REALM_VALID:
        finalS.add(format.checkFormatSMT(fm, finalS))
    for i in range(len(lines)):
        line = lines[i]
        tokens = line.split(" ")
        if len(tokens) != 2: # malleation iterable and oracle result boolean
            continue
        try:
            mall = json.loads(tokens[0])
            res = tokens[1].strip() == "True"
        except ValueError as e:
            print("Malformed bootstrap file line: {}".format(line))
            raise e
        if i in approxmc_range:
            finalS.push()
            AddIterativeConstraint_FinalSolver(finalS, fm, not res, mall)
            try:
                counts[i] = finalS.approxmc(TMPDIR, verbose=True)
            except Exception as e:
                counts[i] = (str(e),)
            finalS.pop()
        elif i > max(approxmc_range):
            break
        AddIterativeConstraint_FinalSolver(finalS, fm, res, mall)
    q.put(counts)

def bootstrapPrevRun(filename, finalS, fm, solver, m1_arr, m2_arr, approxmc):
    """ Continue a partial attack by extracting realM, malleations, and results
        from a log file

        Or, approxmc count the queries of an attack by extracting the above
        from a log file, writing results to the file given by the `approxmc'
        argument

        FIXME eventually make this two functions
    """
    with open(filename) as f:
        lines = f.readlines()
    if DOPRINT:
        print("Bootstrapping from {} ({} queries)".format(filename,
            len(lines)-(2 if "sawGood" in lines[-1] else 1)
        ))
    try:
        realM = int((lines[0].split(" "))[6])
    except Exception as e:
        print("Malformed bootstrap file (missing realM?)")
        raise e
    lines = lines[1:]
    if "sawGood" in lines[-1]:
        lines = lines[:-1]
    queryNum = 0
    if approxmc != "":
        full_range = [x for x in range(len(lines))]
        q = mp.Queue()
        procs = []
        ranges = []
        counts = {}
        range_len = int(math.ceil(float(len(lines))/NPROCS))
        for i in range(NPROCS):
            _range = full_range[i*range_len:(i+1)*range_len]
            if _range:
                ranges.append(_range)
        assert len(ranges) <= NPROCS
        for i in full_range:
            if not any(map(lambda x: i in x, ranges)):
                raise ValueError("Missing {} in ranges".format(i))
        for r in ranges:
            p = mp.Process(target=bootstrapAndApproxQueries,
                           args=(q, lines, r))
            p.daemon = True
            p.start()
            procs.append(p)
        while len(counts) < len(full_range):
            new = q.get()
            counts.update(new)
            with open(approxmc, 'a') as f:
                for query in new:
                    if len(new[query]) == 2:
                        count, time = new[query]
                        f.write("{}\n".format(json.dumps(
                            {'query': query, 'count': count,
                             'time': time}))
                        )
                    else:
                        f.write("{}\n".format(json.dump(
                            {'query':query, 'error': new[query]}))
                        )
        for p in procs:
            p.join()
        with open(approxmc + '_final', 'w') as f:
            for i in range(len(lines)):
                if len(counts[i]) == 2:
                    f.write("{}\n".format(json.dumps(
                        {'query': i, 'count': counts[i][0],
                         'time': counts[i][1]}))
                    )
                else:
                    f.write("{}\n".format(json.dump(
                        {'query':i, 'error': counts[i][0]}))
                    )
    else:
        bootstrapQueries(finalS, fm, solver, m1_arr, m2_arr, lines)
    return len(lines), realM

if __name__ == "__main__":
    exit(main())
