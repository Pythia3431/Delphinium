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

from cms_utils import *
from cnf_utils import *
from attackerConstraints import *
from logger import Logger
import oracle
import solver as libSolver
import formats

DATE = '-'.join(
    [str(datetime.now().year),
     str(datetime.now().month),
     str(datetime.now().day)])

def MakeStructuralConstraint(solver, m1_arr, m2_arr, p):
    """ Add initial constraints to set up the attack
        require that m1 and m2 be validly formatted
        require that mall(m1, p) be validly formatted
        require that mall(m2, p) NOT be validly formatted
    """
    for t in range(PARAMS["trials"]):
        solver.add(
            ORACLE.pure_query_constr(m1_arr[t], p, 0, solver),
            ORACLE.pure_query_constr(m2_arr[t], p, 1, solver),
        )

def AddIterativeConstraint_IterativeSolver(solver, m1_arr, m2_arr,
                                           result, malleation):
    """ Step forward in the adaptive attack by inputting the malleation
        and the corresponding oracle result
    """
    for i in range(PARAMS["trials"]):
        solver.add(
            ORACLE.query_constr(m1_arr[i], malleation, result, solver),
            ORACLE.query_constr(m2_arr[i], malleation, result, solver)
        )

def AddIterativeConstraint_FinalSolver(finalS, fm, result, malleation):
    """ Update the final message solver to iteratively include the step in
        the adaptive attack
    """
    finalS.add(
        ORACLE.query_constr(fm, malleation, result, finalS)
    )

def AddIterativeConstraint_CNFSolver(cnfS, cnf, m1c_arr, m2c_arr,
                                     result, malleation):
    """ Update the CNF to include the derived CNF constraints from
        an iterative constraint
    """
    cnfS.push()
    for i in range(PARAMS["trials"]):
        cnfS.add(
            ORACLE.query_constr(m1c_arr[i], malleation, result, cnfS),
            ORACLE.query_constr(m2c_arr[i], malleation, result, cnfS)
        )
    new_cnf = cnfS.cnf(addTrue=False)
    cnfS.pop()
    # convert new_cnf to use variables from old cnf in order to extend old cnf
    updateCurrentCNF(cnf, new_cnf)

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
    if PARAMS["delta"] != 0.5:
        raise Exception("FIX T/DELTA")
    xor_indices, coins, seed = SingleSizeExperimentXors(size, unknown_positions, PARAMS["trials"], PARAMS["israndom"], PARAMS["k"])
    procspersolver = max(int(NPROCS/WINDOW_SIZE), 1)
    for m in range(2): # m1 or m2
        for t in range(PARAMS["trials"]):
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
                                   "--maxnummatrices", "100",
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
        for b in range(PARAMS["bit_vec_length"]):
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
            mall = mall[0] # this is awful -- will fix
            res = ORACLE.do_query(realM, mall)
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
        LOG.writeRegular("{} {}\n".format(json.dumps(mall), res))
        LOG.writeMbound("{} {}\n".format(actual_size_mbound, total_time))
    else:
        if DOPRINT:
            print("No MBound-satisfiable malleations found")
        LOG.writeMbound("{} {}\n".format(None, total_time))

def attackStats(finalS, fm, queryNum, realM, overall_start):
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

def Trial(bootstrap, prevcnf=""):
    if bootstrap[0] == "":
        realM = format.makePaddedMessage()
        if not format.checkFormat(realM):
            raise ValueError("makePaddedMessage created an invalid message")
    else:
        realM = None # will get from bootstrap file

    overall_start = time.time()
    # Initialize Solvers ###############################
    libSolver.z3.set_param("parallel.enable", True)
    libSolver.z3.set_param("parallel.threads.max", NPROCS)
    solver = libSolver.Z3Solver(); cnfS = libSolver.Z3Solver()
    finalS = libSolver.Z3Solver()
    PopulateSizeResults = PopulateSizeResultsCMS
    m1_arr = []; m2_arr = []; m1c_arr = []; m2c_arr = []
    for t in range(PARAMS["trials"]):
        m1_arr.append(solver.bv('m1_' + str(t), PARAMS["bit_vec_length"]))
        m2_arr.append(solver.bv('m2_' + str(t), PARAMS["bit_vec_length"]))
        m1c_arr.append(cnfS.bv('m1_' + str(t), PARAMS["bit_vec_length"]))
        m2c_arr.append(cnfS.bv('m2_' + str(t), PARAMS["bit_vec_length"]))
    p = solver.bv('p', PARAMS["bit_vec_length"]); pC = cnfS.bv('p', PARAMS["bit_vec_length"])
    fm = finalS.bv('fm', PARAMS["bit_vec_length"])
    MakeStructuralConstraint(solver, m1_arr, m2_arr, p)
    MakeStructuralConstraint(cnfS, m1c_arr, m2c_arr, pC)
    CreateBoolMapping(solver, m1_arr, m2_arr, p)
    CreateBoolMapping(cnfS, m1c_arr, m2c_arr, pC)
    if REALM_VALID:
        finalS.add(ORACLE.correct_msg_constr(fm, finalS))
        for t in range(PARAMS["trials"]):
            solver.add(
                ORACLE.correct_msg_constr(m1_arr[t], solver),
                ORACLE.correct_msg_constr(m2_arr[t], solver),
            )
            cnfS.add(
                ORACLE.correct_msg_constr(m1c_arr[t], cnfS),
                ORACLE.correct_msg_constr(m2c_arr[t], cnfS)
            )
    if "length_field_size" in dir(format):
        AddLengthKnowledge(finalS, solver, m1_arr, m2_arr, fm, realM, PARAMS["trials"])

    if format.hasIV:
        AddIVKnowledge(finalS, solver, m1_arr, m2_arr, fm, realM, PARAMS["trials"])
    #######################################################
    queryNum = 0
    ### CHECKING FOR BOOTSTRAP INFO #######################
    if bootstrap[0] != "":
        bootstrap_file = bootstrap[0]
        approxmc_file = bootstrap[1]
        queryNum, realM = bootstrapPrevRun(bootstrap_file, finalS, fm,
                                           solver, m1_arr, m2_arr,
                                           approxmc_file)
        if approxmc_file != "":
            return
    if DOPRINT:
        print "Real Message: {}".format(bin(realM))
    # TODO create a logger object 
    LOG.initTrialLogging(realM, PARAMS)
    t0 = time.time()
    # needs to also be run if you HAVE a bootstrapped file 
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
        print("Finished Initialization ({}s)".format(time.time()-t0))

    curr_size = PARAMS["bit_vec_length"]
    unknown_positions = {i for i in range(PARAMS["bit_vec_length"])}
    sol_vect = ['?' for _ in range(PARAMS["bit_vec_length"])]
    rebuild = REBUILD
    while solver.check() and '?' in sol_vect:
        if DOPRINT:
            print "Starting query #", queryNum
        queryNum += 1
        t0 = time.time()
        #### checking if parameters need to be updated #####
        if DOPRINT:
            print("Determining known bits...")
        sol_vect = finalS.knownbits("fm")
        if DOPRINT:
            print("Done ({}s)".format(time.time()-t0))
        if sol_vect.count('?') < curr_size: # did we learn some bits?
            curr_size = sol_vect.count('?')
            
            if PARAMS["israndom"]:
                PARAMS["k"] = int(curr_size/2)
            else:
                PARAMS["k"] = int(math.floor(math.log(curr_size, 2)))
            # the upper bound on how big the size of the set can be
            # is 2**(PARAMS["bit_vec_length"] - # of bits known)
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
        #############################################################
        # Actual Search for a new malleation string 

        if DOPRINT:
            print "Solver knows ({} bits): {}".format(
                    PARAMS["bit_vec_length"]-curr_size, ''.join(list(reversed(sol_vect)))
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
    ## Finished attack, output results 
    assert finalS.check()
    sol_vect = finalS.knownbits("fm")
    if DOPRINT:
        print "Fell through".format(curr_size)
        print "".join([str(s) for s in sol_vect])
    return attackStats(finalS, fm, queryNum, realM, overall_start)

PARAMS = {}
def main():
    global TESTNAME, LOG, BOOTSTRAP, DOPRINT, TMPDIR, DOPRINT
    global WINDOW_SIZE, NPROCS,REBUILD, INVERT
    global PARAMS
    global ORACLE, format, REALM_VALID
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
    parser.add_argument("--valid", action='store_true', help="Specifies whether original ciphertext is well-formed.")
    parser.add_argument("-f", "--format", type=str, required=True, help="Location of format function to use. Preface with format.[filename in format/ dir]")
    parser.add_argument("-m", "--malform", type=str, default="", help="Location of malformation function to use. Preface with malform.[filename in malform/ dir]")
    parser.add_argument("-k", type=int, default=0, help="MAX#SAT paramter, for hash funct")
    parser.add_argument("-t", "--trials", type=int, default=2, help="MAX#SAT parameter, for domain extension")
    parser.add_argument("-d", "--delta", type=float, default=0.5, help="MAX#SAT parameter, percentage passing trials")
    parser.add_argument("-p", "--procs", type=int, default=mp.cpu_count(), help="total number of processors available to provide to tool")
    parser.add_argument("-w", "--window", type=int, default=mp.cpu_count(), help="number of processes to run in parallel for MAX#SAT oracle")
    parser.add_argument("-i", "--invert", action='store_true', help="Start testing size window from highest possible size")
    parser.add_argument("-r", "--random", action='store_true', help="MAX#SAT oracle specific -- achieves theoretical guarantees at cost of efficiency")
    parser.add_argument("-c", "--cnf", type=str, default="", help="previously generated CNF file, correct for current configuration")
    parser.add_argument("--bootstrap", type=str, default="", help="file containing a partially completed previous attack run, correct for current configuration")
    parser.add_argument("--approxmc", type=str, default="")
    parser.add_argument("-b", "--rebuild", type=int, default=0)
    parser.add_argument("-q", "--quiet", action='store_true')
    parser.add_argument("-x", "--tmp", type=str, default=gettempdir())

    args = vars(parser.parse_args(sys.argv[1:]))
    formats.setFormat(args["format"])
    global format
    format = formats.CURRENT_FORMAT
    try:
        PARAMS["bit_vec_length"] = format.test_length * format.num_blocks
    except AttributeError:
        PARAMS["bit_vec_length"] = format.test_length
    malformLib = importlib.import_module(args["malform"])    
    REALM_VALID = args["valid"]
    BOOTSTRAP = (args["bootstrap"], args["approxmc"])
    ORACLE = oracle.Oracle(format.checkFormat, format.checkFormatSMT, malformLib)
    WINDOW_SIZE = args["window"]
    INVERT = args["invert"]
    NPROCS = args["procs"]
    PARAMS["israndom"] = args["random"]
    PARAMS["trials"] = args["trials"]
    PARAMS["delta"] = args["delta"]
    if PARAMS["delta"] != 0.5:
        raise NotImplementedError("delta must be 0.5")
    PREVCNF = args["cnf"]
    REBUILD = args["rebuild"]
    DOPRINT = not args["quiet"]
    TMPDIR = args["tmp"]
    if args['k'] == 0:
        if PARAMS["israndom"]:
            PARAMS["k"] = int(PARAMS["bit_vec_length"]/2)
        else:
            PARAMS["k"] = int(math.floor(math.log(PARAMS["bit_vec_length"], 2)))
    else:
        PARAMS["k"] = args["k"]
    if DOPRINT:
        print("Logging to {}".format(LOGNAME))
        print("Writing MBound results to {}".format(GNU_LOG))

    # Initialize Logger  ###############################
    LOG = Logger(LOGNAME, GNU_LOG)
    trial_res = Trial(bootstrap=BOOTSTRAP, prevcnf=PREVCNF)
    if BOOTSTRAP[1] != "":
        LOG.writeRegular(json.dumps(trial_res))
    return 0

    
if __name__ == "__main__":
    exit(main())

# bootstrap functions

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
    fm = finalS.bv('fm', PARAMS["bit_vec_length"])
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
