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
import struct
from datetime import datetime
from tempfile import NamedTemporaryFile

import oracle
import solver as libSolver
# changes based on which malformations are being used
from malformations import xor_and_trunc_valid, xor_trunc_per_msg
import malformations
format = None

DOPRINT = True
DATE = '-'.join(
    [str(datetime.now().year),
     str(datetime.now().month),
     str(datetime.now().day)])

TESTNAME= None
LOGNAME = None
CONSTRAINT_GROWTH = None
GNU_LOG = None # file used to create graphs -- contains all model counting results
BOOTSTRAP = None
MULT_OUTPUT = True

CMS_SAT = 10
CMS_UNSAT = 20

# total size of bit vectors in bits
bit_vec_length = None
ORACLE = None


WINDOW_SIZE = None # sliding window for parallelization
NPROCS = None # mp.cpu_count()
# setting for size of parity contraints when ISRANDOM is true
# is based off of https://arxiv.org/pdf/1512.08863v1.pdf        
ISRANDOM = None
K = None
TRIALS = None
DELTA = None



def write_debug_to_file(query, cnf_clause, cnf_var, z3_check, cms_check, final_bits, query_run):
    line_to_write = " ".join([str(query), str(cnf_clause), str(cnf_var),str(z3_check), str(cms_check), str(final_bits), str(query_run)])
    with open(CONSTRAINT_GROWTH, "a") as write_f:
        write_f.write(line_to_write + "\n")

def write_debug_header():
    with open(CONSTRAINT_GROWTH, "w") as write_f:
        write_f.write("Query Number | Number of CNF clauses | Number of CNF vars | Z3 add iterative constraint time | CMS-Experiment time | Known Bits Query Time\n")

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
            solver._eq(ORACLE.do_query_smt(m1_arr[t], solver, *p), solver.true()),
            solver._eq(
                ORACLE.do_query_smt(m2_arr[t], solver, *p), solver.false()
            ),
        )

def MakeStructuralConstraintMultiOutput(solver, m1_arr, m2_arr, fmt, *p): #time_var, valid_time, state, *p):
    """ Same as previous MakeStructuralConstraint except works for
        one specific format function's definition of true and false
        we could specify what true and false mean in the actual format
        file
    """
    
    for i in range(TRIALS):
        # change 1 -> solver.true()
        # change 0 -> solver.false()
        # remove valid_time and time_var from format function and oracle query respectively
        # get rid of the valid gcm function
        solver.add(
            solver._eq(fmt(m1_arr[i], solver), solver.true()), #, valid_time, state),1),
            solver._eq(fmt(m2_arr[i], solver), solver.true()), #, valid_time, state),1),
            solver._eq(ORACLE.do_query_smt(m1_arr[i], solver, *p), solver.true()), #time_var, *p), 1),
            solver._eq(ORACLE.do_query_smt(m2_arr[i], solver, *p), solver.false()), #time_var, *p),0)
            xor_trunc_per_msg(solver, m1_arr[i], *p),
            xor_trunc_per_msg(solver, m2_arr[i], *p)
        )
    #solver.add(gcm_mallValid(solver, *p))
    solver.add(xor_and_trunc_valid(solver, *p)) 


def AddAttackerKnowledge(final_solver, iterative_solver, m1_arr, m2_arr, fm, realM):
    """ Add extra constraints corresponding to knowledge an attacker would
        have about the real message, this is format and malleation dependent
    """
    try:
        print("Trying to add attacker knowledge...") 
        realMsgLength = realM & ((1 << format.length_field_size) - 1)
        print("Length of the message is {}".format(realMsgLength))
        if not final_solver is None:
            final_solver.add(
                final_solver._eq(final_solver.extract(fm, format.length_field_size-1, 0), realMsgLength)
            )
        for i in range(TRIALS):
            iterative_solver.add(
                iterative_solver._eq(iterative_solver.extract(m1_arr[i], format.length_field_size-1,0), realMsgLength)
            )
            iterative_solver.add(
                iterative_solver._eq(iterative_solver.extract(m2_arr[i], format.length_field_size-1,0), realMsgLength)
            )
    except:
        print("Exception occurred in AddAttackerKnowledge")
        return
    """
    # CBC MODE SPECIFIC    
    number_blocks = realMsgLength // format.test_length
    realMsgIV = (realM >> ((number_blocks-1)*format.test_length + format.length_field_size))
    if not final_solver is None:
        final_solver.add(final_solver._eq(final_solver.extract(fm, format.length_field_size - 1, 0), realMsgLength))
        final_solver.add(final_solver._eq(final_solver.extract(fm, bit_vec_length-1, (number_blocks - 1) * format.test_length + format.length_field_size), realMsgIV))
    for i in range(TRIALS):
        iterative_solver.add(
            iterative_solver._eq(iterative_solver.extract(m1_arr[i], bit_vec_length-1, (number_blocks-1)*format.test_length + format.length_field_size), realMsgIV),
        )
        iterative_solver.add(
            iterative_solver._eq(iterative_solver.extract(m2_arr[i], bit_vec_length-1, (number_blocks-1)*format.test_length + format.length_field_size), realMsgIV),
   
        )
    """
    
def AddIterativeConstraint_IterativeSolver(solver, m1_arr, m2_arr, 
       result, malleation, save=False):
    """ Step forward in the adaptive attack by inputting the malleation
        and the corresponding oracle result
    """
    add_res = result if MULT_OUTPUT else solver._bool(result)
    if save:
        solver.malleations.append((result, malleation))
    for i in range(TRIALS):
        solver.add(
            solver._iff(
                ORACLE.do_query_smt_realMall(m1_arr[i], solver, *malleation), add_res
            ),
            solver._iff(
                ORACLE.do_query_smt_realMall(m2_arr[i], solver, *malleation), add_res
            ),
        )

def AddIterativeConstraint_CNFSolver(cnfS, cnf, m1c_arr, m2c_arr,
                                     result, malleation):
    """ Update the CNF to include the derived CNF constraints from
        an iterative constraint
    """
    add_res = result if MULT_OUTPUT else cnfS._bool(result)
    cnfS.push()
    for i in range(TRIALS):
        cnfS.add(
            cnfS._iff(
                ORACLE.do_query_smt_realMall(m1c_arr[i], cnfS, *malleation), add_res
            ),
            cnfS._iff(
                ORACLE.do_query_smt_realMall(m2c_arr[i], cnfS, *malleation), add_res
            ),
        )
    print("Making a new cnf....")
    start_t = time.time()
    new_cnf = cnfS.cnf(addTrue=False)
    print("Time to convert cnfS to cnf file {}".format(time.time() - start_t))
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
            elif inv_mapped.startswith("p") or inv_mapped.startswith("m") or inv_mapped == "true" or inv_mapped.startswith("v"):
                v = cnf.variables[inv_mapped]
            else:
                raise Exception("Invalid variable mapping lookup: {}".format(inv_mapped))
            new_cnf.clauses[i][j] = ("-" if neg else "") + v
    cnf.clauses.extend(new_cnf.clauses)

def AddIterativeConstraint_FinalSolver(finalS, fm, result, malleation):
    """ Update the final message solver to iteratively include the step in
        the adaptive attack
    """
    add_res = result if MULT_OUTPUT else finalS._bool(result)
    finalS.add(
        finalS._iff(ORACLE.do_query_smt_realMall(fm, finalS, *malleation), add_res),
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

def RecoverMalleation(malleation_fields, targ_map, cnf):
     all_fields = []
     for malleation in malleation_fields:
         mall_value = long(0)
         for b in range(malleation[1]):
             targ = cnf.variables["{}_{}".format(malleation[0],b)]
             mall_value |= (targ_map[targ] << b)
         all_fields.append(mall_value)
     return tuple(all_fields)

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
    # Change Malleation Recovery to also recover the time 
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
    with NamedTemporaryFile(mode="w+") as out:
        with NamedTemporaryFile(mode="w+") as f:
            cnf_to_file = str(cnf)
            f.write(cnf_to_file)
            cnf.xors = []
            f.seek(0)
            ret = subprocess.call(["cryptominisat5",
                                   "--verb", "0", "-t", str(procspersolver),
                                   f.name], stdout=out)
            if ret not in [CMS_SAT, CMS_UNSAT]:
                f.seek(0)
                subprocess.call(["cp", f.name, "new_cms_error_{}.cnf".format(ret)])
                raise Exception("CMS returned bad status {}".format(ret))
        out.seek(0)
        dimacs = out.readlines()
    if ret == CMS_SAT:
        targ_map = ExtractModel(dimacs)
        #mall = RecoverMalleation([('v', format.TIME_FIELD*8), ('p', format.length_field_size + format.bit_vec_length)], targ_map, cnf)
        mall = RecoverMalleation([('p', format.bit_vec_length + (2*format.length_field_size))], targ_map, cnf)
    elif ret == CMS_UNSAT:
        mall = None
    else:
        raise Exception("CMS returned bad status {}".format(ret))
    q.put((size, mall, time.time()-t0))

def logZ3Time(assertions):
    test_time = libSolver.Z3Solver()
    test_time.add(assertions)
    start_time = time.time()
    res = test_time.check()
    time_duration = time.time() - start_time
    if not res:
        raise ValueError("Implemented incorrectly")
    else:
       with open("debugZ3CMSBridge.log", "a") as write_f:
           write_f.write("{}\n".format(time_duration))

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
        for i in range(curr_size-WINDOW_SIZE*w,
                       max(curr_size-WINDOW_SIZE*(w+1), -1), -1):
            p = mp.Process(target=GetSizeResultCMS,
                           args=(q, cnf, i, unknown_positions)
            )
            p.daemon = True
            procs.append(p)
        map(lambda p: p.start(), procs)
        map(lambda p: p.join(), procs)
        for _ in range(len(procs)):
            size, mall_, time_run = q.get()
            if mall_ is not None:
                done = True
            if type(mall_) is not tuple:
                mall = (mall_,)
            else:
                mall = mall_
            size_results[size] = (mall, time_run)
        w += 1
    return size_results

def CreateBoolMapping(solver, m1_arr, m2_arr, auxiliary):
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
    for bv_pair in auxiliary:
        bv = bv_pair[1]
        bv_name = bv_pair[0]
        for j in range(bv.size()):
            mall_var = solver.bool("{}_{}".format(bv_name, j))
            solver.add(
                solver._eq(mall_var, solver._eq(solver.extract(bv, j, j), one))
            )

def Trial(bootstrap=None, log=None, prevcnf=""):
    # reinstantiate time vectors and change makestructuralconstraint
    # add constraints so the attack would actually be carried out in a reasonable amount of time
    # change the auxiliary information that gets printed
    write_debug_header()
    global ORACLE
    if bootstrap is None:
        realM = format.makePaddedMessage()
        #msg_size = realM & ((1 << format.length_field_size)-1)
        realM = format.makePaddedMessage()
        #state_obj
        #ORACLE.initialize_state(state_obj) 
        #check_against = time.time() * 10**9
        if not format.checkFormat(realM):
            #if not format.checkFormat(realM, check_against, state_obj):
            raise ValueError("makePaddedMessage created an invalid message")
    else:
        with open(bootstrap, "r") as read_f:
            firstline = read_f.readlines()[0]
            realM = int(firstline.split(" ")[6])
            #state_obj, ticket_time = format.initialize_state_from_ticket(realM)
            #ORACLE.initialize_state(state_obj)
            # add a few seconds to simulate a valid time
            #check_against = ticket_time + (4 * 10**9)
           # we're going to assume that any new attacks you are going to do at this time are going to be recently after you run the attack algorithm starting from now

    overall_start = time.time()
    # Setup solvers
    #procspersolver = int(NPROCS / WINDOW_SIZE)
    procspersolver = NPROCS
    assert procspersolver > 0
    libSolver.z3.set_param("parallel.enable", True)
    libSolver.z3.set_param("parallel.threads.max", procspersolver)
    solver = libSolver.Z3Solver(); cnfS = libSolver.Z3Solver()
    finalS = libSolver.Z3Solver()
    PopulateSizeResults = PopulateSizeResultsCMS
    m1_arr = []; m2_arr = []; m1c_arr = []; m2c_arr = []
    for t in range(TRIALS):
        m1_arr.append(solver.bv('m1_' + str(t), bit_vec_length))
        m2_arr.append(solver.bv('m2_' + str(t), bit_vec_length))
        m1c_arr.append(cnfS.bv('m1_' + str(t), bit_vec_length))
        m2c_arr.append(cnfS.bv('m2_' + str(t), bit_vec_length))
    # how long the malleation is also changes based on the malleation function
    p = solver.bv('p', format.bit_vec_length + (2*format.length_field_size));
    pC = cnfS.bv('p', format.bit_vec_length + (2*format.length_field_size))
    #time_var = solver.bv("v", format.TIME_FIELD * 8); time_var_c = cnfS.bv("v", format.TIME_FIELD * 8)
    fm = finalS.bv('fm', bit_vec_length)
    MakeStructuralConstraintMultiOutput(solver, m1_arr, m2_arr, format.checkFormatSMT, p)#time_var, check_against, state_obj, p)
    MakeStructuralConstraintMultiOutput(cnfS, m1c_arr, m2c_arr, format.checkFormatSMT, pC)#time_var, check_against, state_obj, pC)
    #time_duration = 60 * 60 * 5 * 10**9 # we want to conduct the attack over a short range of time
    #time_must_end = 60 * 60 * 24 * 10**9
    #const_now_time = (time.time()*(10**9))
    #solver.add(solver._uge(time_var, time_duration + const_now_time))
    #cnfS.add(cnfS._uge(time_var_c, time_duration + const_now_time))
    #solver.add(solver._ule(time_var, time_must_end + const_now_time))
    #cnfS.add(cnfS._ule(time_var_c, time_must_end + const_now_time))

    AddAttackerKnowledge(finalS, solver, m1_arr, m2_arr, fm, realM)
    AddAttackerKnowledge(None, cnfS, m1c_arr, m2c_arr, None, realM)
    CreateBoolMapping(solver, m1_arr, m2_arr, [("p", p)])#, ("v", time_var)])
    CreateBoolMapping(cnfS, m1c_arr, m2c_arr,[("p", pC)])#, ("v", time_var_c)])
    #final_time = finalS.bv("time", format.TIME_FIELD * 8)
    # assuming that the session ticket picked up actually is still "alive"
    finalS.add(
        finalS._eq(format.checkFormatSMT(fm, finalS), finalS.true())#check_against, state_obj), 1)
    )
    queryNum = 0
    if bootstrap is not None:
        print("Bootstrapping previous run....")
        queryNum, _, _ = bootstrapPrevRun(bootstrap, finalS, fm, solver, m1_arr, m2_arr)
        startQueryNum = queryNum + 1
    aux = "" #"State object is {}\n Valid time was {}".format(state_obj, check_against)
    InitTrialLogging(realM, aux)
    t0 = time.time()
    if prevcnf is "":
        if DOPRINT:
            print("Generating inital CNF...")
        print("Checking bit_blast")
        start_t = time.time()
        cnf = solver.cnf()
        end_duration = time.time() - start_t
        print("Amount of time it took to simplify and bit blast was {}".format(end_duration))
        out = DATE+"/"+TESTNAME+".cnf"
        if DOPRINT:
            print("Saving structural constraint CNF to file: {}".format(out))
        with open(out, 'w') as f:
            f.write("c map {}\n".format(json.dumps(cnf.variables)))
            in_mem = str(cnf)
            print("Size in bytes is {}".format(len(in_mem)))
            f.write(in_mem)
    else:
        if DOPRINT:
            print("Parsing previous CNF file {}...".format(prevcnf))
        cnf = bootstrapPrevCNF(prevcnf)
    if DOPRINT:
        print("Done ({}s)".format(time.time()-t0))
    curr_size = bit_vec_length

    unknown_positions = {i for i in range(bit_vec_length)}
    sol_vect = ['?' for _ in range(bit_vec_length)]
    while solver.check() and '?' in sol_vect:
        print("Time at start of query {} is {}".format(queryNum, time.time()))
        if DOPRINT:
            print "Starting query #", queryNum
        queryNum += 1
        # only going to conduct known bits every 10 queries to save time -- this is call is getting expensive (/approx 600 sec = 10 min)
        discovered_bits = False
        known_bits_call = -1
        if queryNum % 7 == 1 or (bootstrap is not None and queryNum == startQueryNum):
            t0 = time.time()
            
            if DOPRINT:
                print("Determining known bits...")
            sol_vect = finalS.knownbits("fm")
            msg_check = list(bin(realM)[2:].zfill(format.bit_vec_length))
            msg_check.reverse() 
            print("Checking to make sure no wrong bits were learned...")
            for i in range(len(sol_vect)):
                if sol_vect[i] != msg_check[i] and sol_vect[i] != "?":
                    raise ValueError("Learned a wrong bit")
            print("Finished check")
            known_bits_call = time.time() - t0
            if DOPRINT:
                print("Finished known bits query on final message ({}s)".format(known_bits_call))
            CNF_extract_time = -1
            if sol_vect.count('?') < curr_size: # did we learn some bits?
                discovered_bits = True
                curr_size = sol_vect.count('?')
                global K
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
        else:
            known_bits_call = -1
        # compact iterative constraints back into the solver
        if discovered_bits or queryNum % 10 == 0:
            t0 = time.time()
            if DOPRINT:
                print("Re-extracting CNF")
            
            # re-extract CNF now encoding all iterative constraints thus far
            CNF_extract_time = time.time()
            cnf = solver.cnf()
            CNF_extract_time = time.time() - CNF_extract_time

            if DOPRINT:
                print("Time to convert solver to cnf ({}s)".format(time.time()-t0))
        if DOPRINT:
            print "Solver knows ({} bits): {}".format(
                    bit_vec_length-curr_size, ''.join(list(reversed(sol_vect)))
            )
        CNF_clause = len(cnf.clauses)
        CNF_var = len(cnf.variables)
        t0 = time.time()
        size_results = PopulateSizeResults(solver, cnf, curr_size,
                                                m1_arr, m2_arr,
                                                realM, unknown_positions)
        if DOPRINT:
            print("Running CMS in parallel ({}s)".format(time.time()-t0))
            print("Processing CMS results...") 
        t1 = time.time()
        total_time, iterative_time = ProcessSizeResults(size_results, finalS, solver, cnfS, cnf,
                           fm, m1_arr, m2_arr, m1c_arr, m2c_arr, realM)
        if DOPRINT:
            print("Finished processing size results ({}s)".format(time.time()-t1))
        elap = time.time() - t0
        write_debug_to_file(queryNum, CNF_clause, CNF_var, iterative_time, total_time, known_bits_call, elap) 
        size_results = []
        if DOPRINT:
            print "Elapsed: {}s in query {}".format(elap, queryNum)
            print "Elapsed: {}s so far".format(time.time() - overall_start) 
        print("Time at end of query {} is {}".format(queryNum-1, time.time()))
    if DOPRINT:
        print "Fell through at current size {}".format(curr_size)

    cardinality_satisfied = 0
    sawGood = False
    # check to see if the final message is in the model and then do a model count
    finalS.push()

    finalS.add(finalS._eq(fm, realM))
    if finalS.check():
        sawGood = True
    finalS.pop()
    cardinality_satisfied, _ = finalS.approxmc()
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
            # first argument is actually time
            #res = ORACLE.do_query(realM, mall[0], mall[1])
            # malleation first, time is second
            res = ORACLE.do_query(realM, *mall)
            actual_size_mbound = i
            if DOPRINT:
                print("Success at size {} (oracle: {})".format(i, res))
            break
    iterative_time = -1
    if res is not None:
        t0 = time.time()
        if DOPRINT:
            print("Adding iterative constraints...")
        AddIterativeConstraint_IterativeSolver(solver, m1_arr, m2_arr,
                                               res, mall)
        AddIterativeConstraint_CNFSolver(cnfS, cnf, m1c_arr, m2c_arr, res, mall)
        AddIterativeConstraint_FinalSolver(finalS, fm, res, mall)
        iterative_time = time.time()-t0
        if DOPRINT:
            print("Time to add iterative constraints ({}s)".format(time.time()-t0))
        with open(GNU_LOG, "a") as log_w:
            log_w.write("{} {}\n".format(actual_size_mbound, total_time))
        with open(LOGNAME, "a") as log_w:
            log_w.write("{} {}\n".format(json.dumps(mall), res))
    else:
        if DOPRINT:
            print("No MBound-satisfiable malleations found")
        with open(GNU_LOG, "a") as log_w:
            log_w.write("{} {}\n".format(None, total_time))
    return (total_time, iterative_time)

def InitTrialLogging(realM, extra=None):
    """ Write initial information to the first lines of the log files """
    if DOPRINT:
        print "Real Message: {}".format(bin(realM))
    if ISRANDOM:
        format_header = "Full run of attack with message {} at {} Bit with trials {}, delta {}, and expected constraint length {}. Threshold for success is {}/{}\n".format(realM, format.test_length, TRIALS, DELTA, K, math.floor((DELTA + 0.5) * TRIALS), TRIALS)
    else:
        format_header = "Full run of attack with message {} at {} Bit with trials {}, delta {}, and k is {}. Threshold for success is {}/{}\n".format(realM, format.test_length, TRIALS, DELTA, K, math.floor((DELTA + 0.5) * TRIALS), TRIALS)
    with open(GNU_LOG, "w") as dat_write:
        dat_write.write(format_header)
        if extra is not None:
            dat_write.write(extra)
        dat_write.write("MBound size (log2) | Query time (longest in parallel)\n")        
    with open(LOGNAME, "w") as write_log:
        write_log.write(format_header)

def main():
    # Change the oracle from Time -> Malleation and change the plethora of malformation functions
    global TESTNAME, LOGNAME, CONSTRAINT_GROWTH, GNU_LOG, BOOTSTRAP, ORACLE, bit_vec_length, format
    try:
        TESTNAME = os.environ["NAME"]
    except KeyError as e:
        print "Must provide NAME in environment for log file name"
        raise e
    BOOTSTRAP = os.environ.get("PREV")
    LOGNAME = DATE+"/"+TESTNAME 
    GNU_LOG = DATE+"/"+TESTNAME
    CONSTRAINT_GROWTH = DATE + "/" + TESTNAME
    if not os.path.exists(DATE):
        os.mkdir(DATE)
    ext = 0
    while (os.path.exists(LOGNAME + ('_' + str(ext) if ext > 0 else '')+".log")
           or
           os.path.exists(GNU_LOG + ('_' + str(ext) if ext > 0 else '')+".dat")):
        ext += 1
    LOGNAME = DATE+"/"+TESTNAME+('_'+str(ext) if ext > 0 else '')+".log"
    GNU_LOG = DATE+"/"+TESTNAME+('_'+str(ext) if ext > 0 else '')+".dat"
    CONSTRAINT_GROWTH = DATE+"/"+TESTNAME+('_'+str(ext) if ext > 0 else '')+"constraint_size.log"
    if DOPRINT:
        print("Logging to {}".format(LOGNAME))
        print("Writing MBound results to {}".format(GNU_LOG))

    parser = argparse.ArgumentParser(description="Run format oracle attack")
    parser.add_argument("-f", "--format", type=str, required=True)
    parser.add_argument("-k", type=int, default=7)
    parser.add_argument("-t", "--trials", type=int, default=5)
    parser.add_argument("-d", "--delta", type=float, default=0.3)
    parser.add_argument("-p", "--procs", type=int, default=64)
    parser.add_argument("-w", "--window", type=int, default=64)
    parser.add_argument("-r", "--random", action='store_true')
    parser.add_argument("-c", "--cnf", type=str, default="")
    args = vars(parser.parse_args(sys.argv[1:]))
    global WINDOW_SIZE, NPROCS, ISRANDOM, K, TRIALS, DELTA
    format = importlib.import_module(args["format"])
    try:
        bit_vec_length = format.test_length * format.num_blocks + format.length_field_size
    except AttributeError:
        try:
            bit_vec_length = format.bit_vec_length
        except AttributeError:
            bit_vec_length = format.test_length
    ORACLE = oracle.MalleationOracle(format.checkFormat, format.checkFormatSMT, malformations.XOR_AND_TRUNC_MALLS[0], malformations.XOR_AND_TRUNC_MALLS[1], malformations.XOR_AND_TRUNC_MALLS[2])
    WINDOW_SIZE = args["window"]
    NPROCS = args["procs"]
    ISRANDOM = args["random"]
    K = args["k"]
    TRIALS = args["trials"]
    DELTA = args["delta"]
    prevcnf = args["cnf"]
    trial_res = Trial(bootstrap=BOOTSTRAP, prevcnf=prevcnf)
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
        return {k.encode('utf-8') if isinstance(k,unicode) else k : int(v)
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

def bootstrapPrevRun(filename, finalS, fm, solver, m1_arr, m2_arr):
    """ Continue a partial attack by extracting realM, malleations, and results
        from a log file
    """
    with open(filename) as f:
        lines = f.readlines()
    if DOPRINT:
        print("Bootstrapping from {} ({} queries)".format(filename, len(lines)-1))
    try:
        realM = int((lines[0].split(" "))[6])
        state_obj = format.initialize_state_from_ticket(realM)
    except Exception as e:
        print("Malformed bootstrap file")
        raise e
    queryNum = 0
    for line in lines[1:]:
        tokens = line.split("] ")
        if len(tokens) != 2: # malleation integer and oracle result
            continue
        try:
            mall = json.loads(tokens[0] + "]")
            res = int(tokens[1].strip())
        except ValueError as e:
            print("Malformed bootstrap file")
            raise e
        queryNum += 1
        AddIterativeConstraint_IterativeSolver(solver, m1_arr, m2_arr,
                                                   res, mall)
        AddIterativeConstraint_FinalSolver(finalS, fm, res, mall)
    return queryNum, realM, state_obj
    #return queryNum, realM

if __name__ == "__main__":
    exit(main())
