# CNF Utility Functions 

## Solver/CNF Glue ###############################

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
    eltsToTrack = len(m1_arr)
    for t in range(eltsToTrack): # for each trial
        bitsPerElt = m1_arr[t].size()
        for i in range(bitsPerElt): # for each bit
            b1 = solver.bool('m1_t{}_{}'.format(t, i))
            b2 = solver.bool('m2_t{}_{}'.format(t, i))
            solver.add(
                solver._eq(b1, solver._eq(solver.extract(m1_arr[t], i, i), one)))
            solver.add(
                solver._eq(b2, solver._eq(solver.extract(m2_arr[t], i, i), one)))
    bitsPerMall = p.size()
    for i in range(bitsPerMall):
        pi = solver.bool("p_{}".format(i))
        solver.add(solver._eq(pi, solver._eq(solver.extract(p, i, i), one)))

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

## Pure CNF functions ############################

def updateCurrentCNF(cnf, new_cnf):
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
