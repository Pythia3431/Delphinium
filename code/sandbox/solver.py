import z3
import copy
import stp
import subprocess
import time
from tempfile import NamedTemporaryFile

class CNF:
    def __init__(self):
        self.clauses = []
        self.xors = []
        self.variables = {}
        self.var = 1

    def newvar(self):
        v = str(self.var)
        self.var += 1
        return v

    def __str__(self):
        header = "c ind {} 0\np cnf {} {}\n".format(
                " ".join(self.variables.values()),
                len(self.variables), len(self.clauses)+len(self.xors)
        )
        body = ""
        for clause in self.clauses:
            c_str = " ".join(clause) + " 0\n"
            body += c_str
        for xor in self.xors:
            x_str = "x" + " ".join(xor) + " 0\n"
            body += x_str
        return header+body

class SolverInterface:
    """
        check() -> bool
        add([constraints]) -> None
        bv(name, length) -> bitvector
        _bool(bool) -> boolean value
        true() -> boolean value
        false() -> boolean value
        bvconst(value, length) -> bitvector value
        _not(expr) -> expr
        _SHIFT(bv, i) -> bv
            SHIFT = {lshift, rshift}
        _BINOP(expr, expr) -> expr
            BINOP = {and, or, xor, eq, mult, ule, uge, ult, ugt}
        _if(expr, expr, expr) -> expr
        _mod(expr, i) -> expr
        push() -> None
        pop() -> None
        model([names]) -> {(name: value) for name in names}
        assertions() -> [constraints]
        bvlen(name) -> size
        extract(bv, high, low) -> bv
        knownbits(name) -> ['0', '1', '?', ...]
        mbound(size, t, delta, k, bvs, subset) -> expr
        exact(name) -> count
        atleastx(name, x) -> bool
        cnf() -> cnf object, bitvector-variable map
        approxmc() -> count
    """
    def __init__(self):
        """ return new solver """
        raise NotImplementedError

    def check(self):
        """ check SAT """
        raise NotImplementedError

    def add(self, *constraints):
        """ add constraints """
        raise NotImplementedError

    def bv(self, name, length=0):
        """ return a named bitvector or a new one
            if the name doesn't exist yet
        """
        raise NotImplementedError

    def true(self):
        """ return new boolean constant """
        raise NotImplementedError

    def false(self):
        """ return new boolean constant """
        raise NotImplementedError

    def bvconst(self, value, length):
        """ return new bv constant """
        raise NotImplementedError

    def bool(self):
        """ return new boolean """
        raise NotImplementedError

    def _bool(self, value):
        if value is True:
            return self.true()
        elif value is False:
            return self.false()
        else:
            raise ValueError("_bool can only cant bool, not {} ({})".format(value, type(value)))

    def _and(self, bv1, bv2):
        """ bitwise and """
        raise NotImplementedError

    def _or(self, bv1, bv2):
        """ bitwise or """
        raise NotImplementedError

    def _xor(self, bv1, bv2):
        """ bitwise xor """
        raise NotImplementedError

    def _eq(self, bv1, bv2):
        """ bitwise compare """
        raise NotImplementedError

    def _iff(self, b1, b2):
        """ if and only if
            eq for booleans
        """
        raise NotImplementedError

    def _not(self, bv):
        """ bitwise not """
        raise NotImplementedError

    def _if(self, cond, then, els):
        """ ternary conditional """
        raise NotImplementedError

    def _lshift(self, bv, i):
        """ left shift (drop upper bits, shift in 0s) """
        raise NotImplementedError

    def _rshift(self, bv, i):
        """ right shift (drop lower bits, shift in 0s) """
        raise NotImplementedError

    def _mult(self, bv1, bv2):
        """ unsigned multiplication """
        raise NotImplementedError

    def _mod(self, bv, mod):
        """ unsigned modulo """
        raise NotImplementedError

    def _ule(self, bv1, bv2):
        """ unsigned less than or equal """
        raise NotImplementedError

    def _uge(self, bv1, bv2):
        """ unsigned greater than or equal """
        raise NotImplementedError

    def _ult(self, bv1, bv2):
        """ unsigned less than """
        return self._not(self._uge(bv1, bv2))

    def _ugt(self, bv1, bv2):
        """ unsigned greater than """
        return self._not(self._ule(bv1, bv2))

    def implies(self, bv1, bv2):
        return self._and(self._not(bv1), bv2)

    def push(self):
        """ push solver state """
        raise NotImplementedError

    def pop(self):
        """ pop solver state """
        raise NotImplementedError

    def model(self, *names):
        """ extract concrete values for bitvectors """
        raise NotImplementedError

    def assertions(self):
        """ extract assertions list """
        raise NotImplementedError

    def bvlen(self, name):
        """ get length of a bitvector """
        raise NotImplementedError

    def extract(self, bv, high, low):
        """ get sub-bitstring of a bitvector
            NOTE high, low
        """
        raise NotImplementedError

    def knownbits(self, name):
        """ get list of '0', '1', or '?' for bitvector
            lower bound on information about a bitvector
        """
        if name in self.knownbitscache:
            previous = self.knownbitscache[name]
        else:
            previous = []
        _bv = self.bv(name)
        l = self.bvlen(name)
        soln = ['?']*l
        if not self.check():
            raise ValueError("Solver must be satisfiable")
        for i in range(l):
            if len(previous) != 0 and previous[i] != '?':
                soln[i] = previous[i]
                continue
            critical = False
            for guess in (0, 1):
                self.push()
                self.add(self.extract(_bv,i,i) != self.bvconst(guess,1))
                if not self.check():
                    critical = True
                    soln[i] = str(guess)
                    self.pop()
                    break
                self.pop()
            if not critical:
                soln[i] = '?'
        self.knownbitscache[name] = copy.copy(soln)
        return soln

    def mbound(self, size, t, delta, bvs, subset, parity):
        """ mbound count the current solver
            bvs is an array of bitvecs of length t with the same
            constraints on them
        """
        trials_passed = self.bvconst(0, t) # only need log(t) bits but w/e
        for trial in range(t):
            compound = self.true()
            for i in range(size):
                inner = self.bvconst(0,1)
                for idx in range(len(subset[trial][i])):
                    row_val = subset[trial][i][idx]
                    inner = self._xor(
                            inner,
                            self.extract(bvs[trial], row_val, row_val)
                    )
                parity_i = self.bvconst(parity[trial][i], 1)
                compound = self._and(compound, self._eq(inner, parity_i))
            trials_passed = self._if(compound,
                                     trials_passed+self.bvconst(1,t),
                                     trials_passed)
        return self._uge(trials_passed, self.bvconst(int(((0.5+delta)*t)), t))

    def approxandtime(self):
        with NamedTemporaryFile(mode='w+') as f:
            cnf_start = time.time()
            cnf_duration = time.time() - cnf_start
            f.write(write_stream)
            f.seek(0)
            try:
                output = subprocess.check_output(['approxmc', f.name])
            except subprocess.CalledProcessError as e:
                if "UNSAT" in e.output:
                    raise ValueError("Solver must be satisfiable")
                elif "Number of solutions" in e.output:
                    sols = e.output[e.output.find("Number of solutions"):]
                    sols = sols.split(": ")[1].split(" x ")
                    total = 1
                    for number in sols:
                        number = number.strip()
                        if "^" in number:
                            sub = number.split("^")
                            num = int(sub[0])**int(sub[1])
                        else:
                            num = int(number)
                        total *= num
                    return total, cnf_duration
                else:
                    raise e

    def approxmc(self):
        """ approxmc count the current solver """
        with NamedTemporaryFile(mode='w+') as f:
            cnf_start = time.time()
            write_stream = str(self.cnf())
            cnf_duration = time.time() - cnf_start
            f.write(write_stream)
            f.seek(0)
            try:
                output = subprocess.check_output(['approxmc', f.name])
            except subprocess.CalledProcessError as e:
                if "UNSAT" in e.output:
                    print(e.output)
                    raise ValueError("Solver must be satisfiable")
                elif "Number of solutions" in e.output:
                    sols = e.output[e.output.find("Number of solutions"):]
                    sols = sols.split(": ")[1].split(" x ")
                    total = 1
                    for number in sols:
                        number = number.strip()
                        if "^" in number:
                            sub = number.split("^")
                            num = int(sub[0])**int(sub[1])
                        else:
                            num = int(number)
                        total *= num
                    return total, cnf_duration
                else:
                    raise e

    def cnf(self):
        raise NotImplementedError

    def exact(self, name):
        """ exact count the current solver on the named bitvec """
        self.push()
        count = 0
        while self.check():
            count += 1
            m = self.model([name])[name]
            self.add(self._not(self._eq(self.bv(name),
                                        self.bvconst(m, self.bvlen(name)))))
        self.pop()
        return count

    def atleastx(self, name, x):
        self.push()
        count = 0
        while self.check() and count < x:
            count += 1
            m = self.model(name)[name]
            self.add(self._not(self._eq(self.bv(name),
                                        self.bvconst(m, self.bvlen(name)))))
        self.pop()
        return count == x

class Z3Solver(SolverInterface):
    def __init__(self):
        self.solver = z3.SolverFor("QF_BV")
        self.solver.set("cache_all", True)
        self.bitvecs = {}
        self.knownbitscache = {}
        self.malleations = []
        
    def unsat_core(self):
        return self.solver.unsat_core()

    def check(self):
        is_satisfiable = self.solver.check()
        if is_satisfiable == z3.sat:
            return True
        elif is_satisfiable == z3.unsat:
            return False
        else:
            raise ValueError("Z3 Solver returned neither sat nor unsat")

    def add(self, *constraints):
        self.solver.add(*constraints)

    def bv(self, name, length=0):
        if name in self.bitvecs:
            return self.bitvecs[name]
        else:
            if length == 0:
                raise ValueError("New bitvecs must specify length")
            self.bitvecs[name] = z3.BitVec(name, length)
            return self.bitvecs[name]

    def bool(self, name):
        return z3.Bool(name)

    def true(self):
        return True

    def false(self):
        return False

    def bvconst(self, value, length):
        return z3.BitVecVal(value, length)

    def udiv(self, bv1, bv2):
        return z3.UDiv(bv1, bv2)

    def _and(self, bv1, bv2):
        return z3.And(bv1, bv2)

    def _or(self, bv1, bv2):
        return z3.Or(bv1, bv2)

    def _bitwiseor(self, bv1, bv2):
        return bv1 | bv2

    def _xor(self, bv1, bv2):
        return bv1 ^ bv2

    def _eq(self, bv1, bv2):
        return bv1 == bv2

    def _iff(self, bv1, bv2):
        return bv1 == bv2

    def _not(self, bv):
        return z3.Not(bv)

    def _if(self, cond, then, els):
        return z3.If(cond, then, els)

    def _lshift(self, bv, i):
        return (bv << i)

    def _rshift(self, bv, i):
        """ Change necessary here because Z3 will not
            let you shift bitvectors by bvs of differing lengths
            this is a hack
        """
        if isinstance(i, z3.BitVecRef):
            len_i = i.size()
            len_bv = bv.size()
            if len_i > len_bv: 
                raise ValueError("No support right now for logical shifts by bit vectors greater than the original bv length. :(")
                ext_bv = z3.ZeroExt(len_i - len_bv, bv)
            elif len_bv > len_i:
                ext_i = z3.ZeroExt(len_bv - len_i, i)
                return z3.LShR(bv, ext_i)
            else:
                return z3.LShR(bv,i)
        return z3.LShR(bv, i)

    def _mult(self, bv1, bv2):
        return (bv1 * bv2)

    def _mod(self, bv, mod):
        return (bv % mod)

    def _div(self, bv1, bv2):
        return (bv1 // bv2)

    def _ule(self, bv1, bv2):
        return z3.ULE(bv1, bv2)

    def _uge(self, bv1, bv2):
        return z3.UGE(bv1, bv2)

    def _ult(self, bv1, bv2):
        return self._not(self._uge(bv1, bv2))

    def _ugt(self, bv1, bv2):
        return self._not(self._ule(bv1, bv2))

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def assertions(self):
        return self.solver.assertions()

    def model(self, *names):
        m = self.solver.model()
        result = {}
        for n in names:
            result[n] = m[self.bv(n)].as_long()
        return result

    def bvlen(self, name):
        return self.bitvecs[name].size()

    def cnf(self, addTrue=True):
        goal = z3.Goal()
        goal.add(self.solver.assertions())
        tactic = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')
        subgoal = tactic(goal)
        cnf = CNF()
        for clause in subgoal[0]: # each clause is ANDed together
            cnf_clause = []
            if not clause.children():
                # clause is a bare variable
                if str(clause) in cnf.variables:
                    v = cnf.variables[str(clause)]
                else:
                    v = cnf.newvar()
                    cnf.variables[str(clause)] = v
                cnf_clause.append(v)
            else:
                # clause is an OR or a NOT
                if clause.decl().name() == 'or':
                    for subclause in clause.children():
                        if subclause.decl().name() == "not":
                            # negated variable
                            negated = subclause.children()
                            if len(negated) != 1:
                                raise ValueError("Malformed NOT in CNF")
                            if str(negated[0]) in cnf.variables:
                                v = cnf.variables[str(negated[0])]
                            else:
                                v = cnf.newvar()
                                cnf.variables[str(negated[0])] = v
                            cnf_clause.append("-{}".format(v))
                        else:
                            # variable
                            if subclause.children():
                                raise ValueError("Expected variable, got {}".format(subclause.decl().name()))
                            if str(subclause) in cnf.variables:
                                v = cnf.variables[str(subclause)]
                            else:
                                v = cnf.newvar()
                                cnf.variables[str(subclause)] = v
                            cnf_clause.append(v)
                elif clause.decl().name() == 'not':
                    negated = clause.children()
                    if len(negated) != 1:
                        raise ValueError("Malformed NOT in CNF")
                    if str(negated[0]) in cnf.variables:
                        v = cnf.variables[str(negated[0])]
                    else:
                        v = cnf.newvar()
                        cnf.variables[str(negated[0])] = v
                    cnf_clause.append("-{}".format(v))
                else:
                    raise ValueError("Expected NOT, got {}".format(clause.decl().name()))
            if cnf_clause: # if we somehow had an empty OR or empty NOT, skip
                cnf.clauses.append(cnf_clause)
        if addTrue:
            true = cnf.newvar()
            cnf.variables["true"] = true
            cnf.clauses.append([true])
        return cnf

    def extract(self, bv, high, low):
        return z3.Extract(high, low, bv)

    def concat(self, *bvs):
        return z3.Concat(bvs)

    def extend(self, bv, n_zeroes):
        return z3.ZeroExt(n_zeroes,bv)

class STPSolver(SolverInterface):
    def __init__(self):
        self.solver = stp.Solver()
        self.solver.useCryptominisat()
        if not self.solver.isUsingCryptominisat():
            print("Solver not using cryptominisat")
        self.bitvecs = {}
        self.knownbitscache = {}
        self.malleations = []

    def check(self):
        return self.solver.check()

    def add(self, *constraints):
        self.solver.add(*constraints)

    def bv(self, name, length=0):
        if name in self.bitvecs:
            return self.bitvecs[name][0]
        else:
            if length == 0:
                raise ValueError("New bitvecs must specify length")
            self.bitvecs[name] = (self.solver.bitvec(name, length), length)
            return self.bitvecs[name][0]

    def true(self):
        return self.solver.true()

    def false(self):
        return self.solver.false()

    def bvconst(self, value, length):
        return self.solver.bitvecval(length, value)

    def _and(self, bv1, bv2):
        return self.solver.and_(bv1, bv2)

    def _or(self, bv1, bv2):
        return self.solver.or_(bv1, bv2)

    def _xor(self, bv1, bv2):
        return bv1 ^ bv2

    def _eq(self, bv1, bv2):
        return bv1 == bv2

    def _iff(self, b1, b2):
        return self.solver.iff(b1, b2)

    def _not(self, bv):
        return self.solver.not_(bv)

    def _if(self, cond, then, els):
        return self.solver.ite(cond, then, els)

    def _lshift(self, bv, i):
        return (bv << i)

    def _rshift(self, bv, i):
        return (bv >> i)

    def _mult(self, bv1, bv2):
        return (bv1 * bv2)

    def _mod(self, bv, mod):
        return (bv % mod)

    def _ule(self, bv1, bv2):
        return (bv1 <= bv2)

    def _uge(self, bv1, bv2):
        return (bv1 >= bv2)

    def _ult(self, bv1, bv2):
        return (bv1 < bv2)

    def _ugt(self, bv1, bv2):
        return (bv1 > bv2)

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def model(self, *names):
        m = self.solver.model()
        result = {}
        for n in names:
            result[n] = m[n]
        return result

    def bvlen(self, name):
        return self.bitvecs[name][1]

    def extract(self, bv, high, low):
        return bv.extract(high, low)
