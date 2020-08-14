from TLSCBC_For_Network_Test.shim import Client
import math

# temporary fix -- this will be changed
def processLibrary(library):
    subsetAvailable = dir(library)
    pure_smt_malform_func = None
    real_smt_malform_func = None
    malform_func = None
    mallBot = False
    if "mallBotOutput" in subsetAvailable:
        mallBot = library.mallBotOutput
    if not "maul" in subsetAvailable:
        raise ImportError("malform func doesn't exist --") 
    else:
        malform_func = library.maul
    if "maulSMT" in subsetAvailable:
        pure_smt_malform_func = library.maulSMT
    if "maulSMTMsg" in subsetAvailable:
        real_smt_malform_func = library.maulSMTMsg
    return malform_func, pure_smt_malform_func, real_smt_malform_func, mallBot 

# the oracle to be used w/ the p.t. message 
class Oracle(object):
    def __init__(self, format_func, smt_format_func,
                            malformLibrary):
        malform_func, pure_smt_malform_func, real_smt_malform_func, mallBotOutput = processLibrary(malformLibrary)
        self.mangle = malform_func
        self.check_format = format_func
        self.check_format_smt = smt_format_func

        if pure_smt_malform_func is None:
            self.pure_smt_malform_func = self.mangle
        else:
            self.pure_smt_malform_func = pure_smt_malform_func
        if real_smt_malform_func is None:
            self.real_smt_malform_func = pure_smt_malform_func
        else:
            self.real_smt_malform_func = real_smt_malform_func
        if isinstance(mallBotOutput, bool) and mallBotOutput:
            self.mall_bot = mallBotOutput
            self.outputSize = int(math.ceil(math.log(3, 2))) # I know this is 2
            # keeping it around because we may want to support functions with
            # larger output range
            self.cardinality = 3
        else:
            self.outputSize = 1
            self.cardinality = 2

        return
   
    # query that uses the real message -- information hidden 
    # from adversary  
    def do_query(self, message, malleation):
        return self.check_format(self.mangle(message, malleation))

    # for the solver, uses a *symbolic representation* of the 
    # message
    def _query_constr(self, message, malleation, output, solver, pure):
        malform_func = None
        if pure:
            malform_func = self.pure_smt_malform_func
        else:
            malform_func = self.real_smt_malform_func
        malled_res = malform_func(message, malleation, solver)
        if self.cardinality == 2:
            return solver._iff(self.check_format_smt(malled_res, solver), bool(output))
        else:
            return solver._iff(self.check_format_smt(malled_res, solver), solver.bvconst(output, self.outputSize))

    def pure_query_constr(self, message, malleation, output, solver): 
        return self._query_constr(message, malleation, output, solver, True)

    def query_constr(self, message, malleation, output, solver):
        return self._query_constr(message, malleation, output, solver, False)

    def correct_msg_constr(self, message, solver):
        if self.cardinality == 2:
            return solver._iff(self.check_format_smt(message, solver), True)
        else:
            return solver._iff(self.check_format_smt(message, solver), solver.bvconst(1, self.outputSize))

# the oracle w/ the c.t. that calls a remote service
class NetworkOracle(Oracle):
    def __init__(self, ct, smt_format_func, malform_func, malformSMT=None):
        self.mangle = malform_func
        self.check_format_smt = smt_format_func
        self.mangle_smt = malformSMT
        self.c = Client(ct)

    def do_query(self, mall):
        return self.c.send(mall)

    def shutdown(self):
        self.c.done()

# still experimental, not supported fully in codebase 
class OracleWithState(Oracle):
    def __init__(self, format_func, smt_format_func, malform_func, malform_SMTMsg, malformSMT):
        super(OracleWithState, self).__init__(format_func, smt_format_func, malform_func, malformSMT)        
        self._state = None

    def initialize_state(self, realMState):
        self._state = realMState

    def do_query(self, message, time, malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")
        mangled_res = self.mangle(message, malleation)  
        return self.check_format(mangled_res, time, self._state)

    def do_query_smt(self, message, solver, time, malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")   
        mangled_res = self.mangle_smt(message, malleation, solver)
        return self.check_format_smt(mangled_res, solver, time, self._state)

    def do_query_smt_realMall(self, message, solver, time, malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")  
        if type(time) is not int and type(time) is not long:
            raise TypeError("Time value MUST be real when doing an actual query")
        mangled_res = self.malformSMTMsg(message, malleation, solver)
        return self.check_format_smt(mangled_res, solver, time, self._state)
