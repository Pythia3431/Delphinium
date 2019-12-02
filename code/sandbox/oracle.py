class Oracle(object):
    def __init__(self, format_func, smt_format_func, malform_func, malformSMT=None):
        self.mangle = malform_func
        self.check_format = format_func
        self.check_format_smt= smt_format_func
        self.mangle_smt = malformSMT
    
    def do_query(self, message, *malleation):
        return self.check_format(self.mangle(message, *malleation))

    def do_query_smt(self, message, solver, *malleation):
        if self.mangle_smt: 
            return self.check_format_smt(self.mangle_smt(message, solver, *malleation), solver)
        return self.check_format_smt(self.mangle(message, *malleation), solver)

# need support for a malleation function that takes in a solver object 
class MalleationOracle(Oracle):
    def __init__(self, format_func, smt_format_func, malform_realMall_realMsg, malform_realMall_symbMsg, malform_symbMall_symbMsg):
        super(MalleationOracle, self).__init__(format_func, smt_format_func, malform_realMall_realMsg)
        self.mangle_realM = malform_realMall_symbMsg
        self.mangle_smt = malform_symbMall_symbMsg

    def do_query(self, message, *malleation):
        mangled_res = self.mangle(message, *malleation)
        return self.check_format(mangled_res) 

    def do_query_smt(self, message, solver, *malleation):
        mangled_res = self.mangle_smt(message, solver, *malleation)
        return self.check_format_smt(mangled_res, solver)

    def do_query_smt_realMall(self, message, solver, *malleation):
        mangled_res = self.mangle_realM(message, solver, *malleation)
        return self.check_format_smt(mangled_res, solver)

class TimeOracle(Oracle):
    def __init__(self, format_func, smt_format_func, malform_func, malform_SMTMsg, malformSMT):
        super(TimeOracle, self).__init__(format_func, smt_format_func, malform_func, malformSMT)        
        self._state = None
        self.malformSMTMsg = malform_SMTMsg

    def initialize_state(self, realMState):
        self._state = realMState

    def do_query(self, message, time, *malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")
        mangled_res = self.mangle(message, *malleation)  
        return self.check_format(mangled_res, time, self._state)

    def do_query_smt(self, message, solver, time, *malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")   
        mangled_res = self.mangle_smt(message, solver, *malleation)
        return self.check_format_smt(mangled_res, solver, time, self._state)

    def do_query_smt_realMall(self, message, solver, time, *malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")  
        if type(time) is not int and type(time) is not long:
            raise TypeError("Time value MUST be real when doing an actual query")
        mangled_res = self.malformSMTMsg(message, solver, *malleation)
        return self.check_format_smt(mangled_res, solver, time, self._state)
