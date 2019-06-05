class Oracle(object):
    def __init__(self, format_func=None, smt_format_func=None, malform_func=None, malformSMT=None):
        if not malform_func:
            raise ValueError("Need a malform function")
        if not format_func:
            raise ValueError("Need a format function")
        if not smt_format_func:
            raise ValueError("Need an smt format function")
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

""" Malleation Oracle needed for malleatino function to take in a solver object""" 
class MalleationOracle(Oracle):
    def __init__(self, format_func, smt_format_func, malform_func, malform_real, malform_symb):
        super(MalleationOracle, self).__init__(format_func, smt_format_func, malform_func)
        self.mangle_realM = malform_real
        self.mangle_smt = malform_symb

    # need to overwrite Oracle do_query function completely
    def do_query(self, message, *malleation):
        mangled_res, mask = self.mangle(message, *malleation)
        return self.check_format(mangled_res, mask) 

    def do_query_smt(self, message, solver, *malleation):
        mangled_res, mask = self.mangle_smt(message, solver, *malleation)
        return self.check_format_smt(mangled_res, solver, mask)

    def do_query_smt_realMall(self, message, solver, *malleation):
        mangled_res, mask = self.mangle_realM(message, solver, *malleation)
        return self.check_format_smt(mangled_res, solver, mask)
""" Time Oracle class needed for format function that is stateful"""
class TimeOracle(Oracle):
    def __init__(self, format_func, smt_format_func, malform_func, malformSMT):
        super(TimeOracle, self).__init__(format_func, smt_format_func, malform_func, malformSMT)        
        self._state = None

    def initialize_state(self, realMState):
        self._state = realMState

    def do_query(self, message, time, *malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")
        mangled_res = self.mangle(message, *malleation)  
        return self.check_format(mangled_res, time, self._state, *malleation)

    def do_query_smt(self, message, solver, time, *malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")   
        mangled_res = self.mangle_smt(message, solver, *malleation)
        return self.check_format_smt(mangled_res, solver, time, self._state, *malleation)

    def do_query_smt_realMall(self, message, solver, time, *malleation):
        if self._state is None:
            raise ValueError("Need to initialize query message state")  
        if type(time) is not int and type(time) is not long:
            raise TypeError("Time value MUST be real when doing an actual query")
        mangled_res = self.mangle_smt(message, solver, *malleation, symb_mall=False)
        return self.check_format_smt(mangled_res, solver, time, self._state, *malleation)
