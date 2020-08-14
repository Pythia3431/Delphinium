import truncate
import xor 

import formats
format = formats.CURRENT_FORMAT
mall_size = (format.length_field_size * 2) + test_length

def maul(msg, mall_packed):
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1)
    mall = mall_packed >> 2*format.length_field_size
    res = truncate.maul(msg, trunc)
    return xor.maul(res, mall)

def maulSMT(msg, mall_packed, solver):
    trunc = solver.extract(mall_packed, 2*format.length_field_size -1, 0)
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    res = truncate.maulSMT(msg, trunc, solver)
    return xor.maulSMT(res, mall, solver)

def maulSMTMsg(msg, mall_packed, solver):
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1)
    mall = mall_packed >> 2*format.length_field_size
    res = truncate.maulSMTMsg(msg, trunc, solver)
    return xor.maulSMTMsg(res, mall, solver)

def XORIsNotExt(solver, mall_packed, msg):
    # after you truncate, the malleation should not extend the message 
    trunc = solver.extract(mall_packed, 2*format.length_field_size -1, 0)
    trunc_end = solver.extract(trunc, 2*format.length_field_size -1, format.length_field_size)
    trunc_beg = solver.extract(trunc, format.length_field_size-1, 0)
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    msg_len = solver.extract(msg, format.length_field_size-1,0)
    max_mall_length = solver.extend(msg_len - (trunc_beg+trunc_end),mall.size() - msg_len.size())
    return solver._ule(mall, (1 << max_mall_length)-1)

def AddMalleationConstraints(solver, mall_packed, msg_vectors):
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    # no extension
    solver.add(solver._eq(solver.extract(mall, format.length_field_size-1, 0), 0))
    all_msg_constr = solver.true()
    for msg in msg_vectors:
        all_msg_constr = solver._and(all_msg_constr, XORIsNotExt(solver, mall_packed, msg))
    solver.add(all_msg_constr)
    return


