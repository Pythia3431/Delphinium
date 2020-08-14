import truncate
import xor_with_extension

import formats
format = formats.CURRENT_FORMAT
mall_size = format.test_length + (2*format.length_field_size)

def maul(msg, mall_packed):
    mall =  mall_packed >> (2 * format.length_field_size)
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1)
    msg_truncated = truncate.maul(msg, trunc)
    final_msg = xor_with_extension.maul(msg_truncated, mall)
    return final_msg

def maulSMTMsg(msg, mall_packed, solver):
    mall =  mall_packed >> (2 * format.length_field_size)
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1)
    msg_truncated = truncate.maulSMTMsg(msg, trunc, solver)
    return xor.maulSMTMsg(msg_truncated, mall, solver)

def maulSMT(msg, mall_packed, solver):
    mall =  solver.extract(mall_packed, mall_packed.size()-1, 2 * format.length_field_size)
    trunc = solver.extract(mall_packed, 2 * format.length_field_size-1, 0)
    msg_trunc = truncate.maulSMT(msg, trunc, solver)
    return xor_with_extension.maulSMT(msg_trunc, mall, solver)

def AddMalleationConstraints(solver, packed_mall, msg_vector):
    xor_with_extension.AddMalleationConstraints(solver, packed_mall, msg_vector)
     
