import xor_and_truncate

import formats
format = formats.CURRENT_FORMAT
mall_size = format.test_length + (format.length_field_size*2)

maul = xor_and_truncate.maul

maulSMT = xor_and_truncate.maulSMT

maulSMTMsg = xor_and_truncate.maulSMTMsg

def AddMalleationConstraints(solver, mall_packed, msg_vectors):
    xor_and_truncate.AddMalleationConstraints(solver, mall_packed, msg_vectors)

    trunc = solver.extract(mall_packed, 2*format.length_field_size -1, 0)
    trunc_beg = trunc & ((1 << format.length_field_size)-1)
    solver.add(solver._eq(solver._mod(trunc_beg, block_size), 0))

    return




