import formats

format = formats.CURRENT_FORMAT
mall_size = format.test_length

def maul(msg, mall, solver=None):
    return (msg ^ mall)

maulSMT = maul

maulSMTMsg = maul

def AddMalleationConstraints(solver, mall, msg_vectors):
    return
