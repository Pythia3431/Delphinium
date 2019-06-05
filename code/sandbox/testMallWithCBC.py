import solver as solver_t
import malformations as malform
import formats.PKCS7MultBlocks as formats
# IMPORTANT: when doing this test please do it with the block size set to 
# 16 bytes 
bit_vec_length = (formats.test_length * formats.num_blocks) + formats.length_field_size

def truncateTest():
    print("Truncate Test\n----------------------------------")
    z3solver = solver_t.Z3Solver()

    s1 = z3solver.bv("s1", bit_vec_length)
    # try trunc here with symbolic value
    t1 = z3solver.bv("t1", 2*formats.length_field_size)
    z3solver.add(z3solver._eq(t1, formats.test_length))
    z3solver.add(z3solver._eq(z3solver.extract(s1, formats.length_field_size - 1, 0), formats.test_length * 2))
    z3solver.add(z3solver._eq(malform.truncate_SMT(s1, t1, z3solver) >> formats.length_field_size, 432))
    if not z3solver.check():
        raise ValueError("Should still be satisfiable - first check")
    model_string = z3solver.model("s1")["s1"]
    # try trunc with actual malleation
    if (model_string >> (formats.length_field_size + formats.test_length)) == 432:
        print("Succeeded symbolic trunc test")
    else:
        raise ValueError("Failed symbolic trunc test, string model is {}".format(model_string >> 128))
    

    second_solver = solver_t.Z3Solver()
    s2 = second_solver.bv("s2", bit_vec_length)
    t2 = formats.test_length
    second_solver.add(second_solver._eq(second_solver.extract(s2, formats.length_field_size - 1, 0), formats.test_length * 2))
    second_solver.add(
        second_solver._eq(malform.truncate_SMT(s2, t2, second_solver, symb_mall=False) >> formats.length_field_size, 514)
    )

    if not second_solver.check():
        raise ValueError("Should still be satisfiable - second check")

    string2 = second_solver.model("s2")["s2"]
    if (string2 >> (formats.length_field_size + formats.test_length)) == 514:
        print("Succeeded real trunc test")
    else:
        raise ValueError("Failed real trunc test, string model is {}".format(string2 >> 128))

    return

def checkPKCSFormat():
    print("Testing PKCS 7 Format Function\n--------------------------------")
    new_solver = solver_t.Z3Solver()
    msgn = new_solver.bv("msgn", bit_vec_length)
    new_solver.add(new_solver._eq(formats.checkFormatSMT(msgn, new_solver), 1))
    if new_solver.check():
        message_model = new_solver.model("msgn")["msgn"]
        if not formats.checkFormat(message_model):
            raise ValueError("Message {} does not match the PKCS7 format specified by checkFormat".format(message_model))
        else:
            print("Succeeded PKCS Format Check")
    else:
        raise Exception("Solver is not even satisfiable, fail.")
    return

def CBCmodetest():
    print("CBC Malleation Test\n---------------------------------")
    cbc_solver = solver_t.Z3Solver()
    msg = cbc_solver.bv("msg", bit_vec_length)
    symb_trunc = cbc_solver.bv("mall_trunc", 2*formats.length_field_size)
    symb_mall = cbc_solver.bv("mall",formats.max_msg_size)
    no_taint = cbc_solver.bvconst(0, bit_vec_length)
    cbc_solver.add(cbc_solver._eq(formats.checkFormatSMT(msg, cbc_solver), 1))
    cbc_solver.add(cbc_solver._eq(symb_trunc, 0))
    cbc_solver.add(cbc_solver._eq(symb_mall, 1 << (formats.test_length + 8)))
    zerror, mask = malform.CBC_MODE_symb_mall_msg(msg,cbc_solver,symb_mall,symb_trunc)
    cbc_solver.add(
        cbc_solver._eq(
            formats.checkFormatSMT(zerror, cbc_solver, mask),
            1
        )
    )

    if not cbc_solver.check():
        raise Exception("FAILED to pass a format check")
        return

    msg_value = cbc_solver.model("msg")["msg"]
    for i in range(10):
        if ((msg_value >> formats.length_field_size) & ((1 << formats.test_length)-1)) & ((1 << 8)-1) != 1:
            msg_malleated, mask = malform.CBC_MODE(msg_value, 1 << (formats.test_length + 8), 0)
            format_result = formats.checkFormat(msg_malleated, mask)
            raise Exception("Failed whole integration CBC test on round {}".format(i))
        cbc_solver.add(msg != msg_value)

    # cut from left side test for truncate
    sec_cbc = solver_t.Z3Solver()
    sec_msg = sec_cbc.bv("secmsg", bit_vec_length)
    sec_cbc.add(sec_cbc._eq(sec_cbc.extract(sec_msg, formats.length_field_size - 1, 0), formats.test_length * 2))
    mall = 1 << (formats.test_length + 8)
    trunc = formats.test_length << (formats.length_field_size)

    sec_cbc.add(
        sec_cbc._eq(
            formats.checkFormatSMT(sec_msg,sec_cbc),
            1
        )
    )
    second_zerror, second_mask = malform.CBC_MODE_symb_msg(sec_msg, sec_cbc, mall, trunc)
    sec_cbc.add(
        sec_cbc._eq(
            formats.checkFormatSMT(second_zerror, sec_cbc, second_mask),
            1
        )
    )

    if not sec_cbc.check():
        raise Exception("Failed even solver satisfiability check")

    some_msg = sec_cbc.model("secmsg")["secmsg"]
    if ((some_msg >> formats.length_field_size) & ((1<<formats.test_length)-1)) & ((1 << 8)-1) != 1:
        print("Failed CBC with real malleation and truncation values")
        if not formats.checkFormat(some_msg):
            raise Exception("Message is also not correctly formatted")
    else:
        print("CBC passed")
    third_zerror, third_mask = malform.CBC_MODE(some_msg, mall, trunc)
    if formats.checkFormat(third_zerror, third_mask):
        print("Message found was correctly formatted")
    print("Testing non empty taint for correct verification")
    fourth_zerror, fourth_mask = malform.CBC_MODE_symb_msg(sec_msg, sec_cbc, 1 << formats.length_field_size ,0)
    sec_cbc.add(
        sec_cbc._eq(
            formats.checkFormatSMT(fourth_zerror, sec_cbc, fourth_mask),
            2
        )
    ) 
    if not sec_cbc.check():
        raise Exception("Failed, expected pass")
    else:
        print("Passed first check, checking checkFormat...")
        if formats.checkFormat(0, 1 << formats.length_field_size) == 2:
            print("Passed second check")
        else:
            raise Exception("Failed checkFormat pass")
    return


def main():
    # truncate test
    truncateTest()
    checkPKCSFormat()
    CBCmodetest()
    return

if __name__ == "__main__":
    main()
