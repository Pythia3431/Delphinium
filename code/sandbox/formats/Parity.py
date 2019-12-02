import random
from math import floor, log

test_length = 36
size_field = 5
message_field = test_length-size_field

def truncate(m, p):
    return m ^ (p & ((1 << size_field)-1))

def checkFormat(m):
    p = 0
    v = m >> size_field
    size = m & ((1 << size_field)-1)
    v = (v & ((1 << size) - 1))
    while v != 0:
        p ^= (v & 1)
        v >>= 1
    return p == 1

def checkFormatSMT(m, solver):
    p = solver.false()
    size = solver.extract(m, size_field-1, 0)
    parity = solver.bvconst(0, 1)
    for i in range(test_length-1, size_field-1, -1):
        bit = solver.extract(m, i, i)
        parity = solver._if(
                solver._ult(solver.bvconst(i-size_field, size_field), size),
                solver._xor(parity, bit),
                parity)
    return solver._and(solver._ugt(size, solver.bvconst(0, size_field)),
                       solver._eq(parity, solver.bvconst(1, 1)))

def makePaddedMessage():
    v = random.randint(0, 2**message_field - 1)
    return (v << size_field) | test_length


if __name__ == '__main__':
    assert checkFormat((1 << size_field) | 1)
    assert checkFormat((1 << size_field) | 31)
    assert checkFormat((1 << size_field) | message_field)
    assert not checkFormat((1 << size_field))
    assert checkFormat((42 << size_field) | message_field)
    assert checkFormat((82 << size_field) | 20)
    assert not checkFormat((0 << size_field)|5)
    assert not checkFormat((1337 << size_field) | message_field)
    assert not checkFormat((2019 << size_field) | message_field)
    import solver as ls
    s = ls.Z3Solver()
    a = s.bv('a', test_length)
    b = s.bv('b', test_length)
    c = s.bv('c', test_length)
    d = s.bv('d', test_length)
    e = s.bv('e', test_length)
    f = s.bv('f', test_length)
    g = s.bv('g', test_length)
    s.add(s._eq(b, s.bvconst((0b10101 << size_field) | 31, test_length)))
    s.add(s._eq(c, s.bvconst((0b10101 << size_field) | 5, test_length)))
    s.add(s._eq(d, s.bvconst((0b10101 << size_field) | 20, test_length)))
    s.add(s._eq(e, s.bvconst((0b1010 << size_field) | 4, test_length)))
    s.add(s._eq(f, s.bvconst((0b1010 << size_field) | 17, test_length)))
    s.add(s._eq(g, s.bvconst((0b10101 << size_field) | 4, test_length)))
    s.add(checkFormatSMT(a, s))
    s.add(checkFormatSMT(b, s))
    s.add(checkFormatSMT(c, s))
    s.add(checkFormatSMT(d, s))
    s.add(s._not(checkFormatSMT(e, s)))
    s.add(s._not(checkFormatSMT(f, s)))
    s.add(s._not(checkFormatSMT(g, s)))
    assert s.check()

