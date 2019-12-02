import CRC32 as crc
# L32 currently should be L16 (its only a 16 bit message)
import L16Bit as toy_format

max_msg_size = crc.CRC_SIZE + toy_format.test_length
length_field_size = max_msg_size.bit_length()
test_length = max_msg_size + length_field_size
# go for a message that is a little longer.

# format is as follows

# [16 bit padded Toy format msg] [32 bit CRC] [length field]
# you MAY not need a length field... 
# Use with simple XOR malform.
def checkFormat(msg):
    format_crc_res = crc.checkFormat(msg)
    if not format_crc_res:
        return False
    toy_msg = msg >> (crc.CRC_SIZE + length_field_size)
    return toy_format.checkFormat(toy_msg)

def checkFormatSMT(msg, solver):
    crc_check = crc.checkFormatSMT(msg, solver)
    toy_msg = solver.extract(msg, msg.size()-1, crc.CRC_SIZE + length_field_size)
    toy_check = toy_format.checkFormat(toy_msg, solver)
    return solver._and(crc_check, toy_check)

def makePaddedMessage():
    toy_msg = toy_format.makePaddedMessage()
    crc_of_msg = crc.calculateCRCNormal(toy_msg, (toy_format.test_length + 7) // 8 )
    final_msg = toy_msg << (crc.CRC_SIZE + length_field_size)
    final_msg |=  crc_of_msg << length_field_size
    final_msg |= max_msg_size
    return final_msg
