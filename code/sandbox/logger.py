import math

class Logger(object):
    def __init__(self, full_log, mbound_log):
        self.regularLog = full_log 
        self.mboundOutput = mbound_log

    def initTrialLogging(self, realM, globalDict):
        """ Write initial information to the first lines of the log files """
        if globalDict["israndom"]:
            format_header = "Full run of attack with message {} at {} Bit with trials {}, delta {}, and expected constraint length {}. Threshold for success is {}/{}\n".format(realM, globalDict["bit_vec_length"], globalDict["trials"], globalDict["delta"], globalDict["k"], math.floor((globalDict["delta"] + 0.5) * globalDict["trials"]), globalDict["trials"])
        else:
            format_header = "Full run of attack with message {} at {} Bit with trials {}, delta {}, and k is {}. Threshold for success is {}/{}\n".format(realM, globalDict["bit_vec_length"], globalDict["trials"], globalDict["delta"], globalDict["k"], math.floor((globalDict["delta"] + 0.5) * globalDict["trials"]), globalDict["trials"])
        with open(self.mboundOutput, "w") as dat_write:
            dat_write.write(format_header)
            dat_write.write("MBound size (log2) | Query time (longest in parallel)\n")
        with open(self.regularLog, "w") as write_log:
            write_log.write(format_header)

    def writeRegular(self, text):
        with open(self.regularLog, "a") as fileobj:
            fileobj.write(text)

    def writeMbound(self, text):
        with open(self.mboundOutput, "a") as fileobj:
            fileobj.write(text)
