"""
Convert CORE-X sim log to standard riscv instruction trace format
"""

import argparse
import os
import re
import sys
import logging

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *
# from lib import *

# RD_RE = re.compile(
#     r"(core\s+\d+:\s+)?(?P<pri>\d)\s+0x(?P<addr>[a-f0-9]+?)\s+" \
#     r"\((?P<bin>.*?)\)\s+(?P<reg>[xf]\s*\d*?)\s+0x(?P<val>[a-f0-9]+)" \
#     r"(\s+(?P<csr>\S+)\s+0x(?P<csr_val>[a-f0-9]+))?")

CORE_RE = re.compile( \
                    #  r"^\s*(?P<time>\d+ns)\s*\|" \
                     r"\s*(?P<cycles>\d+)\s*\|" \
                     r"\s*(?P<addr>[0-9a-fA-F]+)\s*\|" \
                     r"\s*(?P<instr>[^\|]+?)\s*\|" \
                     r"\s*(?P<bin>[0-9a-fA-F]+)\s*\|" \
                     r"\s*(?P<gpr>[^\|]*)\s*\|" \
                     r"\s*(?P<csr>[^\|]*)\s*\|" \
                     r"\s*(?P<trap>[01])\s*$" \
                    )


# CORE_RE = re.compile(
#     r"core\s+\d+:\s+0x(?P<addr>[a-f0-9]+?)\s+\(0x(?P<bin>.*?)\)\s+(?P<instr>.*?)$")
ADDR_RE = re.compile(
    r"(?P<rd>[a-z0-9]+?),(?P<imm>[\-0-9]+?)\((?P<rs1>[a-z0-9]+)\)")
# ILLE_RE = re.compile(r"trap_illegal_instruction")

LOGGER = logging.getLogger()


def process_instr(trace):
    if trace.instr == "jal":
        # Spike jal format jal rd, -0xf -> jal rd, -15
        idx = trace.operand.rfind(",")
        imm = trace.operand[idx + 1:]
        if imm[0] == "-":
            imm = "-" + str(int(imm[1:], 16))
        else:
            imm = str(int(imm, 16))
        trace.operand = trace.operand[0:idx + 1] + imm
    # Properly format operands of all instructions of the form:
    # <instr> <reg1> <imm>(<reg2>)
    # The operands should be converted into CSV as:
    # "<reg1>,<reg2>,<imm>"
    m = ADDR_RE.search(trace.operand)
    if m:
        trace.operand = "{},{},{}".format(
            m.group("rd"), m.group("rs1"), m.group("imm"))


def read_riscx_instr(match, full_trace):
    """Unpack a regex match for CORE_RE to a RiscvInstructionTraceEntry

    If full_trace is true, extract operand data from the disassembled
    instruction.

    """

    # Extract the disassembled instruction.
    disasm = match.group('instr')

    # Spike's disassembler shows a relative jump as something like "j pc +
    # 0x123" or "j pc - 0x123". We just want the relative offset.
    # disasm = disasm.replace('pc + ', '').replace('pc - ', '-')

    instr = RiscvInstructionTraceEntry()
    instr.pc = match.group('addr')
    instr.instr_str = disasm
    instr.binary = match.group('bin')
    
    instr.gpr.append(match.group('gpr').replace(' ', ''))
    instr.csr.append(match.group('csr').replace(' ', ''))
    
    instr.mode = '3'

    if full_trace:
        opcode = disasm.split(' ')[0]
        operand = disasm[len(opcode):].replace(' ', '')
        instr.instr, instr.operand = \
            convert_pseudo_instr(opcode, operand, instr.binary)

        process_instr(instr)
    
    # print(instr.instr_str)
    return instr


def read_riscx_trace(path, full_trace):
    """Read a RISC-X simulation log at <path>, yielding executed instructions.

    This assumes that the log was generated with the xxxxx options
    to RISC-X.

    If full_trace is true, extract operands from the disassembled instructions.

    At the end of a DV program, there's an ECALL instruction, which
    we take as a signal to stop checking, so we ditch everything that follows
    that instruction.

    This function yields instructions as it parses them as tuples of the form
    (entry, illegal). entry is a RiscvInstructionTraceEntry. illegal is a
    boolean, which is true if the instruction caused an illegal instruction trap.

    """

    # This loop is a simple FSM with states TRAMPOLINE, INSTR, EFFECT. The idea
    # is that we're in state TRAMPOLINE until we get to the end of RISC-X's
    # trampoline, then we switch between INSTR (where we expect to read an
    # instruction) and EFFECT (where we expect to read commit information).
    #
    # We yield a RiscvInstructionTraceEntry object each time we leave EFFECT
    # (going back to INSTR), we loop back from INSTR to itself, or we get to the
    # end of the file and have an instruction in hand.
    #
    # On entry to the loop body, we are in state TRAMPOLINE if in_trampoline is
    # true. Otherwise, we are in state EFFECT if instr is not None, otherwise we
    # are in state INSTR.

    instr = None

    with open(path, 'r') as handle:
        for line in handle:
            instr_match = CORE_RE.match(line)
            # if instr_match:
            #     instr = read_riscx_instr(instr_match, full_trace)
            # else:
            #     continue
            
            # print(instr_match)
            if not instr_match:
                continue
            
            instr = read_riscx_instr(instr_match, full_trace)
            
            if instr.instr_str == 'ecall':
                break
            
            if instr.gpr[0] == "":
                continue
            # groups = instr_match.groupdict()
            # print(instr.gpr)
            
            if instr_match.group('trap') == "1":
                yield (instr, True)
                continue
            
            yield (instr, False)

        # print(groups)
        
        # At EOF, we might have an instruction in hand. Yield it if so.
        if instr is not None:
            yield (instr, False)


def process_riscx_sim_log(riscx_log, csv, full_trace=0):
    """Process RISC-X simulation log.

    Extract instruction and affected register information from RISC-X simulation
    log and write the results to a CSV file at csv. Returns the number of
    instructions written.

    """
    logging.info("Processing RISC-X log : {}".format(riscx_log))
    instrs_in = 0
    instrs_out = 0

    with open(csv, "w") as csv_fd:
        trace_csv = RiscvInstructionTraceCsv(csv_fd)
        trace_csv.start_new_trace()

        for (entry, illegal) in read_riscx_trace(riscx_log, full_trace):
            instrs_in += 1

            if illegal and full_trace:
                logging.debug("Illegal instruction: {}, opcode:{}"
                              .format(entry.instr_str, entry.binary))

            # Instructions that cause no architectural update (which includes illegal
            # instructions) are ignored if full_trace is false.
            #
            # We say that an instruction caused an architectural update if either we
            # saw a commit line (in which case, entry.gpr will contain a single
            # entry) or the instruction was 'wfi' or 'ecall'.
            if not (full_trace or entry.gpr or entry.instr_str in ['wfi',
                                                                   'ecall']):
                # print("YEAAAH")
                continue

            trace_csv.write_trace_entry(entry)
            instrs_out += 1

    logging.info("Processed instruction count : {}".format(instrs_in))
    logging.info("CSV saved to : {}".format(csv))
    return instrs_out


def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=str, help="Input RISC-X simulation log")
    parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
    parser.add_argument("-f", "--full_trace", dest="full_trace",
                        action="store_true",
                        help="Generate the full trace")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        help="Verbose logging")
    parser.set_defaults(full_trace=False)
    parser.set_defaults(verbose=False)
    args = parser.parse_args()
    setup_logging(args.verbose)
    # Process RISC-X log
    process_riscx_sim_log(args.log, args.csv, args.full_trace)


if __name__ == "__main__":
    main()
