import sys

def twos_complement(hex_num):
    decimal_num = int(hex_num, 16)
    n = 32
    twos_comp = decimal_num - (1 << n)
    if twos_comp < 0:
        twos_comp = -twos_comp
    return hex(twos_comp)

if __name__ == "__main__":
    # Check if the user provided a hexadecimal number as an argument
    if len(sys.argv) != 2:
        print("Usage: python script.py <32-bit hexadecimal number>")
        sys.exit(1)

    hex_input = sys.argv[1]
    result = twos_complement(hex_input)
    print(f"The 2's complement of {hex_input} is {result}.")
