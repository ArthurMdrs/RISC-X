import os, sys

tool = "jg"
if len(sys.argv) > 1:
    assert len(sys.argv) == 2
    tool = sys.argv[1]

with open('summary.txt', 'w') as summary_file:
    for root, dirs, files in os.walk('checks'):
        for file in files:
            if file == 'PASS' or file == 'FAIL' or file == 'ERROR':
                folder_name = os.path.basename(root)
                result = file
                summary_file.write(f"{folder_name}: {result}\n")
                i = 0
                with open(os.path.join(root, file), 'r') as f:
                    for line in f:
                        if i < 2:
                            summary_file.write(line)
                            i += 1
                        if "counterexample" in line and tool == "jg":
                            temp = line.split(":", 2)[-1]
                            summary_file.write(temp)
                        if "proven unreachable" in line and tool == "jg":
                            temp = line.split(":", 2)[-1]
                            summary_file.write(temp)
                        if "failed assertion" in line and tool == "sby":
                            summary_file.write(line)
                summary_file.write("\n")
