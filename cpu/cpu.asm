# Count down from 5 to 0, then halt in a loop (JMP 4 at word 4).
LOAD 5      # 0
SUB 1       # 1
JZ 4        # 2   acc == 0: go to the halt
JMP 1       # 3
JMP 4       # 4   halt
