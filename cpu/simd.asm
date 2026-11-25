# SIMD demo: every lane counts down to 0 at its own pace; a lane at 0 sits out (predication, no jump).
# Start with: --init 3,7,0,12
PRED 2      # 0  mask &= (ACC != 0): lanes that are done switch off
SUB 1       # 1  only the active lanes run it
PRED 1      # 2  every lane back on
JMP 0       # 3
