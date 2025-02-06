An attempt to use spin to verify a blackbox implementation of a switch state machine (implemented in boost::msm). While Promela partially backtracks in its tree and internal state to explore another run/word, the state machine keeps its state and the verification fails at the second word even though both the verifier and the state machine are sound; they just do not work in sync as needed.

