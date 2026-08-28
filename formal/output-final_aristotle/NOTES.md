# Correctness of the binary64 square root unit — notes

This file records how the development is organised.

## File structure

| file | contents |
| --- | --- |
| `Proj/RTL.lean` | the signals of the unit and their types |
| `Proj/Properties.lean` | the assumptions on a trace (`ValidTrace`) derived from SVA |
| `Proj/Bits.lean` | bit-level lemmas about `BitVec` slices, `getBit`, `extractBits` and the leading-zero count |
| `Proj/FP.lean` | the definitions `decodeFP`, `fp64ToReal` and its neighbours, and lemmas evaluating them |
| `Proj/Operand.lean` | `operand_value`: the operand as a real number, in terms of the fixed point significand `XVal` and the exponent (normal and subnormal cases) |
| `Proj/Result.lean` | `result_values`: the five real numbers attached to the packed result, in terms of the rounded quotient |
| `Proj/Round.lean` | the arithmetic core: comparisons with square roots, and the rounding lemmas for each rounding decision, including the proof that ties never occur |
| `Proj/Proof.lean` | `rCorrect`, `qMod4`, `done_two_le`, `operand_ne_zero`, `doneTiming`, `sqrt_core` and the main theorem `sqrtCorrect` |
| `Proj/Example.lean` | a concrete trace computing `√1 = 1`, a proof that it satisfies `ValidTrace`, and non-vacuity of `sqrtCorrect` |

## Non-vacuity

Because a correctness statement is worthless if its assumptions cannot be met,
`Proj/Example.lean` exhibits an explicit trace of the unit computing `√1 = 1`,
proves `ValidTrace` for it, and derives
`sqrtCorrect_hypotheses_satisfiable`, which states that all hypotheses of
`sqrtCorrect` (a valid trace with the unit signalling completion of a
non-special operation) hold simultaneously.
