# Proof of Fpnew floating point square root

## The top level property proven

When the DivSqrt unit signals that a 64-bit square root operation has been completed, the output is correct (compliant with IEEE-754 standard).

## General proof strategy

We prove SystemVerilog Assertions (SVAs) about the RTL using Jasper. These SVAs should be enough to mathematically imply that the operations are correct. We translate the SVAs into Lean, and prove a top level correctness theorem in Lean using the translated SVA as assumptions. More details of this methodology may be found in the paper `methodology_paper.pdf`.

## Setup

The following instructions allow you to reproduce the proof. 

1. Run the following commands (you will need to have JasperGold installed): 
```bash
cd formal
make build/filelist.txt
make jg
```
2. Prove the assertions in Jasper. This can be done with one command: `prove -task {<embedded>} -bg`. This concludes the model checking part of the proof.

3. For the Lean part of the proof, it is recommended to install the Lean 4 VS Code extension. Two blue tick marks next to theorem `sqrtCorrect` in `formal/output-final_aristotle/Proj/Proof.lean` indicates that Lean has proven the top level property.

## File layout

`formal/formal_fpnew_top.sv` contains all the SVAs needed to prove correctness. The only assumption used is that the custom Fpnew rounding modes "ROD" and "DYN" are not used. These rounding modes are not standard RISC-V rounding modes and are not supported by the C910 DivSqrt unit.

`formal/output-final_aristotle` is the Lean project where the proof is finalised. As the name suggests, it was mostly produced by the AI tool [Aristotle](https://aristotle.harmonic.fun/).

#### More about `formal_fpnew_top.sv`:

It should be noted that the top level property does not tell us that if the unit receives an instruction which is never flushed, then the unit will signal it's done at some point. Nor does the property tell us that an attempt at flushing really does prevent the unit from signalling it's done. These are proven as `NoDisappearingOps` and `DoneImpNoFlush` in `formal_fpnew_top.sv`.

## The hardware design

The unit itself is the DivSqrt unit used in the [T-Head XuanTie C910](https://github.com/XUANTIE-RV/openc910) open source 64-bit RISC-V processor. It is one of three DivSqrt units supported by Fpnew and the unit used in Fpnew with its default parameters.

