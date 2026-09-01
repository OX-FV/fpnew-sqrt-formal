-- Copyright 2026 University of Oxford.
-- Licensed under the Apache License, Version 2.0 (see LICENSE for details).
-- Original Author: Ashraf Alam - co-authored by Aristotle (Harmonic)
-- SPDX-License-Identifier: Apache-2.0

import Proj.Proof

/-!
# A trace of the unit, and non-vacuity of the correctness theorem

`ValidTrace` is a long list of assumptions, and a correctness statement whose
assumptions cannot be met is worthless.  This file exhibits a concrete trace
`exampleTrace` of the unit -- one computing `√1 = 1` -- proves that it
satisfies `ValidTrace`, and deduces that the hypotheses of `sqrtCorrect` are
simultaneously satisfiable.
-/

namespace RTL
namespace Properties
namespace Proof

/-- The binary64 bit pattern of `1.0`. -/
def oneFP : BitVec 64 := 4607182418800017408

/-- The signal values of the example trace at time `t`.  The unit is started so
that the single SRT stage happens at `t = 1` (producing the quotient digit `4`,
i.e. the quotient `2 ^ 56`, with residual `0`), the last stage is `t = 2`, the
packing stage is `t = 3` and the result is signalled at `t = 4`. -/
def exVal (t : Nat) : (s : Signal) → SignalVal s
  | .rndModeQ => RoundModes.RNE
  | .unitDone => decide (t = 4)
  | .unitResult => oneFP
  | .vfdsuDpFdivBusy => decide (1 ≤ t ∧ t ≤ 3)
  | .ctrlEx3Pipedown => decide (t = 2)
  | .ctrlEx4Pipedown => decide (t = 3)
  | .noSpecial => true
  | .srcf0Q => oneFP
  | .QAfterRnd => if t = 2 then (2 : ℤ) ^ 53 else (0 : ℤ)
  | .Q_raw => if t = 2 then (2 : ℤ) ^ 56 else (0 : ℤ)
  | .QRnd => if t = 2 then (2 : ℤ) ^ 56 else (0 : ℤ)
  | .R_raw => if t = 1 then (2 : ℤ) ^ 56 else (0 : ℤ)
  | .QNext => if t = 1 then (2 : ℤ) ^ 56 else (0 : ℤ)
  | .RNext => (0 : ℤ)
  | .j_val => if t = 2 then (1 : Nat) else (0 : Nat)
  | .first_stage => decide (t = 1)
  | .middle_stage => false
  | .last_stage => decide (t = 2)
  | .packEx4OutResult => oneFP
  | .packVfdsuEx4Frac => (2 : ℤ) ^ 53
  | .q_val => if t = 1 then (4 : ℤ) else (0 : ℤ)
  | .flush_combined => false
  | .sqrt64B => true

/-- The example trace: the unit computes `√1 = 1` in round to nearest. -/
def exampleTrace : Nat → State := exVal


section Eval

variable (t : Nat)

lemma ex_flush : flush exampleTrace t = false := rfl
lemma ex_busy : vfdsuDpFdivBusy exampleTrace t = decide (1 ≤ t ∧ t ≤ 3) := rfl
lemma ex_done : unitDone exampleTrace t = decide (t = 4) := rfl
lemma ex_ex3 : ctrlEx3Pipedown exampleTrace t = decide (t = 2) := rfl
lemma ex_ex4 : ctrlEx4Pipedown exampleTrace t = decide (t = 3) := rfl
lemma ex_noSpecial : noSpecial exampleTrace t = true := rfl
lemma ex_sqrt64B : sqrt64B exampleTrace t = true := rfl
lemma ex_first : firstStage exampleTrace t = decide (t = 1) := rfl
lemma ex_middle : middleStage exampleTrace t = false := rfl
lemma ex_last : lastStage exampleTrace t = decide (t = 2) := rfl
lemma ex_j : jVal exampleTrace t = if t = 2 then 1 else 0 := rfl
lemma ex_Q : Q exampleTrace t = if t = 2 then 2 ^ 56 else 0 := rfl
lemma ex_QRnd : QRnd exampleTrace t = if t = 2 then 2 ^ 56 else 0 := rfl
lemma ex_R : RVal exampleTrace t = if t = 1 then 2 ^ 56 else 0 := rfl
lemma ex_QNext : QNext exampleTrace t = if t = 1 then 2 ^ 56 else 0 := rfl
lemma ex_RNext : RNext exampleTrace t = 0 := rfl
lemma ex_QAfterRnd : QAfterRnd exampleTrace t = if t = 2 then 2 ^ 53 else 0 := rfl
lemma ex_frac : packVfdsuEx4Frac exampleTrace t = 2 ^ 53 := rfl
lemma ex_q : qVal exampleTrace t = if t = 1 then 4 else 0 := rfl
lemma ex_rm : rmQ exampleTrace t = RoundModes.RNE := rfl
lemma ex_src : srcf0Q exampleTrace t = oneFP := rfl
lemma ex_result : unitResult exampleTrace t = oneFP := rfl
lemma ex_pack : packEx4OutResult exampleTrace t = oneFP := rfl

/-- The operand of the example trace is normalised to `2 ^ 56`. -/
lemma ex_X : XVal exampleTrace t = 2 ^ 56 :=
  (XVal_congr exampleTrace t 3 rfl).trans (by decide)

end Eval

/-- The example trace satisfies all the assumptions of `ValidTrace`.  In
particular the assumptions of `sqrtCorrect` are consistent. -/
theorem exampleTrace_valid : ValidTrace exampleTrace := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- OpStable
    intro t _
    exact ⟨rfl, rfl, by rw [ex_X, ex_X]⟩
  · -- ResultEqPack
    intro t
    rfl
  · -- Ex4UnitDone
    intro t
    simp only [ex_done, ex_flush, ex_ex4, decide_eq_true_eq, true_and]
    omega
  · -- Ex4ResStable
    intro t h
    simp only [ex_done, decide_eq_true_eq] at h
    exact ⟨by omega, rfl⟩
  · -- WasBusy
    intro t h
    simp only [ex_done, decide_eq_true_eq] at h
    subst h
    exact ⟨by omega, rfl⟩
  · -- NoSpecialStable
    intro t _
    rfl
  · -- PackMantissa
    intro t h
    obtain ⟨h1, -, -⟩ := h
    simp only [ex_ex4, decide_eq_true_eq] at h1
    subst h1
    decide
  · -- PackExpnt
    intro t h
    obtain ⟨h1, -, -⟩ := h
    simp only [ex_ex4, decide_eq_true_eq] at h1
    subst h1
    decide
  · -- PackInp
    intro t _ h
    simp only [ex_ex4, decide_eq_true_eq] at h
    subst h
    decide
  · -- Ex3Ex4
    intro t
    simp only [ex_ex4, ex_flush, ex_ex3, decide_eq_true_eq, true_and]
    omega
  · -- Ex3Ex4Stable
    intro t _ _
    exact ⟨rfl, rfl⟩
  · -- RNE_add1
    intro t h
    obtain ⟨h1, -, -, -, h5⟩ := h
    simp only [ex_ex3, decide_eq_true_eq] at h1
    subst h1
    revert h5
    decide
  · -- RNE_orig
    intro t h
    obtain ⟨h1, -, -, -, -⟩ := h
    simp only [ex_ex3, decide_eq_true_eq] at h1
    subst h1
    decide
  · -- RTZ_sub1
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- RTZ_orig
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- RUP_add1
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- RUP_orig
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- RDN_sub1
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- RDN_orig
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- RMM_add1
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- RMM_orig
    intro t h
    exact RoundModes.noConfusion h.2.2.1
  · -- BaseCase
    intro t h
    obtain ⟨h1, h2⟩ := h
    simp only [ex_first, ex_middle, ex_last, ex_j, decide_eq_true_eq] at h1 h2 ⊢
    have h1' : t = 1 ∨ t = 2 := by simpa using h1
    split_ifs at h2 with hc
    omega
  · -- Q_initial
    intro t h
    simp only [ex_first, decide_eq_true_eq] at h
    subst h
    rfl
  · -- R_initial
    intro t h
    obtain ⟨h1, -⟩ := h
    simp only [ex_first, decide_eq_true_eq] at h1
    subst h1
    rw [ex_R, ex_X]
    norm_num
  · -- J_initial
    intro t h
    simp only [ex_first, decide_eq_true_eq] at h
    subst h
    rfl
  · -- J_next
    intro t h
    obtain ⟨h1, -⟩ := h
    simp only [ex_middle, ex_last, decide_eq_true_eq] at h1
    have ht : t = 2 := by simpa using h1
    subst ht
    exact ⟨rfl, by decide⟩
  · -- R_next_eq
    intro t h
    obtain ⟨h1, -⟩ := h
    simp only [ex_middle, ex_last, decide_eq_true_eq] at h1
    have ht : t = 2 := by simpa using h1
    subst ht
    rfl
  · -- Q_next_eq
    intro t h
    obtain ⟨h1, -⟩ := h
    simp only [ex_middle, ex_last, decide_eq_true_eq] at h1
    have ht : t = 2 := by simpa using h1
    subst ht
    rfl
  · -- TimeConsistency
    intro t h
    obtain ⟨h1, -⟩ := h
    simp only [ex_middle, ex_last, decide_eq_true_eq] at h1
    have ht : t = 2 := by simpa using h1
    subst ht
    exact ⟨by omega, Or.inl rfl⟩
  · -- SrtBusy
    intro t h
    simp only [ex_first, ex_middle, ex_last, ex_busy, decide_eq_true_eq] at h ⊢
    have h' : t = 1 ∨ t = 2 := by simpa using h
    omega
  · -- Q_recur
    intro t h
    obtain ⟨h1, -⟩ := h
    simp only [ex_first, ex_middle, decide_eq_true_eq] at h1
    have ht : t = 1 := by simpa using h1
    subst ht
    decide
  · -- R_recur
    intro t h
    obtain ⟨h1, -⟩ := h
    simp only [ex_first, ex_middle, decide_eq_true_eq] at h1
    have ht : t = 1 := by simpa using h1
    subst ht
    decide
  · -- DefOfLast
    intro t
    exact Iff.rfl
  · -- QEquals
    intro t
    rfl
  · -- QRndIneq
    intro t h
    obtain ⟨h1, -, -⟩ := h
    simp only [ex_ex3, decide_eq_true_eq] at h1
    subst h1
    decide
  · -- StopEarly
    intro t h
    obtain ⟨h1, -, -, -⟩ := h
    simp only [ex_ex3, decide_eq_true_eq] at h1
    subst h1
    rfl
  · -- ResNoDenorm
    intro t _ h
    have h1 : t = 4 := by simpa [ex_done] using h.1
    subst h1
    decide
  · -- jBound
    intro t h
    simp only [ex_first, ex_middle, decide_eq_true_eq] at h
    have ht : t = 1 := by simpa using h
    subst ht
    decide
  · -- OpNonZero
    intro t _
    rw [ex_src]
    decide
  · -- Sqrt64BStable
    intro t _
    rfl

/-- The operand (and the result) of the example trace denotes the real
number `1`. -/
lemma fp64ToReal_oneFP : fp64ToReal oneFP = 1 := by
  have hE : oneFP.toNat / 2 ^ 52 % 2 ^ 11 ≠ 0 := by decide
  obtain ⟨hm, he⟩ := decodeFP_normal oneFP hE
  obtain ⟨h1, -, -, -, -⟩ :=
    fp64_values oneFP (2 ^ 52) 1023 (by rw [hm]; decide) (by rw [he]; decide) (by norm_num)
  rw [h1, show (1023 : ℤ) - 1075 = -52 from by norm_num, zpow_neg]
  push_cast
  norm_num

/-- The hypotheses of `sqrtCorrect` are simultaneously satisfiable, so the
theorem is not vacuous: they all hold for `exampleTrace` at `t = 4`. -/
theorem sqrtCorrect_hypotheses_satisfiable :
    ∃ (tr : Nat → State) (t : Nat), ValidTrace tr ∧
      unitDone tr t = true ∧ noSpecial tr t = true ∧ sqrt64B tr t = true :=
  ⟨exampleTrace, 4, exampleTrace_valid, rfl, rfl, rfl⟩

/-- On the example trace the unit indeed returns `√1 = 1`. -/
theorem exampleTrace_result :
    fp64ToReal (unitResult exampleTrace 4)
      = Real.sqrt (fp64ToReal (srcf0Q exampleTrace 4)) := by
  rw [ex_result, ex_src, fp64ToReal_oneFP, Real.sqrt_one]

end Proof
end Properties
end RTL
