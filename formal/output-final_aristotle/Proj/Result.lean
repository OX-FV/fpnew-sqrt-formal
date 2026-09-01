-- Copyright 2026 University of Oxford.
-- Licensed under the Apache License, Version 2.0 (see LICENSE for details).
-- Original Author: Ashraf Alam - co-authored by Aristotle (Harmonic)
-- SPDX-License-Identifier: Apache-2.0

import Proj.FP

/-!
# The value of the result produced by the packing stage

The packing stage of the unit produces a 64 bit result whose fraction and
exponent fields are described by `PackMantissa` and `PackExpnt` in terms of the
55 bit rounded quotient `A = packVfdsuEx4Frac` and of `halfExpnt`.  The main
result of this file, `result_values`, evaluates the five real numbers attached
to that bit pattern: writing `c = 16 * (A / 2)` for the rounded quotient
truncated to the representable precision (in the units in which the SRT
quotient `Q` is computed) and `k = h - 56`, they are
`c * 2 ^ k`, `(c ± 2 * d) * 2 ^ k` and `(c ± d) * 2 ^ k`, where `d` is half an
ulp, either `8` or (in case the rounding overflowed into the next binade) `16`.
-/

namespace RTL
namespace Properties
namespace Proof

/-- Splitting a power of two off a real number. -/
lemma shift_val (x : ℝ) (n : ℕ) (a k : ℤ) (h : a = (n : ℤ) + k) :
    x * 2 ^ a = (x * 2 ^ n) * 2 ^ k := by
  rw [h, zpow_add₀ (two_ne_zero), zpow_natCast]
  ring

/-- The real numbers attached to the result bit pattern of the unit. -/
lemma result_values (v : BitVec 64) (A h : ℤ) (N : ℕ) (hN : v.toNat = N)
    (hA1 : 2 ^ 53 ≤ A) (hA2 : A ≤ 2 ^ 54 + 1)
    (hEne : N / 2 ^ 52 % 2 ^ 11 ≠ 0)
    (hMant : if getBit A 54 then extractBits (N : ℤ) 51 0 = extractBits A 53 2
      else if getBit A 53 then extractBits (N : ℤ) 51 0 = extractBits A 52 1
      else extractBits (N : ℤ) 51 0 = extractBits A 51 0)
    (hExp : extractBits (N : ℤ) 62 52 =
      (if getBit A 54 then h + 1024 else if getBit A 53 then h + 1023 else h + 1022)) :
    ∃ d : ℤ, 8 ≤ d ∧ d ≤ 16 ∧
      fp64ToReal v = ((16 * (A / 2) : ℤ) : ℝ) * 2 ^ (h - 56) ∧
      nextLargestFp64ToReal v = ((16 * (A / 2) + 2 * d : ℤ) : ℝ) * 2 ^ (h - 56) ∧
      nextSmallestFp64ToReal v = ((16 * (A / 2) - 2 * d : ℤ) : ℝ) * 2 ^ (h - 56) ∧
      nextHalfLargestFp64ToReal v = ((16 * (A / 2) + d : ℤ) : ℝ) * 2 ^ (h - 56) ∧
      nextHalfSmallestFp64ToReal v = ((16 * (A / 2) - d : ℤ) : ℝ) * 2 ^ (h - 56) := by
  -- the significand and exponent fields of the result
  subst hN
  obtain ⟨hm, he⟩ := decodeFP_normal v hEne
  have hMcast : extractBits (v.toNat : ℤ) 51 0 = ((v.toNat % 2 ^ 52 : ℕ) : ℤ) := by
    rw [extractBits_natCast]
    norm_num
  have hEcast : extractBits (v.toNat : ℤ) 62 52 = ((v.toNat / 2 ^ 52 % 2 ^ 11 : ℕ) : ℤ) := by
    rw [extractBits_natCast]
  -- the two possible cases for the top bits of `A`
  have hkey : ∃ (m : ℤ) (n : ℕ), 4 ≤ n ∧ n ≤ 5 ∧
      ((v.toNat % 2 ^ 52 : ℕ) : ℤ) = m - 2 ^ 52 ∧
      ((v.toNat / 2 ^ 52 % 2 ^ 11 : ℕ) : ℤ) = h + 1023 + ((n : ℤ) - 4) ∧
      m * 2 ^ n = 16 * (A / 2) ∧ 2 ^ 52 ≤ m := by
    by_cases hbig : 2 ^ 54 ≤ A
    · have h54 : getBit A 54 = true := by
        simp only [getBit_eq_decide, decide_eq_true_eq]
        norm_num
        omega
      rw [if_pos h54] at hMant hExp
      have hM : extractBits A 53 2 = 0 := by
        rw [extractBits_eq]
        norm_num
        omega
      refine ⟨2 ^ 52, 5, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · rw [← hMcast, hMant, hM]; ring
      · rw [← hEcast, hExp]; ring
      · have hhalf : A / 2 = 2 ^ 53 := by omega
        rw [hhalf]; norm_num
      · norm_num
    · push_neg at hbig
      have h54 : getBit A 54 = false := by
        simp only [getBit_eq_decide, decide_eq_false_iff_not, not_not]
        norm_num
        omega
      have h53 : getBit A 53 = true := by
        simp only [getBit_eq_decide, decide_eq_true_eq]
        norm_num
        omega
      rw [if_neg (by simp [h54]), if_pos h53] at hMant hExp
      have hM : extractBits A 52 1 = A / 2 - 2 ^ 52 := by
        rw [extractBits_eq]
        norm_num
        omega
      refine ⟨A / 2, 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · rw [← hMcast, hMant, hM]
      · rw [← hEcast, hExp]; ring
      · ring
      · omega
  obtain ⟨m, n, hn1, hn2, hMval, hEval, hprod, hmlb⟩ := hkey
  -- the significand and exponent of `decodeFP v`
  have hmv : (((decodeFP v).1.toNat : ℤ)) = m := by
    rw [hm]
    push_cast
    push_cast at hMval
    omega
  have hev : (((decodeFP v).2.toNat : ℤ)) = h + 1023 + ((n : ℤ) - 4) := by
    rw [he]; exact hEval
  obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ := fp64_values v m _ hmv hev (by positivity)
  -- rewrite the five values
  have hexp : h + 1023 + ((n : ℤ) - 4) - 1075 = (n : ℤ) + (h - 56) := by ring
  have hpow : ((2 : ℝ) ^ n) = ((2 ^ n : ℤ) : ℝ) := by push_cast; ring
  have hd : ∃ d : ℤ, 8 ≤ d ∧ d ≤ 16 ∧ (2 : ℤ) ^ n = 2 * d := by
    interval_cases n
    · exact ⟨8, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨16, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨d, hd1, hd2, hdeq⟩ := hd
  have h2n : ((2 : ℝ) ^ n) = 2 * (d : ℝ) := by
    rw [hpow, hdeq]; push_cast; ring
  have hMD : (m : ℝ) * (2 * (d : ℝ)) = ((16 * (A / 2) : ℤ) : ℝ) := by
    have hz : m * (2 * d) = 16 * (A / 2) := by rw [← hdeq]; exact hprod
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hz
  refine ⟨d, hd1, hd2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv1, shift_val _ n _ _ hexp]
    congr 1
    rw [h2n]; exact hMD
  · rw [hv2, shift_val _ n _ _ hexp]
    congr 1
    rw [h2n]
    push_cast
    push_cast at hMD
    linarith [hMD]
  · rw [hv3, shift_val _ n _ _ hexp]
    congr 1
    rw [h2n]
    push_cast
    push_cast at hMD
    linarith [hMD]
  · rw [hv4, shift_val _ n _ _ hexp]
    congr 1
    rw [h2n]
    push_cast
    push_cast at hMD
    linarith [hMD]
  · rw [hv5, shift_val _ n _ _ hexp]
    congr 1
    rw [h2n]
    push_cast
    push_cast at hMD
    linarith [hMD]

end Proof
end Properties
end RTL
