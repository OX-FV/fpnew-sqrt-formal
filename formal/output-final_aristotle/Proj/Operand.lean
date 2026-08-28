import Proj.FP

/-!
# The value of the operand of the square root unit

The square root unit works with the integer `XVal`, a fixed point
representation of the significand of the operand `srcf0Q` scaled so that it
lies in `[2 ^ 56, 2 ^ 58)`, the two cases corresponding to the parity of the
exponent.  The main result of this file, `operand_value`, states that

* `fp64ToReal (srcf0Q tr t) = XVal tr t * 2 ^ (2 * ⌊be / 2⌋ - 56)`, where
  `be = biasedExpnt tr t`, and
* `2 ^ 56 ≤ XVal tr t ≤ 2 ^ 58 - 32`.
-/

namespace RTL
namespace Properties
namespace Proof

/-- The exponent field of a bit pattern vanishes iff the corresponding slice of
its `toNat` does. -/
lemma extractLsb_hi_eq_zero_iff (v : BitVec 64) :
    (v.extractLsb 62 52 = 0) ↔ v.toNat / 2 ^ 52 % 2 ^ 11 = 0 := by
  constructor
  · intro h; rw [← extract_hi, h]; simp
  · intro h; exact BitVec.eq_of_toNat_eq (by rw [extract_hi]; simpa using h)

/-- For a subnormal operand, `clzVal` is the leading zero count of the fraction. -/
lemma clzVal_denormal (tr : Nat → State) (t : Nat)
    (hE0 : (srcf0Q tr t).toNat / 2 ^ 52 % 2 ^ 11 = 0) :
    clzVal tr t = (((srcf0Q tr t).extractLsb 51 0).clz).toNat := by
  have h0 : (srcf0Q tr t).extractLsb (WE + WF - 1) WF = 0 := (extractLsb_hi_eq_zero_iff _).2 hE0
  unfold clzVal
  rw [if_pos h0]
  rfl

/-- For a normal operand, `clzVal` is zero. -/
lemma clzVal_normal (tr : Nat → State) (t : Nat)
    (hE0 : (srcf0Q tr t).toNat / 2 ^ 52 % 2 ^ 11 ≠ 0) :
    clzVal tr t = 0 := by
  have h0 : ¬ ((srcf0Q tr t).extractLsb (WE + WF - 1) WF = 0) := fun h =>
    hE0 ((extractLsb_hi_eq_zero_iff _).1 h)
  unfold clzVal
  rw [if_neg h0]

/-- Rescaling: if `X = F * 2 ^ n` and `n + b = a`, then `F * 2 ^ a = X * 2 ^ b`. -/
lemma scale_eq (F : ℕ) (X : ℤ) (a b : ℤ) (n : ℕ) (hX : X = (F : ℤ) * 2 ^ n)
    (h : (n : ℤ) + b = a) : (F : ℝ) * 2 ^ a = (X : ℝ) * 2 ^ b := by
  subst hX
  push_cast
  rw [← h, zpow_add₀ (two_ne_zero), zpow_natCast]
  ring

/-- `XVal` for a subnormal operand. -/
lemma XVal_denormal (tr : Nat → State) (t : Nat) (F clz : ℕ)
    (hF : (srcf0Q tr t).toNat % 2 ^ 52 = F) (hclzd : clzVal tr t = clz)
    (hE0 : (srcf0Q tr t).toNat / 2 ^ 52 % 2 ^ 11 = 0) (hclz : clz ≤ 51)
    (hFlt : F < 2 ^ (52 - clz)) :
    XVal tr t = (F : ℤ) * 2 ^ (if clz % 2 = 0 then clz + 6 else clz + 5) := by
  have h0 : (srcf0Q tr t).extractLsb 62 52 = 0 := (extractLsb_hi_eq_zero_iff _).2 hE0
  have hfrac : (BitVec.extractLsb (52 - 1) 0 (srcf0Q tr t)).toNat = F := by
    rw [extract_lo, hF]
  have hbits : extractBits (F : ℤ) (52 - 1 - clz) 0 = (F : ℤ) := by
    rw [extractBits_natCast]
    congr 1
    simp only [pow_zero, Nat.div_one]
    apply Nat.mod_eq_of_lt
    have h52 : 52 - 1 - clz - 0 + 1 = 52 - clz := by omega
    rw [h52]
    exact hFlt
  unfold XVal
  simp only [WF, WE, L, h0, hclzd, beq_self_eq_true, if_true,
    if_neg (by omega : ¬ (clz ≥ 52)), hfrac, hbits]
  by_cases hpar : clz % 2 = 0
  · rw [if_pos (show ((clz % 2 == 0) = true) by simp [hpar]), if_pos hpar]
    congr 2
    omega
  · rw [if_neg (show ¬ ((clz % 2 == 0) = true) by simp [hpar]), if_neg hpar]
    congr 2
    omega

/-- `XVal` for a normal operand. -/
lemma XVal_normal (tr : Nat → State) (t : Nat) (F : ℕ)
    (hF : (srcf0Q tr t).toNat % 2 ^ 52 = F)
    (hE0 : (srcf0Q tr t).toNat / 2 ^ 52 % 2 ^ 11 ≠ 0) :
    XVal tr t = ((2 ^ 52 + F : ℕ) : ℤ) *
      2 ^ (if (srcf0Q tr t).toNat / 2 ^ 52 % 2 = 1 then 4 else 5) := by
  have h0 : ¬ ((srcf0Q tr t).extractLsb 62 52 = 0) := fun h =>
    hE0 ((extractLsb_hi_eq_zero_iff _).1 h)
  have hfrac : (BitVec.extractLsb (52 - 1) 0 (srcf0Q tr t)).toNat = F := by
    rw [extract_lo, hF]
  have hbit : (srcf0Q tr t).getLsb 52 = decide ((srcf0Q tr t).toNat / 2 ^ 52 % 2 = 1) :=
    getLsb_eq_decide _ ⟨52, by omega⟩
  unfold XVal
  simp only [WF, WE, L, beq_iff_eq, h0, if_false, hfrac, hbit]
  by_cases hpar : (srcf0Q tr t).toNat / 2 ^ 52 % 2 = 1
  · simp only [hpar, decide_true, if_true]
  · simp only [hpar, decide_false, if_false, Bool.false_eq_true]

/-- The operand of the square root unit, as a real number, in terms of the
fixed point significand `XVal` and the (floor of half of the) unbiased
exponent.  The bounds say that `XVal` is normalised to `[2 ^ 56, 2 ^ 58)`. -/
theorem operand_value (tr : Nat → State) (t : Nat) (hne : fp64ToReal (srcf0Q tr t) ≠ 0) :
    fp64ToReal (srcf0Q tr t)
        = ((XVal tr t : ℤ) : ℝ) * 2 ^ (2 * (biasedExpnt tr t / 2) - 56) ∧
      2 ^ 56 ≤ XVal tr t ∧ XVal tr t ≤ 2 ^ 58 - 32 := by
  by_cases hE0 : (srcf0Q tr t).toNat / 2 ^ 52 % 2 ^ 11 = 0
  · -- subnormal operand
    obtain ⟨hm, he⟩ := decodeFP_denormal (srcf0Q tr t) hE0
    set F := (srcf0Q tr t).toNat % 2 ^ 52 with hFdef
    have hFne : F ≠ 0 := by
      intro h0
      apply hne
      simp only [fp64ToReal, hm, h0]
      norm_num
    set clz := clzVal tr t with hclzdef
    have hclzeq : clz = (((srcf0Q tr t).extractLsb 51 0).clz).toNat := by
      rw [hclzdef]; exact clzVal_denormal tr t hE0
    have hxne : ((srcf0Q tr t).extractLsb 51 0) ≠ 0 := by
      intro hc
      apply hFne
      rw [hFdef, ← extract_lo, hc]
      simp
    obtain ⟨hc1, hc2, hc3⟩ := clz_bounds ((srcf0Q tr t).extractLsb 51 0) (by norm_num) hxne
    rw [← hclzeq] at hc1 hc2 hc3
    rw [extract_lo] at hc2 hc3
    rw [← hFdef] at hc2 hc3
    norm_num at hc1 hc2 hc3
    have hbe : biasedExpnt tr t = -1023 - (clz : ℤ) := by
      have h0 : BitVec.extractLsb (WE + WF - 1) WF (srcf0Q tr t) = 0 :=
        (extractLsb_hi_eq_zero_iff _).2 hE0
      simp only [biasedExpnt, h0, ← hclzdef]
      norm_num [bias]
    have hexp : (((decodeFP (srcf0Q tr t)).2.toNat : ℤ) - 1023 - 52) = (-1074 : ℤ) := by
      rw [he]; norm_num
    have hval : fp64ToReal (srcf0Q tr t) = (F : ℝ) * 2 ^ (-1074 : ℤ) := by
      simp only [fp64ToReal, hm, hexp]
    by_cases hpar : clz % 2 = 0
    · have hX : XVal tr t = (F : ℤ) * 2 ^ (clz + 6) := by
        rw [XVal_denormal tr t F clz hFdef.symm hclzdef.symm hE0 hc1 hc3, if_pos hpar]
      have hpow1 : (2 : ℤ) ^ (51 - clz) * 2 ^ (clz + 6) = 2 ^ 57 := by
        rw [← pow_add]; congr 1; omega
      have hpow2 : (2 : ℤ) ^ (52 - clz) * 2 ^ (clz + 6) = 2 ^ 58 := by
        rw [← pow_add]; congr 1; omega
      have hFlb : (2 : ℤ) ^ (51 - clz) ≤ (F : ℤ) := by exact_mod_cast hc2
      have hFub : (F : ℤ) ≤ 2 ^ (52 - clz) - 1 := by
        have : (F : ℤ) < 2 ^ (52 - clz) := by exact_mod_cast hc3
        omega
      have h64 : (64 : ℤ) ≤ 2 ^ (clz + 6) := by
        calc (64 : ℤ) = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ (clz + 6) := by apply pow_le_pow_right₀ (by norm_num); omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hval, hbe]
        exact scale_eq F (XVal tr t) (-1074) _ (clz + 6) hX (by omega)
      · rw [hX]
        calc (2 : ℤ) ^ 56 ≤ 2 ^ 57 := by norm_num
          _ = 2 ^ (51 - clz) * 2 ^ (clz + 6) := hpow1.symm
          _ ≤ (F : ℤ) * 2 ^ (clz + 6) := by
              apply mul_le_mul_of_nonneg_right hFlb (by positivity)
      · rw [hX]
        have : (F : ℤ) * 2 ^ (clz + 6) ≤ (2 ^ (52 - clz) - 1) * 2 ^ (clz + 6) := by
          apply mul_le_mul_of_nonneg_right hFub (by positivity)
        nlinarith [hpow2]
    · have hX : XVal tr t = (F : ℤ) * 2 ^ (clz + 5) := by
        rw [XVal_denormal tr t F clz hFdef.symm hclzdef.symm hE0 hc1 hc3, if_neg hpar]
      have hpow1 : (2 : ℤ) ^ (51 - clz) * 2 ^ (clz + 5) = 2 ^ 56 := by
        rw [← pow_add]; congr 1; omega
      have hpow2 : (2 : ℤ) ^ (52 - clz) * 2 ^ (clz + 5) = 2 ^ 57 := by
        rw [← pow_add]; congr 1; omega
      have hFlb : (2 : ℤ) ^ (51 - clz) ≤ (F : ℤ) := by exact_mod_cast hc2
      have hFub : (F : ℤ) ≤ 2 ^ (52 - clz) - 1 := by
        have : (F : ℤ) < 2 ^ (52 - clz) := by exact_mod_cast hc3
        omega
      have h32 : (32 : ℤ) ≤ 2 ^ (clz + 5) := by
        calc (32 : ℤ) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (clz + 5) := by apply pow_le_pow_right₀ (by norm_num); omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hval, hbe]
        exact scale_eq F (XVal tr t) (-1074) _ (clz + 5) hX (by omega)
      · rw [hX]
        calc (2 : ℤ) ^ 56 = 2 ^ (51 - clz) * 2 ^ (clz + 5) := hpow1.symm
          _ ≤ (F : ℤ) * 2 ^ (clz + 5) := by
              apply mul_le_mul_of_nonneg_right hFlb (by positivity)
      · rw [hX]
        have : (F : ℤ) * 2 ^ (clz + 5) ≤ (2 ^ (52 - clz) - 1) * 2 ^ (clz + 5) := by
          apply mul_le_mul_of_nonneg_right hFub (by positivity)
        nlinarith [hpow2]
  · -- normal operand
    obtain ⟨hm, he⟩ := decodeFP_normal (srcf0Q tr t) hE0
    set F := (srcf0Q tr t).toNat % 2 ^ 52 with hFdef
    set E := (srcf0Q tr t).toNat / 2 ^ 52 % 2 ^ 11 with hEdef
    have hFlt : F < 2 ^ 52 := by
      rw [hFdef]; exact Nat.mod_lt _ (by positivity)
    have hextr : ((srcf0Q tr t).extractLsb (WE + WF - 1) WF).toNat = E := extract_hi _
    have hbe : biasedExpnt tr t = (E : ℤ) - 1023 := by
      simp only [biasedExpnt, hextr, clzVal_normal tr t hE0]
      norm_num [bias]
    have hexp : (((decodeFP (srcf0Q tr t)).2.toNat : ℤ) - 1023 - 52) = (E : ℤ) - 1075 := by
      rw [he]; ring
    have hval : fp64ToReal (srcf0Q tr t) = ((2 ^ 52 + F : ℕ) : ℝ) * 2 ^ ((E : ℤ) - 1075) := by
      simp only [fp64ToReal, hm, hexp]
    have hEpar : E % 2 = (srcf0Q tr t).toNat / 2 ^ 52 % 2 := by omega
    have hmlb : (2 : ℤ) ^ 52 ≤ ((2 ^ 52 + F : ℕ) : ℤ) := by push_cast; omega
    have hmub : ((2 ^ 52 + F : ℕ) : ℤ) ≤ 2 ^ 53 - 1 := by push_cast; omega
    by_cases hpar : (srcf0Q tr t).toNat / 2 ^ 52 % 2 = 1
    · have hX : XVal tr t = ((2 ^ 52 + F : ℕ) : ℤ) * 2 ^ 4 := by
        rw [XVal_normal tr t F hFdef.symm hE0, if_pos hpar]
      refine ⟨?_, ?_, ?_⟩
      · rw [hval, hbe]
        exact scale_eq (2 ^ 52 + F) (XVal tr t) ((E : ℤ) - 1075) _ 4 hX (by omega)
      · rw [hX]; nlinarith
      · rw [hX]; nlinarith
    · have hX : XVal tr t = ((2 ^ 52 + F : ℕ) : ℤ) * 2 ^ 5 := by
        rw [XVal_normal tr t F hFdef.symm hE0, if_neg hpar]
      refine ⟨?_, ?_, ?_⟩
      · rw [hval, hbe]
        exact scale_eq (2 ^ 52 + F) (XVal tr t) ((E : ℤ) - 1075) _ 5 hX (by omega)
      · rw [hX]; nlinarith
      · rw [hX]; nlinarith

end Proof
end Properties
end RTL
