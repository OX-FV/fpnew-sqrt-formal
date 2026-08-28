import Proj.Bits

/-!
# The real number denoted by an IEEE-754 binary64 bit pattern
-/

namespace RTL
namespace Properties
namespace Proof

/-- Split a binary64 bit pattern into (significand, biased exponent), taking
subnormals into account. -/
def decodeFP (operand : BitVec 64) : (BitVec 53) × (BitVec 11) :=
  let exp_bits := operand.extractLsb 62 52
  if exp_bits == 0 then
    -- denormal case
    let frac := (BitVec.ofNat 1 0) ++ (operand.extractLsb 51 0)
    let exp := BitVec.ofNat 11 1
    (frac, exp)
  else
    -- normal case
    let frac := (BitVec.ofNat 1 1) ++ (operand.extractLsb 51 0)
    let exp := exp_bits
    (frac, exp)

/-- The real number denoted by a binary64 bit pattern (ignoring the sign bit). -/
noncomputable def fp64ToReal (x : BitVec 64) : ℝ :=
  let mantissa := (decodeFP x).1
  let exponent := (decodeFP x).2
  (mantissa.toNat : ℝ) * (2 : ℝ) ^ ((exponent.toNat : ℤ) - 1023 - 52)

/-- The real number one ulp above `fp64ToReal x`. -/
noncomputable def nextLargestFp64ToReal (x : BitVec 64) : ℝ :=
  let mantissa := (decodeFP x).1
  let exponent := (decodeFP x).2
  ((mantissa.toNat : ℝ) + 1) * (2 : ℝ) ^ ((exponent.toNat : ℤ) - 1023 - 52)

/-- The real number half an ulp above `fp64ToReal x`. -/
noncomputable def nextHalfLargestFp64ToReal (x : BitVec 64) : ℝ :=
  let mantissa := (decodeFP x).1
  let exponent := (decodeFP x).2
  ((mantissa.toNat : ℝ) + 1 / 2) * (2 : ℝ) ^ ((exponent.toNat : ℤ) - 1023 - 52)

/-- The real number one ulp below `fp64ToReal x`. -/
noncomputable def nextSmallestFp64ToReal (x : BitVec 64) : ℝ :=
  let mantissa := (decodeFP x).1
  let exponent := (decodeFP x).2
  let normalOut := ((mantissa.toNat : ℝ) - 1) * (2 : ℝ) ^ ((exponent.toNat : ℤ) - 1023 - 52)
  if mantissa == 0 then
    normalOut + (2 : ℝ) ^ ((exponent.toNat : ℤ) - 1023 - 52 - 1)
  else
    normalOut

/-- The real number half an ulp below `fp64ToReal x`. -/
noncomputable def nextHalfSmallestFp64ToReal (x : BitVec 64) : ℝ :=
  let mantissa := (decodeFP x).1
  let exponent := (decodeFP x).2
  let normalOut := ((mantissa.toNat : ℝ) - 1 / 2) * (2 : ℝ) ^ ((exponent.toNat : ℤ) - 1023 - 52)
  if mantissa == 0 then
    normalOut + (2 : ℝ) ^ ((exponent.toNat : ℤ) - 1023 - 52 - 2)
  else
    normalOut

/-- `toNat` of a one-bit-wide concatenation. -/
lemma toNat_append_bit {n : ℕ} (x : BitVec 1) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- The exponent field of a binary64 bit pattern. -/
lemma extract_hi (v : BitVec 64) : (v.extractLsb 62 52).toNat = v.toNat / 2 ^ 52 % 2 ^ 11 := by
  simpa using toNat_extractLsb v 62 52

/-- The fraction field of a binary64 bit pattern. -/
lemma extract_lo (v : BitVec 64) : (v.extractLsb 51 0).toNat = v.toNat % 2 ^ 52 := by
  simp [toNat_extractLsb v 51 0]

/-- `decodeFP` on a subnormal bit pattern. -/
lemma decodeFP_denormal (v : BitVec 64) (h : v.toNat / 2 ^ 52 % 2 ^ 11 = 0) :
    (decodeFP v).1.toNat = v.toNat % 2 ^ 52 ∧ (decodeFP v).2.toNat = 1 := by
  have h0 : (v.extractLsb 62 52) = 0 := BitVec.eq_of_toNat_eq (by rw [extract_hi]; simpa using h)
  unfold decodeFP
  simp only [h0, beq_self_eq_true, if_true]
  exact ⟨by rw [toNat_append_bit, extract_lo]; simp, by simp⟩

/-- `decodeFP` on a normal bit pattern. -/
lemma decodeFP_normal (v : BitVec 64) (h : v.toNat / 2 ^ 52 % 2 ^ 11 ≠ 0) :
    (decodeFP v).1.toNat = 2 ^ 52 + v.toNat % 2 ^ 52 ∧
      (decodeFP v).2.toNat = v.toNat / 2 ^ 52 % 2 ^ 11 := by
  have h0 : ¬ ((v.extractLsb 62 52) = 0) := fun hc => h (by rw [← extract_hi, hc]; simp)
  unfold decodeFP
  simp only [beq_iff_eq, h0, if_false]
  exact ⟨by rw [toNat_append_bit, extract_lo]; simp, extract_hi v⟩

/-- The five real numbers attached to a bit pattern, in terms of its
significand `m` and biased exponent `e`. -/
lemma fp64_values (v : BitVec 64) (m e : ℤ) (hm : ((decodeFP v).1.toNat : ℤ) = m)
    (he : ((decodeFP v).2.toNat : ℤ) = e) (hmne : m ≠ 0) :
    fp64ToReal v = (m : ℝ) * 2 ^ (e - 1075) ∧
      nextLargestFp64ToReal v = ((m : ℝ) + 1) * 2 ^ (e - 1075) ∧
      nextSmallestFp64ToReal v = ((m : ℝ) - 1) * 2 ^ (e - 1075) ∧
      nextHalfLargestFp64ToReal v = ((m : ℝ) + 1 / 2) * 2 ^ (e - 1075) ∧
      nextHalfSmallestFp64ToReal v = ((m : ℝ) - 1 / 2) * 2 ^ (e - 1075) := by
  have hmR : ((decodeFP v).1.toNat : ℝ) = (m : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hm
  have heR : (((decodeFP v).2.toNat : ℤ) - 1023 - 52) = e - 1075 := by rw [he]; ring
  have hne : ¬ ((decodeFP v).1 == 0) = true := by
    simp only [beq_iff_eq]
    intro hcon
    apply hmne
    rw [← hm, hcon]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [fp64ToReal, nextLargestFp64ToReal, nextSmallestFp64ToReal,
      nextHalfLargestFp64ToReal, nextHalfSmallestFp64ToReal, hmR, heR, hne, if_false,
      Bool.false_eq_true]

end Proof
end Properties
end RTL
