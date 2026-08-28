import Proj.Properties

/-!
# Bit-level helper lemmas

Generic lemmas about `BitVec` extraction, the `extractBits`/`getBit` helpers of
`Proj.Properties`, and `BitVec.clz`, used in the correctness proof of the
floating point square root unit.
-/

namespace RTL
namespace Properties

/-- `BitVec.extractLsb` in terms of natural number division and modulus. -/
lemma toNat_extractLsb {w : ℕ} (v : BitVec w) (hi lo : ℕ) :
    (v.extractLsb hi lo).toNat = v.toNat / 2 ^ lo % 2 ^ (hi - lo + 1) := by
  simp [BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

/-- `BitVec.getLsb` in terms of natural number division and modulus. -/
lemma getLsb_eq_decide {w : ℕ} (v : BitVec w) (i : Fin w) :
    v.getLsb i = decide (v.toNat / 2 ^ (i : ℕ) % 2 = 1) := by
  simp [BitVec.getLsb, Nat.testBit_eq_decide_div_mod_eq]

/-- `extractBits` applied to (the cast of) a natural number. -/
lemma extractBits_natCast (n hi lo : ℕ) :
    extractBits (n : ℤ) hi lo = ((n / 2 ^ lo % 2 ^ (hi - lo + 1) : ℕ) : ℤ) := by
  push_cast [extractBits, Int.natCast_ediv, Int.natCast_emod]
  norm_num

/-- `extractBits` of a nonnegative integer. -/
lemma extractBits_eq (v : ℤ) (hi lo : ℕ) :
    extractBits v hi lo = v / 2 ^ lo % 2 ^ (hi - lo + 1) := by
  simp [extractBits]

/-- If `v` is small enough, `extractBits v hi lo` is just a division. -/
lemma extractBits_of_lt (v : ℤ) (hi lo : ℕ) (hv : 0 ≤ v) (hlt : v < 2 ^ (hi + 1)) :
    extractBits v hi lo = v / 2 ^ lo := by
  have h2 : (0:ℤ) < 2 ^ lo := by positivity
  rcases Nat.lt_or_ge hi lo with h | h
  · have h1 : v / 2 ^ lo = 0 := by
      apply Int.ediv_eq_zero_of_lt hv
      calc v < 2 ^ (hi + 1) := hlt
        _ ≤ 2 ^ lo := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
    simp [extractBits, h1]
  · have : v / 2 ^ lo < 2 ^ (hi - lo + 1) := by
      rw [Int.ediv_lt_iff_lt_mul h2, ← pow_add]
      calc v < 2 ^ (hi + 1) := hlt
        _ = 2 ^ (hi - lo + 1 + lo) := by congr 1; omega
    have hnn : 0 ≤ v / 2 ^ lo := Int.ediv_nonneg hv (le_of_lt h2)
    simp [extractBits, Int.emod_eq_of_lt hnn this]

/-- `getBit` in terms of integer division. -/
lemma getBit_eq_decide (v : ℤ) (n : ℕ) :
    getBit v n = decide ¬ (v / 2 ^ n % 2 = 0) := by
  unfold getBit
  by_cases h : v / 2 ^ n % 2 = 0 <;> simp [h]

/-- Bounds coming from the count of leading zeros of a nonzero bitvector. -/
lemma clz_bounds {w : ℕ} (x : BitVec w) (hw : 0 < w) (hx : x ≠ 0#w) :
    x.clz.toNat ≤ w - 1 ∧ 2 ^ (w - 1 - x.clz.toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (w - x.clz.toNat) := by
  have h2 : 2 ^ (w - 1 - x.clz.toNat) ≤ x.toNat :=
    BitVec.two_pow_sub_clz_le_toNat_of_ne_zero hw hx
  have h3 : x.toNat < 2 ^ (w - x.clz.toNat) := BitVec.toNat_lt_two_pow_sub_clz
  refine ⟨?_, h2, h3⟩
  by_contra hc
  push_neg at hc
  have : w - x.clz.toNat = 0 := by omega
  rw [this] at h3
  simp only [pow_zero, Nat.lt_one_iff] at h3
  exact hx (by simpa [BitVec.toNat_eq] using h3)

end Properties
end RTL
