import Mathlib

/-!
# The arithmetic core of the rounding argument

This file contains the purely arithmetic part of the correctness proof of the
floating point square root unit:

* `sqrt_cmp`, which turns comparisons between a scaled integer and the square
  root of a scaled integer into comparisons of integers, and
* `round_rtz_sub`, `round_rtz_orig`, ..., which show that the truncated
  quotient `Q - Q % 16` of the SRT recurrence, corrected by the sign of the
  final residual `R` and by the rounding bits `Q % 16`, is the correctly
  rounded square root.

Throughout, `S = 2 ^ 56 * X` is the radicand scaled into the units in which the
partial quotient `Q` is computed, and `R = S - Q ^ 2` is the final residual.
The hypotheses `9 - 6 * Q ≤ R ≤ 9 + 6 * Q` are the invariant maintained by the
digit recurrence, and `Q % 4 = 0` holds because the last quotient digit
produced contributes a multiple of `4`.
-/

namespace RTL
namespace Properties

/-- Comparisons between `c * 2 ^ k` and `√(S * 2 ^ (2 * k))` are comparisons of
integers. -/
lemma sqrt_cmp (S c : ℤ) (k : ℤ) (hS : 0 ≤ S) (hc : 0 ≤ c) :
    ((c : ℝ) * 2 ^ k ≤ Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) ↔ c ^ 2 ≤ S) ∧
      (Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) < (c : ℝ) * 2 ^ k ↔ S < c ^ 2) := by
  have hpos : (0:ℝ) < 2 ^ k := by positivity
  have hSR : (0:ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hcR : (0:ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hsplit : (S : ℝ) * 2 ^ (2 * k) = ((S : ℝ)) * (2 ^ k) ^ 2 := by
    rw [show (2:ℤ) * k = k + k by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; ring
  have hsqrt : Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) = Real.sqrt (S : ℝ) * 2 ^ k := by
    rw [hsplit, Real.sqrt_mul hSR, Real.sqrt_sq (le_of_lt hpos)]
  have key1 : ((c : ℝ) ≤ Real.sqrt (S : ℝ)) ↔ c ^ 2 ≤ S := by
    rw [Real.le_sqrt hcR hSR]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  have key2 : (Real.sqrt (S : ℝ) < (c : ℝ)) ↔ S < c ^ 2 := by
    rw [show ((c : ℝ)) = Real.sqrt ((c : ℝ) ^ 2) by rw [Real.sqrt_sq hcR],
      Real.sqrt_lt_sqrt_iff hSR]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hsqrt, mul_le_mul_iff_of_pos_right hpos, mul_lt_mul_iff_of_pos_right hpos]
  exact ⟨key1, key2⟩

/-- The companion of `sqrt_cmp`: comparisons in which the integer multiple of
`2 ^ k` is an *upper* bound for the square root. -/
lemma sqrt_cmp' (S c : ℤ) (k : ℤ) (hS : 0 ≤ S) (hc : 0 ≤ c) :
    (Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) ≤ (c : ℝ) * 2 ^ k ↔ S ≤ c ^ 2) ∧
      ((c : ℝ) * 2 ^ k < Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) ↔ c ^ 2 < S) := by
  have hpos : (0:ℝ) < 2 ^ k := by positivity
  have hSR : (0:ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hcR : (0:ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hsplit : (S : ℝ) * 2 ^ (2 * k) = ((S : ℝ)) * (2 ^ k) ^ 2 := by
    rw [show (2:ℤ) * k = k + k by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; ring
  have hsqrt : Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) = Real.sqrt (S : ℝ) * 2 ^ k := by
    rw [hsplit, Real.sqrt_mul hSR, Real.sqrt_sq (le_of_lt hpos)]
  have key : (Real.sqrt (S : ℝ) ≤ (c : ℝ)) ↔ S ≤ c ^ 2 := by
    rw [Real.sqrt_le_left hcR]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hsqrt, mul_le_mul_iff_of_pos_right hpos, mul_lt_mul_iff_of_pos_right hpos]
  exact ⟨key, by rw [← not_le, ← not_le, key]⟩

/-- The three shapes of integer bracketing produced by the rounding lemmas,
translated into the real inequalities the specification asks for.  Here `c` is
the result of the unit in the units of the SRT quotient, `2 ^ k` is the weight
of one such unit and `d` is half an ulp of the result (`8`, or `16` when the
result falls in the next binade). -/
lemma sqrt_bracket (S c d k : ℤ) (hS : 0 ≤ S) (hd1 : 8 ≤ d) (hd2 : d ≤ 16)
    (hc : 32 ≤ c) :
    (c ^ 2 ≤ S → S < (c + 16) ^ 2 →
        ((c : ℝ) * 2 ^ k ≤ Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) ∧
          Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) < ((c + 2 * d : ℤ) : ℝ) * 2 ^ k)) ∧
      ((c - 16) ^ 2 < S → S ≤ c ^ 2 →
        (((c - 2 * d : ℤ) : ℝ) * 2 ^ k < Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) ∧
          Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) ≤ (c : ℝ) * 2 ^ k)) ∧
      ((c - 8) ^ 2 < S → S < (c + 8) ^ 2 →
        (((c - d : ℤ) : ℝ) * 2 ^ k < Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) ∧
          Real.sqrt ((S : ℝ) * 2 ^ (2 * k)) < ((c + d : ℤ) : ℝ) * 2 ^ k)) := by
  refine ⟨fun h1 h2 => ⟨?_, ?_⟩, fun h1 h2 => ⟨?_, ?_⟩, fun h1 h2 => ⟨?_, ?_⟩⟩
  · exact (sqrt_cmp S c k hS (by omega)).1.mpr h1
  · exact (sqrt_cmp S (c + 2 * d) k hS (by omega)).2.mpr (by nlinarith)
  · exact (sqrt_cmp' S (c - 2 * d) k hS (by omega)).2.mpr (by nlinarith)
  · exact (sqrt_cmp' S c k hS (by omega)).1.mpr h2
  · exact (sqrt_cmp' S (c - d) k hS (by omega)).2.mpr (by nlinarith)
  · exact (sqrt_cmp S (c + d) k hS (by omega)).2.mpr (by nlinarith)

section

variable {X Q R : ℤ}
  (hX1 : 2 ^ 56 ≤ X) (hX2 : X ≤ 2 ^ 58 - 32)
  (hR : R = 2 ^ 56 * X - Q ^ 2) (hQ4 : Q % 4 = 0)
  (hlo : 9 - 6 * Q ≤ R) (hhi : R ≤ 9 + 6 * Q)

include hX1 hX2 hR hQ4 hlo hhi

/-- Basic consequences of the SRT invariant: the partial quotient is a
57-bit number lying within `3` of the exact square root. -/
lemma srt_basic :
    2 ^ 56 ≤ Q ∧ Q ≤ 2 ^ 57 - 5 ∧ (Q - 3) ^ 2 ≤ 2 ^ 56 * X ∧ 2 ^ 56 * X ≤ (Q + 3) ^ 2 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hlb : (Q - 3) ^ 2 ≤ 2 ^ 56 * X := by nlinarith
  have hub : 2 ^ 56 * X ≤ (Q + 3) ^ 2 := by nlinarith
  have h1 : 2 ^ 56 - 3 ≤ Q := by nlinarith
  have h2 : Q ≤ 2 ^ 57 - 5 := by nlinarith
  exact ⟨by omega, h2, hlb, hub⟩

/-- Round toward zero / round down, exact case: when no rounding bit is set and
the residual is negative, the result is one ulp below the truncated quotient. -/
lemma round_rtz_sub (hRneg : R < 0) :
    (Q - 16) ^ 2 ≤ 2 ^ 56 * X ∧ 2 ^ 56 * X < ((Q - 16) + 16) ^ 2 := by
  obtain ⟨hQlo, hQhi, hlb, hub⟩ := srt_basic hX1 hX2 hR hQ4 hlo hhi
  constructor <;> nlinarith

/-- Round toward zero / round down, generic case. -/
lemma round_rtz_orig (hne : ¬ (Q % 16 = 0 ∧ R < 0)) :
    (Q - Q % 16) ^ 2 ≤ 2 ^ 56 * X ∧ 2 ^ 56 * X < ((Q - Q % 16) + 16) ^ 2 := by
  obtain ⟨hQlo, hQhi, hlb, hub⟩ := srt_basic hX1 hX2 hR hQ4 hlo hhi
  have hu : Q % 16 = 0 ∨ Q % 16 = 4 ∨ Q % 16 = 8 ∨ Q % 16 = 12 := by omega
  rcases hu with h | h | h | h
  · have hR0 : 0 ≤ R := by
      by_contra hcon
      exact hne ⟨h, by omega⟩
    rw [h]; constructor <;> nlinarith
  · rw [h]; constructor <;> nlinarith
  · rw [h]; constructor <;> nlinarith
  · rw [h]; constructor <;> nlinarith

/-- Round up, generic case: the result is the truncated quotient plus one ulp. -/
lemma round_rup_add (hne : Q % 16 ≠ 0 ∨ 0 < R) :
    ((Q - Q % 16 + 16) - 16) ^ 2 < 2 ^ 56 * X ∧ 2 ^ 56 * X ≤ (Q - Q % 16 + 16) ^ 2 := by
  obtain ⟨hQlo, hQhi, hlb, hub⟩ := srt_basic hX1 hX2 hR hQ4 hlo hhi
  have hu : Q % 16 = 0 ∨ Q % 16 = 4 ∨ Q % 16 = 8 ∨ Q % 16 = 12 := by omega
  rcases hu with h | h | h | h
  · have hR0 : 0 < R := by
      rcases hne with hc | hc
      · exact absurd h hc
      · exact hc
    rw [h]; constructor <;> nlinarith
  · rw [h]; constructor <;> nlinarith
  · rw [h]; constructor <;> nlinarith
  · rw [h]; constructor <;> nlinarith

/-- Round up, exact case: the square root is exactly representable, so the
result is the truncated quotient itself. -/
lemma round_rup_orig (hR0 : R ≤ 0) :
    (Q - 16) ^ 2 < 2 ^ 56 * X ∧ 2 ^ 56 * X ≤ Q ^ 2 := by
  obtain ⟨hQlo, hQhi, hlb, hub⟩ := srt_basic hX1 hX2 hR hQ4 hlo hhi
  constructor <;> nlinarith

omit hX1 hX2 hQ4 hlo hhi in
/-- The square root of `2 ^ 56 * X` is never exactly half way between two
consecutive representable results. -/
lemma no_tie (hu : Q % 16 = 8) : R ≠ 0 := by
  intro h0
  have hQ : Q ^ 2 = 2 ^ 56 * X := by omega
  obtain ⟨k, hk⟩ : ∃ k, Q = 16 * k + 8 := ⟨Q / 16, by omega⟩
  have h1 : (2 * k + 1) ^ 2 = 2 ^ 50 * X := by
    have hsq : (16 * k + 8) ^ 2 = 64 * (2 * k + 1) ^ 2 := by ring
    rw [hk, hsq] at hQ
    have h64 : (64 : ℤ) * (2 * k + 1) ^ 2 = 64 * (2 ^ 50 * X) := by rw [hQ]; ring
    exact mul_left_cancel₀ (by norm_num : (64 : ℤ) ≠ 0) h64
  have h2 : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
  have h3 : (2 : ℤ) ^ 50 * X = 2 * (2 ^ 49 * X) := by ring
  omega

/-- Round to nearest, rounding up: the exact square root is above the midpoint,
so the result is one ulp above the truncated quotient. -/
lemma round_rne_add (hcase : 8 < Q % 16 ∨ (Q % 16 = 8 ∧ 0 ≤ R)) :
    ((Q - Q % 16 + 16) - 8) ^ 2 < 2 ^ 56 * X ∧
      2 ^ 56 * X < ((Q - Q % 16 + 16) + 8) ^ 2 := by
  obtain ⟨hQlo, hQhi, hlb, hub⟩ := srt_basic hX1 hX2 hR hQ4 hlo hhi
  rcases hcase with h | ⟨h8, hR0⟩
  · have h12 : Q % 16 = 12 := by omega
    rw [h12]; constructor <;> nlinarith
  · have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm (no_tie hR h8))
    rw [h8]; constructor <;> nlinarith

/-- Round to nearest, rounding down: the exact square root is below the
midpoint, so the result is the truncated quotient. -/
lemma round_rne_orig (hcase : ¬ (8 < Q % 16 ∨ (Q % 16 = 8 ∧ 0 ≤ R))) :
    ((Q - Q % 16) - 8) ^ 2 < 2 ^ 56 * X ∧ 2 ^ 56 * X < ((Q - Q % 16) + 8) ^ 2 := by
  obtain ⟨hQlo, hQhi, hlb, hub⟩ := srt_basic hX1 hX2 hR hQ4 hlo hhi
  push_neg at hcase
  obtain ⟨h1, h2⟩ := hcase
  have hu : Q % 16 = 0 ∨ Q % 16 = 4 ∨ Q % 16 = 8 ∨ Q % 16 = 12 := by omega
  rcases hu with h | h | h | h
  · rw [h]; constructor <;> nlinarith
  · rw [h]; constructor <;> nlinarith
  · have hRneg : R < 0 := by
      by_contra hcon
      exact absurd (h2 h) (by omega)
    rw [h]; constructor <;> nlinarith
  · omega

end

end Properties
end RTL
