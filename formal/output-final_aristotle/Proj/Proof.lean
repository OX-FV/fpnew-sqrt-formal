import Proj.RTL
import Proj.Properties
import Proj.Bits
import Proj.FP
import Proj.Operand
import Proj.Result
import Proj.Round

/-!
# Correctness of the floating point square root unit
-/

namespace RTL
namespace Properties
namespace Proof

/-- `SQRT_64B` is stable across the SRT stages: it is stable while the unit is
busy (`Sqrt64BStable`), and the unit is busy at every SRT stage (`SrtBusy`). -/
lemma sqrt64B_prev (tr : Nat → State) (hProps : ValidTrace tr) (s : Nat) (hs : 0 < s)
    (hprev : firstStage tr (s - 1) = true ∨ middleStage tr (s - 1) = true ∨
      lastStage tr (s - 1) = true) :
    sqrt64B tr s = sqrt64B tr (s - 1) := by
  have hbusy := hProps.srtBusy (s - 1) hprev
  have h := hProps.sqrt64BStable (s - 1) hbusy
  rwa [show s - 1 + 1 = s from by omega] at h

-- Interesting point: we need to have ∀ t as part of the inductive hypothesis
lemma rCorrect (tr : Nat → State) (hProps : ValidTrace tr) (jVar : Nat) :
  ∀ t : Nat,
  let j : Nat := jVal tr t
  let R := RVal tr t
  let X := XVal tr t
  let Q := Q tr t
  j = jVar → ((firstStage tr t ∨ middleStage tr t ∨ lastStage tr t) →
    sqrt64B tr t = true → R * 2 ^ (56 - 4*j) = 2^56 * X - Q^2)
  := by
  have hOpStable := hProps.opStable
  have hBaseCase := hProps.baseCase
  have hQ_initial := hProps.q_initial
  have hR_initial := hProps.r_initial
  have hJ_initial := hProps.j_initial
  have hJ_next := hProps.j_next
  have hR_next_eq := hProps.r_next_eq
  have hQ_next_eq := hProps.q_next_eq
  have hTimeConsistency := hProps.timeConsistency
  have hSrtBusy := hProps.srtBusy
  have hQ_recur := hProps.q_recur
  have hR_recur := hProps.r_recur
  have hjBound := hProps.jBound
  -- start induction now to include ∀ t as part of the IH
  induction jVar
  intro t j R X Q
  intro hjZero
  intro hStage hsq
  have jValZero : jVal tr t = 0 := hjZero
  have hFirst : firstStage tr t = true := hBaseCase t ⟨hStage, jValZero⟩
  have hQZero : Properties.Q tr t = 0 := hQ_initial t hFirst
  simp [Q, j, jValZero, hQZero]
  have hREqX : RVal tr t = XVal tr t := hR_initial t ⟨hFirst, hsq⟩
  simp [R, X, hREqX, mul_comm]
  -- Base Case done
  rename_i i ih
  intro t j R X Q
  intro hj
  have hJnonZero : j ≠ 0 := by
    omega
  intro hStage hsq
  have hNotFirst : ¬(firstStage tr t = true) := by
    intro hFirst
    exact hJnonZero (hJ_initial t hFirst)
  have hMiddleLast : middleStage tr t = true ∨ lastStage tr t = true := by tauto
  obtain ⟨htNonZero, hFirstMiddle⟩ := hTimeConsistency t ⟨hMiddleLast, hsq⟩
  have hStagePrev : firstStage tr (t - 1) = true ∨ middleStage tr (t - 1) = true ∨
      lastStage tr (t - 1) = true := by tauto
  have hsqPrev : sqrt64B tr (t - 1) = true := by
    rw [← sqrt64B_prev tr hProps t htNonZero hStagePrev]; exact hsq
  have hRNext : RVal tr t = RNext tr (t - 1) := hR_next_eq t ⟨hMiddleLast, hsq⟩
  have hRrecur : RVal tr t
      = 16 * RVal tr (t-1) - Properties.Q tr (t-1) * qVal tr (t-1) * 8 - q2Scaled tr (t-1) := by
    rw [hRNext]
    exact hR_recur (t-1) ⟨hFirstMiddle, hsqPrev⟩
  have hQNext : Properties.Q tr t = QNext tr (t - 1) := hQ_next_eq t ⟨hMiddleLast, hsq⟩
  have hQrecur : Properties.Q tr t = Properties.Q tr (t-1) + qScaled tr (t-1) := by
    rw [hQNext]
    exact hQ_recur (t-1) ⟨hFirstMiddle, hsqPrev⟩
  have hjPrev : jVal tr (t-1) = i := by
    have hj_recur : jVal tr t = 1 + jVal tr (t - 1) := (hJ_next t ⟨hMiddleLast, hsq⟩).1
    omega
  have hIH : (RVal tr (t-1)) * 2 ^ (56 - 4 * i)
      = 2 ^ 56 * (XVal tr (t-1)) - (Properties.Q tr (t-1)) ^ 2 := by
    have ih_prev := ih (t-1)
    dsimp only at ih_prev
    have hh := ih_prev hjPrev hStagePrev hsqPrev
    rwa [hjPrev] at hh
  have j_bound : jVal tr (t - 1) ≤ 13 := hjBound (t-1) hFirstMiddle
  have hi : 4 * i + 4 ≤ 56 := by
    have j_bound_copy := j_bound
    rw [hjPrev] at j_bound_copy
    omega
  dsimp only [R, X, Q]
  rw [hRrecur, hQrecur, hj]

  have h_pow : 2 ^ (56 - (4 + i * 4)) * 16 = 2 ^ (56 - 4 * i) := by
    have : 16 = 2 ^ 4 := rfl
    rw [this, ← Nat.pow_add]
    congr 1
    omega  -- Requires 4 + i * 4 ≤ 56 in scope
  have h_pow_z : (2 : ℤ) ^ (56 - (4 + i * 4)) * 16 = (2 : ℤ) ^ (56 - 4 * i) := by
    exact_mod_cast h_pow
  have h_first : RVal tr (t - 1) * 2 ^ (56 - (4 + i * 4)) * 16 = RVal tr (t - 1) * 2 ^ (56 - 4 * i) := by
    rw [mul_assoc, h_pow_z]
  ring
  rw [h_first]
  rw [hIH]
  ring_nf
  simp [qScaled,q2Scaled,q2Val]
  simp [j_bound]
  ring_nf
  rw [hjPrev]
  have hBusyPrev : vfdsuDpFdivBusy tr (t-1) = true := hSrtBusy (t-1) hStagePrev
  have hXStable : XVal tr t = XVal tr (t-1) := by
    have hh := hOpStable (t-1) hBusyPrev
    rw [show t - 1 + 1 = t from by omega] at hh
    exact hh.2.2
  rw [hXStable]
  ring_nf
  have h_pow1 : 2 ^ (56 - (4 + i * 4)) * 8 = 2 ^ (54 - i * 4) * 2 := by
    have h8 : (8 : ℕ) = 2 ^ 3 := rfl
    have h2 : (2 : ℕ) = 2 ^ 1 := rfl
    -- Reduce exponents on both sides to 2 ^ (55 - i * 4)
    rw [h8]
    nth_rewrite 4 [h2]
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have h_pow1_z : (2 : ℤ) ^ (56 - (4 + i * 4)) * (8 : ℤ) = (2 : ℤ) ^ (54 - i * 4) * (2 : ℤ) := by
    exact_mod_cast h_pow1
  have h_sub1 : Properties.Q tr (t - 1) * qVal tr (t - 1) * 2 ^ (56 - (4 + i * 4)) * 8
              = Properties.Q tr (t - 1) * qVal tr (t - 1) * (2 ^ (54 - i * 4) * 2) := by
    rw [mul_assoc, h_pow1_z]
  rw [h_sub1]
  have h_pow2 : 2 ^ (56 - (4 + i * 4)) * 2 ^ (56 - i * 4) = 2 ^ ((54 - i * 4) * 2) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h_pow2_z : (2 : ℤ) ^ (56 - (4 + i * 4)) * (2 : ℤ) ^ (56 - i * 4) = (2 : ℤ) ^ ((54 - i * 4) * 2) := by
    exact_mod_cast h_pow2
  have h_sub2 : qVal tr (t - 1) ^ 2 * 2 ^ (56 - (4 + i * 4)) * 2 ^ (56 - i * 4)
              = qVal tr (t - 1) ^ 2 * 2 ^ ((54 - i * 4) * 2) := by
    rw [mul_assoc, h_pow2_z]
  rw [h_sub2]
  ring

/-- The partial quotient is always a multiple of `4`: each quotient digit
contributes `q * 2 ^ (54 - 4 * j)` with `j ≤ 13`. -/
lemma qMod4 (tr : Nat → State) (hProps : ValidTrace tr) (jVar : Nat) :
    ∀ t : Nat, jVal tr t = jVar →
      (firstStage tr t = true ∨ middleStage tr t = true ∨ lastStage tr t = true) →
      sqrt64B tr t = true →
      Q tr t % 4 = 0 := by
  have hBaseCase := hProps.baseCase
  have hQ_initial := hProps.q_initial
  have hJ_initial := hProps.j_initial
  have hJ_next := hProps.j_next
  have hQ_next_eq := hProps.q_next_eq
  have hTimeConsistency := hProps.timeConsistency
  have hQ_recur := hProps.q_recur
  have hjBound := hProps.jBound
  induction jVar with
  | zero =>
    intro t hj hstage _
    have hFirst : firstStage tr t = true := hBaseCase t ⟨hstage, hj⟩
    rw [hQ_initial t hFirst]
    norm_num
  | succ i ih =>
    intro t hj hstage hsq
    have hNotFirst : ¬ (firstStage tr t = true) := by
      intro hF
      have := hJ_initial t hF
      omega
    have hML : middleStage tr t = true ∨ lastStage tr t = true := by tauto
    obtain ⟨hjrec, -⟩ := hJ_next t ⟨hML, hsq⟩
    obtain ⟨htpos, hprev⟩ := hTimeConsistency t ⟨hML, hsq⟩
    have hstagePrev : firstStage tr (t - 1) = true ∨ middleStage tr (t - 1) = true ∨
        lastStage tr (t - 1) = true := by tauto
    have hsqPrev : sqrt64B tr (t - 1) = true := by
      rw [← sqrt64B_prev tr hProps t htpos hstagePrev]; exact hsq
    have hjprev : jVal tr (t - 1) = i := by omega
    have hQt : Q tr t = QNext tr (t - 1) := hQ_next_eq t ⟨hML, hsq⟩
    have hQrec : QNext tr (t - 1) = Q tr (t - 1) + qScaled tr (t - 1) :=
      hQ_recur (t - 1) ⟨hprev, hsqPrev⟩
    have hIH : Q tr (t - 1) % 4 = 0 := ih (t - 1) hjprev hstagePrev hsqPrev
    have hjb : jVal tr (t - 1) ≤ 13 := hjBound (t - 1) hprev
    have hscaled : qScaled tr (t - 1) % 4 = 0 := by
      unfold qScaled
      rw [if_pos ⟨Nat.zero_le _, hjb⟩]
      have hsplit : (2 : ℤ) ^ (54 - 4 * jVal tr (t - 1))
          = 4 * 2 ^ (52 - 4 * jVal tr (t - 1)) := by
        rw [show (54 - 4 * jVal tr (t - 1)) = 2 + (52 - 4 * jVal tr (t - 1)) from by omega,
          pow_add]
        norm_num
      rw [hsplit, show qVal tr (t - 1) * (4 * 2 ^ (52 - 4 * jVal tr (t - 1)))
        = 4 * (qVal tr (t - 1) * 2 ^ (52 - 4 * jVal tr (t - 1))) from by ring]
      exact Int.mul_emod_right 4 _
    omega

/-- The unit can only signal completion at a cycle `t ≥ 2`: `Ex4UnitDone` puts
the packing stage at `t - 1`, and `Ex3Ex4` in turn requires `t - 1 > 0`. -/
lemma done_two_le (tr : Nat → State) (hProps : ValidTrace tr) (t : Nat)
    (hDone : unitDone tr t = true) : 2 ≤ t := by
  have hEx4UnitDone : Ex4UnitDone tr := hProps.ex4UnitDone
  have hEx3Ex4 : Ex3Ex4 tr := hProps.ex3Ex4
  obtain ⟨ht0, -, hEx4⟩ := (hEx4UnitDone t).1 hDone
  have := ((hEx3Ex4 (t - 1)).1 hEx4).1
  omega

/-- A bit pattern whose real value vanishes has vanishing magnitude bits. -/
lemma extractLsb_eq_zero_of_fp64ToReal_eq_zero (v : BitVec 64) (h : fp64ToReal v = 0) :
    v.extractLsb 62 0 = 0 := by
  by_cases hE0 : v.toNat / 2 ^ 52 % 2 ^ 11 = 0
  · obtain ⟨hm, he⟩ := decodeFP_denormal v hE0
    have hm0 : (decodeFP v).1.toNat = 0 := by
      by_contra hc
      have hpos : (0 : ℝ) < ((decodeFP v).1.toNat : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hc
      have : fp64ToReal v ≠ 0 := by
        simp only [fp64ToReal]
        positivity
      exact this h
    rw [hm] at hm0
    have hz : v.toNat % 2 ^ 63 = 0 := by
      norm_num at hm0 hE0 ⊢
      omega
    simp only [BitVec.toNat_eq, toNat_extractLsb]
    simp
    omega
  · obtain ⟨hm, -⟩ := decodeFP_normal v hE0
    exfalso
    have hpos : (0 : ℝ) < ((decodeFP v).1.toNat : ℝ) := by
      rw [hm]; positivity
    have : fp64ToReal v ≠ 0 := by
      simp only [fp64ToReal]
      positivity
    exact this h

/-- For a non-special operation the operand denotes a non-zero real number.
This is exactly what `OpNonZero` provides: the magnitude bits of the operand
are non-zero. -/
lemma operand_ne_zero (tr : Nat → State) (hProps : ValidTrace tr) (t : Nat)
    (hNoSpec : noSpecial tr t = true) : fp64ToReal (srcf0Q tr t) ≠ 0 := by
  have hOpNonZero : OpNonZero tr := hProps.opNonZero
  exact fun h => hOpNonZero t hNoSpec (extractLsb_eq_zero_of_fp64ToReal_eq_zero _ h)

/-- Timing and stability facts around the cycle at which the unit signals
completion: the last SRT stage happened at `t - 2`, the packing stage at
`t - 1`, and the operand, the rounding mode, the `noSpecial` flag and the
`SQRT_64B` flag did not change in between. -/
lemma doneTiming (tr : Nat → State) (hProps : ValidTrace tr) (t : Nat)
    (hDone : unitDone tr t = true) (hNoSpec : noSpecial tr t = true)
    (hSq : sqrt64B tr t = true) :
    ctrlEx4Pipedown tr (t - 1) = true ∧ ctrlEx3Pipedown tr (t - 2) = true ∧
      lastStage tr (t - 2) = true ∧ noSpecial tr (t - 1) = true ∧
      noSpecial tr (t - 2) = true ∧ srcf0Q tr (t - 1) = srcf0Q tr t ∧
      srcf0Q tr (t - 2) = srcf0Q tr t ∧ rmQ tr (t - 2) = rmQ tr t ∧
      unitResult tr t = packEx4OutResult tr (t - 1) ∧
      sqrt64B tr (t - 1) = true ∧ sqrt64B tr (t - 2) = true := by
  have ht : 2 ≤ t := done_two_le tr hProps t hDone
  have hOpStable := hProps.opStable
  have hResultEqPack := hProps.resultEqPack
  have hEx4UnitDone := hProps.ex4UnitDone
  have hEx4ResStable := hProps.ex4ResStable
  have hWasBusy := hProps.wasBusy
  have hNoSpecialStable := hProps.noSpecialStable
  have hEx3Ex4 := hProps.ex3Ex4
  have hEx3Ex4Stable := hProps.ex3Ex4Stable
  have hDefOfLast := hProps.defOfLast
  have h21 : t - 1 - 1 = t - 2 := by omega
  have h12 : t - 2 + 1 = t - 1 := by omega
  have h11 : t - 1 + 1 = t := by omega
  obtain ⟨-, hflush, hEx4⟩ := (hEx4UnitDone t).1 hDone
  have hEx3 : ctrlEx3Pipedown tr (t - 2) = true := by
    have := ((hEx3Ex4 (t - 1)).1 hEx4).2.2
    rwa [h21] at this
  have hLast : lastStage tr (t - 2) = true := (hDefOfLast (t - 2)).2 hEx3
  obtain ⟨-, hBusyPrev⟩ := hWasBusy t hDone
  obtain ⟨hsrc1, hrm1, -⟩ := hOpStable (t - 1) hBusyPrev
  rw [h11] at hsrc1 hrm1
  obtain ⟨hrm2, hsrc2⟩ := hEx3Ex4Stable (t - 1) (by omega) hEx4
  rw [h21] at hrm2 hsrc2
  have hns1 : noSpecial tr (t - 1) = true := by
    have := hNoSpecialStable (t - 1) (by rw [h11]; exact hsrc1)
    rw [h11] at this
    rw [← this]; exact hNoSpec
  have hns2 : noSpecial tr (t - 2) = true := by
    have := hNoSpecialStable (t - 2) (by rw [h12]; exact hsrc2.symm)
    rw [h12] at this
    rw [← this]; exact hns1
  have hsq1 : sqrt64B tr (t - 1) = true := by
    have := hProps.sqrt64BStable (t - 1) hBusyPrev
    rw [h11] at this
    rw [← this]; exact hSq
  have hsq2 : sqrt64B tr (t - 2) = true := by
    have := sqrt64B_prev tr hProps (t - 1) (by omega)
      (by rw [h21]; exact Or.inr (Or.inr hLast))
    rw [h21] at this
    rw [← this]; exact hsq1
  refine ⟨hEx4, hEx3, hLast, hns1, hns2, hsrc1.symm, ?_, ?_, ?_, hsq1, hsq2⟩
  · rw [hsrc2, hsrc1]
  · rw [hrm2, hrm1]
  · rw [hResultEqPack t]
    exact (hEx4ResStable t hDone).2

/-- `clzVal` only depends on the operand. -/
lemma clzVal_congr (tr : Nat → State) (a b : Nat) (h : srcf0Q tr a = srcf0Q tr b) :
    clzVal tr a = clzVal tr b := by
  simp only [clzVal, h]

/-- `XVal` only depends on the operand. -/
lemma XVal_congr (tr : Nat → State) (a b : Nat) (h : srcf0Q tr a = srcf0Q tr b) :
    XVal tr a = XVal tr b := by
  simp only [XVal, h, clzVal_congr tr a b h]

/-- `biasedExpnt` only depends on the operand. -/
lemma biasedExpnt_congr (tr : Nat → State) (a b : Nat) (h : srcf0Q tr a = srcf0Q tr b) :
    biasedExpnt tr a = biasedExpnt tr b := by
  simp only [biasedExpnt, h, clzVal_congr tr a b h]

/-- The three facts about the last SRT stage that drive the rounding argument:
the residual is the difference between the radicand and the square of the
partial quotient, the partial quotient is a multiple of `4`, and the SRT
invariant holds. -/
lemma srt_facts (tr : Nat → State) (hProps : ValidTrace tr) (s : Nat)
    (hEx3 : ctrlEx3Pipedown tr s = true) (hns : noSpecial tr s = true)
    (hsq : sqrt64B tr s = true) :
    RVal tr s = 2 ^ 56 * XVal tr s - (Q tr s) ^ 2 ∧ Q tr s % 4 = 0 ∧
      9 - 6 * Q tr s ≤ RVal tr s ∧ RVal tr s ≤ 9 + 6 * Q tr s := by
  have hDefOfLast := hProps.defOfLast
  have hQEquals := hProps.qEquals
  have hQRndIneq := hProps.qRndIneq
  have hStopEarly := hProps.stopEarly
  have hLast : lastStage tr s = true := (hDefOfLast s).2 hEx3
  have hstage : firstStage tr s = true ∨ middleStage tr s = true ∨ lastStage tr s = true :=
    Or.inr (Or.inr hLast)
  have hQ4 : Q tr s % 4 = 0 := qMod4 tr hProps (jVal tr s) s rfl hstage hsq
  have hrc := rCorrect tr hProps (jVal tr s) s rfl hstage hsq
  have hR : RVal tr s = 2 ^ 56 * XVal tr s - (Q tr s) ^ 2 := by
    by_cases hj : jVal tr s = 14
    · rw [hj] at hrc
      simpa using hrc
    · have h0 : RVal tr s = 0 := hStopEarly s ⟨hEx3, hns, hsq, hj⟩
      rw [h0] at hrc ⊢
      simp only [zero_mul] at hrc
      omega
  obtain ⟨h1, h2⟩ := hQRndIneq s ⟨hEx3, hns, hsq⟩
  rw [hQEquals s] at h1 h2
  exact ⟨hR, hQ4, h1, h2⟩

/-- All the quantitative information about the cycle `t` at which the unit
signals completion: `Qv`, `Rv` and `X` are the partial quotient, the residual
and the radicand of the last SRT stage `t - 2`, `2 ^ k` is the weight of the
least significant bit of `Qv`, the rounding decision is taken on `Qv % 16` and
the sign of `Rv`, and the last conjunct evaluates the five real numbers
attached to the result of the unit in terms of the rounded quotient `A`. -/
lemma sqrt_core (tr : Nat → State) (hProps : ValidTrace tr) (t : Nat)
    (hDone : unitDone tr t = true) (hNoSpec : noSpecial tr t = true)
    (hSq : sqrt64B tr t = true) :
    ∃ (Qv Rv X k : ℤ),
      Rv = 2 ^ 56 * X - Qv ^ 2 ∧ Qv % 4 = 0 ∧ 9 - 6 * Qv ≤ Rv ∧ Rv ≤ 9 + 6 * Qv ∧
      2 ^ 56 ≤ X ∧ X ≤ 2 ^ 58 - 32 ∧ 2 ^ 56 ≤ Qv ∧ Qv ≤ 2 ^ 57 - 5 ∧
      RVal tr (t - 2) = Rv ∧ rndBits tr (t - 2) = Qv % 16 ∧
      extractBits (QRnd tr (t - 2)) (B + L - 1) 3 = Qv / 8 ∧
      getBit (QRnd tr (t - 2)) 56 = true ∧
      rmQ tr (t - 2) = rmQ tr t ∧
      ctrlEx3Pipedown tr (t - 2) = true ∧ noSpecial tr (t - 2) = true ∧
      Real.sqrt (fp64ToReal (srcf0Q tr t))
        = Real.sqrt (((2 ^ 56 * X : ℤ) : ℝ) * 2 ^ (2 * k)) ∧
      (∀ A : ℤ, QAfterRnd tr (t - 2) = A → 2 ^ 53 ≤ A → A ≤ 2 ^ 54 + 1 →
        ∃ d : ℤ, 8 ≤ d ∧ d ≤ 16 ∧
          fp64ToReal (unitResult tr t) = ((16 * (A / 2) : ℤ) : ℝ) * 2 ^ k ∧
          nextLargestFp64ToReal (unitResult tr t)
            = ((16 * (A / 2) + 2 * d : ℤ) : ℝ) * 2 ^ k ∧
          nextSmallestFp64ToReal (unitResult tr t)
            = ((16 * (A / 2) - 2 * d : ℤ) : ℝ) * 2 ^ k ∧
          nextHalfLargestFp64ToReal (unitResult tr t)
            = ((16 * (A / 2) + d : ℤ) : ℝ) * 2 ^ k ∧
          nextHalfSmallestFp64ToReal (unitResult tr t)
            = ((16 * (A / 2) - d : ℤ) : ℝ) * 2 ^ k) := by
  have hPackMantissa := hProps.packMantissa
  have hPackExpnt := hProps.packExpnt
  have hPackInp := hProps.packInp
  have hQEquals := hProps.qEquals
  have hResNoDenorm := hProps.resNoDenorm
  have ht : 2 ≤ t := done_two_le tr hProps t hDone
  have hne : fp64ToReal (srcf0Q tr t) ≠ 0 := operand_ne_zero tr hProps t hNoSpec
  obtain ⟨hEx4, hEx3, hLast, hns1, hns2, hsrc1, hsrc2, hrm2, hres, hsq1, hsq2⟩ :=
    doneTiming tr hProps t hDone hNoSpec hSq
  -- the operand
  obtain ⟨hopval, hX1, hX2⟩ := operand_value tr t hne
  set X := XVal tr t with hXdef
  set h := biasedExpnt tr t / 2 with hhdef
  -- the last SRT stage
  obtain ⟨hR, hQ4, hlo, hhi⟩ := srt_facts tr hProps (t - 2) hEx3 hns2 hsq2
  rw [XVal_congr tr (t - 2) t hsrc2, ← hXdef] at hR
  set Qv := Q tr (t - 2) with hQdef
  set Rv := RVal tr (t - 2) with hRdef
  obtain ⟨hQlo, hQhi, -, -⟩ := srt_basic hX1 hX2 hR hQ4 hlo hhi
  have hQE : QRnd tr (t - 2) = Qv := hQEquals (t - 2)
  -- the rounding bits
  have h56Q : getBit Qv 56 = true := by
    simp only [getBit]
    rw [if_neg (by omega : ¬ (Qv / 2 ^ 56 % 2 = 0))]
  have h56 : getBit (QRnd tr (t - 2)) 56 = true := by rw [hQE]; exact h56Q
  have hEB : extractBits (QRnd tr (t - 2)) (B + L - 1) 3 = Qv / 8 := by
    rw [hQE]
    simp only [extractBits, B, L]
    norm_num
    omega
  have hrb : rndBits tr (t - 2) = Qv % 16 := by
    simp only [rndBits, qRndBits, hQE, h56Q, if_true, extractBits]
    norm_num
  refine ⟨Qv, Rv, X, h - 56, hR, hQ4, hlo, hhi, hX1, hX2, hQlo, hQhi, rfl, hrb, hEB, h56,
    hrm2, hEx3, hns2, ?_, ?_⟩
  · -- the operand as a scaled radicand
    rw [hopval]
    congr 1
    rw [shift_val (X : ℝ) 56 (2 * h - 56) (2 * (h - 56)) (by ring)]
    congr 1
    push_cast
    ring
  · -- the result of the unit
    intro A hA hA1 hA2
    have hN : (unitResult tr t).toNat = (unitResult tr t).toNat := rfl
    -- the fraction fed to the packing stage
    have hfrac : packVfdsuEx4Frac tr (t - 1) = A := by
      rw [hPackInp (t - 1) (by omega) hEx4, show t - 1 - 1 = t - 2 from by omega, hA]
    -- the result is normal
    have hEne : (unitResult tr t).toNat / 2 ^ 52 % 2 ^ 11 ≠ 0 := by
      have := hResNoDenorm t ⟨hDone, hNoSpec, hSq⟩
      simp only [WF, WE] at this
      norm_num at this
      exact fun hc => this ((extractLsb_hi_eq_zero_iff _).2 hc)
    have hNres : (unitResult tr t).toNat = (packEx4OutResult tr (t - 1)).toNat := by
      rw [hres]
    -- the mantissa and the exponent of the result
    have hMant := hPackMantissa (t - 1) ⟨hEx4, hns1, hsq1⟩
    have hExp := hPackExpnt (t - 1) ⟨hEx4, hns1, hsq1⟩
    simp only [hfrac, WF, WE] at hMant hExp
    rw [← hNres] at hMant hExp
    norm_num at hMant hExp
    have hhe : halfExpnt tr (t - 1) = h + 1023 := by
      simp only [halfExpnt, biasedExpnt_congr tr (t - 1) t hsrc1, ← hhdef, bias]
    simp only [expectedExpnt, hfrac, hhe] at hExp
    refine result_values (unitResult tr t) A h ((unitResult tr t).toNat) rfl hA1 hA2 hEne
      hMant ?_
    rw [hExp]
    split_ifs <;> ring


/-- **Correctness of the floating point square root unit.**

For a trace satisfying `ValidTrace`, at any cycle `t` at which the unit signals
completion of a non-special 64-bit square root, the packed result is the
correctly rounded square root of the operand, in each of the five rounding
modes. -/
theorem sqrtCorrect (tr : Nat → State) (hProps : ValidTrace tr) (t : Nat) :
  let res := unitResult tr t
  let sqrtOperand := (fp64ToReal (srcf0Q tr t)).sqrt
  let resReal := fp64ToReal res
  let resRealLarge := nextLargestFp64ToReal res
  let resRealSmall := nextSmallestFp64ToReal res
  let resRealHalfLarge := nextHalfLargestFp64ToReal res
  let resRealHalfSmall := nextHalfSmallestFp64ToReal res
  let rm := rmQ tr t
  (unitDone tr t = true ∧ noSpecial tr t = true ∧ sqrt64B tr t = true) →
    (((rm = RoundModes.RTZ ∨ rm = RoundModes.RDN) →
        (resReal ≤ sqrtOperand ∧ sqrtOperand < resRealLarge)) ∧
    (rm = RoundModes.RUP → (resRealSmall < sqrtOperand ∧ sqrtOperand ≤ resReal)) ∧
    (rm = RoundModes.RNE →
        ((resRealHalfSmall < sqrtOperand ∧ sqrtOperand < resRealHalfLarge) ∨
          ((sqrtOperand = resRealHalfSmall ∨ sqrtOperand = resRealHalfLarge) ∧
            res.getLsb = 0))) ∧
    (rm = RoundModes.RMM →
      (resRealHalfSmall ≤ sqrtOperand ∧ sqrtOperand < resRealHalfLarge))) := by
  intro res sqrtOperand resReal resRealLarge resRealSmall resRealHalfLarge resRealHalfSmall rm
  rintro ⟨hDone, hNoSpec, hSq⟩
  obtain ⟨Qv, Rv, X, k, hR, hQ4, hlo, hhi, hX1, hX2, hQlo, hQhi, hRv, hrb, hEB, h56, hrm2,
    hEx3, hns2, hsqrtop, hvals⟩ := sqrt_core tr hProps t hDone hNoSpec hSq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsq2⟩ := doneTiming tr hProps t hDone hNoSpec hSq
  have hRNE_add1 := hProps.rne_add1
  have hRNE_orig := hProps.rne_orig
  have hRTZ_sub1 := hProps.rtz_sub1
  have hRTZ_orig := hProps.rtz_orig
  have hRUP_add1 := hProps.rup_add1
  have hRUP_orig := hProps.rup_orig
  have hRDN_sub1 := hProps.rdn_sub1
  have hRDN_orig := hProps.rdn_orig
  have hRMM_add1 := hProps.rmm_add1
  have hRMM_orig := hProps.rmm_orig
  have hSnn : (0 : ℤ) ≤ 2 ^ 56 * X := by omega
  refine ⟨fun hmode => ?_, fun hmode => ?_, fun hmode => ?_, fun hmode => ?_⟩
  · -- round toward zero and round down
    by_cases hsub : rndBits tr (t - 2) = 0 ∧ RVal tr (t - 2) < 0
    · -- the truncated quotient is one ulp too large
      obtain ⟨hrb0, hRneg0⟩ := hsub
      have hQM : Qv % 16 = 0 := by rw [hrb] at hrb0; exact hrb0
      have hRneg : Rv < 0 := by rw [hRv] at hRneg0; exact hRneg0
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 - 2 := by
        have hh : QAfterRnd tr (t - 2) = extractBits (QRnd tr (t - 2)) (B + L - 1) 3 - 2 := by
          rcases hmode with hm | hm
          · have h := hRTZ_sub1 (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hm, hsq2, hrb0, hRneg0⟩
            simpa only [h56, if_true] using h
          · have h := hRDN_sub1 (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hm, hsq2, hrb0, hRneg0⟩
            simpa only [h56, if_true] using h
        rw [hh, hEB]
      have hbig : 2 ^ 56 < Qv := by nlinarith
      obtain ⟨d, hd1, hd2, hv1, hv2, -, -, -⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * ((Qv / 8 - 2) / 2) = Qv - 16 from by omega] at hv1 hv2
      obtain ⟨hb1, hb2⟩ := round_rtz_sub hX1 hX2 hR hQ4 hlo hhi hRneg
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) (Qv - 16) d k hSnn hd1 hd2 (by omega)).1 hb1 hb2
      refine ⟨?_, ?_⟩
      · change fp64ToReal (unitResult tr t) ≤ Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv1, hsqrtop]; exact g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) < nextLargestFp64ToReal (unitResult tr t)
        rw [hv2, hsqrtop]; exact g2
    · -- the truncated quotient is the result
      have hne' : ¬ (Qv % 16 = 0 ∧ Rv < 0) := by
        rw [← hrb, ← hRv]; exact hsub
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 := by
        rcases hmode with hm | hm
        · have h := hRTZ_orig (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hm, hsq2, hsub⟩
          rw [h, hEB]
        · have h := hRDN_orig (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hm, hsq2, hsub⟩
          rw [h, hEB]
      obtain ⟨d, hd1, hd2, hv1, hv2, -, -, -⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * (Qv / 8 / 2) = Qv - Qv % 16 from by omega] at hv1 hv2
      obtain ⟨hb1, hb2⟩ := round_rtz_orig hX1 hX2 hR hQ4 hlo hhi hne'
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) (Qv - Qv % 16) d k hSnn hd1 hd2 (by omega)).1 hb1 hb2
      refine ⟨?_, ?_⟩
      · change fp64ToReal (unitResult tr t) ≤ Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv1, hsqrtop]; exact g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) < nextLargestFp64ToReal (unitResult tr t)
        rw [hv2, hsqrtop]; exact g2
  · -- round up
    by_cases hadd : rndBits tr (t - 2) ≠ 0 ∨ RVal tr (t - 2) > 0
    · -- the result is one ulp above the truncated quotient
      have hadd' : Qv % 16 ≠ 0 ∨ 0 < Rv := by
        rw [hrb, hRv] at hadd; exact hadd
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 + 2 := by
        have h := hRUP_add1 (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hmode, hsq2, hadd⟩
        rw [show QAfterRnd tr (t - 2) = _ from by simpa only [h56, if_true] using h, hEB]
      obtain ⟨d, hd1, hd2, hv1, -, hv3, -, -⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * ((Qv / 8 + 2) / 2) = Qv - Qv % 16 + 16 from by omega] at hv1 hv3
      obtain ⟨hb1, hb2⟩ := round_rup_add hX1 hX2 hR hQ4 hlo hhi hadd'
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) (Qv - Qv % 16 + 16) d k hSnn hd1 hd2 (by omega)).2.1 hb1 hb2
      refine ⟨?_, ?_⟩
      · change nextSmallestFp64ToReal (unitResult tr t) < Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv3, hsqrtop]; exact g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) ≤ fp64ToReal (unitResult tr t)
        rw [hv1, hsqrtop]; exact g2
    · -- the square root is at most the truncated quotient
      push_neg at hadd
      obtain ⟨hrb0, hRnp0⟩ := hadd
      have hQM : Qv % 16 = 0 := by rw [hrb] at hrb0; exact hrb0
      have hRnp : Rv ≤ 0 := by rw [hRv] at hRnp0; exact hRnp0
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 := by
        have h := hRUP_orig (t - 2)
          ⟨hEx3, hns2, by rw [hrm2]; exact hmode, hsq2, by push_neg; exact ⟨hrb0, hRnp0⟩⟩
        rw [h, hEB]
      obtain ⟨d, hd1, hd2, hv1, -, hv3, -, -⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * (Qv / 8 / 2) = Qv from by omega] at hv1 hv3
      obtain ⟨hb1, hb2⟩ := round_rup_orig hX1 hX2 hR hQ4 hlo hhi hRnp
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) Qv d k hSnn hd1 hd2 (by omega)).2.1 hb1 hb2
      refine ⟨?_, ?_⟩
      · change nextSmallestFp64ToReal (unitResult tr t) < Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv3, hsqrtop]; exact g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) ≤ fp64ToReal (unitResult tr t)
        rw [hv1, hsqrtop]; exact g2
  · -- round to nearest, ties to even: the square root is never exactly half way
    -- between two representable numbers, so the left disjunct always holds
    left
    by_cases hadd : rndBits tr (t - 2) > 8 ∨ (rndBits tr (t - 2) = 8 ∧ RVal tr (t - 2) ≥ 0)
    · have hadd' : 8 < Qv % 16 ∨ (Qv % 16 = 8 ∧ 0 ≤ Rv) := by
        rw [hrb, hRv] at hadd; exact hadd
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 + 2 := by
        have h := hRNE_add1 (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hmode, hsq2, hadd⟩
        rw [show QAfterRnd tr (t - 2) = _ from by simpa only [h56, if_true] using h, hEB]
      obtain ⟨d, hd1, hd2, -, -, -, hv4, hv5⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * ((Qv / 8 + 2) / 2) = Qv - Qv % 16 + 16 from by omega] at hv4 hv5
      obtain ⟨hb1, hb2⟩ := round_rne_add hX1 hX2 hR hQ4 hlo hhi hadd'
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) (Qv - Qv % 16 + 16) d k hSnn hd1 hd2 (by omega)).2.2 hb1 hb2
      refine ⟨?_, ?_⟩
      · change nextHalfSmallestFp64ToReal (unitResult tr t) < Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv5, hsqrtop]; exact g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) < nextHalfLargestFp64ToReal (unitResult tr t)
        rw [hv4, hsqrtop]; exact g2
    · have hadd' : ¬ (8 < Qv % 16 ∨ (Qv % 16 = 8 ∧ 0 ≤ Rv)) := by
        rw [← hrb, ← hRv]; exact hadd
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 := by
        have h := hRNE_orig (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hmode, hsq2, hadd⟩
        rw [h, hEB]
      obtain ⟨d, hd1, hd2, -, -, -, hv4, hv5⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * (Qv / 8 / 2) = Qv - Qv % 16 from by omega] at hv4 hv5
      obtain ⟨hb1, hb2⟩ := round_rne_orig hX1 hX2 hR hQ4 hlo hhi hadd'
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) (Qv - Qv % 16) d k hSnn hd1 hd2 (by omega)).2.2 hb1 hb2
      refine ⟨?_, ?_⟩
      · change nextHalfSmallestFp64ToReal (unitResult tr t) < Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv5, hsqrtop]; exact g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) < nextHalfLargestFp64ToReal (unitResult tr t)
        rw [hv4, hsqrtop]; exact g2
  · -- round to nearest, ties away from zero
    by_cases hadd : rndBits tr (t - 2) > 8 ∨ (rndBits tr (t - 2) = 8 ∧ RVal tr (t - 2) ≥ 0)
    · have hadd' : 8 < Qv % 16 ∨ (Qv % 16 = 8 ∧ 0 ≤ Rv) := by
        rw [hrb, hRv] at hadd; exact hadd
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 + 2 := by
        have h := hRMM_add1 (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hmode, hsq2, hadd⟩
        rw [show QAfterRnd tr (t - 2) = _ from by simpa only [h56, if_true] using h, hEB]
      obtain ⟨d, hd1, hd2, -, -, -, hv4, hv5⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * ((Qv / 8 + 2) / 2) = Qv - Qv % 16 + 16 from by omega] at hv4 hv5
      obtain ⟨hb1, hb2⟩ := round_rne_add hX1 hX2 hR hQ4 hlo hhi hadd'
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) (Qv - Qv % 16 + 16) d k hSnn hd1 hd2 (by omega)).2.2 hb1 hb2
      refine ⟨?_, ?_⟩
      · change nextHalfSmallestFp64ToReal (unitResult tr t) ≤ Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv5, hsqrtop]; exact le_of_lt g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) < nextHalfLargestFp64ToReal (unitResult tr t)
        rw [hv4, hsqrtop]; exact g2
    · have hadd' : ¬ (8 < Qv % 16 ∨ (Qv % 16 = 8 ∧ 0 ≤ Rv)) := by
        rw [← hrb, ← hRv]; exact hadd
      have hprop : QAfterRnd tr (t - 2) = Qv / 8 := by
        have h := hRMM_orig (t - 2) ⟨hEx3, hns2, by rw [hrm2]; exact hmode, hsq2, hadd⟩
        rw [h, hEB]
      obtain ⟨d, hd1, hd2, -, -, -, hv4, hv5⟩ := hvals _ hprop (by omega) (by omega)
      rw [show 16 * (Qv / 8 / 2) = Qv - Qv % 16 from by omega] at hv4 hv5
      obtain ⟨hb1, hb2⟩ := round_rne_orig hX1 hX2 hR hQ4 hlo hhi hadd'
      obtain ⟨g1, g2⟩ :=
        (sqrt_bracket (2 ^ 56 * X) (Qv - Qv % 16) d k hSnn hd1 hd2 (by omega)).2.2 hb1 hb2
      refine ⟨?_, ?_⟩
      · change nextHalfSmallestFp64ToReal (unitResult tr t) ≤ Real.sqrt (fp64ToReal (srcf0Q tr t))
        rw [hv5, hsqrtop]; exact le_of_lt g1
      · change Real.sqrt (fp64ToReal (srcf0Q tr t)) < nextHalfLargestFp64ToReal (unitResult tr t)
        rw [hv4, hsqrtop]; exact g2

end Proof
end Properties
end RTL
