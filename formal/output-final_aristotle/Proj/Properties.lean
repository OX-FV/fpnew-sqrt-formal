import Proj.RTL

namespace RTL
namespace Properties

def WE : Nat := 11
def WF : Nat := 52
def B : Nat := 4
def L : Nat := 65
def bias : Int := 1023

def getSignal (tr : Nat → State) (t : Nat) (s : Signal) : SignalVal s :=
  tr t s

def getBit (v : ℤ) (n : Nat) : Bool :=
  if (v / (2^n : ℤ)) % 2 = 0 then false else true

def extractBits (v : ℤ) (high low : Nat) : ℤ :=
  (v / (2^low : ℤ)) % (2^(high - low + 1) : ℤ)

def flush (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.flush_combined

def vfdsuDpFdivBusy (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.vfdsuDpFdivBusy

def unitDone (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.unitDone

def unitResult (tr : Nat → State) (t : Nat) : BitVec 64 :=
  getSignal tr t Signal.unitResult

def noSpecial (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.noSpecial

def sqrt64B (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.sqrt64B

def ctrlEx3Pipedown (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.ctrlEx3Pipedown

def ctrlEx4Pipedown (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.ctrlEx4Pipedown

def srcf0Q (tr : Nat → State) (t : Nat) : BitVec 64 :=
  getSignal tr t Signal.srcf0Q

def rmQ (tr : Nat → State) (t : Nat) : RoundModes :=
  getSignal tr t Signal.rndModeQ

def QAfterRnd (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.QAfterRnd

def Q (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.Q_raw

def QRnd (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.QRnd

def RVal (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.R_raw

def QNext (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.QNext

def RNext (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.RNext

def packEx4OutResult (tr : Nat → State) (t : Nat) : BitVec 64 :=
  getSignal tr t Signal.packEx4OutResult

def packVfdsuEx4Frac (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.packVfdsuEx4Frac

def jVal (tr : Nat → State) (t : Nat) : Nat :=
  getSignal tr t Signal.j_val

def clzVal (tr : Nat → State) (t : Nat) : Nat :=
  let expBits := (srcf0Q tr t).extractLsb (WE + WF - 1) WF
  if expBits = 0 then
    ((srcf0Q tr t).extractLsb (WF-1) 0).clz.toNat
  else
    0

def firstStage (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.first_stage

def middleStage (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.middle_stage

def lastStage (tr : Nat → State) (t : Nat) : Bool :=
  getSignal tr t Signal.last_stage

def qRndBits (tr : Nat → State) (t : Nat) : ℤ :=
  let q := QRnd tr t
  if getBit q 56 then
    extractBits q 3 0
  else
    extractBits q 2 0 * 2

def qVal (tr : Nat → State) (t : Nat) : ℤ :=
  getSignal tr t Signal.q_val

def q2Val (tr : Nat → State) (t : Nat) : ℤ :=
  (qVal tr t)^2

def qScaled (tr : Nat → State) (t : Nat) : ℤ :=
  let j := jVal tr t
  let q := qVal tr t
  if (0 ≤ j ∧ j ≤ 13) then q * 2 ^ (54-4*j) else 0

def q2Scaled (tr : Nat → State) (t : Nat) : ℤ :=
  let j := jVal tr t
  let q2 := q2Val tr t
  if (0 ≤ j ∧ j ≤ 13) then q2 * 2 ^ (56-4*j) else 0

def XVal (tr : Nat → State) (t : Nat) : ℤ :=
  let operand := srcf0Q tr t
  let expnt := operand.extractLsb (WF + WE - 1) WF
  let frac := (operand.extractLsb (WF - 1) 0).toNat
  if expnt == 0 then
    -- Denormal case
    let clz := clzVal tr t
    if clz ≥ 52 then
      -- Default case (operand is ±0 or all zero fraction)
      0b000000000001000000000000000000000000000000000000000000000000000000000
    else
      -- Reconstruct the exact concatenated bit pattern based on clz parity
      let fracCutoff := (WF - 1 - clz)
      let fracBits := extractBits frac fracCutoff 0
      let rightZeros := if clz % 2 == 0 then (L : ℤ) + (clz : ℤ) - 7 - (WF : ℤ)
                        else (L : ℤ) + (clz : ℤ) - 8 - (WF : ℤ)
      -- Left-shift the extracted fraction bits over the lower trailing zeros
      fracBits * (2 ^ rightZeros.toNat)
  else
    -- Normal case
    if (operand.getLsb 52) then
      -- X = {{B+8{1'b0}}, 1'b1, srcf0_q[WF-1:0], {L-9-WF{1'b0}}}
      let val := 2^WF + frac
      val * (2 ^ (L - 9 - WF))
    else
      -- X = {{B+7{1'b0}}, 1'b1, srcf0_q[WF-1:0], {L-8-WF{1'b0}}}
      let val := 2^WF + frac
      val * (2 ^ (L - 8 - WF))

---------------------
-- SVA starts here --
---------------------

def OpStable (tr : Nat → State) : Prop :=
  ∀ t, vfdsuDpFdivBusy tr t = true →
    srcf0Q tr (t + 1) = srcf0Q tr t ∧ rmQ tr (t + 1) = rmQ tr t ∧ XVal tr (t+1) = XVal tr t

def Sqrt64BStable (tr : Nat → State) : Prop :=
  ∀ t, vfdsuDpFdivBusy tr t = true → sqrt64B tr (t + 1) = sqrt64B tr t

def ResultEqPack (tr : Nat → State) : Prop :=
  ∀ t, unitResult tr t = packEx4OutResult tr t

def Ex4UnitDone (tr : Nat → State) : Prop :=
  ∀ t,
    (unitDone tr t = true) ↔
      (t > 0 ∧ (flush tr (t - 1) = false ∧ ctrlEx4Pipedown tr (t - 1) = true))

def Ex4ResStable (tr : Nat → State) : Prop :=
  ∀ t,
   (unitDone tr t = true →
    (t > 0 ∧ packEx4OutResult tr t = packEx4OutResult tr (t-1)))

def WasBusy (tr : Nat → State) : Prop :=
  ∀ t, unitDone tr t = true → (t > 0 ∧ vfdsuDpFdivBusy tr (t - 1) = true)

def NoSpecialStable (tr : Nat → State) : Prop :=
  ∀ t, srcf0Q tr (t + 1) = srcf0Q tr t →
    noSpecial tr (t + 1) = noSpecial tr t

def PackInp (tr : Nat → State) : Prop :=
  ∀ t, t > 0 → ctrlEx4Pipedown tr t = true →
    packVfdsuEx4Frac tr t = QAfterRnd tr (t - 1)

def PackMantissa (tr : Nat → State) : Prop :=
  ∀ t, ctrlEx4Pipedown tr t = true ∧ noSpecial tr t = true ∧ sqrt64B tr t = true →
    let frac := packVfdsuEx4Frac tr t
    let result := (packEx4OutResult tr t).toNat
    if getBit frac 54 then
      extractBits (result : ℤ) (WF - 1) 0 = extractBits frac 53 2
    else if getBit frac 53 then
      extractBits (result : ℤ) (WF - 1) 0 = extractBits frac 52 1
    else
      extractBits (result : ℤ) (WF - 1) 0 = extractBits frac 51 0

def biasedExpnt (tr : Nat → State) (t : Nat) : ℤ :=
  let expBits := (srcf0Q tr t).extractLsb (WE + WF - 1) WF
  expBits.toNat - (bias : ℤ) - (clzVal tr t : ℤ)

def halfExpnt (tr : Nat → State) (t : Nat) : ℤ :=
  let be := biasedExpnt tr t
  (be / 2) + (bias : ℤ)

def expectedExpnt (tr : Nat → State) (t : Nat) : ℤ :=
  let frac := packVfdsuEx4Frac tr t
  let he := halfExpnt tr t
  if getBit frac 54 then
    he + 1
  else if getBit frac 53 then
    he
  else
    he - 1

def PackExpnt (tr : Nat → State) : Prop :=
  ∀ t, ctrlEx4Pipedown tr t = true ∧ noSpecial tr t = true ∧ sqrt64B tr t = true →
    let result := (packEx4OutResult tr t).toNat
    extractBits (result : ℤ) (WF + WE - 1) WF = expectedExpnt tr t

def Ex3Ex4 (tr : Nat → State) : Prop :=
  ∀ t, ctrlEx4Pipedown tr t = true ↔
  (t > 0 ∧ flush tr (t - 1) = false ∧ ctrlEx3Pipedown tr (t - 1) = true)

def Ex3Ex4Stable (tr : Nat → State) : Prop :=
  ∀ t, t > 0 → ctrlEx4Pipedown tr t = true →
    rmQ tr (t - 1) = rmQ tr t ∧ srcf0Q tr (t - 1) = srcf0Q tr t

def rndBits (tr : Nat → State) (t : Nat) : ℤ :=
  qRndBits tr t

def RNE_add1 (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RNE ∧
    sqrt64B tr t = true ∧
    (rndBits tr t > 8 ∨ (rndBits tr t = 8 ∧ RVal tr t ≥ 0)) →
    let q := QRnd tr t
    if getBit q 56 then
      QAfterRnd tr t = extractBits q (B+L-1) 3 + 2
    else
      QAfterRnd tr t = extractBits q (B+L-1) 3 + 1

def RNE_orig (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RNE ∧
    sqrt64B tr t = true ∧
    ¬ (rndBits tr t > 8 ∨ (rndBits tr t = 8 ∧ RVal tr t ≥ 0)) →
    QAfterRnd tr t = extractBits (QRnd tr t) (B+L-1) 3

def RTZ_sub1 (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RTZ ∧
    sqrt64B tr t = true ∧
    rndBits tr t = 0 ∧ RVal tr t < 0 →
    let q := QRnd tr t
    if getBit q 56 then
      QAfterRnd tr t = extractBits q (B+L-1) 3 - 2
    else
      QAfterRnd tr t = extractBits q (B+L-1) 3 - 1

def RTZ_orig (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RTZ ∧
    sqrt64B tr t = true ∧
    ¬ (rndBits tr t = 0 ∧ RVal tr t < 0) →
    QAfterRnd tr t = extractBits (QRnd tr t) (B+L-1) 3

def RUP_add1 (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RUP ∧
    sqrt64B tr t = true ∧
    (rndBits tr t ≠ 0 ∨ RVal tr t > 0) →
    let q := QRnd tr t
    if getBit q 56 then
      QAfterRnd tr t = extractBits q (B+L-1) 3 + 2
    else
      QAfterRnd tr t = extractBits q (B+L-1) 3 + 1

def RUP_orig (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RUP ∧
    sqrt64B tr t = true ∧
    ¬ (rndBits tr t ≠ 0 ∨ RVal tr t > 0) →
    QAfterRnd tr t = extractBits (QRnd tr t) (B+L-1) 3

def RDN_sub1 (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RDN ∧
    sqrt64B tr t = true ∧
    rndBits tr t = 0 ∧ RVal tr t < 0 →
    let q := QRnd tr t
    if getBit q 56 then
      QAfterRnd tr t = extractBits q (B+L-1) 3 - 2
    else
      QAfterRnd tr t = extractBits q (B+L-1) 3 - 1

def RDN_orig (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RDN ∧
    sqrt64B tr t = true ∧
    ¬ (rndBits tr t = 0 ∧ RVal tr t < 0) →
    QAfterRnd tr t = extractBits (QRnd tr t) (B+L-1) 3

def RMM_add1 (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RMM ∧
    sqrt64B tr t = true ∧
    (rndBits tr t > 8 ∨ (rndBits tr t = 8 ∧ RVal tr t ≥ 0)) →
    let q := QRnd tr t
    if getBit q 56 then
      QAfterRnd tr t = extractBits q (B+L-1) 3 + 2
    else
      QAfterRnd tr t = extractBits q (B+L-1) 3 + 1

def RMM_orig (tr : Nat → State) : Prop :=
  ∀ t,
    ctrlEx3Pipedown tr t = true ∧
    noSpecial tr t = true ∧
    rmQ tr t = RoundModes.RMM ∧
    sqrt64B tr t = true ∧
    ¬ (rndBits tr t > 8 ∨ (rndBits tr t = 8 ∧ RVal tr t ≥ 0)) →
    QAfterRnd tr t = extractBits (QRnd tr t) (B+L-1) 3

def BaseCase (tr : Nat → State) : Prop :=
  ∀ t, (firstStage tr t = true ∨ middleStage tr t = true ∨ lastStage tr t = true) ∧
      jVal tr t = 0 →
    firstStage tr t = true

def Q_initial (tr : Nat → State) : Prop :=
  ∀ t, firstStage tr t = true → Q tr t = 0

def R_initial (tr : Nat → State) : Prop :=
  ∀ t, firstStage tr t = true ∧ sqrt64B tr t = true → RVal tr t = XVal tr t

def J_initial (tr : Nat → State) : Prop :=
  ∀ t, firstStage tr t = true → jVal tr t = 0

def J_next (tr : Nat → State) : Prop :=
  ∀ t, (middleStage tr t = true ∨ lastStage tr t = true) ∧ sqrt64B tr t = true →
    jVal tr t = 1 + jVal tr (t - 1) ∧ jVal tr t ≠ 0

def R_next_eq (tr : Nat → State) : Prop :=
  ∀ t, (middleStage tr t = true ∨ lastStage tr t = true) ∧ sqrt64B tr t = true →
    RVal tr t = RNext tr (t - 1)

def Q_next_eq (tr : Nat → State) : Prop :=
  ∀ t, (middleStage tr t = true ∨ lastStage tr t = true) ∧ sqrt64B tr t = true →
    Q tr t = QNext tr (t - 1)

def TimeConsistency (tr : Nat → State) : Prop :=
  ∀ t, (middleStage tr t = true ∨ lastStage tr t = true) ∧ sqrt64B tr t = true →
    (t > 0 ∧ (firstStage tr (t - 1) = true ∨ middleStage tr (t - 1) = true))

def SrtBusy (tr : Nat → State) : Prop :=
  ∀ t, firstStage tr t = true ∨ middleStage tr t = true ∨ lastStage tr t = true →
    vfdsuDpFdivBusy tr t = true

def Q_recur (tr : Nat → State) : Prop :=
  ∀ t, (firstStage tr t = true ∨ middleStage tr t = true) ∧ sqrt64B tr t = true →
    QNext tr t = Q tr t + qScaled tr t

def R_recur (tr : Nat → State) : Prop :=
  ∀ t, (firstStage tr t = true ∨ middleStage tr t = true) ∧ sqrt64B tr t = true →
    RNext tr t = 16 * RVal tr t - (Q tr t)*(qVal tr t)*8 - q2Scaled tr t

def QRndIneq (tr : Nat → State) : Prop :=
  ∀ t, ctrlEx3Pipedown tr t = true ∧ noSpecial tr t = true ∧ sqrt64B tr t = true →
    let r := RVal tr t
    let q := QRnd tr t
    9 - 6 * q ≤ r ∧ r ≤ 9 + 6 * q

def DefOfLast (tr : Nat → State) : Prop :=
  ∀ t, lastStage tr t = true ↔ ctrlEx3Pipedown tr t = true

def QEquals (tr : Nat → State) : Prop :=
  ∀ t, QRnd tr t = Q tr t

def StopEarly (tr : Nat → State) : Prop :=
  ∀ t, (ctrlEx3Pipedown tr t = true ∧ noSpecial tr t = true ∧ sqrt64B tr t = true ∧
      jVal tr t ≠ 14) →
    RVal tr t = 0

def ResNoDenorm (tr : Nat → State) : Prop :=
  ∀ t,
  let expntBits := (unitResult tr t).extractLsb (WF+WE-1) WF
  (unitDone tr t = true ∧ noSpecial tr t = true ∧ sqrt64B tr t = true) → expntBits ≠ 0

def jBound (tr : Nat → State) : Prop :=
  ∀ t, firstStage tr t = true ∨ middleStage tr t = true → jVal tr t ≤ 13

def OpNonZero (tr : Nat → State) : Prop :=
  ∀ t, noSpecial tr t = true → (srcf0Q tr t).extractLsb 62 0 ≠ 0

-------------------
-- SVA ends here --
-------------------

def ValidTrace (tr : Nat → State) : Prop :=
  OpStable tr ∧ ResultEqPack tr ∧
  Ex4UnitDone tr ∧ Ex4ResStable tr ∧ WasBusy tr ∧ NoSpecialStable tr ∧
  PackMantissa tr ∧ PackExpnt tr ∧ PackInp tr ∧
  Ex3Ex4 tr ∧ Ex3Ex4Stable tr ∧
  RNE_add1 tr ∧ RNE_orig tr ∧ RTZ_sub1 tr ∧ RTZ_orig tr ∧
  RUP_add1 tr ∧ RUP_orig tr ∧ RDN_sub1 tr ∧ RDN_orig tr ∧
  RMM_add1 tr ∧ RMM_orig tr ∧
  BaseCase tr ∧ Q_initial tr ∧ R_initial tr ∧ J_initial tr ∧
  J_next tr ∧ R_next_eq tr ∧ Q_next_eq tr ∧ TimeConsistency tr ∧ SrtBusy tr ∧
  Q_recur tr ∧ R_recur tr ∧ DefOfLast tr ∧ QEquals tr ∧
  QRndIneq tr ∧ StopEarly tr ∧ ResNoDenorm tr ∧ jBound tr ∧ OpNonZero tr ∧
  Sqrt64BStable tr

/-- Accessors for the conjuncts of `ValidTrace`. -/
theorem ValidTrace.opStable {tr : Nat → State} (h : ValidTrace tr) : OpStable tr := h.1
theorem ValidTrace.resultEqPack {tr : Nat → State} (h : ValidTrace tr) : ResultEqPack tr := h.2.1
theorem ValidTrace.ex4UnitDone {tr : Nat → State} (h : ValidTrace tr) : Ex4UnitDone tr := h.2.2.1
theorem ValidTrace.ex4ResStable {tr : Nat → State} (h : ValidTrace tr) : Ex4ResStable tr :=
  h.2.2.2.1
theorem ValidTrace.wasBusy {tr : Nat → State} (h : ValidTrace tr) : WasBusy tr := h.2.2.2.2.1
theorem ValidTrace.noSpecialStable {tr : Nat → State} (h : ValidTrace tr) : NoSpecialStable tr :=
  h.2.2.2.2.2.1
theorem ValidTrace.packMantissa {tr : Nat → State} (h : ValidTrace tr) : PackMantissa tr :=
  h.2.2.2.2.2.2.1
theorem ValidTrace.packExpnt {tr : Nat → State} (h : ValidTrace tr) : PackExpnt tr :=
  h.2.2.2.2.2.2.2.1
theorem ValidTrace.packInp {tr : Nat → State} (h : ValidTrace tr) : PackInp tr :=
  h.2.2.2.2.2.2.2.2.1
theorem ValidTrace.ex3Ex4 {tr : Nat → State} (h : ValidTrace tr) : Ex3Ex4 tr :=
  h.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.ex3Ex4Stable {tr : Nat → State} (h : ValidTrace tr) : Ex3Ex4Stable tr :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rne_add1 {tr : Nat → State} (h : ValidTrace tr) : RNE_add1 tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rne_orig {tr : Nat → State} (h : ValidTrace tr) : RNE_orig tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rtz_sub1 {tr : Nat → State} (h : ValidTrace tr) : RTZ_sub1 tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rtz_orig {tr : Nat → State} (h : ValidTrace tr) : RTZ_orig tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rup_add1 {tr : Nat → State} (h : ValidTrace tr) : RUP_add1 tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rup_orig {tr : Nat → State} (h : ValidTrace tr) : RUP_orig tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rdn_sub1 {tr : Nat → State} (h : ValidTrace tr) : RDN_sub1 tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rdn_orig {tr : Nat → State} (h : ValidTrace tr) : RDN_orig tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rmm_add1 {tr : Nat → State} (h : ValidTrace tr) : RMM_add1 tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.rmm_orig {tr : Nat → State} (h : ValidTrace tr) : RMM_orig tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.baseCase {tr : Nat → State} (h : ValidTrace tr) : BaseCase tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.q_initial {tr : Nat → State} (h : ValidTrace tr) : Q_initial tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.r_initial {tr : Nat → State} (h : ValidTrace tr) : R_initial tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.j_initial {tr : Nat → State} (h : ValidTrace tr) : J_initial tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.j_next {tr : Nat → State} (h : ValidTrace tr) : J_next tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.r_next_eq {tr : Nat → State} (h : ValidTrace tr) : R_next_eq tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.q_next_eq {tr : Nat → State} (h : ValidTrace tr) : Q_next_eq tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.timeConsistency {tr : Nat → State} (h : ValidTrace tr) : TimeConsistency tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.srtBusy {tr : Nat → State} (h : ValidTrace tr) : SrtBusy tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.q_recur {tr : Nat → State} (h : ValidTrace tr) : Q_recur tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.r_recur {tr : Nat → State} (h : ValidTrace tr) : R_recur tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.defOfLast {tr : Nat → State} (h : ValidTrace tr) : DefOfLast tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.qEquals {tr : Nat → State} (h : ValidTrace tr) : QEquals tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.qRndIneq {tr : Nat → State} (h : ValidTrace tr) : QRndIneq tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.stopEarly {tr : Nat → State} (h : ValidTrace tr) : StopEarly tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.resNoDenorm {tr : Nat → State} (h : ValidTrace tr) : ResNoDenorm tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.jBound {tr : Nat → State} (h : ValidTrace tr) : jBound tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.opNonZero {tr : Nat → State} (h : ValidTrace tr) : OpNonZero tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ValidTrace.sqrt64BStable {tr : Nat → State} (h : ValidTrace tr) : Sqrt64BStable tr :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Properties
end RTL
