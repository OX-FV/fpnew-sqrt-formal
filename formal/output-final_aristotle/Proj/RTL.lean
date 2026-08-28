import Mathlib

namespace RTL

inductive Signal where
  | rndModeQ
  | unitDone
  | unitResult
  | vfdsuDpFdivBusy
  | ctrlEx3Pipedown
  | ctrlEx4Pipedown
  | noSpecial
  | srcf0Q
  | QAfterRnd
  | Q_raw
  | QRnd
  | R_raw
  | QNext
  | RNext
  | j_val
  | first_stage
  | middle_stage
  | last_stage
  | packEx4OutResult
  | packVfdsuEx4Frac
  | q_val
  | flush_combined
  | sqrt64B

inductive RoundModes where
  | RNE
  | RTZ
  | RUP
  | RDN
  | RMM

def SignalVal : Signal → Type
  | .rndModeQ => RoundModes
  | .unitDone => Bool
  | .unitResult => BitVec 64
  | .vfdsuDpFdivBusy => Bool
  | .ctrlEx3Pipedown => Bool
  | .ctrlEx4Pipedown => Bool
  | .noSpecial => Bool
  | .srcf0Q => BitVec 64
  | .QAfterRnd => ℤ  -- signed 55-bit (logic signed [54:0])
  | .Q_raw => ℤ  -- signed 69-bit (logic signed [B+L-1:0], B=4, L=65)
  | .QRnd => ℤ  -- signed 69-bit
  | .R_raw => ℤ  -- signed 69-bit
  | .QNext => ℤ  -- signed 69-bit
  | .RNext => ℤ  -- signed 69-bit
  | .j_val => Nat  -- jNat assertion says we can treat j as a natural number
  | .first_stage => Bool
  | .middle_stage => Bool
  | .last_stage => Bool
  | .packEx4OutResult => BitVec 64
  | .packVfdsuEx4Frac => ℤ  -- signed 55-bit
  | .q_val => ℤ  -- signed 5-bit (logic signed [4:0])
  | .flush_combined => Bool
  | .sqrt64B => Bool

abbrev State := ∀ s : Signal, SignalVal s

end RTL
