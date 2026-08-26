/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortScatteringChain
public import Physlib.Optics.Systems.Microring.Observables

/-!
# Source bridges for microring transfer formulas

## i. Overview

This file records the parameter and port dictionaries needed to compare Physlib's explicit
microring networks with DATE'14, SysCon'15, and SFG-TR'14. The source statements are catalogued at
`HOL-CORPUS.md:188-208`, `HOL-CORPUS.md:226-274`, and `HOL-CORPUS.md:323-337` in the parity audit
checkout. The DATE parameters are `(r, t, L_c, alpha, lambda, n_eff)`. SysCon's drop model uses
`(phi, x_r, k1, k2, u1, u2)`, and SFG-TR uses `(xi, S1, S2, C1, C2)`.

SysCon Def. 9 has the same two half arcs and the same `-I * k` cross phase as Physlib
(`HOL-CORPUS.md:244-247` and
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`). Its bridge therefore changes only
names and port order. DATE's forward field has the opposite reference-plane sign from Physlib's
through field; that sign is represented by `dateThroughGauge`. SFG-TR's complex square root is
principal, while Physlib stores a selected half-arc factor. Its bridge consequently states their
equality as an explicit hypothesis.

The source writes rejection ratios as `10 log` without an audited logarithm base
(`HOL-CORPUS.md:246-249`). Results below keep the base as data, then separately identify the
base-ten and natural-log readings. No unverified base is silently selected.

Exact parity with SysCon Thm. 6 is withheld. The corpus survey records that theorem only as a
closed form and transcribes no expression (`HOL-CORPUS.md:248`). A previously recorded
transcription of uncertain provenance instead used the denominator
`(1-u1*u2*x_r)^2 + 4*k1*k2*exp(-phi)*sin(phi/2)^2`. At the exact rational fixture
`u1=u2=4/5`, `k1=k2=3/5`, `x_r=9/16`, and `phi=pi`,
`sourceBridgeRegression_disputedDenominator_ne_amplitudeDenominator` proves that this candidate is
`256/625 + (36/25)*exp(-pi)`, whereas the norm-square denominator is `1156/625`. No
available source reading classifies the discrepancy as a paper error, script error, or
transcription error.

The amplitude-derived denominator is proved here from Thm. 5 and yields Thm. 7's power ratio when
evaluated according to Def. 11. Agreement of those two independently transcribed source results is
evidence for that denominator, not a classification of the unverified Thm. 6 statement.

## ii. Key results

- `dateForwardTransfer_eq_gauged_throughTransfer`: DATE's `R` and the Physlib through field.
- `dateBackwardTransfer_eq_dropTransfer`: DATE's `T` and the Physlib drop field.
- `dateTwoPortBehavior_iff_matrix`: DATE Def. 3 implies DATE Thm. 1 in its source order.
- `dateTwoPortChainMatrix_eq_gauged_n7Chain`: DATE Thm. 1 and the typed N7 chain view.
- `dateFourPortChainMatrix_eq_n5Response`: DATE Thm. 2 and the proof-gated N5 response.
- `sysConDropTransfer_eq_dropTransfer`: the SysCon drop formula and the S2 amplitude.
- `sysConDropTransfer_eq_n5Response`: the source formula and the proof-gated N5 response entry.
- `sysConDropPower_eq_n5ResponsePower`: Def. 10 and squared norm of that N5 response entry.
- `sysConDropPower_eq_amplitudePowerDenominator`: Def. 10 derived from Thm. 5.
- `sysConRejectionRatioInBase_eq_closedForm`: Def. 11 and Thm. 7 for an explicit log base.
- `sysConRejectionClosedForm_base_ten`: the base-ten interpretation of SysCon Thm. 7.
- `sfgAddDropTransfer_eq_dropTransfer`: SFG-TR Thm. 7 under its square-root branch map.

## iii. Table of contents

- A. DATE'14 parameter and reference-plane dictionary
- B. DATE'14 transfer fields and four-port formula container
- C. SysCon'15 drop response and power
- D. Log-base-explicit rejection ratios
- E. SFG-TR'14 parameter, port, and square-root dictionary

## iv. References and non-claims

DATE'14 Def. 3 and Thms. 1--2 are summarized at `HOL-CORPUS.md:194-198`. SysCon Defs. 9--11 and
Thms. 5--7 are summarized at `HOL-CORPUS.md:244-249`. SFG-TR Def. 35 and Thm. 7 are summarized at
`HOL-CORPUS.md:332-336`.

The source predicates store their transfer formulas; this file does not recast them as component
derivations. It also does not assert that every source record maps to N7-valid components. Physical
response meaning on the Physlib side remains gated by N5 well-posedness and N7 validity. No
reciprocity, omitted-loss completeness, time-domain causality, bandwidth, dispersion, or
measurement-validation claim is made. The DATE cascade, lattice, termination, and Sylvester
results are not bridged here. SysCon contains no formal through-response result
(`HOL-CORPUS.md:251-269`).

`dateTwoPortChainMatrix` and `dateFourPortBackwardFirstChainMatrix` are totalized quotient-valued
objects. Their chain meanings are asserted only under the respective nonzero pivot gates `t != 0`
and `R != 0`; the four-port N5 bridge also requires the ring solve denominator to be nonzero.
Likewise, `sysConDropResponseSeries` is a total Mathlib `tsum`; it has feedback-series or N5
response meaning only under `SysConParameters.IsContractive` and the stated attenuation gate.
The DATE and SysCon transfer quotients and their norm-square powers are also totalized at zero
denominator. Their algebraic identities remain meaningful there, but an N5 response claim requires
the displayed nonzero-denominator or contraction gate. Exact printed-Thm.-6 parity and the source's
unaudited logarithm base are not claimed.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringSourceBridge

/-! ## A. DATE'14 parameter and reference-plane dictionary -/

/-- The six real DATE'14 microring parameters from `HOL-CORPUS.md:194-196`. -/
structure DateParameters where
  /-- The source reflectivity amplitude `r` (`HOL-CORPUS.md:194-196`). -/
  reflectivity : ℝ
  /-- The source transmissivity amplitude `t` (`HOL-CORPUS.md:194-196`). -/
  transmissivity : ℝ
  /-- The source coupling or cavity length `L_c` (`HOL-CORPUS.md:194-196`). -/
  couplingLength : ℝ
  /-- The source power-attenuation coefficient `alpha` (`HOL-CORPUS.md:194-196`). -/
  powerAttenuation : ℝ
  /-- The source wavelength `lambda` (`HOL-CORPUS.md:194-196`). -/
  wavelength : ℝ
  /-- The source effective index `n_eff` (`HOL-CORPUS.md:194-196`). -/
  effectiveIndex : ℝ

/-- DATE's phase `delta = (2*pi/lambda)*n_eff*L_c` from `HOL-CORPUS.md:196`. -/
def DateParameters.roundTripPhase (p : DateParameters) : ℝ :=
  (2 * Real.pi / p.wavelength) * p.effectiveIndex * p.couplingLength

/-- DATE's field factor `tau = exp(-alpha*L_c/2)` from `HOL-CORPUS.md:196`.

The source calls `alpha` a power-attenuation coefficient, but `tau` itself multiplies fields.
-/
def DateParameters.fieldAttenuation (p : DateParameters) : ℝ :=
  Real.exp (-p.powerAttenuation * p.couplingLength / 2)

/-- DATE's `exp(-j*delta)` written in Physlib's fixed-carrier phase convention
(`HOL-CORPUS.md:196` and `Physlib/Optics/Components/MatchedPropagation.lean:93-99`). -/
def DateParameters.phaseFactor (p : DateParameters) : ℂ :=
  MatchedPropagation.carrierPhaseFactor
    ((p.roundTripPhase : ℝ) : Real.Angle)

/-- DATE's `exp(-j*delta/2)` at the symmetric half-arc reference plane
(`HOL-CORPUS.md:196`, `Physlib/Optics/Systems/Microring/AddDropNetwork.lean:117-122`). -/
def DateParameters.halfPhaseFactor (p : DateParameters) : ℂ :=
  MatchedPropagation.carrierPhaseFactor
    (((p.roundTripPhase / 2 : ℝ)) : Real.Angle)

/-- The DATE amplitudes as an N7 coupler: source `r` is same-arm and source `t` is cross-arm.

This identification follows DATE Def. 3 and Thm. 1 at `HOL-CORPUS.md:196-198`; the N7 cross
coefficient remains the explicit `-I * t` of
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`.
-/
def DateParameters.coupler (p : DateParameters) : DirectionalCoupler.Parameters where
  throughAmplitude := p.reflectivity
  crossAmplitude := p.transmissivity

/-- The ideal DATE amplitude normalization needed by the N7 unitary-coupler model. -/
def DateParameters.IsUnitary (p : DateParameters) : Prop :=
  p.reflectivity ^ 2 + p.transmissivity ^ 2 = 1

/-- DATE's scalar two-sided coupler scattering matrix, adapted from the N7 arm mixer.

The source incident order `(a,d)` and outgoing order `(b,c)` used before DATE Thm. 1 are the two
coordinates of the N7 mixer; see `HOL-CORPUS.md:196-197` and
`Physlib/Optics/Components/DirectionalCoupler.lean:72-77`. This definition only wraps those
coordinates with Physlib's endpoint types; it is not the full four-physical-port scattering view.
-/
def DateParameters.couplerScatteringMatrix (p : DateParameters) :
    ScatteringMatrix (Unit ⊕ Unit) where
  toModeTransform := DirectionalCoupler.mixing p.coupler Unit

/-- The endpoint-typed form of DATE's N7-backed scalar coupler scattering matrix. -/
def DateParameters.couplerScattering (p : DateParameters) :
    TwoPortScatteringTransform Unit Unit :=
  p.couplerScatteringMatrix.toTwoPortScatteringTransform

/-- The left-reflection entry is DATE's reflectivity amplitude. -/
@[simp]
lemma DateParameters.couplerScattering_leftReflection (p : DateParameters) :
    p.couplerScattering.leftReflection
        (BackwardWave.mk ()) (ForwardWave.mk ()) = p.reflectivity := by
  simp [DateParameters.couplerScattering, DateParameters.couplerScatteringMatrix,
    DateParameters.coupler, DirectionalCoupler.mixing]

/-- The right-to-left transmission entry is the N7 coefficient `-I*t`. -/
@[simp]
lemma DateParameters.couplerScattering_rightToLeftTransmission (p : DateParameters) :
    p.couplerScattering.rightToLeftTransmission
        (BackwardWave.mk ()) (BackwardWave.mk ()) =
      -Complex.I * p.transmissivity := by
  simp [DateParameters.couplerScattering, DateParameters.couplerScatteringMatrix,
    DateParameters.coupler, DirectionalCoupler.mixing,
    DirectionalCoupler.crossCoefficient]

/-- The left-to-right transmission entry is the same N7 coefficient `-I*t`. -/
@[simp]
lemma DateParameters.couplerScattering_leftToRightTransmission (p : DateParameters) :
    p.couplerScattering.leftToRightTransmission
        (ForwardWave.mk ()) (ForwardWave.mk ()) =
      -Complex.I * p.transmissivity := by
  simp [DateParameters.couplerScattering, DateParameters.couplerScatteringMatrix,
    DateParameters.coupler, DirectionalCoupler.mixing,
    DirectionalCoupler.crossCoefficient]

/-- The right-reflection entry is DATE's reflectivity amplitude. -/
@[simp]
lemma DateParameters.couplerScattering_rightReflection (p : DateParameters) :
    p.couplerScattering.rightReflection
        (ForwardWave.mk ()) (BackwardWave.mk ()) = p.reflectivity := by
  simp [DateParameters.couplerScattering, DateParameters.couplerScatteringMatrix,
    DateParameters.coupler, DirectionalCoupler.mixing]

/-- A constant scalar amplitude used to expose one-channel source coordinates. -/
def sourceScalarAmplitude {ι : Type*} (value : ℂ) : ModeAmplitude ι :=
  WithLp.toLp 2 fun _ => value

/-- The DATE right-to-left transmission block acts by the N7 cross coefficient. -/
lemma DateParameters.couplerScattering_rightToLeftTransmission_action
    (p : DateParameters) (amplitude : ModeAmplitude (BackwardWave Unit)) :
    p.couplerScattering.rightToLeftTransmission.toLinearMap amplitude =
      sourceScalarAmplitude
        ((-Complex.I * p.transmissivity) * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, sourceScalarAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [DateParameters.couplerScattering, DateParameters.couplerScatteringMatrix,
    DateParameters.coupler, DirectionalCoupler.mixing,
    DirectionalCoupler.crossCoefficient]

/-- DATE's nonzero `t` gate makes the N7 transmission pivot bijective. -/
lemma DateParameters.couplerScattering_hasBijectiveRightToLeftTransmission
    (p : DateParameters) (hTransmissivity : p.transmissivity ≠ 0) :
    p.couplerScattering.HasBijectiveRightToLeftTransmission := by
  have hCoefficient : (-Complex.I * (p.transmissivity : ℂ)) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hTransmissivity)
  constructor
  · intro first second hEqual
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    rw [p.couplerScattering_rightToLeftTransmission_action,
      p.couplerScattering_rightToLeftTransmission_action] at hCoordinate
    exact mul_left_cancel₀ hCoefficient hCoordinate
  · intro output
    refine ⟨sourceScalarAmplitude
      ((-Complex.I * p.transmissivity)⁻¹ * output (BackwardWave.mk ())), ?_⟩
    rw [p.couplerScattering_rightToLeftTransmission_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    simp only [sourceScalarAmplitude]
    rw [← mul_assoc, mul_inv_cancel₀ hCoefficient, one_mul]

/-- The totalized explicit inverse of DATE's scalar N7 transmission pivot.

It is asserted to be an actual inverse only under the source gate `t != 0`.
-/
def DateParameters.couplerTransmissionInverse (p : DateParameters) :
    ModeTransform (BackwardWave Unit) (BackwardWave Unit) :=
  fun _ _ => Complex.I / p.transmissivity

/-- Under `t != 0`, the explicit scalar matrix is a right inverse of the N7 pivot. -/
lemma DateParameters.couplerTransmission_mul_explicitInverse (p : DateParameters)
    (hTransmissivity : p.transmissivity ≠ 0) :
    p.couplerScattering.rightToLeftTransmission * p.couplerTransmissionInverse = 1 := by
  ext ⟨⟨⟩⟩ ⟨⟨⟩⟩
  rw [Matrix.mul_apply, ← BackwardWave.channelEquiv.symm.sum_comp]
  simp [DateParameters.couplerTransmissionInverse,
    DateParameters.couplerScattering, DateParameters.couplerScatteringMatrix,
    DateParameters.coupler, DirectionalCoupler.mixing,
    DirectionalCoupler.crossCoefficient]
  have hTransmissivityComplex : (p.transmissivity : ℂ) ≠ 0 := by
    exact_mod_cast hTransmissivity
  field_simp
  rw [Complex.I_sq]
  ring

/-- The proof-selected pivot inverse is the explicit scalar inverse `I/t`. -/
lemma DateParameters.couplerTransmissionInverse_eq (p : DateParameters)
    (hTransmissivity : p.transmissivity ≠ 0) :
    p.couplerScattering.rightToLeftTransmissionInverse
        (p.couplerScattering_hasBijectiveRightToLeftTransmission hTransmissivity) =
      p.couplerTransmissionInverse := by
  let inverse := p.couplerScattering.rightToLeftTransmissionInverse
    (p.couplerScattering_hasBijectiveRightToLeftTransmission hTransmissivity)
  calc
    inverse = inverse * 1 := (Matrix.mul_one inverse).symm
    _ = inverse *
        (p.couplerScattering.rightToLeftTransmission *
          p.couplerTransmissionInverse) := by
      rw [p.couplerTransmission_mul_explicitInverse hTransmissivity]
    _ = (inverse * p.couplerScattering.rightToLeftTransmission) *
        p.couplerTransmissionInverse := (Matrix.mul_assoc _ _ _).symm
    _ = p.couplerTransmissionInverse := by
      rw [TwoPortScatteringTransform.inverse_mul_rightToLeftTransmission,
        Matrix.one_mul]

/-- The backward-first N7 chain matrix before the DATE sign gauge. -/
def dateN7CouplerChainMatrix (p : DateParameters) :
    BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => -1 / (Complex.I * p.transmissivity)
  | Sum.inl _, Sum.inr _ => p.reflectivity / (Complex.I * p.transmissivity)
  | Sum.inr _, Sum.inl _ => -p.reflectivity / (Complex.I * p.transmissivity)
  | Sum.inr _, Sum.inr _ => 1 / (Complex.I * p.transmissivity)

/-- The typed chain conversion of the N7 mixer yields its explicit backward-first matrix. -/
lemma dateN7CouplerChainTransform_eq (p : DateParameters)
    (hUnitary : p.IsUnitary) (hTransmissivity : p.transmissivity ≠ 0) :
    p.couplerScattering.toBackwardFirstChainTransform
        (p.couplerScattering_hasBijectiveRightToLeftTransmission hTransmissivity) =
      dateN7CouplerChainMatrix p := by
  rw [TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [p.couplerTransmissionInverse_eq hTransmissivity]
  have hUnitaryComplex :
      (p.reflectivity : ℂ) ^ 2 + (p.transmissivity : ℂ) ^ 2 = 1 := by
    exact_mod_cast hUnitary
  have hTransmissivityComplex : (p.transmissivity : ℂ) ≠ 0 := by
    exact_mod_cast hTransmissivity
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp [Matrix.mul_apply, DateParameters.couplerTransmissionInverse,
      dateN7CouplerChainMatrix, DateParameters.couplerScattering,
      DateParameters.couplerScatteringMatrix, DateParameters.coupler,
      DirectionalCoupler.mixing, DirectionalCoupler.crossCoefficient,
      ← BackwardWave.channelEquiv.symm.sum_comp] <;>
    field_simp [hTransmissivityComplex]
  all_goals try simp [Complex.I_sq]
  all_goals rw [show (p.transmissivity : ℂ) ^ 2 =
      1 - (p.reflectivity : ℂ) ^ 2 by linear_combination hUnitaryComplex]
  all_goals ring

/-- The diagonal sign gauge on DATE's second chain coordinate. -/
def dateChainGauge : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => -1

/-- DATE Thm. 1's two-port chain matrix in source order `(a,b) -> (c,d)`
(`HOL-CORPUS.md:197`). -/
def dateTwoPortChainMatrix (p : DateParameters) : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => -1 / (Complex.I * p.transmissivity)
  | Sum.inl _, Sum.inr _ => -p.reflectivity / (Complex.I * p.transmissivity)
  | Sum.inr _, Sum.inl _ => p.reflectivity / (Complex.I * p.transmissivity)
  | Sum.inr _, Sum.inr _ => 1 / (Complex.I * p.transmissivity)

/-- DATE's two-port field tuple in source order `(a,b,c,d)` (`HOL-CORPUS.md:196-197`). -/
structure DateTwoPortFields where
  /-- Source first input coordinate `a`. -/
  input : ℂ
  /-- Source second input coordinate `b`. -/
  backwardInput : ℂ
  /-- Source first output coordinate `c`. -/
  output : ℂ
  /-- Source second output coordinate `d`. -/
  forwardOutput : ℂ

/-- DATE Def. 3's two-port equations in the source order `(a,b) -> (c,d)`
(`HOL-CORPUS.md:196-197`). -/
def dateTwoPortBehavior (p : DateParameters) (f : DateTwoPortFields) : Prop :=
  f.output = -(1 / (Complex.I * p.transmissivity)) *
      (f.input + p.reflectivity * f.backwardInput) ∧
    f.forwardOutput = 1 / (Complex.I * p.transmissivity) *
      (p.reflectivity * f.input + f.backwardInput)

/-- DATE's two-port source input vector has typed order `(a,b)`. -/
def dateTwoPortInputVector (f : DateTwoPortFields) :
    BackwardWave Unit ⊕ ForwardWave Unit → ℂ
  | Sum.inl _ => f.input
  | Sum.inr _ => f.backwardInput

/-- DATE's two-port source output vector has typed order `(c,d)`. -/
def dateTwoPortOutputVector (f : DateTwoPortFields) :
    BackwardWave Unit ⊕ ForwardWave Unit → ℂ
  | Sum.inl _ => f.output
  | Sum.inr _ => f.forwardOutput

/-- DATE Def. 3's two-port equations are exactly its Thm. 1 matrix action. -/
theorem dateTwoPortBehavior_iff_matrix (p : DateParameters) (f : DateTwoPortFields) :
    dateTwoPortBehavior p f ↔
      dateTwoPortOutputVector f =
        Matrix.mulVec (dateTwoPortChainMatrix p) (dateTwoPortInputVector f) := by
  constructor
  · rintro ⟨hOutput, hForward⟩
    funext i
    rcases i with i | i <;> rcases i with ⟨⟨⟩⟩
    · simp [dateTwoPortOutputVector, dateTwoPortChainMatrix,
        dateTwoPortInputVector, Matrix.mulVec, dotProduct, div_eq_mul_inv,
        ← BackwardWave.channelEquiv.symm.sum_comp,
      ← ForwardWave.channelEquiv.symm.sum_comp]
      rw [hOutput]
      simp [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
      ring
    · simp [dateTwoPortOutputVector, dateTwoPortChainMatrix,
        dateTwoPortInputVector, Matrix.mulVec, dotProduct, div_eq_mul_inv,
        ← BackwardWave.channelEquiv.symm.sum_comp,
      ← ForwardWave.channelEquiv.symm.sum_comp]
      rw [hForward]
      simp [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
      ring
  · intro hMatrix
    constructor
    · have hOutput := congrFun hMatrix (Sum.inl (BackwardWave.mk ()))
      simp [dateTwoPortOutputVector, dateTwoPortChainMatrix,
        dateTwoPortInputVector, Matrix.mulVec, dotProduct, div_eq_mul_inv,
        ← BackwardWave.channelEquiv.symm.sum_comp,
        ← ForwardWave.channelEquiv.symm.sum_comp] at hOutput
      rw [hOutput]
      simp [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
      ring
    · have hForward := congrFun hMatrix (Sum.inr (ForwardWave.mk ()))
      simp [dateTwoPortOutputVector, dateTwoPortChainMatrix,
        dateTwoPortInputVector, Matrix.mulVec, dotProduct, div_eq_mul_inv,
        ← BackwardWave.channelEquiv.symm.sum_comp,
        ← ForwardWave.channelEquiv.symm.sum_comp] at hForward
      rw [hForward]
      simp [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
      ring

/-- DATE's source matrix is the N7 chain matrix with the explicit second-coordinate gauge. -/
lemma dateTwoPortChainMatrix_eq_gauged_explicitN7 (p : DateParameters) :
    dateTwoPortChainMatrix p =
      dateChainGauge * dateN7CouplerChainMatrix p * dateChainGauge := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp [Matrix.mul_apply, dateChainGauge, dateN7CouplerChainMatrix,
      dateTwoPortChainMatrix, ← BackwardWave.channelEquiv.symm.sum_comp] <;>
    ring

/-- DATE Thm. 1 is the typed chain conversion of the N7 arm mixer, up to its stated sign gauge. -/
theorem dateTwoPortChainMatrix_eq_gauged_n7Chain (p : DateParameters)
    (hUnitary : p.IsUnitary) (hTransmissivity : p.transmissivity ≠ 0) :
    dateTwoPortChainMatrix p =
      dateChainGauge *
          p.couplerScattering.toBackwardFirstChainTransform
            (p.couplerScattering_hasBijectiveRightToLeftTransmission hTransmissivity) *
        dateChainGauge := by
  rw [dateN7CouplerChainTransform_eq p hUnitary hTransmissivity]
  exact dateTwoPortChainMatrix_eq_gauged_explicitN7 p

/-- The DATE parameters mapped to Physlib's symmetric-coupler add-drop ring.

The source factor `tau` becomes one complete-round-trip field attenuation, and `delta` becomes the
real round-trip phase lift; see `HOL-CORPUS.md:194-198` and
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:117-122`, `:161-170`.
-/
def DateParameters.toAddDrop (p : DateParameters) : AddDrop.Parameters where
  inputThroughAmplitude := p.reflectivity
  inputCrossAmplitude := p.transmissivity
  dropThroughAmplitude := p.reflectivity
  dropCrossAmplitude := p.transmissivity
  fieldAttenuation := p.fieldAttenuation
  roundTripPhase := p.roundTripPhase

/-- The DATE dictionary uses the same N7 coupler at both ring junctions. -/
lemma DateParameters.toAddDrop_dropCoupler_eq_inputCoupler (p : DateParameters) :
    p.toAddDrop.dropCoupler = p.toAddDrop.inputCoupler := rfl

/-- The DATE dictionary uses the same N7 propagation law on both half arcs. -/
lemma DateParameters.toAddDrop_secondArcCoefficient_eq_firstArcCoefficient
    (p : DateParameters) :
    p.toAddDrop.secondArcCoefficient = p.toAddDrop.firstArcCoefficient := rfl

/-- The DATE-to-Physlib dictionary preserves all four coupler amplitudes and the two ring data. -/
lemma DateParameters.toAddDrop_data (p : DateParameters) :
    p.toAddDrop.inputThroughAmplitude = p.reflectivity ∧
      p.toAddDrop.inputCrossAmplitude = p.transmissivity ∧
      p.toAddDrop.dropThroughAmplitude = p.reflectivity ∧
      p.toAddDrop.dropCrossAmplitude = p.transmissivity ∧
      p.toAddDrop.fieldAttenuation = p.fieldAttenuation ∧
      p.toAddDrop.roundTripPhase = p.roundTripPhase :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The DATE field attenuation is strictly positive. -/
lemma DateParameters.fieldAttenuation_pos (p : DateParameters) :
    0 < p.fieldAttenuation := by
  exact Real.exp_pos _

/-- DATE normalization is exactly unitarity of the mapped input N7 coupler. -/
lemma DateParameters.inputCoupler_isUnitary {p : DateParameters} (hp : p.IsUnitary) :
    p.toAddDrop.inputCoupler.IsUnitary := by
  exact hp

/-- DATE normalization is exactly unitarity of the mapped drop N7 coupler. -/
lemma DateParameters.dropCoupler_isUnitary {p : DateParameters} (hp : p.IsUnitary) :
    p.toAddDrop.dropCoupler.IsUnitary := by
  exact hp

/-- The DATE through-output reference plane differs from Physlib by a sign.

DATE's `R` has the leading minus sign shown at `HOL-CORPUS.md:196`; the drop field `T` does not
receive this adapter.
-/
def dateThroughGauge (amplitude : ℂ) : ℂ :=
  -amplitude

/-- The DATE add-input reference plane carries the matching sign used by its four-port ordering
`(c,a) -> (d,b)` at `HOL-CORPUS.md:198`. -/
def dateAddGauge (amplitude : ℂ) : ℂ :=
  -amplitude

/-- The input and drop fields use the identity reference-plane map in the DATE dictionary. -/
def dateIdentityGauge (amplitude : ℂ) : ℂ :=
  amplitude

/-! ## B. DATE'14 transfer fields and four-port formula container -/

/-- DATE's common four-port denominator `1-r^2*tau*exp(-j*delta)`
(`HOL-CORPUS.md:196`). -/
def DateParameters.denominator (p : DateParameters) : ℂ :=
  1 - (p.reflectivity : ℂ) ^ 2 * (p.fieldAttenuation : ℂ) * p.phaseFactor

/-- The exact nonzero-denominator gate omitted by DATE's displayed quotient. -/
def DateParameters.HasNonzeroDenominator (p : DateParameters) : Prop :=
  p.denominator ≠ 0

/-- DATE's forward field `R` from Def. 3 (`HOL-CORPUS.md:196`). -/
def dateForwardTransfer (p : DateParameters) : ℂ :=
  -((p.reflectivity : ℂ) *
      (1 - (p.fieldAttenuation : ℂ) * p.phaseFactor)) / p.denominator

/-- DATE's backward field `T` from Def. 3 (`HOL-CORPUS.md:196`). -/
def dateBackwardTransfer (p : DateParameters) : ℂ :=
  -((p.transmissivity : ℂ) ^ 2 * Real.sqrt p.fieldAttenuation *
      p.halfPhaseFactor) / p.denominator

/-- The mapped Physlib round-trip coefficient is DATE's `tau*exp(-j*delta)`. -/
lemma DateParameters.toAddDrop_roundTripCoefficient (p : DateParameters) :
    p.toAddDrop.roundTripCoefficient =
      (p.fieldAttenuation : ℂ) * p.phaseFactor := by
  exact p.toAddDrop.roundTripCoefficient_eq_fieldAttenuation
    p.fieldAttenuation_pos.le

/-- The mapped first half arc is DATE's `sqrt(tau)*exp(-j*delta/2)`. -/
lemma DateParameters.toAddDrop_firstArcCoefficient (p : DateParameters) :
    p.toAddDrop.firstArcCoefficient =
      (Real.sqrt p.fieldAttenuation : ℂ) * p.halfPhaseFactor := by
  rfl

/-- The DATE denominator is exactly the mapped Physlib feedback denominator. -/
lemma DateParameters.toAddDrop_denominator (p : DateParameters) :
    p.toAddDrop.denominator = p.denominator := by
  rw [AddDrop.Parameters.denominator, AddDrop.Parameters.loopGain,
    p.toAddDrop_roundTripCoefficient]
  simp only [DateParameters.toAddDrop, DateParameters.denominator]
  ring

/-- DATE's solve gate is exactly the mapped Physlib N5 solve gate. -/
lemma DateParameters.hasNonzeroDenominator_iff (p : DateParameters) :
    p.HasNonzeroDenominator ↔ p.toAddDrop.HasNonzeroDenominator := by
  rw [DateParameters.HasNonzeroDenominator, AddDrop.Parameters.HasNonzeroDenominator,
    p.toAddDrop_denominator]

/-- DATE's forward field is the sign-gauged Physlib through amplitude. -/
theorem dateForwardTransfer_eq_gauged_throughTransfer (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator) :
    dateForwardTransfer p = dateThroughGauge (AddDrop.throughTransfer p.toAddDrop) := by
  rw [AddDrop.throughTransfer_eq_standard p.toAddDrop
    (p.inputCoupler_isUnitary hUnitary)
    ((p.hasNonzeroDenominator_iff).mp hDenominator)]
  rw [dateForwardTransfer, dateThroughGauge, AddDrop.standardThroughTransfer,
    p.toAddDrop_denominator, p.toAddDrop_roundTripCoefficient]
  simp only [DateParameters.toAddDrop]
  ring

/-- DATE's backward field is the Physlib drop amplitude in the stated identity gauge. -/
theorem dateBackwardTransfer_eq_dropTransfer (p : DateParameters) :
    dateBackwardTransfer p = dateIdentityGauge (AddDrop.dropTransfer p.toAddDrop) := by
  rw [AddDrop.dropTransfer_eq_standard, dateBackwardTransfer, dateIdentityGauge,
    AddDrop.standardDropTransfer, p.toAddDrop_denominator,
    p.toAddDrop_firstArcCoefficient]
  simp only [DateParameters.toAddDrop]
  ring

/-- DATE's forward field is the sign-gauged, proof-gated N5 response entry. -/
theorem dateForwardTransfer_eq_n5Response (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator) :
    dateForwardTransfer p =
      dateThroughGauge
        ((AddDrop.netlist p.toAddDrop).responseTransform
          (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
            ((p.hasNonzeroDenominator_iff).mp hDenominator))
          (Outgoing.mk (AddDrop.throughChannel p.toAddDrop))
          (Incident.mk (AddDrop.inputChannel p.toAddDrop))) := by
  have hMapped := (p.hasNonzeroDenominator_iff).mp hDenominator
  have hResponse := AddDrop.responseTransform_entry_through_input p.toAddDrop hMapped
  rw [dateForwardTransfer_eq_gauged_throughTransfer p hUnitary hDenominator]
  exact congrArg dateThroughGauge hResponse.symm

/-- DATE's backward field is the proof-gated input-to-drop N5 response entry. -/
theorem dateBackwardTransfer_eq_n5Response (p : DateParameters)
    (hDenominator : p.HasNonzeroDenominator) :
    dateBackwardTransfer p =
      (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
          ((p.hasNonzeroDenominator_iff).mp hDenominator))
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)) := by
  have hMapped := (p.hasNonzeroDenominator_iff).mp hDenominator
  have hResponse := AddDrop.responseTransform_entry_drop_input p.toAddDrop hMapped
  rw [dateBackwardTransfer_eq_dropTransfer, dateIdentityGauge]
  exact hResponse.symm

/-- DATE's four-port field tuple in the source names of `HOL-CORPUS.md:196-198`. -/
structure DateFourPortFields where
  /-- Source input field `a`. -/
  input : ℂ
  /-- Source through field `b`. -/
  through : ℂ
  /-- Source drop field `c`. -/
  drop : ℂ
  /-- Source add field `d`. -/
  add : ℂ

/-- DATE Def. 3's four-port behavior equations (`HOL-CORPUS.md:196`). -/
def dateFourPortBehavior (p : DateParameters) (f : DateFourPortFields) : Prop :=
  f.add = f.drop / dateForwardTransfer p -
      dateBackwardTransfer p / dateForwardTransfer p * f.input ∧
    f.through = dateBackwardTransfer p / dateForwardTransfer p * f.drop +
      (dateForwardTransfer p ^ 2 - dateBackwardTransfer p ^ 2) /
        dateForwardTransfer p * f.input

/-- DATE Thm. 2's matrix in its pinned source order `(c,a) -> (d,b)`
(`HOL-CORPUS.md:198`). -/
def dateFourPortChainMatrix (p : DateParameters) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / dateForwardTransfer p,
      -dateBackwardTransfer p / dateForwardTransfer p;
    dateBackwardTransfer p / dateForwardTransfer p,
      (dateForwardTransfer p ^ 2 - dateBackwardTransfer p ^ 2) /
        dateForwardTransfer p]

/-- DATE's four-port input vector has source order `(c,a)` (`HOL-CORPUS.md:198`). -/
def dateFourPortInputVector (f : DateFourPortFields) : Fin 2 → ℂ :=
  ![f.drop, f.input]

/-- DATE's four-port output vector has source order `(d,b)` (`HOL-CORPUS.md:198`). -/
def dateFourPortOutputVector (f : DateFourPortFields) : Fin 2 → ℂ :=
  ![f.add, f.through]

/-- DATE Def. 3's four-port equations are exactly its Thm. 2 matrix action. -/
theorem dateFourPortBehavior_iff_matrix (p : DateParameters) (f : DateFourPortFields) :
    dateFourPortBehavior p f ↔
      dateFourPortOutputVector f =
        Matrix.mulVec (dateFourPortChainMatrix p) (dateFourPortInputVector f) := by
  constructor
  · rintro ⟨hAdd, hThrough⟩
    funext i
    fin_cases i
    · simpa [dateFourPortOutputVector, dateFourPortChainMatrix,
        dateFourPortInputVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        div_eq_mul_inv, sub_eq_add_neg, mul_comm] using hAdd
    · simpa [dateFourPortOutputVector, dateFourPortChainMatrix,
        dateFourPortInputVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        mul_comm] using hThrough
  · intro hMatrix
    constructor
    · simpa [dateFourPortOutputVector, dateFourPortChainMatrix,
        dateFourPortInputVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        div_eq_mul_inv, sub_eq_add_neg, mul_comm] using congrFun hMatrix (0 : Fin 2)
    · simpa [dateFourPortOutputVector, dateFourPortChainMatrix,
        dateFourPortInputVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        mul_comm] using congrFun hMatrix (1 : Fin 2)

/-- A coherent scalar excitation only at the DATE-mapped add port. -/
def dateAddAmplitude (p : DateParameters) (amplitude : ℂ) :
    ModeAmplitude (AddDrop.netlist p.toAddDrop).ExternalIncident :=
  PiLp.single 2 (Incident.mk (AddDrop.addChannel p.toAddDrop)) amplitude

/-- The add-only excitation vanishes at the input port. -/
@[simp]
lemma dateAddAmplitude_apply_input (p : DateParameters) (amplitude : ℂ) :
    dateAddAmplitude p amplitude
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)) = 0 := by
  rw [dateAddAmplitude]
  simp [Ne.symm (AddDrop.inputChannel_ne_addChannel p.toAddDrop)]

/-- The add-only excitation has its supplied value at the add port. -/
@[simp]
lemma dateAddAmplitude_apply_add (p : DateParameters) (amplitude : ℂ) :
    dateAddAmplitude p amplitude
        (Incident.mk (AddDrop.addChannel p.toAddDrop)) = amplitude := by
  simp [dateAddAmplitude]

/-- The reverse return coordinate obtained by solving the four N5 channel equations. -/
lemma dateAdd_inputCoupler_leftSecond_solution (p : DateParameters)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) (amplitude : ℂ)
    (incident : ModeAmplitude (AddDrop.netlist p.toAddDrop).IncidentIndex)
    (outgoing : ModeAmplitude (AddDrop.netlist p.toAddDrop).OutgoingIndex)
    (hScattering : outgoing =
      (AddDrop.netlist p.toAddDrop).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (AddDrop.netlist p.toAddDrop).connections.incidentAssembly outgoing
        (dateAddAmplitude p amplitude)) :
    incident (Incident.mk (AddDrop.inputCouplerChannel p.toAddDrop
        DirectionalCoupler.Port.leftSecond)) =
      p.toAddDrop.secondArcCoefficient *
          DirectionalCoupler.crossCoefficient p.toAddDrop.dropCoupler * amplitude /
        p.toAddDrop.denominator := by
  have hInput := congrArg (fun state => state (Incident.mk
    (AddDrop.inputCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [AddDrop.incidentAssembly_apply_input_leftFirst, dateAddAmplitude_apply_input] at hInput
  have hAdd := congrArg (fun state => state (Incident.mk
    (AddDrop.dropCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [AddDrop.incidentAssembly_apply_drop_leftFirst, dateAddAmplitude_apply_add] at hAdd
  have hFirst := congrArg (fun state => state (Incident.mk
    (AddDrop.firstArcChannel p.toAddDrop MatchedPropagation.Port.left))) hAssembly
  rw [AddDrop.incidentAssembly_apply_firstArc_left,
    AddDrop.scatteringEquation_inputCoupler_rightSecond _ _ _ hScattering, hInput,
    mul_zero, zero_add] at hFirst
  have hDropRing := congrArg (fun state => state (Incident.mk
    (AddDrop.dropCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [AddDrop.incidentAssembly_apply_dropCoupler_leftSecond,
    AddDrop.scatteringEquation_firstArc_right _ _ _ hScattering, hFirst] at hDropRing
  have hSecond := congrArg (fun state => state (Incident.mk
    (AddDrop.secondArcChannel p.toAddDrop MatchedPropagation.Port.left))) hAssembly
  rw [AddDrop.incidentAssembly_apply_secondArc_left,
    AddDrop.scatteringEquation_dropCoupler_rightSecond _ _ _ hScattering, hAdd,
    hDropRing] at hSecond
  have hReturn := congrArg (fun state => state (Incident.mk
    (AddDrop.inputCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [AddDrop.incidentAssembly_apply_inputCoupler_leftSecond,
    AddDrop.scatteringEquation_secondArc_right _ _ _ hScattering, hSecond] at hReturn
  have hLoop : p.toAddDrop.denominator * incident (Incident.mk
      (AddDrop.inputCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftSecond)) =
      p.toAddDrop.secondArcCoefficient *
        DirectionalCoupler.crossCoefficient p.toAddDrop.dropCoupler * amplitude := by
    rw [AddDrop.Parameters.denominator, AddDrop.Parameters.loopGain,
      AddDrop.Parameters.roundTripCoefficient]
    linear_combination hReturn
  apply (eq_div_iff hDenominator).2
  rw [mul_comm, hLoop]

/-- The add-to-through N5 response is the symmetric DATE drop transfer. -/
lemma dateResponse_through_add (p : DateParameters)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) (amplitude : ℂ) :
    ((AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)).toLinearMap
        (dateAddAmplitude p amplitude)
        (Outgoing.mk (AddDrop.throughChannel p.toAddDrop)) =
      AddDrop.dropTransfer p.toAddDrop * amplitude := by
  let hWellPosed := AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator
  let output := (AddDrop.netlist p.toAddDrop).responseTransform hWellPosed |>.toLinearMap
    (dateAddAmplitude p amplitude)
  have hMember : (dateAddAmplitude p amplitude, output) ∈
      (AddDrop.netlist p.toAddDrop).behavior := by
    rw [← (AddDrop.netlist p.toAddDrop).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((AddDrop.netlist p.toAddDrop).mem_behavior_iff_equations _ _).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (AddDrop.netlist p.toAddDrop).connections.incidentAssembly outgoing
        (dateAddAmplitude p amplitude) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hInput := congrArg (fun state => state (Incident.mk
    (AddDrop.inputCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftFirst))) hAssembly'
  rw [AddDrop.incidentAssembly_apply_input_leftFirst, dateAddAmplitude_apply_input] at hInput
  have hReturn := dateAdd_inputCoupler_leftSecond_solution p hDenominator amplitude
    incident outgoing hScattering hAssembly'
  have hThrough := AddDrop.scatteringEquation_inputCoupler_rightFirst
    p.toAddDrop incident outgoing hScattering
  rw [hInput, mul_zero, zero_add] at hThrough
  have hReadout := congrArg
    (fun state => state (Outgoing.mk (AddDrop.throughChannel p.toAddDrop))) hOutput
  rw [AddDrop.outputReadout_apply_through] at hReadout
  change ((AddDrop.netlist p.toAddDrop).responseTransform hWellPosed).toLinearMap
      (dateAddAmplitude p amplitude)
        (Outgoing.mk (AddDrop.throughChannel p.toAddDrop)) = _
  rw [show hWellPosed =
      AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator from
      Subsingleton.elim _ _, hReadout, hThrough, hReturn, AddDrop.dropTransfer]
  rw [p.toAddDrop_secondArcCoefficient_eq_firstArcCoefficient]
  ring

/-- The drop-port component coordinate obtained from the add-only N5 channel equations. -/
lemma dateAdd_dropCoupler_rightFirst_solution (p : DateParameters)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) (amplitude : ℂ)
    (incident : ModeAmplitude (AddDrop.netlist p.toAddDrop).IncidentIndex)
    (outgoing : ModeAmplitude (AddDrop.netlist p.toAddDrop).OutgoingIndex)
    (hScattering : outgoing =
      (AddDrop.netlist p.toAddDrop).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (AddDrop.netlist p.toAddDrop).connections.incidentAssembly outgoing
        (dateAddAmplitude p amplitude)) :
    outgoing (Outgoing.mk (AddDrop.dropCouplerChannel p.toAddDrop
        DirectionalCoupler.Port.rightFirst)) =
      AddDrop.throughTransfer p.toAddDrop * amplitude := by
  have hAdd := congrArg (fun state => state (Incident.mk
    (AddDrop.dropCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [AddDrop.incidentAssembly_apply_drop_leftFirst, dateAddAmplitude_apply_add] at hAdd
  have hInput := congrArg (fun state => state (Incident.mk
    (AddDrop.inputCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [AddDrop.incidentAssembly_apply_input_leftFirst, dateAddAmplitude_apply_input] at hInput
  have hReturn := dateAdd_inputCoupler_leftSecond_solution p hDenominator amplitude
    incident outgoing hScattering hAssembly
  have hFirst := congrArg (fun state => state (Incident.mk
    (AddDrop.firstArcChannel p.toAddDrop MatchedPropagation.Port.left))) hAssembly
  rw [AddDrop.incidentAssembly_apply_firstArc_left,
    AddDrop.scatteringEquation_inputCoupler_rightSecond _ _ _ hScattering, hInput,
    mul_zero, zero_add, hReturn] at hFirst
  have hDropRing := congrArg (fun state => state (Incident.mk
    (AddDrop.dropCouplerChannel p.toAddDrop DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [AddDrop.incidentAssembly_apply_dropCoupler_leftSecond,
    AddDrop.scatteringEquation_firstArc_right _ _ _ hScattering, hFirst] at hDropRing
  have hDrop := AddDrop.scatteringEquation_dropCoupler_rightFirst
    p.toAddDrop incident outgoing hScattering
  rw [hAdd, hDropRing] at hDrop
  rw [hDrop, AddDrop.throughTransfer, AddDrop.Parameters.roundTripCoefficient]
  rw [p.toAddDrop_dropCoupler_eq_inputCoupler,
    p.toAddDrop_secondArcCoefficient_eq_firstArcCoefficient]
  simp only [DateParameters.toAddDrop]
  ring

/-- The add-to-drop N5 response is the symmetric DATE through transfer. -/
lemma dateResponse_drop_add (p : DateParameters)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) (amplitude : ℂ) :
    ((AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)).toLinearMap
        (dateAddAmplitude p amplitude)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop)) =
      AddDrop.throughTransfer p.toAddDrop * amplitude := by
  let hWellPosed := AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator
  let output := (AddDrop.netlist p.toAddDrop).responseTransform hWellPosed |>.toLinearMap
    (dateAddAmplitude p amplitude)
  have hMember : (dateAddAmplitude p amplitude, output) ∈
      (AddDrop.netlist p.toAddDrop).behavior := by
    rw [← (AddDrop.netlist p.toAddDrop).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((AddDrop.netlist p.toAddDrop).mem_behavior_iff_equations _ _).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (AddDrop.netlist p.toAddDrop).connections.incidentAssembly outgoing
        (dateAddAmplitude p amplitude) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hDrop := dateAdd_dropCoupler_rightFirst_solution p hDenominator amplitude
    incident outgoing hScattering hAssembly'
  have hReadout := congrArg
    (fun state => state (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))) hOutput
  rw [AddDrop.outputReadout_apply_drop] at hReadout
  change ((AddDrop.netlist p.toAddDrop).responseTransform hWellPosed).toLinearMap
      (dateAddAmplitude p amplitude)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop)) = _
  rw [show hWellPosed =
      AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator from
      Subsingleton.elim _ _, hReadout, hDrop]

/-- The N5 add-to-through response-matrix entry is the DATE drop transfer. -/
lemma dateResponseTransform_entry_through_add (p : DateParameters)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) :
    (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
        (Outgoing.mk (AddDrop.throughChannel p.toAddDrop))
        (Incident.mk (AddDrop.addChannel p.toAddDrop)) =
      AddDrop.dropTransfer p.toAddDrop := by
  have hResponse := dateResponse_through_add p hDenominator 1
  simpa [dateAddAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The N5 add-to-drop response-matrix entry is the DATE through transfer. -/
lemma dateResponseTransform_entry_drop_add (p : DateParameters)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) :
    (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.addChannel p.toAddDrop)) =
      AddDrop.throughTransfer p.toAddDrop := by
  have hResponse := dateResponse_drop_add p hDenominator 1
  simpa [dateAddAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The DATE-ordered two-sided scattering matrix extracted from the proof-gated N5 response.

Rows are source `(c,b)` and columns are source `(a,d)`. The `b` output and `d` input use
`dateThroughGauge` and `dateAddGauge`; hence the lower-right entry receives both signs.
-/
def dateN5FourPortScattering (p : DateParameters)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) :
    TwoPortScatteringTransform Unit Unit
  | Sum.inl _, Sum.inl _ =>
      (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop))
  | Sum.inl _, Sum.inr _ => dateAddGauge
      ((AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.addChannel p.toAddDrop)))
  | Sum.inr _, Sum.inl _ => dateThroughGauge
      ((AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
        (Outgoing.mk (AddDrop.throughChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)))
  | Sum.inr _, Sum.inr _ => dateThroughGauge (dateAddGauge
      ((AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
        (Outgoing.mk (AddDrop.throughChannel p.toAddDrop))
        (Incident.mk (AddDrop.addChannel p.toAddDrop))))

/-- DATE Def. 3's four-port scattering matrix in rows `(c,b)` and columns `(a,d)`. -/
def dateSourceFourPortScattering (p : DateParameters) :
    TwoPortScatteringTransform Unit Unit
  | Sum.inl _, Sum.inl _ => dateBackwardTransfer p
  | Sum.inl _, Sum.inr _ => dateForwardTransfer p
  | Sum.inr _, Sum.inl _ => dateForwardTransfer p
  | Sum.inr _, Sum.inr _ => dateBackwardTransfer p

/-- The DATE-ordered matrix extracted from N5 is exactly the source scattering form. -/
theorem dateN5FourPortScattering_eq_source (p : DateParameters)
    (hUnitary : p.IsUnitary)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator) :
    dateN5FourPortScattering p hDenominator =
      dateSourceFourPortScattering p := by
  have hSource := (p.hasNonzeroDenominator_iff).mpr hDenominator
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩
  · change (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)) = dateBackwardTransfer p
    rw [AddDrop.responseTransform_entry_drop_input p.toAddDrop hDenominator]
    simpa [dateIdentityGauge] using (dateBackwardTransfer_eq_dropTransfer p).symm
  · change dateAddGauge
        ((AddDrop.netlist p.toAddDrop).responseTransform
          (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
          (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
          (Incident.mk (AddDrop.addChannel p.toAddDrop))) = dateForwardTransfer p
    rw [dateResponseTransform_entry_drop_add p hDenominator]
    simpa [dateAddGauge, dateThroughGauge] using
      (dateForwardTransfer_eq_gauged_throughTransfer p hUnitary hSource).symm
  · change dateThroughGauge
        ((AddDrop.netlist p.toAddDrop).responseTransform
          (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
          (Outgoing.mk (AddDrop.throughChannel p.toAddDrop))
          (Incident.mk (AddDrop.inputChannel p.toAddDrop))) = dateForwardTransfer p
    rw [AddDrop.responseTransform_entry_through_input p.toAddDrop hDenominator]
    simpa using
      (dateForwardTransfer_eq_gauged_throughTransfer p hUnitary hSource).symm
  · change dateThroughGauge (dateAddGauge
        ((AddDrop.netlist p.toAddDrop).responseTransform
          (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop hDenominator)
          (Outgoing.mk (AddDrop.throughChannel p.toAddDrop))
          (Incident.mk (AddDrop.addChannel p.toAddDrop)))) = dateBackwardTransfer p
    rw [dateResponseTransform_entry_through_add p hDenominator]
    simpa [dateAddGauge, dateThroughGauge, dateIdentityGauge] using
      (dateBackwardTransfer_eq_dropTransfer p).symm

/-- The DATE four-port scattering pivot acts by multiplication by its forward field `R`. -/
lemma dateSourceFourPortScattering_rightToLeftTransmission_action
    (p : DateParameters) (amplitude : ModeAmplitude (BackwardWave Unit)) :
    (dateSourceFourPortScattering p).rightToLeftTransmission.toLinearMap amplitude =
      sourceScalarAmplitude
        (dateForwardTransfer p * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, sourceScalarAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [dateSourceFourPortScattering]

/-- A nonzero DATE forward field makes the four-port chain pivot bijective. -/
lemma dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission
    (p : DateParameters) (hForward : dateForwardTransfer p ≠ 0) :
    (dateSourceFourPortScattering p).HasBijectiveRightToLeftTransmission := by
  constructor
  · intro first second hEqual
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    rw [dateSourceFourPortScattering_rightToLeftTransmission_action,
      dateSourceFourPortScattering_rightToLeftTransmission_action] at hCoordinate
    exact mul_left_cancel₀ hForward hCoordinate
  · intro output
    refine ⟨sourceScalarAmplitude
      ((dateForwardTransfer p)⁻¹ * output (BackwardWave.mk ())), ?_⟩
    rw [dateSourceFourPortScattering_rightToLeftTransmission_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    simp only [sourceScalarAmplitude]
    rw [← mul_assoc, mul_inv_cancel₀ hForward, one_mul]

/-- The N5-extracted DATE scattering view inherits pivot bijectivity from nonzero `R`. -/
lemma dateN5FourPortScattering_hasBijectiveRightToLeftTransmission
    (p : DateParameters) (hUnitary : p.IsUnitary)
    (hDenominator : p.toAddDrop.HasNonzeroDenominator)
    (hForward : dateForwardTransfer p ≠ 0) :
    (dateN5FourPortScattering p hDenominator).HasBijectiveRightToLeftTransmission := by
  rw [dateN5FourPortScattering_eq_source p hUnitary hDenominator]
  exact dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission p hForward

/-- The totalized scalar candidate for the DATE four-port pivot inverse. -/
def dateFourPortTransmissionInverse (p : DateParameters) :
    ModeTransform (BackwardWave Unit) (BackwardWave Unit) :=
  fun _ _ => (dateForwardTransfer p)⁻¹

/-- At nonzero `R`, the explicit scalar matrix is a right inverse of the DATE pivot. -/
lemma dateFourPortTransmission_mul_explicitInverse (p : DateParameters)
    (hForward : dateForwardTransfer p ≠ 0) :
    (dateSourceFourPortScattering p).rightToLeftTransmission *
        dateFourPortTransmissionInverse p = 1 := by
  ext ⟨⟨⟩⟩ ⟨⟨⟩⟩
  rw [Matrix.mul_apply, ← BackwardWave.channelEquiv.symm.sum_comp]
  simp [dateSourceFourPortScattering, dateFourPortTransmissionInverse, hForward]

/-- The proof-selected DATE four-port pivot inverse equals the explicit reciprocal of `R`. -/
lemma dateFourPortTransmissionInverse_eq (p : DateParameters)
    (hForward : dateForwardTransfer p ≠ 0) :
    (dateSourceFourPortScattering p).rightToLeftTransmissionInverse
        (dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission p hForward) =
      dateFourPortTransmissionInverse p := by
  let inverse := (dateSourceFourPortScattering p).rightToLeftTransmissionInverse
    (dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission p hForward)
  calc
    inverse = inverse * 1 := (Matrix.mul_one inverse).symm
    _ = inverse * ((dateSourceFourPortScattering p).rightToLeftTransmission *
        dateFourPortTransmissionInverse p) := by
      rw [dateFourPortTransmission_mul_explicitInverse p hForward]
    _ = (inverse * (dateSourceFourPortScattering p).rightToLeftTransmission) *
        dateFourPortTransmissionInverse p := (Matrix.mul_assoc _ _ _).symm
    _ = dateFourPortTransmissionInverse p := by
      rw [TwoPortScatteringTransform.inverse_mul_rightToLeftTransmission,
        Matrix.one_mul]

/-- DATE Thm. 2's four-port matrix with backward-first endpoint types. -/
def dateFourPortBackwardFirstChainMatrix (p : DateParameters) :
    BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => 1 / dateForwardTransfer p
  | Sum.inl _, Sum.inr _ => -dateBackwardTransfer p / dateForwardTransfer p
  | Sum.inr _, Sum.inl _ => dateBackwardTransfer p / dateForwardTransfer p
  | Sum.inr _, Sum.inr _ =>
      (dateForwardTransfer p ^ 2 - dateBackwardTransfer p ^ 2) /
        dateForwardTransfer p

/-- DATE Thm. 2 is the N3T chain conversion of its four-port scattering matrix. -/
theorem dateSourceFourPortChainTransform_eq (p : DateParameters)
    (hForward : dateForwardTransfer p ≠ 0) :
    (dateSourceFourPortScattering p).toBackwardFirstChainTransform
        (dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission p hForward) =
      dateFourPortBackwardFirstChainMatrix p := by
  rw [TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [dateFourPortTransmissionInverse_eq p hForward]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp [Matrix.mul_apply, dateSourceFourPortScattering,
      dateFourPortTransmissionInverse, dateFourPortBackwardFirstChainMatrix,
      ← BackwardWave.channelEquiv.symm.sum_comp] <;>
    field_simp

/-- DATE Thm. 2 is the chain conversion of the stated gauge/port view of the N5 response. -/
theorem dateFourPortChainMatrix_eq_n5Response (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hForward : dateForwardTransfer p ≠ 0) :
    (dateN5FourPortScattering p
      ((p.hasNonzeroDenominator_iff).mp hDenominator)).toBackwardFirstChainTransform
        (dateN5FourPortScattering_hasBijectiveRightToLeftTransmission p hUnitary
          ((p.hasNonzeroDenominator_iff).mp hDenominator) hForward) =
      dateFourPortBackwardFirstChainMatrix p := by
  have hScattering := dateN5FourPortScattering_eq_source p hUnitary
    ((p.hasNonzeroDenominator_iff).mp hDenominator)
  calc
    _ = (dateSourceFourPortScattering p).toBackwardFirstChainTransform
        (dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission p hForward) := by
      apply ModeTransform.toBehavior_injective
      rw [TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform,
        TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform,
        hScattering]
    _ = dateFourPortBackwardFirstChainMatrix p :=
      dateSourceFourPortChainTransform_eq p hForward

/-! ## C. SysCon'15 drop response and power -/

/-- The six real SysCon'15 drop-response parameters from `HOL-CORPUS.md:244-249`. -/
structure SysConParameters where
  /-- Source round-trip phase `phi`. -/
  phase : ℝ
  /-- Source round-trip field attenuation `x_r`. -/
  fieldAttenuation : ℝ
  /-- Source first cross amplitude `k1`. -/
  inputCrossAmplitude : ℝ
  /-- Source second cross amplitude `k2`. -/
  dropCrossAmplitude : ℝ
  /-- Source first through amplitude `u1`. -/
  inputThroughAmplitude : ℝ
  /-- Source second through amplitude `u2`. -/
  dropThroughAmplitude : ℝ

/-- The SysCon dictionary into Physlib's add-drop parameters.

Def. 9 uses the same `sqrt(x_r)` per half arc, `phi/2` per half phase, and `-j*k` cross gauge;
see `HOL-CORPUS.md:244-247`.
-/
def SysConParameters.toAddDrop (p : SysConParameters) : AddDrop.Parameters where
  inputThroughAmplitude := p.inputThroughAmplitude
  inputCrossAmplitude := p.inputCrossAmplitude
  dropThroughAmplitude := p.dropThroughAmplitude
  dropCrossAmplitude := p.dropCrossAmplitude
  fieldAttenuation := p.fieldAttenuation
  roundTripPhase := p.phase

/-- The SysCon dictionary changes names only and preserves all six scalar values. -/
lemma SysConParameters.toAddDrop_data (p : SysConParameters) :
    p.toAddDrop.inputThroughAmplitude = p.inputThroughAmplitude ∧
      p.toAddDrop.inputCrossAmplitude = p.inputCrossAmplitude ∧
      p.toAddDrop.dropThroughAmplitude = p.dropThroughAmplitude ∧
      p.toAddDrop.dropCrossAmplitude = p.dropCrossAmplitude ∧
      p.toAddDrop.fieldAttenuation = p.fieldAttenuation ∧
      p.toAddDrop.roundTripPhase = p.phase :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- SysCon Def. 9's repeated half-arc factor `exp(-j*phi/2)*sqrt(x_r)`. -/
def SysConParameters.halfArcCoefficient (p : SysConParameters) : ℂ :=
  MatchedPropagation.carrierPhaseFactor (((p.phase / 2 : ℝ)) : Real.Angle) *
    Real.sqrt p.fieldAttenuation

/-- SysCon's real circulation magnitude before its unit-modulus phase factor. -/
def SysConParameters.realLoopGain (p : SysConParameters) : ℝ :=
  p.inputThroughAmplitude * p.dropThroughAmplitude * p.fieldAttenuation

/-- SysCon's complete circulation factor `u1*u2*exp(-j*phi)*x_r`. -/
def SysConParameters.loopGain (p : SysConParameters) : ℂ :=
  (p.inputThroughAmplitude : ℂ) * (p.dropThroughAmplitude : ℂ) *
    MatchedPropagation.carrierPhaseFactor ((p.phase : ℝ) : Real.Angle) *
      p.fieldAttenuation

/-- SysCon Thm. 5's source contraction hypothesis `norm(x_r*u1*u2) < 1`.

All three factors are real in Def. 9, so the scalar norm is the real absolute value.
-/
def SysConParameters.IsContractive (p : SysConParameters) : Prop :=
  |p.realLoopGain| < 1

/-- The source contraction gate is the complex geometric-series gate for the phased loop gain. -/
lemma SysConParameters.IsContractive.norm_loopGain_lt_one {p : SysConParameters}
    (hp : p.IsContractive) : ‖p.loopGain‖ < 1 := by
  rw [SysConParameters.IsContractive, SysConParameters.realLoopGain] at hp
  simpa [SysConParameters.loopGain, MatchedPropagation.carrierPhaseFactor,
    norm_mul, abs_mul, mul_comm, mul_left_comm, mul_assoc] using hp

/-- SysCon Thm. 5's displayed feedback denominator (`HOL-CORPUS.md:247`). -/
def SysConParameters.denominator (p : SysConParameters) : ℂ :=
  1 - p.loopGain

/-- The nonzero-denominator gate required to interpret the SysCon quotient as an N5 response. -/
def SysConParameters.HasNonzeroDenominator (p : SysConParameters) : Prop :=
  p.denominator ≠ 0

/-- SysCon Thm. 5's closed-form drop amplitude (`HOL-CORPUS.md:247`). -/
def sysConDropTransfer (p : SysConParameters) : ℂ :=
  -((p.inputCrossAmplitude : ℂ) * (p.dropCrossAmplitude : ℂ) *
      MatchedPropagation.carrierPhaseFactor (((p.phase / 2 : ℝ)) : Real.Angle) *
        Real.sqrt p.fieldAttenuation) / p.denominator

/-- SysCon Def. 9 expanded as its totalized multiple-circulation scalar series.

The object is a Mathlib `tsum` at every parameter value. It has the source feedback-series meaning
only under `SysConParameters.IsContractive`.
-/
def sysConDropResponseSeries (p : SysConParameters) : ℂ :=
  (-Complex.I * p.inputCrossAmplitude) * p.halfArcCoefficient *
    (∑' circulation : ℕ, p.loopGain ^ circulation) *
      (-Complex.I * p.dropCrossAmplitude)

/-- Under the exact source contraction gate, the Def. 9 series is summable. -/
lemma sysConDropResponseSeries_summable (p : SysConParameters)
    (hContractive : p.IsContractive) :
    Summable (fun circulation : ℕ => p.loopGain ^ circulation) :=
  summable_geometric_of_norm_lt_one hContractive.norm_loopGain_lt_one

/-- SysCon Thm. 5: the convergent Def. 9 series equals its displayed quotient. -/
theorem sysConDropResponseSeries_eq_transfer (p : SysConParameters)
    (_hAttenuation : 0 < p.fieldAttenuation) (hContractive : p.IsContractive) :
    sysConDropResponseSeries p = sysConDropTransfer p := by
  rw [sysConDropResponseSeries, sysConDropTransfer,
    tsum_geometric_of_norm_lt_one hContractive.norm_loopGain_lt_one]
  simp only [SysConParameters.halfArcCoefficient,
    SysConParameters.denominator]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Nonnegative `x_r` makes the mapped first arc exactly the SysCon half-arc factor. -/
lemma SysConParameters.toAddDrop_firstArcCoefficient (p : SysConParameters) :
    p.toAddDrop.firstArcCoefficient =
      (Real.sqrt p.fieldAttenuation : ℂ) *
        MatchedPropagation.carrierPhaseFactor (((p.phase / 2 : ℝ)) : Real.Angle) := by
  rfl

/-- Nonnegative `x_r` makes the mapped round trip exactly the SysCon loop field factor. -/
lemma SysConParameters.toAddDrop_roundTripCoefficient (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.roundTripCoefficient =
      (p.fieldAttenuation : ℂ) *
        MatchedPropagation.carrierPhaseFactor ((p.phase : ℝ) : Real.Angle) := by
  exact p.toAddDrop.roundTripCoefficient_eq_fieldAttenuation hAttenuation

/-- Under nonnegative `x_r`, the SysCon and Physlib feedback denominators coincide. -/
lemma SysConParameters.toAddDrop_denominator (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.denominator = p.denominator := by
  rw [AddDrop.Parameters.denominator, AddDrop.Parameters.loopGain,
    p.toAddDrop_roundTripCoefficient hAttenuation]
  simp only [SysConParameters.toAddDrop, SysConParameters.denominator,
    SysConParameters.loopGain]
  ring

/-- Under nonnegative attenuation, the mapped N5 loop gain is the SysCon phased loop gain. -/
lemma SysConParameters.toAddDrop_loopGain (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.loopGain = p.loopGain := by
  rw [AddDrop.Parameters.loopGain, p.toAddDrop_roundTripCoefficient hAttenuation]
  simp only [SysConParameters.toAddDrop, SysConParameters.loopGain]
  ring

/-- The exact SysCon source contraction gate implies the mapped S2 contraction gate. -/
lemma SysConParameters.IsContractive.toAddDrop {p : SysConParameters}
    (hContractive : p.IsContractive) (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.IsContractive := by
  rw [AddDrop.Parameters.IsContractive, p.toAddDrop_loopGain hAttenuation]
  exact hContractive.norm_loopGain_lt_one

/-- Under nonnegative `x_r`, the SysCon and Physlib solve gates coincide. -/
lemma SysConParameters.hasNonzeroDenominator_iff (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.HasNonzeroDenominator ↔ p.toAddDrop.HasNonzeroDenominator := by
  rw [SysConParameters.HasNonzeroDenominator, AddDrop.Parameters.HasNonzeroDenominator,
    p.toAddDrop_denominator hAttenuation]

/-- SysCon Thm. 5's closed form is exactly the S2 add-drop amplitude under the name dictionary. -/
theorem sysConDropTransfer_eq_dropTransfer (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropTransfer p = AddDrop.dropTransfer p.toAddDrop := by
  rw [AddDrop.dropTransfer_eq_standard, sysConDropTransfer,
    AddDrop.standardDropTransfer, p.toAddDrop_denominator hAttenuation,
    p.toAddDrop_firstArcCoefficient]
  simp only [SysConParameters.toAddDrop]
  ring

/-- SysCon Thm. 5's amplitude is the proof-gated N5 input-to-drop response entry. -/
theorem sysConDropTransfer_eq_n5Response (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) :
    sysConDropTransfer p =
      (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
          ((p.hasNonzeroDenominator_iff hAttenuation).mp hDenominator))
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)) := by
  have hMapped := (p.hasNonzeroDenominator_iff hAttenuation).mp hDenominator
  have hResponse := AddDrop.responseTransform_entry_drop_input p.toAddDrop hMapped
  rw [sysConDropTransfer_eq_dropTransfer p hAttenuation]
  exact hResponse.symm

/-- SysCon Def. 9 and Thm. 5 agree with the proof-gated N5 response on the source domain. -/
theorem sysConDropResponseSeries_eq_n5Response (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation) (hContractive : p.IsContractive) :
    sysConDropResponseSeries p =
      (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
          (hContractive.toAddDrop hAttenuation.le).hasNonzeroDenominator)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)) := by
  rw [sysConDropResponseSeries_eq_transfer p hAttenuation hContractive]
  have hMapped := (hContractive.toAddDrop hAttenuation.le).hasNonzeroDenominator
  have hSource := (p.hasNonzeroDenominator_iff hAttenuation.le).mpr hMapped
  exact sysConDropTransfer_eq_n5Response p hAttenuation.le hSource

/-- SysCon Def. 10's power is squared complex norm of its drop response
(`HOL-CORPUS.md:245`). -/
def sysConDropPower (p : SysConParameters) : ℝ :=
  Complex.normSq (sysConDropTransfer p)

/-- SysCon Def. 10 is the squared norm of the proof-gated N5 input-to-drop response entry. -/
theorem sysConDropPower_eq_n5ResponsePower (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) :
    sysConDropPower p =
      Complex.normSq
        ((AddDrop.netlist p.toAddDrop).responseTransform
          (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
            ((p.hasNonzeroDenominator_iff hAttenuation).mp hDenominator))
          (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
          (Incident.mk (AddDrop.inputChannel p.toAddDrop))) := by
  rw [sysConDropPower, sysConDropTransfer_eq_n5Response p hAttenuation hDenominator]

/-- SysCon Def. 10 is exactly Physlib's drop power under the parameter dictionary. -/
theorem sysConDropPower_eq_dropPower (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p = AddDrop.dropPower p.toAddDrop := by
  rw [sysConDropPower, AddDrop.dropPower,
    sysConDropTransfer_eq_dropTransfer p hAttenuation]

/-- The algebraically correct real closed form obtained from SysCon Thm. 5. -/
def sysConAnalyticDropPower (p : SysConParameters) : ℝ :=
  (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
    (1 + (p.inputThroughAmplitude * p.dropThroughAmplitude *
      p.fieldAttenuation) ^ 2 -
        2 * p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation * Real.cos p.phase)

/-- The power denominator obtained directly by norm-squaring SysCon Thm. 5. -/
def sysConAmplitudePowerDenominator (p : SysConParameters) : ℝ :=
  (1 - p.realLoopGain) ^ 2 +
    4 * p.realLoopGain * Real.sin (p.phase / 2) ^ 2

/-- A previously recorded Thm. 6 denominator whose provenance is presently uncertain.

`HOL-CORPUS.md:248` does not transcribe a Thm. 6 expression. This definition exists only to state
and test the discrepancy; it is not asserted to be the paper's or the HOL Light script's formula.
-/
def sysConDisputedPowerDenominator (p : SysConParameters) : ℝ :=
  (1 - p.realLoopGain) ^ 2 +
    4 * p.inputCrossAmplitude * p.dropCrossAmplitude * Real.exp (-p.phase) *
      Real.sin (p.phase / 2) ^ 2

/-- The quotient formed with the provenance-uncertain denominator candidate.

This totalized comparison object has no claimed source or physical-response meaning.
-/
def sysConDisputedDropPower (p : SysConParameters) : ℝ :=
  (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
    sysConDisputedPowerDenominator p

/-- The half-angle and cosine forms of the amplitude-derived denominator agree exactly. -/
lemma sysConAmplitudePowerDenominator_eq_cosineForm (p : SysConParameters) :
    sysConAmplitudePowerDenominator p =
      1 + p.realLoopGain ^ 2 - 2 * p.realLoopGain * Real.cos p.phase := by
  rw [show p.phase = 2 * (p.phase / 2) by ring, Real.cos_two_mul_eq_one_sub]
  rw [sysConAmplitudePowerDenominator]
  ring

/-- The SysCon amplitude has the analytic real power form on the nonnegative-attenuation domain. -/
theorem sysConDropPower_eq_analytic (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p = sysConAnalyticDropPower p := by
  rw [sysConDropPower_eq_dropPower p hAttenuation,
    AddDrop.dropPower_eq_closedForm p.toAddDrop hAttenuation]
  simp only [AddDrop.Parameters.dropPowerNumerator,
    AddDrop.Parameters.powerDenominator, SysConParameters.toAddDrop,
    sysConAnalyticDropPower]
  ring

/-- The norm-square power bridge can equivalently use the source-style half-angle denominator. -/
theorem sysConDropPower_eq_amplitudePowerDenominator (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p =
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
        sysConAmplitudePowerDenominator p := by
  rw [sysConDropPower_eq_analytic p hAttenuation, sysConAnalyticDropPower,
    sysConAmplitudePowerDenominator_eq_cosineForm]
  simp only [SysConParameters.realLoopGain]
  ring

/-! ## D. Log-base-explicit rejection ratios -/

/-- Ten times a logarithm in an explicit base, applied to a power ratio. -/
def powerRatioInBase (base numerator denominator : ℝ) : ℝ :=
  10 * Real.logb base (numerator / denominator)

/-- At base ten, the explicit-base convention is Physlib's power-ratio decibel convention. -/
lemma powerRatioInBase_ten (numerator denominator : ℝ) :
    powerRatioInBase 10 numerator denominator =
      AddDrop.powerRatioDB numerator denominator := rfl

/-- At base `exp(1)`, the explicit-base convention is ten times the natural logarithm. -/
lemma powerRatioInBase_exp_one (numerator denominator : ℝ) :
    powerRatioInBase (Real.exp 1) numerator denominator =
      10 * Real.log (numerator / denominator) := by
  rw [powerRatioInBase, Real.logb]
  simp

/-- SysCon Thm. 7's closed rejection-ratio argument with an explicit log base
(`HOL-CORPUS.md:246-249`). -/
def sysConRejectionClosedForm (base : ℝ) (p : SysConParameters) : ℝ :=
  10 * Real.logb base
    (((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
      p.fieldAttenuation) ^ 2) /
      ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
        p.fieldAttenuation) ^ 2))

/-- SysCon Def. 11's on-resonance point uses the printed phase `2*pi`. -/
def SysConParameters.atResonance (p : SysConParameters) : SysConParameters :=
  { p with phase := 2 * Real.pi }

/-- SysCon Def. 11's off-resonance point uses the printed phase `pi`. -/
def SysConParameters.atAntiresonance (p : SysConParameters) : SysConParameters :=
  { p with phase := Real.pi }

/-- SysCon Def. 11 with the previously unaudited logarithm base made explicit. -/
def sysConRejectionRatioInBase (base : ℝ) (p : SysConParameters) : ℝ :=
  powerRatioInBase base (sysConDropPower p.atResonance)
    (sysConDropPower p.atAntiresonance)

/-- The SysCon named resonance has the exact amplitude-derived drop power. -/
lemma sysConDropPower_atResonance (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p.atResonance =
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
        (1 - p.realLoopGain) ^ 2 := by
  rw [sysConDropPower_eq_analytic p.atResonance
    (by simpa [SysConParameters.atResonance] using hAttenuation)]
  simp [sysConAnalyticDropPower, SysConParameters.atResonance,
    SysConParameters.realLoopGain, Real.cos_two_pi]
  ring

/-- The SysCon named antiresonance has the exact amplitude-derived drop power. -/
lemma sysConDropPower_atAntiresonance (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p.atAntiresonance =
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
        (1 + p.realLoopGain) ^ 2 := by
  rw [sysConDropPower_eq_analytic p.atAntiresonance
    (by simpa [SysConParameters.atAntiresonance] using hAttenuation)]
  simp [sysConAnalyticDropPower, SysConParameters.atAntiresonance,
    SysConParameters.realLoopGain, Real.cos_pi]
  ring

/-- On the source domain, the SysCon named resonance power is strictly positive. -/
lemma sysConDropPower_atResonance_pos (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    0 < sysConDropPower p.atResonance := by
  rw [sysConDropPower_atResonance p hAttenuation.le]
  have hLoop : -1 < p.realLoopGain ∧ p.realLoopGain < 1 :=
    abs_lt.mp (show |p.realLoopGain| < 1 from hContractive)
  apply div_pos
  · exact mul_pos (sq_pos_of_ne_zero (mul_ne_zero hInputCross hDropCross)) hAttenuation
  · exact sq_pos_of_pos (sub_pos.mpr hLoop.2)

/-- On the source domain, the SysCon named antiresonance power is strictly positive. -/
lemma sysConDropPower_atAntiresonance_pos (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    0 < sysConDropPower p.atAntiresonance := by
  rw [sysConDropPower_atAntiresonance p hAttenuation.le]
  have hLoop : -1 < p.realLoopGain ∧ p.realLoopGain < 1 :=
    abs_lt.mp (show |p.realLoopGain| < 1 from hContractive)
  apply div_pos
  · exact mul_pos (sq_pos_of_ne_zero (mul_ne_zero hInputCross hDropCross)) hAttenuation
  · exact sq_pos_of_pos (by linarith [hLoop.1])

/-- The two positive source powers have SysCon Thm. 7's cancelled denominator ratio. -/
lemma sysCon_namedDropPower_ratio (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    sysConDropPower p.atResonance / sysConDropPower p.atAntiresonance =
      (1 + p.realLoopGain) ^ 2 / (1 - p.realLoopGain) ^ 2 := by
  rw [sysConDropPower_atResonance p hAttenuation.le,
    sysConDropPower_atAntiresonance p hAttenuation.le]
  have hLoop : -1 < p.realLoopGain ∧ p.realLoopGain < 1 :=
    abs_lt.mp (show |p.realLoopGain| < 1 from hContractive)
  have hNumerator :
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 *
        p.fieldAttenuation ≠ 0 := by
    exact ne_of_gt
      (mul_pos (sq_pos_of_ne_zero (mul_ne_zero hInputCross hDropCross)) hAttenuation)
  have hResonance : (1 - p.realLoopGain) ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos (sub_pos.mpr hLoop.2))
  have hAntiresonance : (1 + p.realLoopGain) ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos (by linarith [hLoop.1]))
  field_simp

/-- SysCon Def. 11 equals Thm. 7 for every explicit logarithm base greater than one. -/
theorem sysConRejectionRatioInBase_eq_closedForm (base : ℝ) (p : SysConParameters)
    (_hBase : 1 < base) (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    sysConRejectionRatioInBase base p = sysConRejectionClosedForm base p := by
  rw [sysConRejectionRatioInBase, powerRatioInBase, sysConRejectionClosedForm,
    sysCon_namedDropPower_ratio p hAttenuation hInputCross hDropCross hContractive]
  simp only [SysConParameters.realLoopGain]

/-- The base-ten reading of SysCon Thm. 7 is Physlib's drop rejection ratio. -/
theorem sysConRejectionClosedForm_base_ten (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hResonanceDenominator : p.toAddDrop.atResonance.HasNonzeroDenominator)
    (hAntiresonanceDenominator : p.toAddDrop.atAntiresonance.HasNonzeroDenominator) :
    sysConRejectionClosedForm 10 p = AddDrop.dropRejectionRatioDB p.toAddDrop := by
  rw [sysConRejectionClosedForm,
    AddDrop.dropRejectionRatioDB_eq_denominatorRatio p.toAddDrop hAttenuation
      hInputCross hDropCross hResonanceDenominator hAntiresonanceDenominator]
  rfl

/-- The base-ten reading of SysCon Def. 11 is Physlib's drop rejection ratio. -/
theorem sysConRejectionRatioInBase_ten_eq_dropRejectionRatioDB
    (p : SysConParameters) (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive)
    (hResonanceDenominator : p.toAddDrop.atResonance.HasNonzeroDenominator)
    (hAntiresonanceDenominator : p.toAddDrop.atAntiresonance.HasNonzeroDenominator) :
    sysConRejectionRatioInBase 10 p = AddDrop.dropRejectionRatioDB p.toAddDrop := by
  rw [sysConRejectionRatioInBase_eq_closedForm 10 p (by norm_num) hAttenuation
    hInputCross hDropCross hContractive]
  exact sysConRejectionClosedForm_base_ten p hAttenuation hInputCross hDropCross
    hResonanceDenominator hAntiresonanceDenominator

/-- The natural-log reading of SysCon Thm. 7 is the same positive ratio measured with `ln`. -/
lemma sysConRejectionClosedForm_exp_one (p : SysConParameters) :
    sysConRejectionClosedForm (Real.exp 1) p =
      10 * Real.log
        (((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2) /
          ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
            p.fieldAttenuation) ^ 2)) := by
  rw [sysConRejectionClosedForm, Real.logb]
  simp

/-- The natural-log reading of SysCon Def. 11 is ten times `ln` of Thm. 7's positive ratio. -/
theorem sysConRejectionRatioInBase_exp_one_eq_naturalLog
    (p : SysConParameters) (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    sysConRejectionRatioInBase (Real.exp 1) p =
      10 * Real.log
        (((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2) /
          ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
            p.fieldAttenuation) ^ 2)) := by
  rw [sysConRejectionRatioInBase_eq_closedForm (Real.exp 1) p
      ((Real.one_lt_exp_iff).2 zero_lt_one) hAttenuation hInputCross hDropCross hContractive,
    sysConRejectionClosedForm_exp_one]

/-! ## E. SFG-TR'14 parameter, port, and square-root dictionary -/

/-- The five complex SFG-TR add-drop coefficients from `HOL-CORPUS.md:332-334`. -/
structure SfgParameters where
  /-- Source complete round-trip coefficient `xi`. -/
  roundTripCoefficient : ℂ
  /-- Source first cross amplitude `S1`. -/
  inputCrossAmplitude : ℂ
  /-- Source second cross amplitude `S2`. -/
  dropCrossAmplitude : ℂ
  /-- Source first through amplitude `C1`. -/
  inputThroughAmplitude : ℂ
  /-- Source second through amplitude `C2`. -/
  dropThroughAmplitude : ℂ

/-- Physlib add-drop data mapped to SFG-TR's complex coefficient names.

The SFG input node 1 and output node 8 are Physlib's input and drop channels; Def. 35 and Thm. 7
are at `HOL-CORPUS.md:332-334`.
-/
def SfgParameters.ofAddDrop (p : AddDrop.Parameters) : SfgParameters where
  roundTripCoefficient := p.roundTripCoefficient
  inputCrossAmplitude := p.inputCrossAmplitude
  dropCrossAmplitude := p.dropCrossAmplitude
  inputThroughAmplitude := p.inputThroughAmplitude
  dropThroughAmplitude := p.dropThroughAmplitude

/-- The SFG dictionary preserves the round trip and all four real Physlib coupler amplitudes. -/
lemma SfgParameters.ofAddDrop_data (p : AddDrop.Parameters) :
    (SfgParameters.ofAddDrop p).roundTripCoefficient = p.roundTripCoefficient ∧
      (SfgParameters.ofAddDrop p).inputCrossAmplitude = p.inputCrossAmplitude ∧
      (SfgParameters.ofAddDrop p).dropCrossAmplitude = p.dropCrossAmplitude ∧
      (SfgParameters.ofAddDrop p).inputThroughAmplitude = p.inputThroughAmplitude ∧
      (SfgParameters.ofAddDrop p).dropThroughAmplitude = p.dropThroughAmplitude :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- SFG-TR Thm. 7's transfer `-S1*S2*sqrt(xi)/(1-C1*C2*xi)`
(`HOL-CORPUS.md:334`). -/
def sfgAddDropTransfer (p : SfgParameters) : ℂ :=
  -(p.inputCrossAmplitude * p.dropCrossAmplitude *
      Complex.sqrt p.roundTripCoefficient) /
    (1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
      p.roundTripCoefficient)

/-- SFG-TR's two `-j*S` branches use the N7 negative-quadrature gauge at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`. -/
def sfgCrossCoefficient (crossAmplitude : ℂ) : ℂ :=
  -Complex.I * crossAmplitude

/-- Under an explicit principal-square-root branch match, SFG-TR Thm. 7 is the S2 drop field. -/
theorem sfgAddDropTransfer_eq_dropTransfer (p : AddDrop.Parameters)
    (hSqrt : Complex.sqrt p.roundTripCoefficient = p.firstArcCoefficient) :
    sfgAddDropTransfer (SfgParameters.ofAddDrop p) = AddDrop.dropTransfer p := by
  rw [AddDrop.dropTransfer_eq_standard, sfgAddDropTransfer,
    AddDrop.standardDropTransfer]
  simp only [SfgParameters.ofAddDrop, hSqrt, AddDrop.Parameters.denominator,
    AddDrop.Parameters.loopGain]

/-- With the N5 solve gate, SFG-TR Thm. 7 is the input-to-drop response entry. -/
theorem sfgAddDropTransfer_eq_n5Response (p : AddDrop.Parameters)
    (hSqrt : Complex.sqrt p.roundTripCoefficient = p.firstArcCoefficient)
    (hDenominator : p.HasNonzeroDenominator) :
    sfgAddDropTransfer (SfgParameters.ofAddDrop p) =
      (AddDrop.netlist p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (AddDrop.dropChannel p))
        (Incident.mk (AddDrop.inputChannel p)) := by
  have hResponse := AddDrop.responseTransform_entry_drop_input p hDenominator
  rw [sfgAddDropTransfer_eq_dropTransfer p hSqrt]
  exact hResponse.symm

end MicroringSourceBridge

end

end Optics
