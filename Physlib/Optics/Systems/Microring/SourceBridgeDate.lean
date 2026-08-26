/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module
public import Physlib.Optics.Network.TwoPortScatteringChain
public import Physlib.Optics.Systems.Microring.AddDrop

/-!
# DATE'14 source bridges for microring transfer formulas

## i. Overview

This file records the DATE'14 parameter and port dictionary needed to compare Physlib's explicit
microring network with the source statements catalogued at `HOL-CORPUS.md:188-208` in the
parity audit checkout. The DATE parameters are `(r, t, L_c, alpha, lambda, n_eff)`.

DATE's printed forward field and Physlib's through field differ by an explicit algebraic
channel-sign gauge, represented by `dateThroughGauge`.

## ii. Key results

- `dateForwardTransfer_eq_gauged_throughTransfer`: DATE's `R` and the Physlib through field.
- `dateBackwardTransfer_eq_dropTransfer`: DATE's `T` and the Physlib drop field.
- `dateTwoPortBehavior_iff_matrix`: DATE Def. 3 implies DATE Thm. 1 in its source order.
- `dateTwoPortChainMatrix_eq_gauged_n7Chain`: DATE Thm. 1 and the typed N7 chain view.
- `dateFourPortChainMatrix_eq_reindexed_n5Response`: DATE Thm. 2's own matrix and N5.
- `dateFourPortBehavior_iff_n5Response`: DATE Def. 3 and the proof-gated N5 chain response.

## iii. Table of contents

- A. DATE'14 parameter and algebraic channel-sign dictionary
- B. DATE'14 transfer fields and four-port formula container

## iv. References and non-claims

DATE'14 Def. 3 and Thms. 1--2 are summarized at `HOL-CORPUS.md:194-198`.

The source predicates store their transfer formulas; this file does not recast them as component
derivations. It also does not assert that every source record maps to N7-valid components.
Physical response meaning on the Physlib side remains gated by N5 well-posedness and N7
validity. No reciprocity, omitted-loss completeness, time-domain causality, bandwidth,
dispersion, or measurement-validation claim is made. The DATE cascade, lattice, termination,
and Sylvester results are not bridged here.

`dateTwoPortChainMatrix` and `dateFourPortBackwardFirstChainMatrix` are totalized
quotient-valued objects. Their chain meanings are asserted only under the respective nonzero
pivot gates `t != 0` and `R != 0`; the four-port N5 bridge also requires the ring solve
denominator to be nonzero. The DATE transfer quotients and their norm-square powers are also
totalized at zero denominator. Their algebraic identities remain meaningful there, but an N5
response claim requires the displayed nonzero-denominator gate.
-/
@[expose] public section

namespace Optics

noncomputable section

namespace MicroringSourceBridge
/-! ## A. DATE'14 parameter and algebraic channel-sign dictionary -/

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

/-- DATE's `exp(-j*delta/2)` assigned to each symmetric half arc
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

/-- The DATE through output and Physlib's through channel differ by an algebraic sign gauge.

DATE's `R` has the leading minus sign shown at `HOL-CORPUS.md:196`; the drop field `T` does not
receive this adapter.
-/
def dateThroughGauge (amplitude : ℂ) : ℂ :=
  -amplitude

/-- The DATE add input carries the matching algebraic sign used by its four-port ordering
`(c,a) -> (d,b)` at `HOL-CORPUS.md:198`. -/
def dateAddGauge (amplitude : ℂ) : ℂ :=
  -amplitude

/-- The input and drop fields use the identity channel-sign map in the DATE dictionary. -/
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

/-- The canonical source-order reindex from `Fin 2` to backward-first wave coordinates.

Index zero is the backward coordinate and index one is the forward coordinate, matching DATE's
printed `(d,b)` output and `(c,a)` input order at `HOL-CORPUS.md:198`.
-/
def dateBackwardFirstFinEquiv :
    Fin 2 ≃ (BackwardWave Unit ⊕ ForwardWave Unit) where
  toFun index :=
    if index = 0 then Sum.inl (BackwardWave.mk ())
    else Sum.inr (ForwardWave.mk ())
  invFun
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  left_inv := by
    intro index
    fin_cases index <;> simp
  right_inv := by
    intro index
    rcases index with backward | forward
    · rcases backward with ⟨channel⟩
      rcases channel with ⟨⟩
      simp
    · rcases forward with ⟨channel⟩
      rcases channel with ⟨⟩
      simp

/-- The canonical reindex sends DATE coordinate zero backward and coordinate one forward. -/
lemma dateBackwardFirstFinEquiv_data :
    dateBackwardFirstFinEquiv 0 =
        (Sum.inl (BackwardWave.mk ()) : BackwardWave Unit ⊕ ForwardWave Unit) ∧
      dateBackwardFirstFinEquiv 1 =
        (Sum.inr (ForwardWave.mk ()) : BackwardWave Unit ⊕ ForwardWave Unit) := by
  simp [dateBackwardFirstFinEquiv]

/-- DATE Thm. 2's four-port matrix with backward-first endpoint types. -/
def dateFourPortBackwardFirstChainMatrix (p : DateParameters) :
    BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => 1 / dateForwardTransfer p
  | Sum.inl _, Sum.inr _ => -dateBackwardTransfer p / dateForwardTransfer p
  | Sum.inr _, Sum.inl _ => dateBackwardTransfer p / dateForwardTransfer p
  | Sum.inr _, Sum.inr _ =>
      (dateForwardTransfer p ^ 2 - dateBackwardTransfer p ^ 2) /
        dateForwardTransfer p

/-- The typed backward-first DATE matrix is literally the source `Fin 2` formula after the
canonical source-order reindex. -/
lemma dateFourPortBackwardFirstChainMatrix_reindex (p : DateParameters) :
    (fun output input =>
      dateFourPortBackwardFirstChainMatrix p
        (dateBackwardFirstFinEquiv output) (dateBackwardFirstFinEquiv input)) =
      dateFourPortChainMatrix p := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [dateBackwardFirstFinEquiv, dateFourPortBackwardFirstChainMatrix,
      dateFourPortChainMatrix]

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

/-- DATE Thm. 2's own `Fin 2` matrix is the canonically reindexed, proof-gated N5 chain response. -/
theorem dateFourPortChainMatrix_eq_reindexed_n5Response (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hForward : dateForwardTransfer p ≠ 0) :
    dateFourPortChainMatrix p =
      fun output input =>
        (dateN5FourPortScattering p
          ((p.hasNonzeroDenominator_iff).mp hDenominator)).toBackwardFirstChainTransform
            (dateN5FourPortScattering_hasBijectiveRightToLeftTransmission p hUnitary
              ((p.hasNonzeroDenominator_iff).mp hDenominator) hForward)
            (dateBackwardFirstFinEquiv output) (dateBackwardFirstFinEquiv input) := by
  rw [dateFourPortChainMatrix_eq_n5Response p hUnitary hDenominator hForward]
  exact (dateFourPortBackwardFirstChainMatrix_reindex p).symm

/-- DATE Def. 3's stated behavior is equivalent to action by the canonically reindexed N5 chain
response under the source normalization and exact solve gates. -/
theorem dateFourPortBehavior_iff_n5Response (p : DateParameters) (f : DateFourPortFields)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hForward : dateForwardTransfer p ≠ 0) :
    dateFourPortBehavior p f ↔
      dateFourPortOutputVector f =
        Matrix.mulVec
          (fun output input =>
            (dateN5FourPortScattering p
              ((p.hasNonzeroDenominator_iff).mp hDenominator)).toBackwardFirstChainTransform
                (dateN5FourPortScattering_hasBijectiveRightToLeftTransmission p hUnitary
                  ((p.hasNonzeroDenominator_iff).mp hDenominator) hForward)
                (dateBackwardFirstFinEquiv output) (dateBackwardFirstFinEquiv input))
          (dateFourPortInputVector f) := by
  rw [dateFourPortBehavior_iff_matrix,
    dateFourPortChainMatrix_eq_reindexed_n5Response p hUnitary hDenominator hForward]

end MicroringSourceBridge

end

end Optics
