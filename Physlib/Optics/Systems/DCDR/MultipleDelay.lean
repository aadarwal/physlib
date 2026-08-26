/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.SourceBridge

/-!
# Multiple-delay coherent N7 core for the double-coupler double-ring

## i. Overview

This file extends the coherent N7 DCDR rational family from one formal delay on every path to
three independent natural delay exponents. The upper, lower, and feedback path coefficients are
`G1*q^m1`, `G2*q^m2`, and `G3*q^m3`. The same two coherent couplers, six connections,
selected input, and selected output are retained.

The unit-delay parameters and fixed-carrier path realization being extended are declared at
`Physlib/Optics/Systems/DCDR/Poles.lean:82-110`; its rational N7 path family starts at
`Physlib/Optics/Systems/DCDR/Poles.lean:274-324`.

The one-delay family is the literal specialization `(m1, m2, m3) = (1, 1, 1)`. Pointwise
compilation evaluates each retained polynomial path and recovers the existing coherent N7 flat
netlist. Polynomial degree and reduction results live in `DCDR/MultipleDelayPolynomial.lean`;
the separate printed-source dictionary lives in `DCDR/MultipleDelaySource.lean`.

## ii. Key results

- `DCDR.MultipleDelayParameters`: coherent gains and three natural delay exponents.
- `DCDR.UnitDelayParameters.toMultipleDelayParameters`: the literal unit-delay specialization.
- `DCDR.multipleDelayRationalNetlist`: the complete rational N7 family.
- `DCDR.multipleDelayRationalNetlist_compile_eq`: pointwise compilation into the N7 netlist.
- `DCDR.multipleDelayRationalEliminationResponse_eq_responseModel`: selected N5 response.

## iii. Table of contents

- A. Coherent multiple-delay parameters and polynomial data
- B. Literal unit-delay specialization
- C. Rational component family and complete N7 netlist
- D. Selected compiled response

## iv. References

No result here claims physical resonance, coherent--incoherent equivalence, BIBO stability beyond
S4P's stated gate, normalized-modal or electromagnetic power, causality or time-domain behavior,
a physical-frequency interpretation, or any fact about the unavailable HOL script.

S4P restricts its Schur/BIBO result to the proper causal one-pole class at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:424-457`.

U. Siddique, S. M. Beillahi, and S. Tahar, “On the Formal Analysis of Photonic Signal
Processing Systems”, FMICS 2015, LNCS 9128, Equation 3, Theorem 3, and Table 1, pp. 169--174.

Physlib retains formal `q` and states reciprocal `z` results only through `q = z⁻¹`. This is
a coordinate legend, not a physical-frequency claim. The coherent N7 `t`/`-I*k` construction
is the source's own unprinted coherent branch; the printed incoherent graph remains separate.
-/

@[expose] public section

namespace Optics

noncomputable section

open Polynomial

namespace DCDR

/-!

## A. Coherent multiple-delay parameters and polynomial data

-/

/-- Coherent N7 DCDR parameters with an independent formal-delay exponent on every path. -/
structure MultipleDelayParameters where
  /-- Parameters of the first coherent directional coupler. -/
  firstCoupler : DirectionalCoupler.Parameters
  /-- Parameters of the second coherent directional coupler. -/
  secondCoupler : DirectionalCoupler.Parameters
  /-- Complex gain `G1` on the upper path. -/
  upperGain : ℂ
  /-- Complex gain `G2` on the lower path. -/
  lowerGain : ℂ
  /-- Complex gain `G3` on the feedback path. -/
  feedbackGain : ℂ
  /-- Upper-path delay exponent `m1`. -/
  m1 : ℕ
  /-- Lower-path delay exponent `m2`. -/
  m2 : ℕ
  /-- Feedback-path delay exponent `m3`. -/
  m3 : ℕ

/-- Algebraic admissibility requires each retained path to contain a positive delay.

The complex gains remain unrestricted, so this includes passive, active, and phased algebraic
fixtures. The rational and fixed-carrier laws remain total outside this predicate.
-/
def MultipleDelayParameters.IsAdmissible (p : MultipleDelayParameters) : Prop :=
  0 < p.m1 ∧ 0 < p.m2 ∧ 0 < p.m3

/-- A fixed-carrier path realizing the complex coefficient `gain*q^delay`. -/
def multipleDelayPathAt (gain : ℂ) (delay : ℕ) (q : ℂ) :
    MatchedPropagation.Parameters where
  amplitudeTransmission := ‖gain * q ^ delay‖
  carrierPathPhase := -(Complex.arg (gain * q ^ delay) : Real.Angle)

/-- The fixed-carrier realization has coefficient `gain*q^delay`. -/
@[simp]
lemma transmissionCoefficient_multipleDelayPathAt (gain : ℂ) (delay : ℕ) (q : ℂ) :
    MatchedPropagation.transmissionCoefficient (multipleDelayPathAt gain delay q) =
      gain * q ^ delay := by
  rw [MatchedPropagation.transmissionCoefficient, multipleDelayPathAt,
    MatchedPropagation.carrierPhaseFactor]
  simp only [neg_neg, Real.Angle.toCircle_coe, Circle.coe_exp]
  exact Complex.norm_mul_exp_arg_mul_I (gain * q ^ delay)

/-- The ordinary coherent DCDR parameters obtained by evaluating formal `q`. -/
def MultipleDelayParameters.at (p : MultipleDelayParameters) (q : ℂ) : Parameters where
  firstCoupler := p.firstCoupler
  secondCoupler := p.secondCoupler
  upperPath := multipleDelayPathAt p.upperGain p.m1 q
  lowerPath := multipleDelayPathAt p.lowerGain p.m2 q
  feedbackPath := multipleDelayPathAt p.feedbackGain p.m3 q

/-- Evaluation gives the declared upper coefficient `G1*q^m1`. -/
@[simp]
lemma MultipleDelayParameters.upperCoefficient_at
    (p : MultipleDelayParameters) (q : ℂ) :
    (p.at q).upperCoefficient = p.upperGain * q ^ p.m1 := by
  simp [MultipleDelayParameters.at, Parameters.upperCoefficient]

/-- Evaluation gives the declared lower coefficient `G2*q^m2`. -/
@[simp]
lemma MultipleDelayParameters.lowerCoefficient_at
    (p : MultipleDelayParameters) (q : ℂ) :
    (p.at q).lowerCoefficient = p.lowerGain * q ^ p.m2 := by
  simp [MultipleDelayParameters.at, Parameters.lowerCoefficient]

/-- Evaluation gives the declared feedback coefficient `G3*q^m3`. -/
@[simp]
lemma MultipleDelayParameters.feedbackCoefficient_at
    (p : MultipleDelayParameters) (q : ℂ) :
    (p.at q).feedbackCoefficient = p.feedbackGain * q ^ p.m3 := by
  simp [MultipleDelayParameters.at, Parameters.feedbackCoefficient]

/-- The retained upper-path polynomial `G1*q^m1`. -/
def MultipleDelayParameters.upperPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  C p.upperGain * X ^ p.m1

/-- The retained lower-path polynomial `G2*q^m2`. -/
def MultipleDelayParameters.lowerPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  C p.lowerGain * X ^ p.m2

/-- The retained feedback-path polynomial `G3*q^m3`. -/
def MultipleDelayParameters.feedbackPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  C p.feedbackGain * X ^ p.m3

/-- The coherent feedback-loop polynomial before subtraction from one. -/
def MultipleDelayParameters.loopPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  p.feedbackPolynomial *
    (C (p.secondCoupler.throughAmplitude : ℂ) * p.lowerPolynomial *
        C (p.firstCoupler.throughAmplitude : ℂ) +
      C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.upperPolynomial *
        C (DirectionalCoupler.crossCoefficient p.firstCoupler))

/-- The coherent internal solve denominator `1 - loopPolynomial`. -/
def MultipleDelayParameters.denominatorPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  1 - p.loopPolynomial

/-- The returning drive polynomial obtained from the two coherent arms. -/
def MultipleDelayParameters.feedbackDrivePolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  p.feedbackPolynomial *
    (C (p.secondCoupler.throughAmplitude : ℂ) * p.lowerPolynomial *
        C (DirectionalCoupler.crossCoefficient p.firstCoupler) +
      C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.upperPolynomial *
        C (p.firstCoupler.throughAmplitude : ℂ))

/-- The direct source-to-output polynomial before feedback elimination. -/
def MultipleDelayParameters.directPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.lowerPolynomial *
      C (DirectionalCoupler.crossCoefficient p.firstCoupler) +
    C (p.secondCoupler.throughAmplitude : ℂ) * p.upperPolynomial *
      C (p.firstCoupler.throughAmplitude : ℂ)

/-- The polynomial gain from the feedback coordinate to the selected output. -/
def MultipleDelayParameters.feedbackReadoutPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.lowerPolynomial *
      C (p.firstCoupler.throughAmplitude : ℂ) +
    C (p.secondCoupler.throughAmplitude : ℂ) * p.upperPolynomial *
      C (DirectionalCoupler.crossCoefficient p.firstCoupler)

/-- The selected coherent response numerator after eliminating the feedback coordinate. -/
def MultipleDelayParameters.responseNumeratorPolynomial
    (p : MultipleDelayParameters) : Polynomial ℂ :=
  p.directPolynomial * p.denominatorPolynomial +
    p.feedbackReadoutPolynomial * p.feedbackDrivePolynomial

/-- Evaluation of the upper path polynomial gives `G1*q^m1`. -/
@[simp]
lemma MultipleDelayParameters.eval_upperPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.upperPolynomial.eval q = p.upperGain * q ^ p.m1 := by
  simp [MultipleDelayParameters.upperPolynomial]

/-- Evaluation of the lower path polynomial gives `G2*q^m2`. -/
@[simp]
lemma MultipleDelayParameters.eval_lowerPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.lowerPolynomial.eval q = p.lowerGain * q ^ p.m2 := by
  simp [MultipleDelayParameters.lowerPolynomial]

/-- Evaluation of the feedback path polynomial gives `G3*q^m3`. -/
@[simp]
lemma MultipleDelayParameters.eval_feedbackPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.feedbackPolynomial.eval q = p.feedbackGain * q ^ p.m3 := by
  simp [MultipleDelayParameters.feedbackPolynomial]

/-- Evaluation of the loop polynomial recovers the scalar coherent loop gain. -/
lemma MultipleDelayParameters.eval_loopPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.loopPolynomial.eval q = (p.at q).loopGain := by
  simp [MultipleDelayParameters.loopPolynomial, MultipleDelayParameters.at,
    Parameters.loopGain, Parameters.upperCoefficient, Parameters.lowerCoefficient,
    Parameters.feedbackCoefficient]

/-- Evaluation of the denominator recovers the fixed-carrier solve denominator. -/
lemma MultipleDelayParameters.eval_denominatorPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.denominatorPolynomial.eval q = (p.at q).denominator := by
  simp [MultipleDelayParameters.denominatorPolynomial, Parameters.denominator,
    p.eval_loopPolynomial]

/-- Evaluation of the drive polynomial recovers the fixed-carrier feedback drive. -/
lemma MultipleDelayParameters.eval_feedbackDrivePolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.feedbackDrivePolynomial.eval q = (p.at q).feedbackDrive := by
  simp [MultipleDelayParameters.feedbackDrivePolynomial, MultipleDelayParameters.at,
    Parameters.feedbackDrive, Parameters.upperCoefficient, Parameters.lowerCoefficient,
    Parameters.feedbackCoefficient]

/-- Evaluation of the direct polynomial recovers the fixed-carrier direct gain. -/
lemma MultipleDelayParameters.eval_directPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.directPolynomial.eval q = (p.at q).directGain := by
  simp [MultipleDelayParameters.directPolynomial, MultipleDelayParameters.at,
    Parameters.directGain, Parameters.upperCoefficient, Parameters.lowerCoefficient]

/-- Evaluation of the readout polynomial recovers the fixed-carrier readout gain. -/
lemma MultipleDelayParameters.eval_feedbackReadoutPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.feedbackReadoutPolynomial.eval q = (p.at q).feedbackReadoutGain := by
  simp [MultipleDelayParameters.feedbackReadoutPolynomial, MultipleDelayParameters.at,
    Parameters.feedbackReadoutGain, Parameters.upperCoefficient,
    Parameters.lowerCoefficient]

/-- Evaluation of the response numerator recovers the eliminated scalar numerator. -/
lemma MultipleDelayParameters.eval_responseNumeratorPolynomial
    (p : MultipleDelayParameters) (q : ℂ) :
    p.responseNumeratorPolynomial.eval q = (p.at q).responseNumerator := by
  simp [MultipleDelayParameters.responseNumeratorPolynomial,
    Parameters.responseNumerator, p.eval_directPolynomial,
    p.eval_denominatorPolynomial, p.eval_feedbackReadoutPolynomial,
    p.eval_feedbackDrivePolynomial]

/-- Positive delay exponents force the coherent denominator to evaluate to one at `q = 0`. -/
lemma MultipleDelayParameters.denominatorPolynomial_eval_zero
    (p : MultipleDelayParameters) (hp : p.IsAdmissible) :
    p.denominatorPolynomial.eval 0 = 1 := by
  rcases hp with ⟨hm1, hm2, hm3⟩
  simp [MultipleDelayParameters.denominatorPolynomial,
    MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.upperPolynomial,
    MultipleDelayParameters.lowerPolynomial,
    MultipleDelayParameters.feedbackPolynomial, Nat.ne_of_gt hm1,
    Nat.ne_of_gt hm2, Nat.ne_of_gt hm3]

/-- An admissible multiple-delay denominator is a nonzero formal polynomial. -/
lemma MultipleDelayParameters.denominatorPolynomial_ne_zero
    (p : MultipleDelayParameters) (hp : p.IsAdmissible) :
    p.denominatorPolynomial ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  rw [p.denominatorPolynomial_eval_zero hp] at hEvaluation
  simp at hEvaluation

/-- The retained multiple-delay quotient for the selected coherent DCDR response. -/
def MultipleDelayParameters.responseModel
    (p : MultipleDelayParameters) (hp : p.IsAdmissible) :
    DelayTransfer.RationalModel 1 where
  numerator := p.responseNumeratorPolynomial.toMvPolynomial 0
  denominator := p.denominatorPolynomial.toMvPolynomial 0
  denominator_ne_zero := by
    intro hZero
    apply p.denominatorPolynomial_ne_zero hp
    exact Polynomial.toMvPolynomial_injective (0 : Fin 1) (by simpa using hZero)

/-- Direct evaluation of the retained quotient gives the scalar coherent transfer. -/
lemma MultipleDelayParameters.responseModel_eval
    (p : MultipleDelayParameters) (hp : p.IsAdmissible) (q : ℂ) :
    (p.responseModel hp).eval (fun _ => q) = transfer (p.at q) := by
  rw [DelayTransfer.RationalModel.eval_eq]
  simp only [MultipleDelayParameters.responseModel,
    MvPolynomial.eval_toMvPolynomial]
  rw [p.eval_responseNumeratorPolynomial, p.eval_denominatorPolynomial]
  rfl

/-!

## B. Literal unit-delay specialization

-/

/-- Embed the one-delay family from
`Physlib/Optics/Systems/DCDR/Poles.lean:82-100` by setting every exponent to one. -/
def UnitDelayParameters.toMultipleDelayParameters
    (p : UnitDelayParameters) : MultipleDelayParameters where
  firstCoupler := p.firstCoupler
  secondCoupler := p.secondCoupler
  upperGain := p.upperGain
  lowerGain := p.lowerGain
  feedbackGain := p.feedbackGain
  m1 := 1
  m2 := 1
  m3 := 1

/-- The one-delay embedding stores exactly `(m1, m2, m3) = (1, 1, 1)` and the original data. -/
lemma UnitDelayParameters.toMultipleDelayParameters_data (p : UnitDelayParameters) :
    p.toMultipleDelayParameters.m1 = 1 ∧
      p.toMultipleDelayParameters.m2 = 1 ∧
        p.toMultipleDelayParameters.m3 = 1 ∧
          p.toMultipleDelayParameters.upperGain = p.upperGain ∧
            p.toMultipleDelayParameters.lowerGain = p.lowerGain ∧
              p.toMultipleDelayParameters.feedbackGain = p.feedbackGain :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every embedded one-delay parameter value has positive delay exponents. -/
lemma UnitDelayParameters.toMultipleDelayParameters_isAdmissible
    (p : UnitDelayParameters) : p.toMultipleDelayParameters.IsAdmissible := by
  simp [MultipleDelayParameters.IsAdmissible,
    UnitDelayParameters.toMultipleDelayParameters]

/-- The embedded upper polynomial is the existing unit-delay upper polynomial. -/
lemma UnitDelayParameters.toMultipleDelayParameters_upperPolynomial
    (p : UnitDelayParameters) :
    p.toMultipleDelayParameters.upperPolynomial = p.upperPolynomial := by
  simp [UnitDelayParameters.toMultipleDelayParameters,
    MultipleDelayParameters.upperPolynomial, UnitDelayParameters.upperPolynomial]

/-- The embedded lower polynomial is the existing unit-delay lower polynomial. -/
lemma UnitDelayParameters.toMultipleDelayParameters_lowerPolynomial
    (p : UnitDelayParameters) :
    p.toMultipleDelayParameters.lowerPolynomial = p.lowerPolynomial := by
  simp [UnitDelayParameters.toMultipleDelayParameters,
    MultipleDelayParameters.lowerPolynomial, UnitDelayParameters.lowerPolynomial]

/-- The embedded feedback polynomial is the existing unit-delay feedback polynomial. -/
lemma UnitDelayParameters.toMultipleDelayParameters_feedbackPolynomial
    (p : UnitDelayParameters) :
    p.toMultipleDelayParameters.feedbackPolynomial = p.feedbackPolynomial := by
  simp [UnitDelayParameters.toMultipleDelayParameters,
    MultipleDelayParameters.feedbackPolynomial, UnitDelayParameters.feedbackPolynomial]

/-- The embedded coherent denominator is exactly the existing unit-delay denominator. -/
lemma UnitDelayParameters.toMultipleDelayParameters_denominatorPolynomial
    (p : UnitDelayParameters) :
    p.toMultipleDelayParameters.denominatorPolynomial = p.denominatorPolynomial := by
  simp [MultipleDelayParameters.denominatorPolynomial,
    MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.upperPolynomial,
    MultipleDelayParameters.lowerPolynomial,
    MultipleDelayParameters.feedbackPolynomial,
    UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial,
    UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial,
    UnitDelayParameters.feedbackPolynomial,
    UnitDelayParameters.toMultipleDelayParameters]

/-- The embedded coherent numerator is exactly the existing unit-delay numerator. -/
lemma UnitDelayParameters.toMultipleDelayParameters_responseNumeratorPolynomial
    (p : UnitDelayParameters) :
    p.toMultipleDelayParameters.responseNumeratorPolynomial =
      p.responseNumeratorPolynomial := by
  simp [MultipleDelayParameters.responseNumeratorPolynomial,
    MultipleDelayParameters.directPolynomial,
    MultipleDelayParameters.denominatorPolynomial,
    MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.feedbackReadoutPolynomial,
    MultipleDelayParameters.feedbackDrivePolynomial,
    MultipleDelayParameters.upperPolynomial,
    MultipleDelayParameters.lowerPolynomial,
    MultipleDelayParameters.feedbackPolynomial,
    UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial,
    UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial,
    UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial,
    UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial,
    UnitDelayParameters.feedbackPolynomial,
    UnitDelayParameters.toMultipleDelayParameters]

/-!

## C. Rational component family and complete N7 netlist

-/

/-- A reflectionless path entry with retained coefficient `gain*q^delay`. -/
def multipleDelayRationalPathEntryModel (gain : ℂ) (delay : ℕ)
    (output input : (MatchedPropagation.portFamily Unit).Channel) :
    DelayTransfer.RationalModel 1 :=
  match output.1, input.1 with
  | .left, .right | .right, .left =>
      DelayTransfer.RationalModel.ofPolynomial
        (MvPolynomial.C gain * MvPolynomial.X 0 ^ delay)
  | _, _ => DelayTransfer.RationalModel.constant 0

/-- Evaluating a retained path entry gives `gain*q^delay` across the arc. -/
lemma multipleDelayRationalPathEntryModel_eval (gain : ℂ) (delay : ℕ) (q : ℂ)
    (output input : (MatchedPropagation.portFamily Unit).Channel) :
    (multipleDelayRationalPathEntryModel gain delay output input).eval (fun _ => q) =
      match output.1, input.1 with
      | .left, .right | .right, .left => gain * q ^ delay
      | _, _ => 0 := by
  rcases output with ⟨outputPort, outputMode⟩
  rcases input with ⟨inputPort, inputMode⟩
  cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode <;>
    simp [multipleDelayRationalPathEntryModel]

/-- The evaluated rational path entries in the existing N7 channel labels. -/
def multipleDelayEvaluatedPathScattering (gain : ℂ) (delay : ℕ) (q : ℂ) :
    ScatteringMatrix ((MatchedPropagation.portFamily Unit).Channel) where
  toModeTransform output input :=
    (multipleDelayRationalPathEntryModel gain delay output input).eval (fun _ => q)

/-- Evaluated rational path entries equal the fixed-carrier path realization. -/
lemma multipleDelayEvaluatedPathScattering_eq
    (gain : ℂ) (delay : ℕ) (q : ℂ) :
    multipleDelayEvaluatedPathScattering gain delay q =
      MatchedPropagation.physicalScattering (multipleDelayPathAt gain delay q) Unit := by
  change ScatteringMatrix.mk _ = ScatteringMatrix.mk _
  congr 1
  funext output input
  rcases output with ⟨outputPort, outputMode⟩
  rcases input with ⟨inputPort, inputMode⟩
  cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode
  all_goals
    simp only [multipleDelayRationalPathEntryModel,
      DelayTransfer.RationalModel.eval_ofPolynomial,
      DelayTransfer.RationalModel.eval_constant, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_pow, MvPolynomial.eval_X]
    rw [ModeTransform.reindex_apply]
    simp [MatchedPropagation.scattering, ReflectionlessTwoPort.scattering,
      MatchedPropagation.transmission, MatchedPropagation.channelEquiv,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- The five N7 component laws with constant couplers and three retained path exponents. -/
def multipleDelayRationalComponents (p : MultipleDelayParameters) :
    DelayTransfer.RationalComponentFamily 1 where
  Component := Component
  portFamily := componentPortFamily
  entryModel
    | .firstCoupler => fun output input =>
        DelayTransfer.RationalModel.constant
          ((DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
            output input)
    | .secondCoupler => fun output input =>
        DelayTransfer.RationalModel.constant
          ((DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
            output input)
    | .upperPath => multipleDelayRationalPathEntryModel p.upperGain p.m1
    | .lowerPath => multipleDelayRationalPathEntryModel p.lowerGain p.m2
    | .feedbackPath => multipleDelayRationalPathEntryModel p.feedbackGain p.m3
  ModelValidAt := fun _ _ => p.IsAdmissible

/-- The complete multiple-delay DCDR retains the original six proof-carrying connections. -/
def multipleDelayRationalNetlist (p : MultipleDelayParameters) :
    DelayTransfer.RationalNetlist 1 where
  components := multipleDelayRationalComponents p
  Connection := Connection
  connections := connections (p.at 0)

/-- The multiple-delay rational DCDR retains the finite aggregate channel family. -/
noncomputable instance multipleDelayRationalChannelFintype
    (p : MultipleDelayParameters) : Fintype (multipleDelayRationalNetlist p).Channel :=
  channelFintype (p.at 0)

/-- The multiple-delay rational DCDR retains the finite connected channel family. -/
noncomputable instance multipleDelayRationalConnectedChannelFintype
    (p : MultipleDelayParameters) :
    Fintype (multipleDelayRationalNetlist p).ConnectedChannel :=
  connectedChannelFintype (p.at 0)

/-- Pointwise compilation retains the finite aggregate channel family. -/
noncomputable instance multipleDelayRationalCompileChannelFintype
    (p : MultipleDelayParameters) (value : DelayTransfer.DelayTuple 1) :
    Fintype ((multipleDelayRationalNetlist p).compile value).Channel :=
  ParameterizedNetlist.compileChannelFintype
    (multipleDelayRationalNetlist p).toParameterizedNetlist value

/-- Pointwise compilation retains the finite connected channel family. -/
noncomputable instance multipleDelayRationalCompileConnectedChannelFintype
    (p : MultipleDelayParameters) (value : DelayTransfer.DelayTuple 1) :
    Fintype ((multipleDelayRationalNetlist p).compile value).ConnectedChannel :=
  ParameterizedNetlist.compileConnectedChannelFintype
    (multipleDelayRationalNetlist p).toParameterizedNetlist value

/-- Pointwise compiled aggregate channels have classical decidable equality. -/
noncomputable instance multipleDelayRationalCompileChannelDecidableEq
    (p : MultipleDelayParameters) (value : DelayTransfer.DelayTuple 1) :
    DecidableEq ((multipleDelayRationalNetlist p).compile value).Channel :=
  Classical.decEq _

/-- Pointwise compiled connected channels have classical decidable equality. -/
noncomputable instance multipleDelayRationalCompileConnectedChannelDecidableEq
    (p : MultipleDelayParameters) (value : DelayTransfer.DelayTuple 1) :
    DecidableEq ((multipleDelayRationalNetlist p).compile value).ConnectedChannel :=
  Classical.decEq _

/-- Evaluating every rational entry recovers the fixed-carrier N7 component family. -/
lemma multipleDelayRationalComponents_scattering_eq
    (p : MultipleDelayParameters) (q : ℂ) :
    (multipleDelayRationalComponents p).scattering (fun _ => q) =
      componentScattering (p.at q) := by
  funext component
  cases component
  · unfold DelayTransfer.RationalComponentFamily.scattering
    dsimp [multipleDelayRationalComponents, componentScattering,
      MultipleDelayParameters.at]
    congr 1
    funext output input
    rw [DelayTransfer.RationalModel.eval_constant]
    rfl
  · unfold DelayTransfer.RationalComponentFamily.scattering
    dsimp [multipleDelayRationalComponents, componentScattering,
      MultipleDelayParameters.at]
    congr 1
    funext output input
    rw [DelayTransfer.RationalModel.eval_constant]
    rfl
  · change multipleDelayEvaluatedPathScattering p.upperGain p.m1 q = _
    exact multipleDelayEvaluatedPathScattering_eq p.upperGain p.m1 q
  · change multipleDelayEvaluatedPathScattering p.lowerGain p.m2 q = _
    exact multipleDelayEvaluatedPathScattering_eq p.lowerGain p.m2 q
  · change multipleDelayEvaluatedPathScattering p.feedbackGain p.m3 q = _
    exact multipleDelayEvaluatedPathScattering_eq p.feedbackGain p.m3 q

/-- Pointwise rational compilation is the complete fixed-carrier coherent N7 netlist. -/
lemma multipleDelayRationalNetlist_compile_eq
    (p : MultipleDelayParameters) (q : ℂ) :
    (multipleDelayRationalNetlist p).compile (fun _ => q) = netlist (p.at q) := by
  have hScattering := multipleDelayRationalComponents_scattering_eq p q
  change FlatNetlist.mk
      { Component := Component
        portFamily := componentPortFamily
        scattering := (multipleDelayRationalComponents p).scattering (fun _ => q) }
      Connection (connections (p.at 0)) = netlist (p.at q)
  rw [hScattering]
  rfl

/-- Pointwise compilation and the fixed-carrier realization assemble the same transform. -/
lemma multipleDelayRationalNetlist_scatteringTransform_eq
    (p : MultipleDelayParameters) (q : ℂ) :
    ((multipleDelayRationalNetlist p).compile (fun _ => q)).scatteringTransform =
      (netlist (p.at q)).scatteringTransform := by
  have hScattering := multipleDelayRationalComponents_scattering_eq p q
  unfold FlatNetlist.scatteringTransform FlatNetlist.scatteringMatrix
  dsimp only [DelayTransfer.RationalNetlist.compile,
    DelayTransfer.RationalNetlist.toParameterizedNetlist,
    DelayTransfer.RationalComponentFamily.toParameterizedComponentFamily,
    ParameterizedNetlist.compile, ParameterizedComponentFamily.evaluate,
    multipleDelayRationalNetlist, netlist]
  rw [hScattering]
  rfl

/-- Pointwise compilation and fixed-carrier realization have the same internal operator. -/
lemma multipleDelayRationalNetlist_feedbackOperator_eq
    (p : MultipleDelayParameters) (q : ℂ) :
    ((multipleDelayRationalNetlist p).compile (fun _ => q)).feedbackOperator =
      (netlist (p.at q)).feedbackOperator := by
  unfold FlatNetlist.feedbackOperator
  rw [multipleDelayRationalNetlist_scatteringTransform_eq]
  rfl

/-- Compiled well-posedness is nonvanishing of the hand-expanded denominator. -/
lemma multipleDelayRationalNetlist_isWellPosed_iff
    (p : MultipleDelayParameters) (q : ℂ) :
    ((multipleDelayRationalNetlist p).compile (fun _ => q)).IsWellPosed ↔
      p.denominatorPolynomial.eval q ≠ 0 := by
  classical
  let compiled := (multipleDelayRationalNetlist p).compile (fun _ => q)
  calc
    compiled.IsWellPosed ↔ compiled.feedbackOperator.det ≠ 0 :=
      compiled.isWellPosed_iff_feedbackOperator_det_ne_zero
    _ ↔ (netlist (p.at q)).feedbackOperator.det ≠ 0 := by
      rw [multipleDelayRationalNetlist_feedbackOperator_eq p q]
      rfl
    _ ↔ (netlist (p.at q)).IsWellPosed :=
      (netlist (p.at q)).isWellPosed_iff_feedbackOperator_det_ne_zero.symm
    _ ↔ (p.at q).HasNonzeroDenominator := isWellPosed_iff (p.at q)
    _ ↔ p.denominatorPolynomial.eval q ≠ 0 := by
      rw [Parameters.HasNonzeroDenominator, ← p.eval_denominatorPolynomial]

/-- Every rational component entry is valid at an admissible multiple-delay point. -/
lemma multipleDelayRationalComponents_isValidAt
    (p : MultipleDelayParameters) (hp : p.IsAdmissible)
    (value : DelayTransfer.DelayTuple 1) (component : Component) :
    (multipleDelayRationalComponents p).toParameterizedComponentFamily.IsValidAt
      component value := by
  constructor
  · exact hp
  · intro output input
    cases component
    · simp [multipleDelayRationalComponents,
        DelayTransfer.RationalModel.evaluationDomain,
        DelayTransfer.RationalModel.constant,
        DelayTransfer.RationalModel.ofPolynomial]
    · simp [multipleDelayRationalComponents,
        DelayTransfer.RationalModel.evaluationDomain,
        DelayTransfer.RationalModel.constant,
        DelayTransfer.RationalModel.ofPolynomial]
    all_goals
      rcases output with ⟨outputPort, outputMode⟩
      rcases input with ⟨inputPort, inputMode⟩
      cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode <;>
        simp [multipleDelayRationalComponents,
          multipleDelayRationalPathEntryModel,
          DelayTransfer.RationalModel.evaluationDomain,
          DelayTransfer.RationalModel.constant,
          DelayTransfer.RationalModel.ofPolynomial]

/-- An admissible non-singular point belongs to the selected N5 response domain. -/
lemma multipleDelayRationalNetlist_mem_responseDomain
    (p : MultipleDelayParameters) (q : ℂ) (hp : p.IsAdmissible)
    (hDenominator : p.denominatorPolynomial.eval q ≠ 0) :
    (fun _ : Fin 1 => q) ∈ (multipleDelayRationalNetlist p).responseDomain := by
  constructor
  · exact (multipleDelayRationalNetlist_isWellPosed_iff p q).2 hDenominator
  · intro component
    exact multipleDelayRationalComponents_isValidAt p hp (fun _ => q) component

/-- The disconnected first-coupler source channel of the multiple-delay netlist. -/
def multipleDelayRationalInputChannel (p : MultipleDelayParameters) :
    (multipleDelayRationalNetlist p).ExternalChannel :=
  inputChannel (p.at 0)

/-- The disconnected second-coupler output channel of the multiple-delay netlist. -/
def multipleDelayRationalOutputChannel (p : MultipleDelayParameters) :
    (multipleDelayRationalNetlist p).ExternalChannel :=
  outputChannel (p.at 0)

/-- The compiled and fixed-carrier feedback inverses agree at a common point. -/
lemma multipleDelayRationalNetlist_feedbackInverse_eq
    (p : MultipleDelayParameters) (q : ℂ)
    (hCompiled : ((multipleDelayRationalNetlist p).compile (fun _ => q)).IsWellPosed)
    (hFixed : (netlist (p.at q)).IsWellPosed) :
    ((multipleDelayRationalNetlist p).compile (fun _ => q)).feedbackInverse hCompiled =
      (netlist (p.at q)).feedbackInverse hFixed := by
  rw [FlatNetlist.feedbackInverse_eq_matrix_inv _ hCompiled,
    FlatNetlist.feedbackInverse_eq_matrix_inv _ hFixed,
    multipleDelayRationalNetlist_feedbackOperator_eq]
  rfl

/-- The compiled and fixed-carrier proof-gated N5 response transforms agree. -/
lemma multipleDelayRationalNetlist_responseTransform_eq
    (p : MultipleDelayParameters) (q : ℂ)
    (hCompiled : ((multipleDelayRationalNetlist p).compile (fun _ => q)).IsWellPosed)
    (hFixed : (netlist (p.at q)).IsWellPosed) :
    ((multipleDelayRationalNetlist p).compile (fun _ => q)).responseTransform hCompiled =
      (netlist (p.at q)).responseTransform hFixed := by
  rw [((multipleDelayRationalNetlist p).compile
      (fun _ => q)).responseTransform_eq_blockFormula,
    (netlist (p.at q)).responseTransform_eq_blockFormula,
    ((multipleDelayRationalNetlist p).compile
      (fun _ => q)).responseBlockFormula_eq,
    (netlist (p.at q)).responseBlockFormula_eq,
    multipleDelayRationalNetlist_feedbackInverse_eq p q hCompiled hFixed,
    multipleDelayRationalNetlist_scatteringTransform_eq]
  rfl

/-!

## D. Selected compiled response

-/

/-- The selected proof-gated input-to-output response of the multiple-delay rational netlist. -/
def multipleDelayRationalEliminationResponse
    (p : MultipleDelayParameters) (q : ℂ)
    (hDomain : (fun _ : Fin 1 => q) ∈
      (multipleDelayRationalNetlist p).responseDomain) : ℂ :=
  (multipleDelayRationalNetlist p).toParameterizedNetlist.response hDomain
    (Outgoing.mk (multipleDelayRationalOutputChannel p))
    (Incident.mk (multipleDelayRationalInputChannel p))

/-- The selected compiled N5 response equals the retained multiple-delay quotient. -/
lemma multipleDelayRationalEliminationResponse_eq_responseModel
    (p : MultipleDelayParameters) (hp : p.IsAdmissible) (q : ℂ)
    (hDomain : (fun _ : Fin 1 => q) ∈
      (multipleDelayRationalNetlist p).responseDomain) :
    multipleDelayRationalEliminationResponse p q hDomain =
      (p.responseModel hp).eval (fun _ => q) := by
  have hCompiled := hDomain.1
  change ((multipleDelayRationalNetlist p).compile (fun _ => q)).IsWellPosed at hCompiled
  have hDenominator : (p.at q).HasNonzeroDenominator := by
    change (p.at q).denominator ≠ 0
    simpa only [← p.eval_denominatorPolynomial] using
      (multipleDelayRationalNetlist_isWellPosed_iff p q).1 hCompiled
  have hFixed : (netlist (p.at q)).IsWellPosed :=
    isWellPosed_of_hasNonzeroDenominator (p.at q) hDenominator
  have hEntry : multipleDelayRationalEliminationResponse p q hDomain =
      eliminationResponse (p.at q) hFixed := by
    change ((multipleDelayRationalNetlist p).compile
        (fun _ => q)).responseTransform hCompiled
        (Outgoing.mk (multipleDelayRationalOutputChannel p))
        (Incident.mk (multipleDelayRationalInputChannel p)) =
      (netlist (p.at q)).responseTransform hFixed
        (Outgoing.mk (outputChannel (p.at q)))
        (Incident.mk (inputChannel (p.at q)))
    rw [multipleDelayRationalNetlist_responseTransform_eq p q hCompiled hFixed]
    rfl
  rw [hEntry, eliminationResponse_eq_transfer (p.at q) hDenominator]
  exact (p.responseModel_eval hp q).symm

end DCDR

end

end Optics
