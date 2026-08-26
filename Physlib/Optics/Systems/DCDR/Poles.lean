/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistMason
public import Physlib.Optics.Systems.DCDR.Response
public import Physlib.Optics.Systems.DelayTransfer.Stability

/-!
# Formal-delay response and poles of the double-coupler double-ring

## i. Overview

This file presents the coherent DCDR as a one-variable `DelayTransfer.RationalNetlist`. Each of
the three propagation arcs contributes its declared real gain times the same formal delay `q`;
the two N7 couplers retain their constant `t`/`-I * k` scattering entries. Pointwise compilation
is proved equal to the complete DCDR flat netlist, and its selected proof-gated N5 response is
proved equal to the retained rational quotient.

The reused S4 interface is `RationalNetlist` at
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:150-169`, its proof-gated response domain at
lines 227-260, the reciprocal substitution at lines 396-399, the abstract reduction and explicit
`NoPoleCancellation` gate at `Physlib/Optics/Systems/DelayTransfer/Poles.lean:167-236`, and the
reduced Schur predicate at `Physlib/Optics/Systems/DelayTransfer/Stability.lean:185-232`.

Candidate singularities come from failure of invertibility of the compiled internal N5 operator. A
`ResponseReduction` separately certifies that an S4 `RationalReduction` reduces the selected
network response polynomials. Reduced poles are always candidates; candidates become actual
reduced poles only under S4's explicit pointwise no-cancellation criterion.

Coherent N7 `t`/`-I * k` is the FMICS'15 source's own unprinted coherent branch. Its printed
incoherent `1 - k`/`k` formulas are a different case and are not identified with this response.

## ii. Key definitions and results

- `UnitDelayParameters`: two coherent couplers and three real formal-delay gains.
- `rationalNetlist`: the complete one-delay DCDR `RationalNetlist`.
- `rationalEliminationResponse_eq_responseModel`: compiled N5 response equals the quotient.
- `candidateSingularities`: singular values of the compiled internal operator.
- `ResponseReduction`: a reduction certificate tied to the selected network response.
- `ResponseReduction.actualPoles_subset_candidatePoles`: the unconditional pole direction.
- `ResponseReduction.candidatePoles_eq_actualPoles`: equality under no cancellation.

## iii. Table of contents

- A. Formal-delay parameters and polynomial response data
- B. Rational component family and complete netlist
- C. Compiled response certificate
- D. Candidate singularities and response-indexed reduction

## iv. References and non-claims

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definition 8, Table 1, and Theorem 4.

The nonnegative formal gains admit Table 1's active-amplifier case; they are not a material
amplifier law or a passivity certificate. Formal `q` and reciprocal `z` are not physical frequency.
No result calls zeros inside the unit disk a resonance, asserts a physical resonance, identifies
the printed incoherent equations with the coherent netlist, or supplies power observables.
Schur stability is only the abstract reduced-denominator predicate imported from S4. The S4 BIBO
equivalence is stated only for `ProperCausalOnePole`; no two-pole DCDR BIBO theorem is claimed.
No time-domain impulse-response or causality interpretation is supplied.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial

/-!

## A. Formal-delay parameters and polynomial response data

-/

/-- The coherent couplers and three real gains in the common one-delay DCDR specialization. -/
structure UnitDelayParameters where
  /-- Parameters of the first coherent directional coupler. -/
  firstCoupler : DirectionalCoupler.Parameters
  /-- Parameters of the second coherent directional coupler. -/
  secondCoupler : DirectionalCoupler.Parameters
  /-- Gain multiplying the formal delay on the upper arm. -/
  upperGain : ℝ
  /-- Gain multiplying the formal delay on the lower arm. -/
  lowerGain : ℝ
  /-- Gain multiplying the formal delay on the feedback arm. -/
  feedbackGain : ℝ

/-- Algebraic admissibility of the real formal-delay gains.

There is deliberately no upper bound: this predicate includes Table 1's active-amplifier case.
-/
def UnitDelayParameters.IsAdmissible (p : UnitDelayParameters) : Prop :=
  0 ≤ p.upperGain ∧ 0 ≤ p.lowerGain ∧ 0 ≤ p.feedbackGain

/-- A fixed-carrier path whose complex transmission coefficient realizes `gain * q`. -/
def pathAt (gain : ℝ) (q : ℂ) : MatchedPropagation.Parameters where
  amplitudeTransmission := gain * ‖q‖
  carrierPathPhase := -(Complex.arg q : Real.Angle)

/-- The fixed-carrier realization has complex coefficient `gain * q`. -/
@[simp]
lemma transmissionCoefficient_pathAt (gain : ℝ) (q : ℂ) :
    MatchedPropagation.transmissionCoefficient (pathAt gain q) = (gain : ℂ) * q := by
  rw [MatchedPropagation.transmissionCoefficient, pathAt,
    MatchedPropagation.carrierPhaseFactor]
  simp only [neg_neg, Real.Angle.toCircle_coe, Circle.coe_exp]
  push_cast
  rw [mul_assoc, Complex.norm_mul_exp_arg_mul_I]

/-- The ordinary DCDR parameters obtained by evaluating the shared formal delay at `q`. -/
def UnitDelayParameters.at (p : UnitDelayParameters) (q : ℂ) : Parameters where
  firstCoupler := p.firstCoupler
  secondCoupler := p.secondCoupler
  upperPath := pathAt p.upperGain q
  lowerPath := pathAt p.lowerGain q
  feedbackPath := pathAt p.feedbackGain q

/-- Evaluation gives the declared upper-arm coefficient. -/
@[simp]
lemma UnitDelayParameters.upperCoefficient_at (p : UnitDelayParameters) (q : ℂ) :
    (p.at q).upperCoefficient = (p.upperGain : ℂ) * q := by
  simp [UnitDelayParameters.at, Parameters.upperCoefficient]

/-- Evaluation gives the declared lower-arm coefficient. -/
@[simp]
lemma UnitDelayParameters.lowerCoefficient_at (p : UnitDelayParameters) (q : ℂ) :
    (p.at q).lowerCoefficient = (p.lowerGain : ℂ) * q := by
  simp [UnitDelayParameters.at, Parameters.lowerCoefficient]

/-- Evaluation gives the declared feedback-arm coefficient. -/
@[simp]
lemma UnitDelayParameters.feedbackCoefficient_at (p : UnitDelayParameters) (q : ℂ) :
    (p.at q).feedbackCoefficient = (p.feedbackGain : ℂ) * q := by
  simp [UnitDelayParameters.at, Parameters.feedbackCoefficient]

/-- The upper-arm polynomial `upperGain * q`. -/
def UnitDelayParameters.upperPolynomial (p : UnitDelayParameters) : Polynomial ℂ :=
  C (p.upperGain : ℂ) * X

/-- The lower-arm polynomial `lowerGain * q`. -/
def UnitDelayParameters.lowerPolynomial (p : UnitDelayParameters) : Polynomial ℂ :=
  C (p.lowerGain : ℂ) * X

/-- The feedback-arm polynomial `feedbackGain * q`. -/
def UnitDelayParameters.feedbackPolynomial (p : UnitDelayParameters) : Polynomial ℂ :=
  C (p.feedbackGain : ℂ) * X

/-- The polynomial obtained by expanding the coherent feedback loop. -/
def UnitDelayParameters.loopPolynomial (p : UnitDelayParameters) : Polynomial ℂ :=
  p.feedbackPolynomial *
    (C (p.secondCoupler.throughAmplitude : ℂ) * p.lowerPolynomial *
        C (p.firstCoupler.throughAmplitude : ℂ) +
      C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.upperPolynomial *
        C (DirectionalCoupler.crossCoefficient p.firstCoupler))

/-- The polynomial denominator `1 - loopPolynomial`. -/
def UnitDelayParameters.denominatorPolynomial (p : UnitDelayParameters) : Polynomial ℂ :=
  1 - p.loopPolynomial

/-- The returning drive polynomial obtained from the two coherent arms. -/
def UnitDelayParameters.feedbackDrivePolynomial (p : UnitDelayParameters) : Polynomial ℂ :=
  p.feedbackPolynomial *
    (C (p.secondCoupler.throughAmplitude : ℂ) * p.lowerPolynomial *
        C (DirectionalCoupler.crossCoefficient p.firstCoupler) +
      C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.upperPolynomial *
        C (p.firstCoupler.throughAmplitude : ℂ))

/-- The direct source-to-output polynomial before feedback elimination. -/
def UnitDelayParameters.directPolynomial (p : UnitDelayParameters) : Polynomial ℂ :=
  C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.lowerPolynomial *
      C (DirectionalCoupler.crossCoefficient p.firstCoupler) +
    C (p.secondCoupler.throughAmplitude : ℂ) * p.upperPolynomial *
      C (p.firstCoupler.throughAmplitude : ℂ)

/-- The polynomial gain from the feedback coordinate to the selected output. -/
def UnitDelayParameters.feedbackReadoutPolynomial
    (p : UnitDelayParameters) : Polynomial ℂ :=
  C (DirectionalCoupler.crossCoefficient p.secondCoupler) * p.lowerPolynomial *
      C (p.firstCoupler.throughAmplitude : ℂ) +
    C (p.secondCoupler.throughAmplitude : ℂ) * p.upperPolynomial *
      C (DirectionalCoupler.crossCoefficient p.firstCoupler)

/-- The hand-expanded polynomial numerator after eliminating the feedback coordinate. -/
def UnitDelayParameters.responseNumeratorPolynomial
    (p : UnitDelayParameters) : Polynomial ℂ :=
  p.directPolynomial * p.denominatorPolynomial +
    p.feedbackReadoutPolynomial * p.feedbackDrivePolynomial

/-- Evaluation of the loop polynomial recovers the scalar loop gain. -/
lemma UnitDelayParameters.eval_loopPolynomial (p : UnitDelayParameters) (q : ℂ) :
    p.loopPolynomial.eval q = (p.at q).loopGain := by
  simp [UnitDelayParameters.loopPolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    UnitDelayParameters.at, Parameters.loopGain, Parameters.upperCoefficient,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient]

/-- Evaluation of the denominator polynomial recovers the scalar solve denominator. -/
lemma UnitDelayParameters.eval_denominatorPolynomial (p : UnitDelayParameters) (q : ℂ) :
    p.denominatorPolynomial.eval q = (p.at q).denominator := by
  simp [UnitDelayParameters.denominatorPolynomial, Parameters.denominator,
    p.eval_loopPolynomial]

/-- Evaluation of the drive polynomial recovers the scalar feedback drive. -/
lemma UnitDelayParameters.eval_feedbackDrivePolynomial (p : UnitDelayParameters) (q : ℂ) :
    p.feedbackDrivePolynomial.eval q = (p.at q).feedbackDrive := by
  simp [UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    UnitDelayParameters.at, Parameters.feedbackDrive, Parameters.upperCoefficient,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient]

/-- Evaluation of the direct polynomial recovers the direct scalar gain. -/
lemma UnitDelayParameters.eval_directPolynomial (p : UnitDelayParameters) (q : ℂ) :
    p.directPolynomial.eval q = (p.at q).directGain := by
  simp [UnitDelayParameters.directPolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.at, Parameters.directGain,
    Parameters.upperCoefficient, Parameters.lowerCoefficient]

/-- Evaluation of the readout polynomial recovers the scalar feedback readout gain. -/
lemma UnitDelayParameters.eval_feedbackReadoutPolynomial
    (p : UnitDelayParameters) (q : ℂ) :
    p.feedbackReadoutPolynomial.eval q = (p.at q).feedbackReadoutGain := by
  simp [UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.upperPolynomial, UnitDelayParameters.lowerPolynomial,
    UnitDelayParameters.at, Parameters.feedbackReadoutGain,
    Parameters.upperCoefficient, Parameters.lowerCoefficient]

/-- Evaluation of the numerator polynomial recovers the eliminated scalar numerator. -/
lemma UnitDelayParameters.eval_responseNumeratorPolynomial
    (p : UnitDelayParameters) (q : ℂ) :
    p.responseNumeratorPolynomial.eval q = (p.at q).responseNumerator := by
  simp [UnitDelayParameters.responseNumeratorPolynomial, Parameters.responseNumerator,
    p.eval_directPolynomial, p.eval_denominatorPolynomial,
    p.eval_feedbackReadoutPolynomial, p.eval_feedbackDrivePolynomial]

/-- The response denominator is a nonzero formal polynomial because its value at zero is one. -/
lemma UnitDelayParameters.denominatorPolynomial_ne_zero (p : UnitDelayParameters) :
    p.denominatorPolynomial ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  simp [UnitDelayParameters.denominatorPolynomial, UnitDelayParameters.loopPolynomial,
    UnitDelayParameters.upperPolynomial, UnitDelayParameters.lowerPolynomial,
    UnitDelayParameters.feedbackPolynomial] at hEvaluation

/-- The retained one-delay polynomial quotient for the selected coherent DCDR response. -/
def responseModel (p : UnitDelayParameters) : DelayTransfer.RationalModel 1 where
  numerator := p.responseNumeratorPolynomial.toMvPolynomial 0
  denominator := p.denominatorPolynomial.toMvPolynomial 0
  denominator_ne_zero := by
    intro hZero
    apply p.denominatorPolynomial_ne_zero
    exact Polynomial.toMvPolynomial_injective (0 : Fin 1) (by simpa using hZero)

/-- Direct evaluation of the retained quotient gives the scalar DCDR transfer. -/
lemma responseModel_eval (p : UnitDelayParameters) (q : ℂ) :
    (responseModel p).eval (fun _ => q) = transfer (p.at q) := by
  rw [DelayTransfer.RationalModel.eval_eq]
  simp only [responseModel, MvPolynomial.eval_toMvPolynomial]
  rw [p.eval_responseNumeratorPolynomial, p.eval_denominatorPolynomial]
  rfl

/-!

## B. Rational component family and complete netlist

-/

/-- A reflectionless path entry with retained formal coefficient `gain * q`. -/
def rationalPathEntryModel (gain : ℝ)
    (output input : (MatchedPropagation.portFamily Unit).Channel) :
    DelayTransfer.RationalModel 1 :=
  match output.1, input.1 with
  | .left, .right | .right, .left =>
      DelayTransfer.RationalModel.ofPolynomial
        (MvPolynomial.C (gain : ℂ) * MvPolynomial.X 0)
  | _, _ => DelayTransfer.RationalModel.constant 0

/-- Evaluating a formal path gives `gain * q` across the arc and zero reflection. -/
lemma rationalPathEntryModel_eval (gain : ℝ) (q : ℂ)
    (output input : (MatchedPropagation.portFamily Unit).Channel) :
    (rationalPathEntryModel gain output input).eval (fun _ => q) =
      match output.1, input.1 with
      | .left, .right | .right, .left => (gain : ℂ) * q
      | _, _ => 0 := by
  rcases output with ⟨outputPort, outputMode⟩
  rcases input with ⟨inputPort, inputMode⟩
  cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode <;>
    simp [rationalPathEntryModel]

/-- The rational path entries collected in the physical N7 channel labels. -/
def evaluatedPathScattering (gain : ℝ) (q : ℂ) :
    ScatteringMatrix ((MatchedPropagation.portFamily Unit).Channel) where
  toModeTransform output input :=
    (rationalPathEntryModel gain output input).eval (fun _ => q)

/-- Evaluated rational path entries equal the fixed-carrier path realization. -/
lemma evaluatedPathScattering_eq (gain : ℝ) (q : ℂ) :
    evaluatedPathScattering gain q =
      MatchedPropagation.physicalScattering (pathAt gain q) Unit := by
  change ScatteringMatrix.mk _ = ScatteringMatrix.mk _
  congr 1
  funext output input
  rcases output with ⟨outputPort, outputMode⟩
  rcases input with ⟨inputPort, inputMode⟩
  cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode
  all_goals
    simp only [rationalPathEntryModel, DelayTransfer.RationalModel.eval_ofPolynomial,
      DelayTransfer.RationalModel.eval_constant, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [ModeTransform.reindex_apply]
    simp [MatchedPropagation.scattering, ReflectionlessTwoPort.scattering,
      MatchedPropagation.transmission, MatchedPropagation.channelEquiv,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- The five DCDR component laws with constant couplers and three formal-delay paths. -/
def rationalComponents (p : UnitDelayParameters) :
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
    | .upperPath => rationalPathEntryModel p.upperGain
    | .lowerPath => rationalPathEntryModel p.lowerGain
    | .feedbackPath => rationalPathEntryModel p.feedbackGain
  ModelValidAt := fun _ _ => p.IsAdmissible

/-- The complete one-delay DCDR uses the original six proof-carrying connections. -/
def rationalNetlist (p : UnitDelayParameters) : DelayTransfer.RationalNetlist 1 where
  components := rationalComponents p
  Connection := Connection
  connections := connections (p.at 0)

/-- The rational DCDR retains the finite aggregate N7 channel family. -/
noncomputable instance rationalChannelFintype (p : UnitDelayParameters) :
    Fintype (rationalNetlist p).Channel :=
  channelFintype (p.at 0)

/-- The rational DCDR retains the finite internally connected channel family. -/
noncomputable instance rationalConnectedChannelFintype (p : UnitDelayParameters) :
    Fintype (rationalNetlist p).ConnectedChannel :=
  connectedChannelFintype (p.at 0)

/-- Pointwise compilation retains the finite aggregate DCDR channel family. -/
noncomputable instance rationalCompileChannelFintype (p : UnitDelayParameters)
    (value : DelayTransfer.DelayTuple 1) :
    Fintype ((rationalNetlist p).compile value).Channel :=
  ParameterizedNetlist.compileChannelFintype
    (rationalNetlist p).toParameterizedNetlist value

/-- Pointwise compilation retains the finite connected DCDR channel family. -/
noncomputable instance rationalCompileConnectedChannelFintype (p : UnitDelayParameters)
    (value : DelayTransfer.DelayTuple 1) :
    Fintype ((rationalNetlist p).compile value).ConnectedChannel :=
  ParameterizedNetlist.compileConnectedChannelFintype
    (rationalNetlist p).toParameterizedNetlist value

/-- Pointwise compiled aggregate DCDR channels have classical decidable equality. -/
noncomputable instance rationalCompileChannelDecidableEq (p : UnitDelayParameters)
    (value : DelayTransfer.DelayTuple 1) :
    DecidableEq ((rationalNetlist p).compile value).Channel := Classical.decEq _

/-- Pointwise compiled connected DCDR channels have classical decidable equality. -/
noncomputable instance rationalCompileConnectedChannelDecidableEq
    (p : UnitDelayParameters) (value : DelayTransfer.DelayTuple 1) :
    DecidableEq ((rationalNetlist p).compile value).ConnectedChannel := Classical.decEq _

/-- Reciprocal-Z reparameterization retains the finite aggregate DCDR channel family. -/
noncomputable instance rationalReciprocalZChannelFintype (p : UnitDelayParameters) :
    Fintype (rationalNetlist p).reciprocalZ.Channel :=
  inferInstanceAs (Fintype (rationalNetlist p).Channel)

/-- Reciprocal-Z reparameterization retains the finite connected DCDR channel family. -/
noncomputable instance rationalReciprocalZConnectedChannelFintype
    (p : UnitDelayParameters) :
    Fintype (rationalNetlist p).reciprocalZ.ConnectedChannel :=
  inferInstanceAs (Fintype (rationalNetlist p).ConnectedChannel)

/-- Evaluating all rational component entries recovers the fixed-carrier DCDR component family. -/
lemma rationalComponents_scattering_eq (p : UnitDelayParameters) (q : ℂ) :
    (rationalComponents p).scattering (fun _ => q) = componentScattering (p.at q) := by
  funext component
  cases component
  · unfold DelayTransfer.RationalComponentFamily.scattering
    dsimp [rationalComponents, componentScattering, UnitDelayParameters.at]
    congr 1
    funext output input
    rw [DelayTransfer.RationalModel.eval_constant]
    rfl
  · unfold DelayTransfer.RationalComponentFamily.scattering
    dsimp [rationalComponents, componentScattering, UnitDelayParameters.at]
    congr 1
    funext output input
    rw [DelayTransfer.RationalModel.eval_constant]
    rfl
  · change evaluatedPathScattering p.upperGain q = _
    exact evaluatedPathScattering_eq p.upperGain q
  · change evaluatedPathScattering p.lowerGain q = _
    exact evaluatedPathScattering_eq p.lowerGain q
  · change evaluatedPathScattering p.feedbackGain q = _
    exact evaluatedPathScattering_eq p.feedbackGain q

/-- Pointwise rational compilation is exactly the complete fixed-carrier DCDR flat netlist. -/
lemma rationalNetlist_compile_eq (p : UnitDelayParameters) (q : ℂ) :
    (rationalNetlist p).compile (fun _ => q) = netlist (p.at q) := by
  have hScattering := rationalComponents_scattering_eq p q
  change FlatNetlist.mk
      { Component := Component
        portFamily := componentPortFamily
        scattering := (rationalComponents p).scattering (fun _ => q) }
      Connection (connections (p.at 0)) = netlist (p.at q)
  rw [hScattering]
  rfl

/-- Pointwise compilation and the fixed-carrier realization have the same assembled scattering
transform. -/
lemma rationalNetlist_scatteringTransform_eq (p : UnitDelayParameters) (q : ℂ) :
    ((rationalNetlist p).compile (fun _ => q)).scatteringTransform =
      (netlist (p.at q)).scatteringTransform := by
  have hScattering := rationalComponents_scattering_eq p q
  unfold FlatNetlist.scatteringTransform FlatNetlist.scatteringMatrix
  dsimp only [DelayTransfer.RationalNetlist.compile,
    DelayTransfer.RationalNetlist.toParameterizedNetlist,
    DelayTransfer.RationalComponentFamily.toParameterizedComponentFamily,
    ParameterizedNetlist.compile, ParameterizedComponentFamily.evaluate,
    rationalNetlist, netlist]
  rw [hScattering]
  rfl

/-- Pointwise compilation and the fixed-carrier realization have the same internal operator. -/
lemma rationalNetlist_feedbackOperator_eq (p : UnitDelayParameters) (q : ℂ) :
    ((rationalNetlist p).compile (fun _ => q)).feedbackOperator =
      (netlist (p.at q)).feedbackOperator := by
  unfold FlatNetlist.feedbackOperator
  rw [rationalNetlist_scatteringTransform_eq]
  rfl

/-- Compiled rational well-posedness is exactly nonvanishing of the response denominator. -/
lemma rationalNetlist_isWellPosed_iff (p : UnitDelayParameters) (q : ℂ) :
    ((rationalNetlist p).compile (fun _ => q)).IsWellPosed ↔
      p.denominatorPolynomial.eval q ≠ 0 := by
  classical
  let compiled := (rationalNetlist p).compile (fun _ => q)
  calc
    compiled.IsWellPosed ↔ compiled.feedbackOperator.det ≠ 0 :=
      compiled.isWellPosed_iff_feedbackOperator_det_ne_zero
    _ ↔ (netlist (p.at q)).feedbackOperator.det ≠ 0 := by
      rw [rationalNetlist_feedbackOperator_eq p q]
      rfl
    _ ↔ (netlist (p.at q)).IsWellPosed :=
      (netlist (p.at q)).isWellPosed_iff_feedbackOperator_det_ne_zero.symm
    _ ↔ (p.at q).HasNonzeroDenominator := isWellPosed_iff (p.at q)
    _ ↔ p.denominatorPolynomial.eval q ≠ 0 := by
      rw [Parameters.HasNonzeroDenominator, ← p.eval_denominatorPolynomial]

/-- Every retained rational component entry is valid at an admissible delay point. -/
lemma rationalComponents_isValidAt (p : UnitDelayParameters) (hp : p.IsAdmissible)
    (value : DelayTransfer.DelayTuple 1) (component : Component) :
    (rationalComponents p).toParameterizedComponentFamily.IsValidAt component value := by
  constructor
  · exact hp
  · intro output input
    cases component
    · simp [rationalComponents, DelayTransfer.RationalModel.evaluationDomain,
        DelayTransfer.RationalModel.constant, DelayTransfer.RationalModel.ofPolynomial]
    · simp [rationalComponents, DelayTransfer.RationalModel.evaluationDomain,
        DelayTransfer.RationalModel.constant, DelayTransfer.RationalModel.ofPolynomial]
    all_goals
      rcases output with ⟨outputPort, outputMode⟩
      rcases input with ⟨inputPort, inputMode⟩
      cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode <;>
        simp [rationalComponents, rationalPathEntryModel,
          DelayTransfer.RationalModel.evaluationDomain,
          DelayTransfer.RationalModel.constant, DelayTransfer.RationalModel.ofPolynomial]

/-- An admissible point with nonzero response denominator lies in the N5 response domain. -/
lemma rationalNetlist_mem_responseDomain (p : UnitDelayParameters) (q : ℂ)
    (hp : p.IsAdmissible) (hDenominator : p.denominatorPolynomial.eval q ≠ 0) :
    (fun _ : Fin 1 => q) ∈ (rationalNetlist p).responseDomain := by
  constructor
  · exact (rationalNetlist_isWellPosed_iff p q).2 hDenominator
  · intro component
    exact rationalComponents_isValidAt p hp (fun _ => q) component

/-- The disconnected first-coupler source channel of the rational DCDR. -/
def rationalInputChannel (p : UnitDelayParameters) :
    (rationalNetlist p).ExternalChannel :=
  inputChannel (p.at 0)

/-- The disconnected second-coupler output channel of the rational DCDR. -/
def rationalOutputChannel (p : UnitDelayParameters) :
    (rationalNetlist p).ExternalChannel :=
  outputChannel (p.at 0)

/-- The compiled and fixed-carrier feedback inverses agree under their respective solve proofs. -/
lemma rationalNetlist_feedbackInverse_eq (p : UnitDelayParameters) (q : ℂ)
    (hCompiled : ((rationalNetlist p).compile (fun _ => q)).IsWellPosed)
    (hFixed : (netlist (p.at q)).IsWellPosed) :
    ((rationalNetlist p).compile (fun _ => q)).feedbackInverse hCompiled =
      (netlist (p.at q)).feedbackInverse hFixed := by
  rw [FlatNetlist.feedbackInverse_eq_matrix_inv _ hCompiled,
    FlatNetlist.feedbackInverse_eq_matrix_inv _ hFixed,
    rationalNetlist_feedbackOperator_eq]
  rfl

/-- The compiled and fixed-carrier proof-gated N5 response transforms agree. -/
lemma rationalNetlist_responseTransform_eq (p : UnitDelayParameters) (q : ℂ)
    (hCompiled : ((rationalNetlist p).compile (fun _ => q)).IsWellPosed)
    (hFixed : (netlist (p.at q)).IsWellPosed) :
    ((rationalNetlist p).compile (fun _ => q)).responseTransform hCompiled =
      (netlist (p.at q)).responseTransform hFixed := by
  rw [((rationalNetlist p).compile (fun _ => q)).responseTransform_eq_blockFormula,
    (netlist (p.at q)).responseTransform_eq_blockFormula,
    ((rationalNetlist p).compile (fun _ => q)).responseBlockFormula_eq,
    (netlist (p.at q)).responseBlockFormula_eq,
    rationalNetlist_feedbackInverse_eq p q hCompiled hFixed,
    rationalNetlist_scatteringTransform_eq]
  rfl

/-!

## C. Compiled response certificate

-/

/-- The selected input-to-output entry of the proof-gated rational DCDR response. -/
def rationalEliminationResponse (p : UnitDelayParameters) (q : ℂ)
    (hDomain : (fun _ : Fin 1 => q) ∈ (rationalNetlist p).responseDomain) : ℂ :=
  (rationalNetlist p).toParameterizedNetlist.response hDomain
    (Outgoing.mk (rationalOutputChannel p)) (Incident.mk (rationalInputChannel p))

/-- The selected compiled N5 response equals the independently retained rational quotient. -/
lemma rationalEliminationResponse_eq_responseModel (p : UnitDelayParameters) (q : ℂ)
    (hDomain : (fun _ : Fin 1 => q) ∈ (rationalNetlist p).responseDomain) :
    rationalEliminationResponse p q hDomain =
      (responseModel p).eval (fun _ => q) := by
  have hCompiled := hDomain.1
  change ((rationalNetlist p).compile (fun _ => q)).IsWellPosed at hCompiled
  have hDenominator : (p.at q).HasNonzeroDenominator := by
    change (p.at q).denominator ≠ 0
    simpa only [← p.eval_denominatorPolynomial] using
      (rationalNetlist_isWellPosed_iff p q).1 hCompiled
  have hFixed : (netlist (p.at q)).IsWellPosed :=
    isWellPosed_of_hasNonzeroDenominator (p.at q) hDenominator
  have hEntry : rationalEliminationResponse p q hDomain =
      eliminationResponse (p.at q) hFixed := by
    change ((rationalNetlist p).compile (fun _ => q)).responseTransform hCompiled
        (Outgoing.mk (rationalOutputChannel p))
        (Incident.mk (rationalInputChannel p)) =
      (netlist (p.at q)).responseTransform hFixed
        (Outgoing.mk (outputChannel (p.at q)))
        (Incident.mk (inputChannel (p.at q)))
    rw [rationalNetlist_responseTransform_eq p q hCompiled hFixed]
    rfl
  rw [hEntry, eliminationResponse_eq_transfer (p.at q) hDenominator]
  exact (responseModel_eval p q).symm

/-- The selected proof-gated response entry after S4's reciprocal substitution `q = z⁻¹`. -/
def rationalZEliminationResponse (p : UnitDelayParameters) (z : ℂ)
    (hZ : z ∈ (rationalNetlist p).reciprocalZ.responseDomain) : ℂ :=
  ((rationalNetlist p).reciprocalZ.response hZ).reindex
      (Incident.relabelEquiv (rationalNetlist p).reciprocalZExternalChannelEquiv)
      (Outgoing.relabelEquiv (rationalNetlist p).reciprocalZExternalChannelEquiv)
    (Outgoing.mk (rationalOutputChannel p)) (Incident.mk (rationalInputChannel p))

/-- The proof-gated reciprocal-Z response is the retained quotient evaluated at `q = z⁻¹`. -/
lemma rationalZEliminationResponse_eq_responseModel (p : UnitDelayParameters) (z : ℂ)
    (hZ : z ∈ (rationalNetlist p).reciprocalZ.responseDomain) :
    rationalZEliminationResponse p z hZ =
      (responseModel p).eval (fun _ : Fin 1 => z⁻¹) := by
  have hDelayRaw : DelayTransfer.zInverseEvaluation z ∈
      (rationalNetlist p).responseDomain := by
    have hDomainMembership := congrArg (fun domain : Set ℂ => z ∈ domain)
      ((rationalNetlist p).responseDomain_reciprocalZ)
    exact hDomainMembership.mp hZ
  have hEvaluation : DelayTransfer.zInverseEvaluation z = (fun _ : Fin 1 => z⁻¹) := by
    funext delay
    exact DelayTransfer.zInverseEvaluation_apply z delay
  have hDelay : (fun _ : Fin 1 => z⁻¹) ∈ (rationalNetlist p).responseDomain := by
    rw [← hEvaluation]
    exact hDelayRaw
  have hResponse :=
    (rationalNetlist p).response_reciprocalZ_reindex_of_evaluation_eq
      hZ hEvaluation hDelay
  have hEntry := congrArg (fun response =>
      response (Outgoing.mk (rationalOutputChannel p))
        (Incident.mk (rationalInputChannel p))) hResponse
  have hModel := rationalEliminationResponse_eq_responseModel p z⁻¹ hDelay
  change (rationalNetlist p).toParameterizedNetlist.response hDelay
      (Outgoing.mk (rationalOutputChannel p))
      (Incident.mk (rationalInputChannel p)) =
    (responseModel p).eval (fun _ : Fin 1 => z⁻¹) at hModel
  change ((rationalNetlist p).reciprocalZ.response hZ).reindex
      (Incident.relabelEquiv (rationalNetlist p).reciprocalZExternalChannelEquiv)
      (Outgoing.relabelEquiv (rationalNetlist p).reciprocalZExternalChannelEquiv)
        (Outgoing.mk (rationalOutputChannel p))
        (Incident.mk (rationalInputChannel p)) =
    (responseModel p).eval (fun _ : Fin 1 => z⁻¹)
  exact hEntry.trans hModel

/-!

## D. Candidate singularities and response-indexed reduction

-/

/-- Formal delay values where the compiled DCDR internal feedback operator is not invertible. -/
def candidateSingularities (p : UnitDelayParameters) : Set ℂ :=
  {q | ¬Function.Bijective
    ((rationalNetlist p).compile (fun _ => q)).feedbackOperator.toLinearMap}

/-- Candidate membership is equivalently failure of compiled N5 well-posedness. -/
lemma mem_candidateSingularities_iff_not_isWellPosed
    (p : UnitDelayParameters) (q : ℂ) :
    q ∈ candidateSingularities p ↔
      ¬((rationalNetlist p).compile (fun _ => q)).IsWellPosed := by
  change (¬Function.Bijective
      ((rationalNetlist p).compile (fun _ => q)).feedbackOperator.toLinearMap) ↔
    ¬((rationalNetlist p).compile (fun _ => q)).IsWellPosed
  let compiled := (rationalNetlist p).compile (fun _ => q)
  exact not_congr compiled.isWellPosed_iff_feedbackOperator_bijective.symm

/-- Internal-operator singularity is exactly vanishing of the hand-expanded response denominator. -/
lemma mem_candidateSingularities_iff (p : UnitDelayParameters) (q : ℂ) :
    q ∈ candidateSingularities p ↔ p.denominatorPolynomial.eval q = 0 := by
  rw [mem_candidateSingularities_iff_not_isWellPosed,
    rationalNetlist_isWellPosed_iff]
  simp

/-- Nonzero reciprocal `z` values whose formal inverse is an internal candidate singularity. -/
def candidatePoles (p : UnitDelayParameters) : Set ℂ :=
  {z | z ≠ 0 ∧ z⁻¹ ∈ candidateSingularities p}

/-- An S4 polynomial reduction tied to this DCDR's selected N5 response polynomials. -/
structure ResponseReduction (p : UnitDelayParameters) where
  /-- The explicit S4 common-factor reduction. -/
  reduction : DelayTransfer.RationalReduction
  /-- The reduction's raw numerator is the selected DCDR response numerator. -/
  rawNumerator_eq : reduction.rawNumerator = p.responseNumeratorPolynomial
  /-- The reduction's raw denominator is the DCDR internal solve denominator. -/
  rawDenominator_eq : reduction.rawDenominator = p.denominatorPolynomial

namespace ResponseReduction

variable {p : UnitDelayParameters}

/-- Formal-`q` zeros of the certified reduced DCDR response.

This is not the reciprocal-coordinate `zZeros` set: in particular, `q = 0` represents `z = ∞`.
-/
def formalZeros (certificate : ResponseReduction p) : Set ℂ :=
  certificate.reduction.reduced.zeros

/-- Reciprocal-coordinate poles of the certified reduced DCDR response. -/
def actualPoles (certificate : ResponseReduction p) : Set ℂ :=
  certificate.reduction.reduced.zPoles

/-- Every actual reduced response pole is an internal-operator candidate pole. -/
lemma actualPoles_subset_candidatePoles (certificate : ResponseReduction p) :
    certificate.actualPoles ⊆ candidatePoles p := by
  rintro z ⟨hz, hReduced⟩
  refine ⟨hz, (mem_candidateSingularities_iff p z⁻¹).2 ?_⟩
  rw [← certificate.rawDenominator_eq]
  exact certificate.reduction.reducedPoles_subset_rawDenominatorRoots hReduced

/-- S4's explicit no-cancellation gate promotes every internal candidate to an actual pole. -/
lemma candidatePoles_subset_actualPoles (certificate : ResponseReduction p)
    (hNoCancellation : ∀ q ∈ certificate.reduction.rawDenominatorRoots,
      certificate.reduction.NoPoleCancellation q) :
    candidatePoles p ⊆ certificate.actualPoles := by
  rintro z ⟨hz, hCandidate⟩
  refine ⟨hz, certificate.reduction.rawDenominatorRoots_subset_reducedPoles
    hNoCancellation ?_⟩
  change certificate.reduction.rawDenominator.eval z⁻¹ = 0
  rw [certificate.rawDenominator_eq]
  exact (mem_candidateSingularities_iff p z⁻¹).1 hCandidate

/-- With no cancellation, internal candidate poles and actual reduced poles coincide. -/
lemma candidatePoles_eq_actualPoles (certificate : ResponseReduction p)
    (hNoCancellation : ∀ q ∈ certificate.reduction.rawDenominatorRoots,
      certificate.reduction.NoPoleCancellation q) :
    candidatePoles p = certificate.actualPoles :=
  Set.Subset.antisymm
    (certificate.candidatePoles_subset_actualPoles hNoCancellation)
    certificate.actualPoles_subset_candidatePoles

/-- Away from the cancelled factor and reduced denominator, the reduced quotient evaluates to
the retained raw DCDR response quotient. -/
lemma reduced_eval_eq_responseModel (certificate : ResponseReduction p) (q : ℂ)
    (hFactor : certificate.reduction.NoPoleCancellation q)
    (hReduced : q ∈ certificate.reduction.reduced.evaluationDomain) :
    certificate.reduction.reduced.eval q = (responseModel p).eval (fun _ => q) := by
  change certificate.reduction.cancelledFactor.eval q ≠ 0 at hFactor
  change certificate.reduction.reduced.denominator.eval q ≠ 0 at hReduced
  rw [DelayTransfer.ReducedRationalResponse.eval,
    DelayTransfer.RationalModel.eval_eq]
  simp only [responseModel, MvPolynomial.eval_toMvPolynomial]
  rw [← certificate.rawNumerator_eq, ← certificate.rawDenominator_eq,
    certificate.reduction.rawNumerator_eq, certificate.reduction.rawDenominator_eq,
    eval_mul, eval_mul]
  field_simp

/-- On the common N5 and reduced-quotient domain, the reduction evaluates to the compiled DCDR
response entry. -/
lemma reduced_eval_eq_rationalEliminationResponse (certificate : ResponseReduction p) (q : ℂ)
    (hDomain : (fun _ : Fin 1 => q) ∈ (rationalNetlist p).responseDomain)
    (hFactor : certificate.reduction.NoPoleCancellation q)
    (hReduced : q ∈ certificate.reduction.reduced.evaluationDomain) :
    certificate.reduction.reduced.eval q =
      rationalEliminationResponse p q hDomain := by
  rw [certificate.reduced_eval_eq_responseModel q hFactor hReduced,
    rationalEliminationResponse_eq_responseModel p q hDomain]

end ResponseReduction

end

end Optics.DCDR
