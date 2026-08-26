/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.NetlistCoefficients
public import Physlib.Optics.Network.NetlistMatricesRegression

/-!
# Regression tests for rational-coefficient finite netlists

## i. Overview

The certified two-component, one-link shape is reused with two nonconstant executable gains. A
`2q` entry and a `1 / (1 - q)` entry evaluate to the existing asymmetric integer fixture at
`q = 1/2`. The point satisfies every stored denominator guard, while `q = 1` is rejected by the
stored pole. Exact matrix theorems then pin guarded evaluation of `S`, `C`, all three external
boundary matrices, and the implicit feedback matrix `1 - C * S`.

The evaluated feedback matrix remains singular. This is an intentional sentinel that the
coefficient backend adds no inverse, determinant, or well-posedness hypothesis.

## ii. Key results

## iii. Table of contents

- A. Rational-gain fixture
- B. Guarded point evaluation
- C. Matrix commutation and singular feedback

## iv. References

The formal variable is algebraic. The fixture assigns it no frequency units, delay convention,
causal domain, or physical response interpretation.

-/

@[expose] public section

namespace Optics

open Physlib

attribute [local instance] FiniteNetlistData.channelFintype
  FiniteNetlistData.channelDecidableEq FiniteNetlistData.connectedChannelFintype
  FiniteNetlistData.connectedChannelDecidableEq

/-!

## A. Rational-gain fixture

-/

/-- The polynomial gain `2q`, equal to one at `q = 1/2`. -/
def netlistCoefficientsRegressionScaledVariable : RationalCoefficients ℚ where
  numerator := PolynomialCoefficients.ofList [0, 2]
  denominator := 1
  denominator_nonempty := by simp

/-- The rational gain `1 / (1 - q)`, equal to two at `q = 1/2`. -/
def netlistCoefficientsRegressionPole : RationalCoefficients ℚ where
  numerator := 1
  denominator := PolynomialCoefficients.ofList [1, -1]
  denominator_nonempty := by decide

/-- The polynomial fixture retains its normalized numerator. -/
@[simp]
lemma netlistCoefficientsRegressionScaledVariable_numerator :
    netlistCoefficientsRegressionScaledVariable.numerator.coefficients = [0, 2] := by
  decide

/-- The polynomial fixture has unit stored denominator. -/
@[simp]
lemma netlistCoefficientsRegressionScaledVariable_denominator :
    netlistCoefficientsRegressionScaledVariable.denominator.coefficients = [1] := by
  decide

/-- The pole fixture has unit numerator. -/
@[simp]
lemma netlistCoefficientsRegressionPole_numerator :
    netlistCoefficientsRegressionPole.numerator.coefficients = [1] := by
  decide

/-- The pole fixture retains its constant-term-first denominator. -/
@[simp]
lemma netlistCoefficientsRegressionPole_denominator :
    netlistCoefficientsRegressionPole.denominator.coefficients = [1, -1] := by
  decide

/-- Rational local scattering with one polynomial and one rational nonconstant entry. -/
def netlistCoefficientsRegressionScattering
    (component : netlistDataRegressionShape.Component) :
    Matrix (netlistDataRegressionShape.LocalChannel component)
      (netlistDataRegressionShape.LocalChannel component) (RationalCoefficients ℚ) :=
  fun output input =>
    if output.1.val = 0 then
      if input.1.val = 0 then 0
      else if component.val = 0 then netlistCoefficientsRegressionScaledVariable
      else netlistCoefficientsRegressionPole
    else 1

/-- The certified one-link topology equipped with executable rational gains. -/
def netlistCoefficientsRegressionData : FiniteNetlistData (RationalCoefficients ℚ) where
  shape := netlistDataRegressionShape
  scattering := netlistCoefficientsRegressionScattering
  connections := #[netlistDataRegressionConnection]

/-- Coefficients are evaluated in `ℚ` without changing the constant field. -/
def netlistCoefficientsRegressionEvaluate : ℚ →+* ℚ := RingHom.id ℚ

/-- The guarded evaluation point `q = 1/2`. -/
def netlistCoefficientsRegressionPoint : ℚ := 1 / 2

/-!

## B. Guarded point evaluation

-/

/-- Every stored denominator is nonzero at `q = 1/2`. -/
lemma netlistCoefficientsRegression_guard :
    netlistCoefficientsRegressionData.StoredDenominatorsNonzeroAt
      netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint := by
  intro component output input
  change RationalCoefficients.StoredDenominatorNonzeroAt
    (netlistCoefficientsRegressionScattering component output input)
      netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint
  unfold netlistCoefficientsRegressionScattering
  by_cases hOutput : output.1.val = 0
  · rw [if_pos hOutput]
    by_cases hInput : input.1.val = 0
    · rw [if_pos hInput]
      exact RationalCoefficients.storedDenominatorNonzeroAt_zero _ _
    · rw [if_neg hInput]
      by_cases hComponent : component.val = 0
      · rw [if_pos hComponent]
        norm_num [RationalCoefficients.StoredDenominatorNonzeroAt,
          PolynomialCoefficients.eval, netlistCoefficientsRegressionEvaluate,
          netlistCoefficientsRegressionPoint]
      · rw [if_neg hComponent]
        norm_num [RationalCoefficients.StoredDenominatorNonzeroAt,
          PolynomialCoefficients.eval, netlistCoefficientsRegressionEvaluate,
          netlistCoefficientsRegressionPoint]
  · rw [if_neg hOutput]
    exact RationalCoefficients.storedDenominatorNonzeroAt_one _ _

/-- The same executable data rejects `q = 1`, where the stored pole denominator vanishes. -/
lemma netlistCoefficientsRegression_guard_fails_at_one :
    ¬netlistCoefficientsRegressionData.StoredDenominatorsNonzeroAt
      netlistCoefficientsRegressionEvaluate 1 := by
  intro hGuard
  have hPole := hGuard netlistDataRegressionComponentB
    (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
      (netlistDataRegressionExternalPort netlistDataRegressionComponentB).2)
    (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
      (netlistDataRegressionLinkPort netlistDataRegressionComponentB).2)
  change netlistCoefficientsRegressionPole.StoredDenominatorNonzeroAt
    netlistCoefficientsRegressionEvaluate 1 at hPole
  unfold RationalCoefficients.StoredDenominatorNonzeroAt PolynomialCoefficients.eval at hPole
  rw [netlistCoefficientsRegressionPole_denominator] at hPole
  norm_num [netlistCoefficientsRegressionEvaluate] at hPole

/-- The polynomial entry evaluates to one at the guarded point. -/
lemma netlistCoefficientsRegression_scaledVariable_evalAt :
    netlistCoefficientsRegressionScaledVariable.evalAt netlistCoefficientsRegressionEvaluate
      netlistCoefficientsRegressionPoint = 1 := by
  unfold RationalCoefficients.evalAt PolynomialCoefficients.eval
  rw [netlistCoefficientsRegressionScaledVariable_numerator,
    netlistCoefficientsRegressionScaledVariable_denominator]
  norm_num [netlistCoefficientsRegressionEvaluate, netlistCoefficientsRegressionPoint]

/-- The rational entry evaluates to two at the guarded point. -/
lemma netlistCoefficientsRegression_pole_evalAt :
    netlistCoefficientsRegressionPole.evalAt netlistCoefficientsRegressionEvaluate
      netlistCoefficientsRegressionPoint = 2 := by
  unfold RationalCoefficients.evalAt PolynomialCoefficients.eval
  rw [netlistCoefficientsRegressionPole_numerator,
    netlistCoefficientsRegressionPole_denominator]
  norm_num [netlistCoefficientsRegressionEvaluate, netlistCoefficientsRegressionPoint]

/-!

## C. Matrix commutation and singular feedback

-/

/-- The assembled symbolic scattering matrix evaluates exactly by the executable lists. -/
lemma netlistCoefficientsRegression_scatteringMatrix_evalAt :
    netlistCoefficientsRegressionData.toRatFuncData.scatteringMatrix.map
        (RatFunc.eval netlistCoefficientsRegressionEvaluate
          netlistCoefficientsRegressionPoint) =
      (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).scatteringMatrix :=
  netlistCoefficientsRegressionData.scatteringMatrix_evalAt
    netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint
      netlistCoefficientsRegression_guard

/-- Unit-gain routing evaluates without any denominator hypothesis. -/
lemma netlistCoefficientsRegression_routingMatrix_evalAt :
    netlistCoefficientsRegressionData.toRatFuncData.routingMatrix.map
        (RatFunc.eval netlistCoefficientsRegressionEvaluate
          netlistCoefficientsRegressionPoint) =
      (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).routingMatrix :=
  netlistCoefficientsRegressionData.routingMatrix_evalAt
    netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint

/-- Evaluation transports external incident exposure along the canonical channel relabeling. -/
lemma netlistCoefficientsRegression_inputExposureMatrix_evalAt :
    (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).inputExposureMatrix =
      Matrix.reindex (Equiv.refl _)
        (Incident.relabelEquiv
          (netlistCoefficientsRegressionData.externalChannelEquivEvaluation
            netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint))
        (netlistCoefficientsRegressionData.toRatFuncData.inputExposureMatrix.map
          (RatFunc.eval netlistCoefficientsRegressionEvaluate
            netlistCoefficientsRegressionPoint)) :=
  netlistCoefficientsRegressionData.inputExposureMatrix_evalAt
    netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint

/-- Evaluation transports external outgoing exposure along the canonical channel relabeling. -/
lemma netlistCoefficientsRegression_outputExposureMatrix_evalAt :
    (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).outputExposureMatrix =
      Matrix.reindex (Equiv.refl _)
        (Outgoing.relabelEquiv
          (netlistCoefficientsRegressionData.externalChannelEquivEvaluation
            netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint))
        (netlistCoefficientsRegressionData.toRatFuncData.outputExposureMatrix.map
          (RatFunc.eval netlistCoefficientsRegressionEvaluate
            netlistCoefficientsRegressionPoint)) :=
  netlistCoefficientsRegressionData.outputExposureMatrix_evalAt
    netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint

/-- Evaluation transports external outgoing readout along the canonical channel relabeling. -/
lemma netlistCoefficientsRegression_outputReadoutMatrix_evalAt :
    (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).outputReadoutMatrix =
      Matrix.reindex
        (Outgoing.relabelEquiv
          (netlistCoefficientsRegressionData.externalChannelEquivEvaluation
            netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint))
        (Equiv.refl _)
        (netlistCoefficientsRegressionData.toRatFuncData.outputReadoutMatrix.map
          (RatFunc.eval netlistCoefficientsRegressionEvaluate
            netlistCoefficientsRegressionPoint)) :=
  netlistCoefficientsRegressionData.outputReadoutMatrix_evalAt
    netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint

/-- Guarded evaluation commutes with the implicit feedback matrix without an inverse premise. -/
lemma netlistCoefficientsRegression_feedbackMatrix_evalAt :
    netlistCoefficientsRegressionData.toRatFuncData.feedbackMatrix.map
        (RatFunc.eval netlistCoefficientsRegressionEvaluate
          netlistCoefficientsRegressionPoint) =
      (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).feedbackMatrix :=
  netlistCoefficientsRegressionData.feedbackMatrix_evalAt
    netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint
      netlistCoefficientsRegression_guard

/-- The exact coefficient embedding used to compare with the established integer fixture. -/
def netlistCoefficientsRegressionIntCast : ℤ →+* ℚ := Int.castRingHom ℚ

/-- Point evaluation recovers every local entry of the asymmetric integer fixture over `ℚ`. -/
lemma netlistCoefficientsRegression_evaluated_scattering
    (component : netlistDataRegressionShape.Component) :
    (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).scattering component =
      (netlistDataRegression.scattering component).map
        netlistCoefficientsRegressionIntCast := by
  ext output input
  change
    (netlistCoefficientsRegressionScattering component output input).evalAt
        netlistCoefficientsRegressionEvaluate netlistCoefficientsRegressionPoint =
      netlistCoefficientsRegressionIntCast
        (netlistDataRegressionScattering component output input)
  unfold netlistCoefficientsRegressionScattering netlistDataRegressionScattering
  by_cases hOutput : output.1.val = 0
  · rw [if_pos hOutput, if_pos hOutput]
    by_cases hInput : input.1.val = 0
    · rw [if_pos hInput, if_pos hInput]
      simp
    · rw [if_neg hInput, if_neg hInput]
      by_cases hComponent : component.val = 0
      · rw [if_pos hComponent, if_pos hComponent]
        exact netlistCoefficientsRegression_scaledVariable_evalAt
      · rw [if_neg hComponent, if_neg hComponent]
        exact netlistCoefficientsRegression_pole_evalAt
  · rw [if_neg hOutput, if_neg hOutput]
    simp

/-- Aggregate evaluated scattering is the coefficientwise cast of the integer matrix. -/
lemma netlistCoefficientsRegression_evaluated_scatteringMatrix :
    (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).scatteringMatrix =
      netlistDataRegression.scatteringMatrix.map netlistCoefficientsRegressionIntCast := by
  change
    (netlistCoefficientsRegressionData.mapGains
        (fun gain => gain.evalAt netlistCoefficientsRegressionEvaluate
          netlistCoefficientsRegressionPoint)).scatteringMatrix =
      netlistDataRegression.scatteringMatrix.map netlistCoefficientsRegressionIntCast
  rw [← netlistDataRegression.scatteringMatrix_mapGains
    netlistCoefficientsRegressionIntCast (map_zero _)]
  have hScattering :
      (netlistCoefficientsRegressionData.mapGains
        (fun gain => gain.evalAt netlistCoefficientsRegressionEvaluate
          netlistCoefficientsRegressionPoint)).scattering =
        (netlistDataRegression.mapGains
          netlistCoefficientsRegressionIntCast).scattering := by
    funext component
    exact netlistCoefficientsRegression_evaluated_scattering component
  unfold FiniteNetlistData.scatteringMatrix FiniteNetlistData.indexedScatteringMatrix
  rw [hScattering]
  simp only [netlistCoefficientsRegressionData, netlistDataRegression]
  rfl

/-- Point evaluation leaves the topology-only routing matrix equal to the cast integer routing. -/
lemma netlistCoefficientsRegression_evaluated_routingMatrix :
    (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).routingMatrix =
      netlistDataRegression.routingMatrix.map netlistCoefficientsRegressionIntCast := by
  change
    (netlistCoefficientsRegressionData.mapGains
        (fun gain => gain.evalAt netlistCoefficientsRegressionEvaluate
          netlistCoefficientsRegressionPoint)).routingMatrix =
      netlistDataRegression.routingMatrix.map netlistCoefficientsRegressionIntCast
  rw [← netlistDataRegression.routingMatrix_mapGains
    netlistCoefficientsRegressionIntCast (map_zero _) (map_one _)]
  ext incident outgoing
  unfold FiniteNetlistData.routingMatrix
  simp only [FiniteNetlistData.connectedChannelMap_mapGains,
    FiniteNetlistData.mate_mapGains]
  unfold netlistCoefficientsRegressionData netlistDataRegression
    FiniteNetlistData.connectedChannelMap FiniteNetlistData.mate
    FiniteNetlistData.connection
  simp only [FiniteNetlistData.mapGains]
  congr 1
  apply propext
  constructor
  · rintro ⟨⟨index, mode | mode⟩, hOutgoing, hIncident⟩
    · exact ⟨⟨index, Sum.inl mode⟩, hOutgoing, hIncident⟩
    · exact ⟨⟨index, Sum.inr mode⟩, hOutgoing, hIncident⟩
  · rintro ⟨⟨index, mode | mode⟩, hOutgoing, hIncident⟩
    · exact ⟨⟨index, Sum.inl mode⟩, hOutgoing, hIncident⟩
    · exact ⟨⟨index, Sum.inr mode⟩, hOutgoing, hIncident⟩

/-- The entire evaluated feedback matrix is the coefficientwise cast of the integer fixture. -/
lemma netlistCoefficientsRegression_evaluated_feedbackMatrix :
    (netlistCoefficientsRegressionData.evaluateAt
        netlistCoefficientsRegressionEvaluate
        netlistCoefficientsRegressionPoint).feedbackMatrix =
      netlistDataRegression.feedbackMatrix.map netlistCoefficientsRegressionIntCast := by
  unfold FiniteNetlistData.feedbackMatrix
  rw [netlistCoefficientsRegression_evaluated_routingMatrix,
    netlistCoefficientsRegression_evaluated_scatteringMatrix,
    Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_mul]
  rfl

/-- The established integer kernel viewed on the data projection's definitionally equal shape. -/
abbrev netlistCoefficientsRegressionIntegerKernelVector :
    Incident netlistDataRegression.shape.Channel → ℤ :=
  netlistMatricesRegressionKernelVector

/-- A nonzero rational incident vector supported on the two internal-link channels. -/
def netlistCoefficientsRegressionKernelVector :
    Incident netlistDataRegression.shape.Channel → ℚ :=
  fun incident => Int.castRingHom ℚ
    (netlistCoefficientsRegressionIntegerKernelVector incident)

/-- The evaluated link-supported kernel vector is nonzero. -/
lemma netlistCoefficientsRegression_kernelVector_ne_zero :
    netlistCoefficientsRegressionKernelVector ≠ 0 := by
  intro hZero
  have hCoordinate := congrFun hZero (Incident.mk netlistMatricesRegressionALink)
  change (1 : ℚ) = 0 at hCoordinate
  norm_num at hCoordinate

/-- The evaluated implicit feedback matrix remains singular at the guarded point. -/
lemma netlistCoefficientsRegression_feedbackMatrix_kernel :
    Matrix.mulVec
        (netlistCoefficientsRegressionData.evaluateAt
          netlistCoefficientsRegressionEvaluate
          netlistCoefficientsRegressionPoint).feedbackMatrix
      netlistCoefficientsRegressionKernelVector = 0 := by
  rw [netlistCoefficientsRegression_evaluated_feedbackMatrix]
  change Matrix.mulVec (netlistDataRegression.feedbackMatrix.map
      netlistCoefficientsRegressionIntCast)
      (netlistCoefficientsRegressionIntCast ∘
        netlistCoefficientsRegressionIntegerKernelVector) = 0
  have hIntegerKernel :
      Matrix.mulVec netlistDataRegression.feedbackMatrix
        netlistCoefficientsRegressionIntegerKernelVector = 0 :=
    netlistMatricesRegression_feedbackMatrix_kernel
  funext incident
  rw [← RingHom.map_mulVec,
    hIntegerKernel]
  rfl

end Optics
