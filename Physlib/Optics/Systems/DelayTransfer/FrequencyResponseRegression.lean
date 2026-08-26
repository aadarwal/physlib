/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.EvaluationRegression
public import Physlib.Optics.Systems.DelayTransfer.FrequencyResponse

/-!
# Regression tests for proof-gated delay frequency response

## i. Overview

The compiled all-pass rational netlist is evaluated at unit delay and angular frequency `π/2`.
The frequency-delay map is hand-expanded to `q = -I`, while the reciprocal-Z unit-circle point is
hand-expanded to `z = I`. The proof-gated response entry is then shown to be the non-real value
`75/109 + (32/109) I` by directly invoking the compiled all-pass channel-equation solve.

These anchors can fail if the exponential sign, imaginary-axis embedding, reciprocal convention,
frequency response domain, channel reindexing, rational compilation, or loop equations are
changed.

## ii. Key results

- `frequencyDelayEvaluation_quadrature`: the exact negative-exponential delay value.
- `unitCirclePoint_quadrature`: the exact reciprocal-Z point.
- `allPassRationalNetlistFrequencyQuadratureDomain`: the proof-gated frequency witness.
- `allPassRationalNetlist_quadrature_compiled_entry_via_equations`: the direct equation solve.
- `allPassRationalNetlist_frequency_quadrature_response_entry`: the compiled response anchor.
- `allPassRationalNetlist_frequency_eq_reciprocalZ_quadrature_entry`: selected entries agree.

## iii. Table of contents

- A. Convention anchors
- B. Compiled proof-gated response anchors

## iv. References and non-claims

The rational all-pass fixture and its direct compiled channel-equation solve are in
`Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:150-298` and `845-912`. The
physical all-pass channel equation is proved independently in
`Physlib/Optics/Systems/Microring/AllPass.lean:1174-1239`. This regression does not use the prior
formal-delay, Laplace, or reciprocal-Z response-value anchors.

The fixture checks one declared constant delay. It proves no rational dependence on physical
frequency, dispersion model, group-delay theorem, passivity result, or response outside the N5F
domain.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-- The rational all-pass fixture retains finite aggregate channels. -/
local instance frequencyRegressionChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).Channel :=
  AllPass.channelFintype p

/-- The rational all-pass fixture retains finite connected channels. -/
local instance frequencyRegressionConnectedChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).ConnectedChannel :=
  AllPass.connectedChannelFintype p

/-- Formal-delay compilation retains finite aggregate all-pass channels. -/
local instance frequencyRegressionCompileChannelFintype (p : AllPass.Parameters)
    (value : DelayTuple 1) :
    Fintype ((allPassRationalNetlist p).compile value).Channel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).Channel)

/-- Formal-delay compilation retains finite connected all-pass channels. -/
local instance frequencyRegressionCompileConnectedChannelFintype
    (p : AllPass.Parameters) (value : DelayTuple 1) :
    Fintype ((allPassRationalNetlist p).compile value).ConnectedChannel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).ConnectedChannel)

/-- Laplace reparameterization retains finite aggregate all-pass channels. -/
local instance frequencyRegressionLaplaceChannelFintype (p : AllPass.Parameters)
    (delays : Fin 1 → ℝ) :
    Fintype ((allPassRationalNetlist p).laplace delays).Channel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).Channel)

/-- Laplace reparameterization retains finite connected all-pass channels. -/
local instance frequencyRegressionLaplaceConnectedChannelFintype
    (p : AllPass.Parameters) (delays : Fin 1 → ℝ) :
    Fintype ((allPassRationalNetlist p).laplace delays).ConnectedChannel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).ConnectedChannel)

/-- Reciprocal-Z reparameterization retains finite aggregate all-pass channels. -/
local instance frequencyRegressionReciprocalZChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).reciprocalZ.Channel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).Channel)

/-- Reciprocal-Z reparameterization retains finite connected all-pass channels. -/
local instance frequencyRegressionReciprocalZConnectedChannelFintype
    (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).reciprocalZ.ConnectedChannel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).ConnectedChannel)

/-!

## A. Convention anchors

-/

/-- With unit delay and angular frequency `π/2`, the selected frequency map gives `q = -I`. -/
lemma frequencyDelayEvaluation_quadrature :
    frequencyDelayEvaluation (fun _ : Fin 1 ↦ 1) (Real.pi / 2) =
      (fun _ ↦ -Complex.I) := by
  funext i
  rw [frequencyDelayEvaluation_apply]
  have hExponent :
      -Complex.I * ((((Real.pi / 2) * 1 : ℝ)) : ℂ) =
        ((-(Real.pi / 2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hExponent, Complex.exp_mul_I]
  simp

/-- At unit delay and angular frequency `π/2`, the selected unit-circle point is `z = I`. -/
lemma unitCirclePoint_quadrature : unitCirclePoint 1 (Real.pi / 2) = Complex.I := by
  rw [unitCirclePoint]
  have hExponent :
      Complex.I * ((((Real.pi / 2) * 1 : ℝ)) : ℂ) =
        (((Real.pi / 2 : ℝ) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [hExponent, Complex.exp_mul_I]
  simp

/-!

## B. Compiled proof-gated response anchors

-/

/-- The unit-delay quadrature point belongs to the compiled frequency response domain. -/
lemma allPassRationalNetlistFrequencyQuadratureDomain :
    Real.pi / 2 ∈
      (allPassRationalNetlist allPassRationalQuadratureParameters).frequencyResponseDomain
        (fun _ : Fin 1 ↦ 1) := by
  rw [(allPassRationalNetlist
    allPassRationalQuadratureParameters).mem_frequencyResponseDomain_iff,
    frequencyDelayEvaluation_quadrature]
  exact allPassRationalQuadratureDomain

/-- Direct expansion of the compiled channel equations gives the quadrature response entry.

This proof does not use a formal-delay, Laplace, reciprocal-Z, or frequency response anchor.
-/
lemma allPassRationalNetlist_quadrature_compiled_entry_via_equations :
    (((allPassRationalNetlist
      allPassRationalQuadratureParameters).compile
        (fun _ : Fin 1 ↦ -Complex.I)).responseTransform
          allPassRationalQuadratureDomain.1)
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      75 / 109 + (32 / 109) * Complex.I := by
  have hResponse := allPassRationalNetlist_responseThrough
    allPassRationalQuadratureParameters (-Complex.I)
    allPassRational_quadrature_loopCoefficient allPassRationalQuadratureDomain
    allPassRational_quadrature_hasNonzeroDenominator 1
  rw [allPassRational_quadrature_throughTransfer] at hResponse
  simp [allPassRationalInputAmplitude, ModeTransform.toLinearMap,
    Matrix.toLpLin_apply] at hResponse
  convert hResponse using 1
  all_goals rfl

/-- The compiled all-pass frequency response has the exact non-real quadrature entry. -/
lemma allPassRationalNetlist_frequency_quadrature_response_entry :
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).frequencyResponse
        (fun _ : Fin 1 ↦ 1) allPassRationalNetlistFrequencyQuadratureDomain
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      75 / 109 + (32 / 109) * Complex.I := by
  change ((((allPassRationalNetlist
    allPassRationalQuadratureParameters).laplace (fun _ : Fin 1 ↦ 1)).response
      allPassRationalNetlistFrequencyQuadratureDomain).reindex
        (Incident.relabelEquiv ((allPassRationalNetlist
          allPassRationalQuadratureParameters).laplaceExternalChannelEquiv
            (fun _ : Fin 1 ↦ 1)))
        (Outgoing.relabelEquiv ((allPassRationalNetlist
          allPassRationalQuadratureParameters).laplaceExternalChannelEquiv
            (fun _ : Fin 1 ↦ 1))))
      (Outgoing.mk (allPassRationalFormalThroughChannel
        allPassRationalQuadratureParameters))
      (Incident.mk (allPassRationalFormalInputChannel
        allPassRationalQuadratureParameters)) = _
  have hDomainProof : allPassRationalNetlistFrequencyQuadratureDomain =
      allPassRationalNetlistLaplaceQuadratureDomain := Subsingleton.elim _ _
  rw [hDomainProof]
  have hMapped :=
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).response_laplace_reindex_of_evaluation_eq
        (fun _ : Fin 1 => 1) allPassRationalNetlistLaplaceQuadratureDomain
        laplaceEvaluation_quadrature allPassRationalQuadratureDomain
  have hEntry := congrArg
    (fun response => response
      (Outgoing.mk (allPassRationalFormalThroughChannel
        allPassRationalQuadratureParameters))
      (Incident.mk (allPassRationalFormalInputChannel
        allPassRationalQuadratureParameters))) hMapped
  exact hEntry.trans allPassRationalNetlist_quadrature_compiled_entry_via_equations

/-- At quadrature, the selected proof-gated frequency entry equals the reciprocal-Z entry at
`z = I`. -/
lemma allPassRationalNetlist_frequency_eq_reciprocalZ_quadrature_entry :
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).frequencyResponse
        (fun _ : Fin 1 ↦ 1) allPassRationalNetlistFrequencyQuadratureDomain
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      ((allPassRationalNetlist
        allPassRationalQuadratureParameters).reciprocalZ.response
          allPassRationalNetlistReciprocalZQuadratureDomain).reindex
            (Incident.relabelEquiv ((allPassRationalNetlist
              allPassRationalQuadratureParameters).reciprocalZExternalChannelEquiv))
            (Outgoing.relabelEquiv ((allPassRationalNetlist
              allPassRationalQuadratureParameters).reciprocalZExternalChannelEquiv))
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) := by
  rw [allPassRationalNetlist_frequency_quadrature_response_entry]
  symm
  have hMapped :=
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).response_reciprocalZ_reindex_of_evaluation_eq
        allPassRationalNetlistReciprocalZQuadratureDomain
        zInverseEvaluation_quadrature allPassRationalQuadratureDomain
  have hEntry := congrArg
    (fun response => response
      (Outgoing.mk (allPassRationalFormalThroughChannel
        allPassRationalQuadratureParameters))
      (Incident.mk (allPassRationalFormalInputChannel
        allPassRationalQuadratureParameters))) hMapped
  exact hEntry.trans allPassRationalNetlist_quadrature_compiled_entry_via_equations

end

end Optics.DelayTransfer
