/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Physlib.Optics.Systems.DelayTransfer.FrequencyResponseRegression
public import Physlib.Optics.Systems.DelayTransfer.GroupDelay

/-!
# Regression tests for local group delay and dispersion

## i. Overview

The scalar response
`exp (-I * (delay * ω + dispersion * ω² / 2))` is nonzero everywhere. Its local group
delay is exactly `delay + dispersion * ω`, and its group-delay dispersion is exactly the
coefficient named `dispersion`. Exact rational instances test both the negative exponential sign
and a nonzero dispersion value. A separate zero-crossing fixture proves that differentiability
alone does not enter the logarithmic-derivative domain. The compiled all-pass fixture uses
`t = 3/5`, `κ = 4/5`, `a = 1/2`, unit delay, and `ω₀ = π/2`. Direct channel-equation solving and
an independently differentiated scalar extension give its exact network group delay
`2176/6649`.

## ii. Key results

- `chirpedDelayResponse`: a nonvanishing response with quadratic local phase.
- `chirpedDelayResponse_localGroupDelay`: its exact affine group delay.
- `chirpedDelayResponse_localGroupDelayDispersion`: its exact constant dispersion.
- `pureDelay_groupDelay_three`: the negative-exponential sign anchor.
- `chirpedDelay_groupDelay_at_five`: a nonzero-dispersion value anchor.
- `zeroCrossing_not_mem_localLogDerivativeDomain`: the required zero guard.
- `allPassRationalNetlist_frequencyGroupDelay_quadrature`: the compiled-network value anchor.

## iii. Table of contents

- A. Quadratic-phase response
- B. Exact sign, dispersion, and zero-domain anchors
- C. Compiled all-pass group-delay anchor

## iv. References and non-claims

The local logarithmic-derivative domains and totalized quantities are defined in
`Physlib/Optics/Systems/DelayTransfer/GroupDelay.lean:76-185`. This regression derives exact
values from a displayed scalar derivative and cancellation; it does not use `Complex.arg` or a
global phase branch.
The selected delay convention `q = exp (-I * ω * τ)` is defined in
`Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:81-94`.
The rational all-pass fixture is defined in
`Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:220-280`, and its solve helper
expands the three channel equations through `mem_behavior_iff_equations` in that file at
lines 845-912.

Only the displayed compiled all-pass network is differentiated. General N5F interior
differentiability remains withheld, and the production network formulas require user-supplied
local regularity. No material-dispersion law, rational-in-frequency result, time-domain causality
statement, passivity claim, units assignment, or source-parity claim is made. The coefficient
called dispersion is literally the derivative of the displayed local group delay.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-!

## A. Quadratic-phase response

-/

/-- A nonvanishing scalar response with phase
`-(delay * ω + dispersion * ω² / 2)`.
-/
def chirpedDelayResponse (delay dispersion angularFrequency : ℝ) : ℂ :=
  Complex.exp
    (-Complex.I *
      ((delay : ℂ) * angularFrequency +
        (dispersion : ℂ) / 2 * (angularFrequency : ℂ) ^ 2))

/-- The quadratic-phase response never vanishes. -/
lemma chirpedDelayResponse_ne_zero (delay dispersion angularFrequency : ℝ) :
    chirpedDelayResponse delay dispersion angularFrequency ≠ 0 :=
  Complex.exp_ne_zero _

/-- The exact real-frequency derivative of the quadratic-phase response. -/
lemma hasDerivAt_chirpedDelayResponse (delay dispersion angularFrequency : ℝ) :
    HasDerivAt (chirpedDelayResponse delay dispersion)
      (chirpedDelayResponse delay dispersion angularFrequency *
        (-Complex.I *
          ((delay : ℂ) + (dispersion : ℂ) * angularFrequency)))
      angularFrequency := by
  have hFrequency : HasDerivAt (fun frequency : ℝ => (frequency : ℂ)) 1
      angularFrequency := (hasDerivAt_id angularFrequency).ofReal_comp
  have hLinear := hFrequency.const_mul (delay : ℂ)
  have hQuadratic := (hFrequency.pow 2).const_mul ((dispersion : ℂ) / 2)
  have hExponent := (hLinear.add hQuadratic).const_mul (-Complex.I)
  refine hExponent.cexp.congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply, mul_one, Nat.reduceSub, pow_one,
    chirpedDelayResponse]
  ring

/-- Every frequency lies in the local logarithmic-derivative domain. -/
lemma chirpedDelayResponse_localLogDerivativeDomain (delay dispersion : ℝ) :
    localLogDerivativeDomain (chirpedDelayResponse delay dispersion) = Set.univ := by
  ext angularFrequency
  simp only [Set.mem_univ, iff_true]
  exact mem_localLogDerivativeDomain_of_hasDerivAt
    (hasDerivAt_chirpedDelayResponse delay dispersion angularFrequency)
    (chirpedDelayResponse_ne_zero delay dispersion angularFrequency)

/-- The quadratic-phase response has affine local group delay
`delay + dispersion * ω`.
-/
lemma chirpedDelayResponse_localGroupDelay (delay dispersion angularFrequency : ℝ) :
    localGroupDelay (chirpedDelayResponse delay dispersion) angularFrequency =
      delay + dispersion * angularFrequency := by
  rw [localGroupDelay_eq_of_hasDerivAt
    (hasDerivAt_chirpedDelayResponse delay dispersion angularFrequency)
    (chirpedDelayResponse_ne_zero delay dispersion angularFrequency)]
  have hCancel :
      (chirpedDelayResponse delay dispersion angularFrequency *
          (-Complex.I *
            ((delay : ℂ) + (dispersion : ℂ) * angularFrequency))) /
          chirpedDelayResponse delay dispersion angularFrequency =
        -Complex.I *
          ((delay : ℂ) + (dispersion : ℂ) * angularFrequency) := by
    field_simp [chirpedDelayResponse_ne_zero]
  rw [hCancel]
  simp [Complex.mul_im]

/-- Every frequency lies in the local group-delay-dispersion domain. -/
lemma chirpedDelayResponse_localGroupDelayDispersionDomain (delay dispersion : ℝ) :
    localGroupDelayDispersionDomain (chirpedDelayResponse delay dispersion) = Set.univ := by
  ext angularFrequency
  simp only [Set.mem_univ, iff_true]
  rw [mem_localGroupDelayDispersionDomain_iff]
  refine ⟨(hasDerivAt_chirpedDelayResponse delay dispersion
    angularFrequency).differentiableAt,
    chirpedDelayResponse_ne_zero delay dispersion angularFrequency, ?_⟩
  have hGroupDelay : localGroupDelay (chirpedDelayResponse delay dispersion) =
      fun frequency => delay + dispersion * frequency := by
    funext frequency
    exact chirpedDelayResponse_localGroupDelay delay dispersion frequency
  rw [hGroupDelay]
  fun_prop

/-- The quadratic-phase response has constant local group-delay dispersion. -/
lemma chirpedDelayResponse_localGroupDelayDispersion
    (delay dispersion angularFrequency : ℝ) :
    localGroupDelayDispersion (chirpedDelayResponse delay dispersion) angularFrequency =
      dispersion := by
  have hGroupDelay : localGroupDelay (chirpedDelayResponse delay dispersion) =
      fun frequency => delay + dispersion * frequency := by
    funext frequency
    exact chirpedDelayResponse_localGroupDelay delay dispersion frequency
  rw [localGroupDelayDispersion, hGroupDelay]
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id angularFrequency).const_mul dispersion).const_add delay).deriv

/-!

## B. Exact sign, dispersion, and zero-domain anchors

-/

/-- A pure delay of three has local group delay three under the selected negative exponential. -/
lemma pureDelay_groupDelay_three :
    localGroupDelay (chirpedDelayResponse 3 0) 7 = 3 := by
  rw [chirpedDelayResponse_localGroupDelay]
  norm_num

/-- A response with delay `3/2` and dispersion `2/5` has group delay `7/2` at `ω = 5`. -/
lemma chirpedDelay_groupDelay_at_five :
    localGroupDelay (chirpedDelayResponse (3 / 2) (2 / 5)) 5 = 7 / 2 := by
  rw [chirpedDelayResponse_localGroupDelay]
  norm_num

/-- The same nonzero-dispersion fixture has group-delay dispersion `2/5`. -/
lemma chirpedDelay_dispersion_two_fifths :
    localGroupDelayDispersion (chirpedDelayResponse (3 / 2) (2 / 5)) 5 = 2 / 5 := by
  rw [chirpedDelayResponse_localGroupDelayDispersion]

/-- A differentiable scalar response that crosses zero. -/
def zeroCrossingResponse (angularFrequency : ℝ) : ℂ :=
  angularFrequency

/-- Differentiability alone does not put a zero response in the logarithmic-derivative domain. -/
lemma zeroCrossing_not_mem_localLogDerivativeDomain :
    0 ∉ localLogDerivativeDomain zeroCrossingResponse := by
  rw [mem_localLogDerivativeDomain_iff]
  simp [zeroCrossingResponse]

/-!

## C. Compiled all-pass group-delay anchor

-/

/-- The rational all-pass fixture retains finite aggregate channels. -/
local instance groupDelayAllPassChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).Channel :=
  AllPass.channelFintype p

/-- The rational all-pass fixture retains finite connected channels. -/
local instance groupDelayAllPassConnectedChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).ConnectedChannel :=
  AllPass.connectedChannelFintype p

/-- Compilation retains finite aggregate all-pass channels. -/
local instance groupDelayAllPassCompileChannelFintype (p : AllPass.Parameters)
    (value : DelayTuple 1) :
    Fintype ((allPassRationalNetlist p).compile value).Channel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).Channel)

/-- Compilation retains finite connected all-pass channels. -/
local instance groupDelayAllPassCompileConnectedChannelFintype
    (p : AllPass.Parameters) (value : DelayTuple 1) :
    Fintype ((allPassRationalNetlist p).compile value).ConnectedChannel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).ConnectedChannel)

/-- Laplace reparameterization retains finite aggregate all-pass channels. -/
local instance groupDelayAllPassLaplaceChannelFintype (p : AllPass.Parameters)
    (delays : Fin 1 → ℝ) :
    Fintype ((allPassRationalNetlist p).laplace delays).Channel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).Channel)

/-- Laplace reparameterization retains finite connected all-pass channels. -/
local instance groupDelayAllPassLaplaceConnectedChannelFintype
    (p : AllPass.Parameters) (delays : Fin 1 → ℝ) :
    Fintype ((allPassRationalNetlist p).laplace delays).ConnectedChannel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).ConnectedChannel)

/-- The physical all-pass parameters whose phase follows angular frequency. -/
def groupDelayAllPassFrequencyParameters (angularFrequency : ℝ) :
    AllPass.Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
  fieldAttenuation := 1 / 2
  roundTripPhase := (angularFrequency : Real.Angle)

/-- The unit-delay formal value `q(ω) = exp (-I * ω)`. -/
def groupDelayAllPassFrequencyDelay (angularFrequency : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (angularFrequency : ℂ))

/-- The displayed scalar extension independently differentiated below. -/
def groupDelayAllPassExtension (angularFrequency : ℝ) : ℂ :=
  ((3 / 5 : ℂ) -
      (1 / 2 : ℂ) * groupDelayAllPassFrequencyDelay angularFrequency) /
    (1 - (3 / 10 : ℂ) * groupDelayAllPassFrequencyDelay angularFrequency)

/-- The unit-delay formal value has norm one. -/
lemma groupDelayAllPassFrequencyDelay_norm (angularFrequency : ℝ) :
    ‖groupDelayAllPassFrequencyDelay angularFrequency‖ = 1 := by
  rw [groupDelayAllPassFrequencyDelay]
  have hExponent : -Complex.I * (angularFrequency : ℂ) =
      (((-angularFrequency : ℝ) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [hExponent, Complex.norm_exp_ofReal_mul_I]

/-- Every member of the variable-phase all-pass family satisfies component validity. -/
lemma groupDelayAllPassFrequencyParameters_isValid (angularFrequency : ℝ) :
    (groupDelayAllPassFrequencyParameters angularFrequency).IsValid := by
  constructor
  · constructor
    · norm_num [groupDelayAllPassFrequencyParameters,
        DirectionalCoupler.Parameters.IsValid]
    · constructor
      · norm_num [groupDelayAllPassFrequencyParameters,
          DirectionalCoupler.Parameters.IsValid]
      · norm_num [groupDelayAllPassFrequencyParameters,
          DirectionalCoupler.Parameters.IsUnitary,
          DirectionalCoupler.Parameters.powerFactor]
  · norm_num [groupDelayAllPassFrequencyParameters,
      MatchedPropagation.Parameters.IsValid]

/-- The variable physical phase is carried by the formal delay value after compilation. -/
lemma groupDelayAllPass_compiled_eq (angularFrequency : ℝ) :
    (allPassRationalNetlist
      (groupDelayAllPassFrequencyParameters angularFrequency)).compile
        (fun _ : Fin 1 ↦ groupDelayAllPassFrequencyDelay angularFrequency) =
      (allPassRationalNetlist allPassRationalQuadratureParameters).compile
        (fun _ : Fin 1 ↦ groupDelayAllPassFrequencyDelay angularFrequency) := by
  rfl

/-- The variable-phase fixture has one-pass coefficient `(1/2) * q(ω)`. -/
lemma groupDelayAllPass_loopCoefficient (angularFrequency : ℝ) :
    (groupDelayAllPassFrequencyParameters angularFrequency).loopCoefficient =
      ((1 / 2 : ℝ) : ℂ) *
        groupDelayAllPassFrequencyDelay angularFrequency := by
  simp [groupDelayAllPassFrequencyParameters, groupDelayAllPassFrequencyDelay,
    AllPass.Parameters.loopCoefficient, AllPass.Parameters.propagation,
    MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe,
    Circle.coe_exp, ← Complex.exp_neg]
  congr 1
  ring

/-- The variable-phase fixture has denominator `1 - (3/10) * q(ω)`. -/
lemma groupDelayAllPass_denominator (angularFrequency : ℝ) :
    (groupDelayAllPassFrequencyParameters angularFrequency).denominator =
      1 - (3 / 10 : ℂ) *
        groupDelayAllPassFrequencyDelay angularFrequency := by
  rw [AllPass.Parameters.denominator, AllPass.Parameters.loopGain]
  rw [groupDelayAllPass_loopCoefficient]
  norm_num [groupDelayAllPassFrequencyParameters]
  ring

/-- The displayed feedback denominator is nonzero at every real frequency. -/
lemma groupDelayAllPass_hasNonzeroDenominator (angularFrequency : ℝ) :
    (groupDelayAllPassFrequencyParameters
      angularFrequency).HasNonzeroDenominator := by
  rw [AllPass.Parameters.HasNonzeroDenominator,
    groupDelayAllPass_denominator]
  intro hZero
  have hEqual :
      (3 / 10 : ℂ) * groupDelayAllPassFrequencyDelay angularFrequency = 1 :=
    (sub_eq_zero.mp hZero).symm
  have hNorm := congrArg norm hEqual
  rw [norm_mul, groupDelayAllPassFrequencyDelay_norm, norm_one, mul_one] at hNorm
  norm_num at hNorm

/-- Direct all-pass algebra equals the displayed scalar extension. -/
lemma groupDelayAllPass_throughTransfer_eq_extension (angularFrequency : ℝ) :
    AllPass.throughTransfer
        (groupDelayAllPassFrequencyParameters angularFrequency) =
      groupDelayAllPassExtension angularFrequency := by
  rw [AllPass.throughTransfer, groupDelayAllPassExtension,
    groupDelayAllPass_denominator]
  rw [groupDelayAllPass_loopCoefficient]
  simp only [groupDelayAllPassFrequencyParameters,
    AllPass.Parameters.coupler, DirectionalCoupler.crossCoefficient]
  have hDenominator :
      1 - (3 / 10 : ℂ) *
        groupDelayAllPassFrequencyDelay angularFrequency ≠ 0 := by
    simpa [AllPass.Parameters.HasNonzeroDenominator,
      groupDelayAllPass_denominator] using
        groupDelayAllPass_hasNonzeroDenominator angularFrequency
  apply (eq_div_iff hDenominator).2
  rw [add_mul, div_mul_cancel₀ _ hDenominator]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The production unit-delay frequency map is the displayed formal value. -/
lemma groupDelayAllPass_frequencyDelayEvaluation (angularFrequency : ℝ) :
    frequencyDelayEvaluation (fun _ : Fin 1 ↦ 1) angularFrequency =
      (fun _ ↦ groupDelayAllPassFrequencyDelay angularFrequency) := by
  funext i
  rw [frequencyDelayEvaluation_apply, groupDelayAllPassFrequencyDelay]
  congr 1
  push_cast
  ring

/-- Every real frequency lies in the fixed rational netlist's formal response domain. -/
lemma groupDelayAllPassFormalDomain (angularFrequency : ℝ) :
    (fun _ : Fin 1 ↦ groupDelayAllPassFrequencyDelay angularFrequency) ∈
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).toParameterizedNetlist.responseDomain := by
  change
    ((allPassRationalNetlist allPassRationalQuadratureParameters).compile
        (fun _ : Fin 1 ↦ groupDelayAllPassFrequencyDelay angularFrequency)).IsWellPosed ∧
      (fun _ : Fin 1 ↦ groupDelayAllPassFrequencyDelay angularFrequency) ∈
        (allPassRationalNetlist
          allPassRationalQuadratureParameters).toParameterizedNetlist.components.validityDomain
  constructor
  · exact allPassRationalNetlist_isWellPosed
      (groupDelayAllPassFrequencyParameters angularFrequency)
      (groupDelayAllPassFrequencyDelay angularFrequency)
      (groupDelayAllPass_loopCoefficient angularFrequency)
      (groupDelayAllPass_hasNonzeroDenominator angularFrequency)
  · intro component
    exact allPassRationalComponents_isValidAt
      allPassRationalQuadratureParameters allPassRational_quadrature_isValid
      (fun _ ↦ groupDelayAllPassFrequencyDelay angularFrequency) component

/-- Every real frequency lies in the fixed network's proof-gated response domain. -/
lemma groupDelayAllPassFrequencyDomain (angularFrequency : ℝ) :
    angularFrequency ∈
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).frequencyResponseDomain
          (fun _ : Fin 1 ↦ 1) := by
  rw [(allPassRationalNetlist
    allPassRationalQuadratureParameters).mem_frequencyResponseDomain_iff,
    groupDelayAllPass_frequencyDelayEvaluation]
  exact groupDelayAllPassFormalDomain angularFrequency

/-- The quadrature point is interior to the proof-gated response domain. -/
lemma groupDelayAllPassFrequencyInterior : Real.pi / 2 ∈
    interior
      ((allPassRationalNetlist
        allPassRationalQuadratureParameters).frequencyResponseDomain
          (fun _ : Fin 1 ↦ 1)) := by
  have hDomain :
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).frequencyResponseDomain
          (fun _ : Fin 1 ↦ 1) = Set.univ := by
    exact Set.eq_univ_of_forall groupDelayAllPassFrequencyDomain
  rw [hDomain]
  simp

/-- Raw compiled channel equations give the displayed response at every real frequency.

The proof invokes the all-pass solve helper that expands `mem_behavior_iff_equations`; it does
not use a prior proof-gated response-value anchor or a group-delay identity.
-/
lemma groupDelayAllPass_compiledResponse_eq_extension (angularFrequency : ℝ) :
    (((allPassRationalNetlist allPassRationalQuadratureParameters).compile
        (fun _ : Fin 1 ↦ groupDelayAllPassFrequencyDelay angularFrequency)).responseTransform
          (groupDelayAllPassFormalDomain angularFrequency).1)
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      groupDelayAllPassExtension angularFrequency := by
  have hAuxiliaryDomain := allPassRationalNetlist_mem_responseDomain
    (groupDelayAllPassFrequencyParameters angularFrequency)
    (groupDelayAllPassFrequencyDelay angularFrequency)
    (groupDelayAllPass_loopCoefficient angularFrequency)
    (groupDelayAllPassFrequencyParameters_isValid angularFrequency)
    (groupDelayAllPass_hasNonzeroDenominator angularFrequency)
  have hResponse := allPassRationalNetlist_responseThrough
    (groupDelayAllPassFrequencyParameters angularFrequency)
    (groupDelayAllPassFrequencyDelay angularFrequency)
    (groupDelayAllPass_loopCoefficient angularFrequency) hAuxiliaryDomain
    (groupDelayAllPass_hasNonzeroDenominator angularFrequency) 1
  rw [groupDelayAllPass_throughTransfer_eq_extension] at hResponse
  simp [allPassRationalInputAmplitude, ModeTransform.toLinearMap,
    Matrix.toLpLin_apply] at hResponse
  convert hResponse using 1
  all_goals rfl

/-- The proof-gated frequency response agrees with the independently displayed extension. -/
lemma groupDelayAllPass_frequencyResponse_eq_extension (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).frequencyResponseDomain
          (fun _ : Fin 1 ↦ 1)) :
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).frequencyResponse
        (fun _ : Fin 1 ↦ 1) hFrequency
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters)) =
      groupDelayAllPassExtension angularFrequency := by
  change ((((allPassRationalNetlist
    allPassRationalQuadratureParameters).laplace (fun _ : Fin 1 ↦ 1)).response
      hFrequency).reindex
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
  have hLaplaceEvaluation :
      laplaceEvaluation (fun _ : Fin 1 ↦ 1)
          (imaginaryFrequency angularFrequency) =
        (fun _ ↦ groupDelayAllPassFrequencyDelay angularFrequency) := by
    exact groupDelayAllPass_frequencyDelayEvaluation angularFrequency
  have hMapped :=
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).response_laplace_reindex_of_evaluation_eq
        (fun _ : Fin 1 ↦ 1) hFrequency hLaplaceEvaluation
        (groupDelayAllPassFormalDomain angularFrequency)
  have hEntry := congrArg
    (fun response => response
      (Outgoing.mk (allPassRationalFormalThroughChannel
        allPassRationalQuadratureParameters))
      (Incident.mk (allPassRationalFormalInputChannel
        allPassRationalQuadratureParameters))) hMapped
  exact hEntry.trans (by
    change (((allPassRationalNetlist
      allPassRationalQuadratureParameters).compile
        (fun _ : Fin 1 ↦ groupDelayAllPassFrequencyDelay angularFrequency)).responseTransform _)
          (Outgoing.mk (allPassRationalFormalThroughChannel
            allPassRationalQuadratureParameters))
          (Incident.mk (allPassRationalFormalInputChannel
            allPassRationalQuadratureParameters)) = _
    convert groupDelayAllPass_compiledResponse_eq_extension angularFrequency using 1
    congr 1)

/-- The exact derivative of the unit-delay formal value. -/
lemma hasDerivAt_groupDelayAllPassFrequencyDelay (angularFrequency : ℝ) :
    HasDerivAt groupDelayAllPassFrequencyDelay
      (-Complex.I * groupDelayAllPassFrequencyDelay angularFrequency)
      angularFrequency := by
  have hFrequency : HasDerivAt (fun frequency : ℝ => (frequency : ℂ)) 1
      angularFrequency := (hasDerivAt_id angularFrequency).ofReal_comp
  have hExponent := hFrequency.const_mul (-Complex.I)
  refine hExponent.cexp.congr_deriv ?_
  simp only [groupDelayAllPassFrequencyDelay]
  ring

/-- At quadrature the independently displayed unit-delay value is `-I`. -/
lemma groupDelayAllPassFrequencyDelay_quadrature :
    groupDelayAllPassFrequencyDelay (Real.pi / 2) = -Complex.I := by
  rw [groupDelayAllPassFrequencyDelay]
  have hExponent :
      -Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        ((-(Real.pi / 2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hExponent, Complex.exp_mul_I]
  simp

/-- Hand expansion of the displayed extension at quadrature. -/
lemma groupDelayAllPassExtension_quadrature :
    groupDelayAllPassExtension (Real.pi / 2) =
      75 / 109 + (32 / 109) * Complex.I := by
  rw [groupDelayAllPassExtension,
    groupDelayAllPassFrequencyDelay_quadrature]
  have hInverse : (1 + (3 / 10 : ℂ) * Complex.I)⁻¹ =
      (100 - 30 * Complex.I) / 109 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring_nf
    norm_num [Complex.I_sq]
  rw [div_eq_mul_inv]
  have hDenominator :
      1 - (3 / 10 : ℂ) * -Complex.I =
        1 + (3 / 10 : ℂ) * Complex.I := by
    ring
  rw [hDenominator, hInverse]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The quotient-rule derivative displayed independently of the network response. -/
def groupDelayAllPassExtensionDerivative (angularFrequency : ℝ) : ℂ :=
  (((-1 / 2 : ℂ) *
      (-Complex.I * groupDelayAllPassFrequencyDelay angularFrequency)) *
      (1 - (3 / 10 : ℂ) * groupDelayAllPassFrequencyDelay angularFrequency) -
    ((3 / 5 : ℂ) -
        (1 / 2 : ℂ) * groupDelayAllPassFrequencyDelay angularFrequency) *
      ((-3 / 10 : ℂ) *
        (-Complex.I * groupDelayAllPassFrequencyDelay angularFrequency))) /
    (1 - (3 / 10 : ℂ) *
      groupDelayAllPassFrequencyDelay angularFrequency) ^ 2

/-- The scalar extension has its displayed quotient-rule derivative. -/
lemma hasDerivAt_groupDelayAllPassExtension (angularFrequency : ℝ) :
    HasDerivAt groupDelayAllPassExtension
      (groupDelayAllPassExtensionDerivative angularFrequency)
      angularFrequency := by
  have hDelay := hasDerivAt_groupDelayAllPassFrequencyDelay angularFrequency
  have hNumerator :=
    (hDelay.const_mul (1 / 2 : ℂ)).const_sub (3 / 5 : ℂ)
  have hDenominator :=
    (hDelay.const_mul (3 / 10 : ℂ)).const_sub (1 : ℂ)
  have hDenominatorNonzero :
      1 - (3 / 10 : ℂ) *
        groupDelayAllPassFrequencyDelay angularFrequency ≠ 0 := by
    simpa [AllPass.Parameters.HasNonzeroDenominator,
      groupDelayAllPass_denominator] using
        groupDelayAllPass_hasNonzeroDenominator angularFrequency
  have hQuotient := hNumerator.div hDenominator hDenominatorNonzero
  have hFunctions : groupDelayAllPassExtension =
      ((fun frequency => (3 / 5 : ℂ) -
          (1 / 2 : ℂ) * groupDelayAllPassFrequencyDelay frequency) /
        fun frequency => 1 -
          (3 / 10 : ℂ) * groupDelayAllPassFrequencyDelay frequency) := by
    funext frequency
    rfl
  have hSameFunction := hQuotient.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun frequency : ℝ =>
      congrFun hFunctions frequency))
  refine hSameFunction.congr_deriv ?_
  rw [groupDelayAllPassExtensionDerivative]
  ring

/-- Independent differentiation gives the exact quadrature derivative. -/
lemma hasDerivAt_groupDelayAllPassExtension_quadrature :
    HasDerivAt groupDelayAllPassExtension
      ((2912 / 11881 : ℂ) - (1920 / 11881) * Complex.I)
      (Real.pi / 2) := by
  refine (hasDerivAt_groupDelayAllPassExtension (Real.pi / 2)).congr_deriv ?_
  rw [groupDelayAllPassExtensionDerivative,
    groupDelayAllPassFrequencyDelay_quadrature]
  have hDenominator :
      1 - (3 / 10 : ℂ) * -Complex.I =
        1 + (3 / 10 : ℂ) * Complex.I := by
    ring
  rw [hDenominator]
  have hInverse : (1 + (3 / 10 : ℂ) * Complex.I)⁻¹ =
      (100 - 30 * Complex.I) / 109 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring_nf
    norm_num [Complex.I_sq]
  rw [div_eq_mul_inv, ← inv_pow, hInverse]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The exact quadrature response value is nonzero. -/
lemma groupDelayAllPassExtension_quadrature_ne_zero :
    groupDelayAllPassExtension (Real.pi / 2) ≠ 0 := by
  rw [groupDelayAllPassExtension_quadrature]
  intro hZero
  have hReal := congrArg Complex.re hZero
  norm_num at hReal

/-- The compiled all-pass through entry has exact group delay `2176/6649` at quadrature. -/
lemma allPassRationalNetlist_frequencyGroupDelay_quadrature :
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).frequencyGroupDelay
        (fun _ : Fin 1 ↦ 1)
        (Outgoing.mk (allPassRationalFormalThroughChannel
          allPassRationalQuadratureParameters))
        (Incident.mk (allPassRationalFormalInputChannel
          allPassRationalQuadratureParameters))
        (Real.pi / 2) = 2176 / 6649 := by
  rw [(allPassRationalNetlist
    allPassRationalQuadratureParameters).frequencyGroupDelay_eq_of_extension_hasDerivAt
      (fun _ : Fin 1 ↦ 1)
      (Outgoing.mk (allPassRationalFormalThroughChannel
        allPassRationalQuadratureParameters))
      (Incident.mk (allPassRationalFormalInputChannel
        allPassRationalQuadratureParameters))
      groupDelayAllPassFrequencyInterior
      (fun frequency hFrequency =>
        (groupDelayAllPass_frequencyResponse_eq_extension
          frequency hFrequency).symm)
      hasDerivAt_groupDelayAllPassExtension_quadrature
      groupDelayAllPassExtension_quadrature_ne_zero]
  rw [groupDelayAllPassExtension_quadrature]
  have hInverse :
      (75 / 109 + (32 / 109 : ℂ) * Complex.I)⁻¹ =
        8175 / 6649 - (3488 / 6649) * Complex.I := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring_nf
    norm_num [Complex.I_sq]
  rw [div_eq_mul_inv, hInverse]
  norm_num [Complex.mul_im]

end

end Optics.DelayTransfer
