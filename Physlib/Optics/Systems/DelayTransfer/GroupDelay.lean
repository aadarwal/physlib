/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.FrequencyResponse

/-!
# Local logarithmic derivatives, group delay, and dispersion

## i. Overview

For a scalar complex response `response : ℝ → ℂ`, the local logarithmic derivative is
`response'(ω) / response(ω)`. It is assigned that meaning only where `response` is real-
differentiable and nonzero. The local group delay is the negative imaginary part of this ratio.
Its dispersion is the real derivative of local group delay, and is assigned that meaning only
where this second derivative exists.

No complex argument is selected. The congruence results show that these quantities depend only
on the germ of the complex response near the point, so no global phase branch or phase unwrap is
used. For an N5F frequency-response entry, the audited domain additionally requires the frequency
to lie in the interior of the proof-gated response domain. This makes the arbitrary value of the
total extension outside that domain locally irrelevant.

## ii. Key results

- `localLogDerivativeDomain`: differentiability and a nonzero response value.
- `eventually_ne_zero_of_mem_localLogDerivativeDomain`: the audited zero-free germ.
- `localLogDerivative`: the totalized quotient `response' / response`.
- `localGroupDelay`: the negative imaginary part of the local logarithmic derivative.
- `localGroupDelayDispersionDomain`: the exact additional derivative gate.
- `localGroupDelayDispersion`: the derivative of local group delay.
- `RationalNetlist.frequencyResponseEntry`: a total extension of one proof-gated entry.
- `RationalNetlist.frequencyGroupDelayDomain`: local N5F well-posedness plus scalar gates.
- `RationalNetlist.frequencyGroupDelay_eq_of_extension_hasDerivAt`: local extension formula.
- `RationalNetlist.frequencyGroupDelayDispersion_eq_of_extension_hasDerivAt`: dispersion formula.

## iii. Table of contents

- A. Scalar local logarithmic derivatives
- B. Proof-gated frequency-response entries

## iv. References

The proof-gated frequency response and its exact domain are defined in
`Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:174-203`. The underlying N5F
response domain combines solve-domain membership with retained component validity, as documented
in `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:16-24`; neither gate is removed here.

This is the Physlib-original extension requested by `goal.md:2269-2271`; the source claim is
unverified. Mathlib defines `deriv` to be zero when a derivative does not exist in
`Mathlib/Analysis/Calculus/Deriv/Basic.lean:148-154`. The definitions here are total functions,
but no group-delay or dispersion interpretation is asserted outside the named domains. General
N5F interior differentiability is withheld. Both network formulas are conditional on
user-supplied local regularity: an agreeing extension with `HasDerivAt` for the displayed
derivative or derivatives. There is
no global `Complex.arg`, phase-unwrapping, continuity-across-zeros,
rational-in-physical-frequency, time-domain causality, passivity, material-dispersion, or units
claim. In particular, the quantity named dispersion below is literally the angular-frequency
derivative of local group delay, not a constitutive material dispersion law.

-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Filter Set Topology

/-!

## A. Scalar local logarithmic derivatives

-/

/-- Frequencies where a scalar complex response is differentiable and nonzero. -/
def localLogDerivativeDomain (response : ℝ → ℂ) : Set ℝ :=
  {ω | DifferentiableAt ℝ response ω ∧ response ω ≠ 0}

/-- The totalized local logarithmic derivative `response'(ω) / response(ω)`.

It has logarithmic-derivative meaning only on `localLogDerivativeDomain response`.
-/
noncomputable def localLogDerivative (response : ℝ → ℂ) (ω : ℝ) : ℂ :=
  deriv response ω / response ω

/-- Local group delay, defined as `-Im (response'(ω) / response(ω))`.

It has group-delay meaning only on `localLogDerivativeDomain response`.
-/
noncomputable def localGroupDelay (response : ℝ → ℂ) (ω : ℝ) : ℝ :=
  -(localLogDerivative response ω).im

/-- Frequencies where local group delay has the derivative used as dispersion. -/
def localGroupDelayDispersionDomain (response : ℝ → ℂ) : Set ℝ :=
  {ω | ω ∈ localLogDerivativeDomain response ∧
    DifferentiableAt ℝ (localGroupDelay response) ω}

/-- The totalized angular-frequency derivative of local group delay.

It has group-delay-dispersion meaning only on `localGroupDelayDispersionDomain response`.
-/
noncomputable def localGroupDelayDispersion (response : ℝ → ℂ) (ω : ℝ) : ℝ :=
  deriv (localGroupDelay response) ω

/-- Membership in the logarithmic-derivative domain states its two exact gates. -/
lemma mem_localLogDerivativeDomain_iff (response : ℝ → ℂ) (ω : ℝ) :
    ω ∈ localLogDerivativeDomain response ↔
      DifferentiableAt ℝ response ω ∧ response ω ≠ 0 :=
  Iff.rfl

/-- Membership in the logarithmic-derivative domain gives a zero-free response germ. -/
lemma eventually_ne_zero_of_mem_localLogDerivativeDomain {response : ℝ → ℂ} {ω : ℝ}
    (hDomain : ω ∈ localLogDerivativeDomain response) :
    ∀ᶠ frequency in 𝓝 ω, response frequency ≠ 0 :=
  hDomain.1.continuousAt.eventually_ne hDomain.2

/-- A displayed derivative and a nonzero value put a point in the local domain. -/
lemma mem_localLogDerivativeDomain_of_hasDerivAt {response : ℝ → ℂ} {ω : ℝ}
    {responseDerivative : ℂ} (hDerivative : HasDerivAt response responseDerivative ω)
    (hNonzero : response ω ≠ 0) : ω ∈ localLogDerivativeDomain response :=
  ⟨hDerivative.differentiableAt, hNonzero⟩

/-- On its domain, a displayed derivative computes the local logarithmic derivative. -/
lemma localLogDerivative_eq_of_hasDerivAt {response : ℝ → ℂ} {ω : ℝ}
    {responseDerivative : ℂ} (hDerivative : HasDerivAt response responseDerivative ω)
    (_hNonzero : response ω ≠ 0) :
    localLogDerivative response ω = responseDerivative / response ω := by
  rw [localLogDerivative, hDerivative.deriv]

/-- On its domain, a displayed derivative computes local group delay. -/
lemma localGroupDelay_eq_of_hasDerivAt {response : ℝ → ℂ} {ω : ℝ}
    {responseDerivative : ℂ} (hDerivative : HasDerivAt response responseDerivative ω)
    (hNonzero : response ω ≠ 0) :
    localGroupDelay response ω = -(responseDerivative / response ω).im := by
  rw [localGroupDelay, localLogDerivative_eq_of_hasDerivAt hDerivative hNonzero]

/-- Eventually equal responses have eventually equal local logarithmic derivatives. -/
lemma localLogDerivative_eventuallyEq {first second : ℝ → ℂ} {ω : ℝ}
    (hResponse : first =ᶠ[𝓝 ω] second) :
    localLogDerivative first =ᶠ[𝓝 ω] localLogDerivative second := by
  filter_upwards [hResponse, hResponse.deriv] with frequency hValue hDerivative
  simp only [localLogDerivative, hValue, hDerivative]

/-- Eventually equal responses have the same local logarithmic derivative at the base point. -/
lemma localLogDerivative_eq_of_eventuallyEq {first second : ℝ → ℂ} {ω : ℝ}
    (hResponse : first =ᶠ[𝓝 ω] second) :
    localLogDerivative first ω = localLogDerivative second ω :=
  (localLogDerivative_eventuallyEq hResponse).self_of_nhds

/-- Eventually equal responses have eventually equal local group delays. -/
lemma localGroupDelay_eventuallyEq {first second : ℝ → ℂ} {ω : ℝ}
    (hResponse : first =ᶠ[𝓝 ω] second) :
    localGroupDelay first =ᶠ[𝓝 ω] localGroupDelay second :=
  (localLogDerivative_eventuallyEq hResponse).fun_comp fun value ↦ -value.im

/-- Eventually equal responses have the same local group delay at the base point. -/
lemma localGroupDelay_eq_of_eventuallyEq {first second : ℝ → ℂ} {ω : ℝ}
    (hResponse : first =ᶠ[𝓝 ω] second) :
    localGroupDelay first ω = localGroupDelay second ω :=
  (localGroupDelay_eventuallyEq hResponse).self_of_nhds

/-- Membership in the dispersion domain states all three local gates. -/
lemma mem_localGroupDelayDispersionDomain_iff (response : ℝ → ℂ) (ω : ℝ) :
    ω ∈ localGroupDelayDispersionDomain response ↔
      DifferentiableAt ℝ response ω ∧ response ω ≠ 0 ∧
        DifferentiableAt ℝ (localGroupDelay response) ω := by
  simp only [localGroupDelayDispersionDomain, localLogDerivativeDomain, Set.mem_ofPred_eq,
    and_assoc]

/-- A displayed derivative of local group delay computes its dispersion. -/
lemma localGroupDelayDispersion_eq_of_hasDerivAt {response : ℝ → ℂ} {ω slope : ℝ}
    (_hResponseDomain : ω ∈ localLogDerivativeDomain response)
    (hDerivative : HasDerivAt (localGroupDelay response) slope ω) :
    localGroupDelayDispersion response ω = slope := by
  rw [localGroupDelayDispersion, hDerivative.deriv]

/-- Eventually equal responses have the same local group-delay dispersion at the base point. -/
lemma localGroupDelayDispersion_eq_of_eventuallyEq {first second : ℝ → ℂ}
    {ω : ℝ} (hResponse : first =ᶠ[𝓝 ω] second) :
    localGroupDelayDispersion first ω = localGroupDelayDispersion second ω := by
  rw [localGroupDelayDispersion, localGroupDelayDispersion]
  exact (localGroupDelay_eventuallyEq hResponse).deriv_eq

/-!

## B. Proof-gated frequency-response entries

-/

namespace RationalNetlist

universe u v w x

variable {n : ℕ} (netlist : RationalNetlist.{u, v, w, x} n)
variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- A total scalar extension of one proof-gated frequency-response entry.

It equals the N5F response entry on `frequencyResponseDomain` and is zero outside. Derivatives
are interpreted only at interior domain points, where the outside value is locally irrelevant.
-/
noncomputable def frequencyResponseEntry (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    (angularFrequency : ℝ) : ℂ := by
  classical
  exact if hFrequency : angularFrequency ∈ netlist.frequencyResponseDomain delays then
      netlist.frequencyResponse delays hFrequency output input
    else
      0

/-- On the proof-gated domain, the total entry is exactly the N5F frequency response. -/
lemma frequencyResponseEntry_eq (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    {angularFrequency : ℝ}
    (hFrequency : angularFrequency ∈ netlist.frequencyResponseDomain delays) :
    netlist.frequencyResponseEntry delays output input angularFrequency =
      netlist.frequencyResponse delays hFrequency output input := by
  simp only [frequencyResponseEntry, dif_pos hFrequency]

/-- Outside the proof-gated domain, the chosen total extension is zero. -/
lemma frequencyResponseEntry_eq_zero (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    {angularFrequency : ℝ}
    (hFrequency : angularFrequency ∉ netlist.frequencyResponseDomain delays) :
    netlist.frequencyResponseEntry delays output input angularFrequency = 0 := by
  simp only [frequencyResponseEntry, dif_neg hFrequency]

/-- Exact branch-audited domain for one network frequency-response group delay.

The interior condition gives a neighborhood of proof-gated N5F responses; the second condition
is the scalar differentiability and nonzero gate.
-/
def frequencyGroupDelayDomain (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident) : Set ℝ :=
  interior (netlist.frequencyResponseDomain delays) ∩
    localLogDerivativeDomain (netlist.frequencyResponseEntry delays output input)

/-- Local group delay of a selected network frequency-response entry.

It has that interpretation only on `frequencyGroupDelayDomain`.
-/
noncomputable def frequencyGroupDelay (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    (angularFrequency : ℝ) : ℝ :=
  localGroupDelay (netlist.frequencyResponseEntry delays output input) angularFrequency

/-- Exact branch-audited domain for group-delay dispersion of one network response entry. -/
def frequencyGroupDelayDispersionDomain (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident) : Set ℝ :=
  interior (netlist.frequencyResponseDomain delays) ∩
    localGroupDelayDispersionDomain
      (netlist.frequencyResponseEntry delays output input)

/-- Group-delay dispersion of a selected network frequency-response entry.

It has that interpretation only on `frequencyGroupDelayDispersionDomain`.
-/
noncomputable def frequencyGroupDelayDispersion (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    (angularFrequency : ℝ) : ℝ :=
  localGroupDelayDispersion
    (netlist.frequencyResponseEntry delays output input) angularFrequency

/-- Network group-delay-domain membership exposes all pointwise gates. -/
lemma mem_frequencyGroupDelayDomain_iff (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    (angularFrequency : ℝ) :
    angularFrequency ∈ netlist.frequencyGroupDelayDomain delays output input ↔
      angularFrequency ∈ interior (netlist.frequencyResponseDomain delays) ∧
        DifferentiableAt ℝ (netlist.frequencyResponseEntry delays output input)
          angularFrequency ∧
        netlist.frequencyResponseEntry delays output input angularFrequency ≠ 0 := by
  rfl

/-- Network dispersion-domain membership exposes well-posedness, nonzero response, and both
derivative gates. -/
lemma mem_frequencyGroupDelayDispersionDomain_iff (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    (angularFrequency : ℝ) :
    angularFrequency ∈ netlist.frequencyGroupDelayDispersionDomain delays output input ↔
      angularFrequency ∈ interior (netlist.frequencyResponseDomain delays) ∧
        DifferentiableAt ℝ (netlist.frequencyResponseEntry delays output input)
          angularFrequency ∧
        netlist.frequencyResponseEntry delays output input angularFrequency ≠ 0 ∧
        DifferentiableAt ℝ
          (localGroupDelay (netlist.frequencyResponseEntry delays output input))
          angularFrequency := by
  simp only [frequencyGroupDelayDispersionDomain, localGroupDelayDispersionDomain,
    localLogDerivativeDomain, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]

/-- An ambient extension agreeing with the N5F entry on its domain is locally equal to the chosen
total entry at every interior domain point. -/
lemma frequencyResponseEntry_eventuallyEq_of_extension (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    {angularFrequency : ℝ} (extension : ℝ → ℂ)
    (hInterior : angularFrequency ∈ interior (netlist.frequencyResponseDomain delays))
    (hExtension : ∀ frequency
      (hFrequency : frequency ∈ netlist.frequencyResponseDomain delays),
      extension frequency = netlist.frequencyResponse delays hFrequency output input) :
    netlist.frequencyResponseEntry delays output input =ᶠ[𝓝 angularFrequency]
      extension := by
  filter_upwards [mem_interior_iff_mem_nhds.mp hInterior] with frequency hFrequency
  rw [netlist.frequencyResponseEntry_eq delays output input hFrequency]
  exact (hExtension frequency hFrequency).symm

/-- A differentiable nonzero local extension certifies the network group-delay domain. -/
lemma mem_frequencyGroupDelayDomain_of_extension (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    {angularFrequency : ℝ} {extension : ℝ → ℂ}
    (hInterior : angularFrequency ∈ interior (netlist.frequencyResponseDomain delays))
    (hExtension : ∀ frequency
      (hFrequency : frequency ∈ netlist.frequencyResponseDomain delays),
      extension frequency = netlist.frequencyResponse delays hFrequency output input)
    (hDifferentiable : DifferentiableAt ℝ extension angularFrequency)
    (hNonzero : extension angularFrequency ≠ 0) :
    angularFrequency ∈ netlist.frequencyGroupDelayDomain delays output input := by
  have hEventually := netlist.frequencyResponseEntry_eventuallyEq_of_extension
    delays output input extension hInterior hExtension
  refine ⟨hInterior, (hEventually.differentiableAt_iff.mpr hDifferentiable), ?_⟩
  rw [hEventually.self_of_nhds]
  exact hNonzero

/-- A displayed derivative of a local response extension computes the selected network group
delay on the branch-audited domain. -/
lemma frequencyGroupDelay_eq_of_extension_hasDerivAt (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    {angularFrequency : ℝ} {extension : ℝ → ℂ} {responseDerivative : ℂ}
    (hInterior : angularFrequency ∈ interior (netlist.frequencyResponseDomain delays))
    (hExtension : ∀ frequency
      (hFrequency : frequency ∈ netlist.frequencyResponseDomain delays),
      extension frequency = netlist.frequencyResponse delays hFrequency output input)
    (hDerivative : HasDerivAt extension responseDerivative angularFrequency)
    (hNonzero : extension angularFrequency ≠ 0) :
    netlist.frequencyGroupDelay delays output input angularFrequency =
      -(responseDerivative / extension angularFrequency).im := by
  have hEventually := netlist.frequencyResponseEntry_eventuallyEq_of_extension
    delays output input extension hInterior hExtension
  rw [frequencyGroupDelay, localGroupDelay_eq_of_eventuallyEq hEventually]
  exact localGroupDelay_eq_of_hasDerivAt hDerivative hNonzero

/-- A differentiable nonzero local extension whose group delay is differentiable certifies the
network dispersion domain. -/
lemma mem_frequencyGroupDelayDispersionDomain_of_extension (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    {angularFrequency : ℝ} {extension : ℝ → ℂ}
    (hInterior : angularFrequency ∈ interior (netlist.frequencyResponseDomain delays))
    (hExtension : ∀ frequency
      (hFrequency : frequency ∈ netlist.frequencyResponseDomain delays),
      extension frequency = netlist.frequencyResponse delays hFrequency output input)
    (hDifferentiable : DifferentiableAt ℝ extension angularFrequency)
    (hNonzero : extension angularFrequency ≠ 0)
    (hGroupDelayDifferentiable :
      DifferentiableAt ℝ (localGroupDelay extension) angularFrequency) :
    angularFrequency ∈
      netlist.frequencyGroupDelayDispersionDomain delays output input := by
  have hEventually := netlist.frequencyResponseEntry_eventuallyEq_of_extension
    delays output input extension hInterior hExtension
  refine ⟨hInterior, ?_⟩
  rw [mem_localGroupDelayDispersionDomain_iff]
  refine ⟨hEventually.differentiableAt_iff.mpr hDifferentiable, ?_, ?_⟩
  · rw [hEventually.self_of_nhds]
    exact hNonzero
  · exact (localGroupDelay_eventuallyEq hEventually).differentiableAt_iff.mpr
      hGroupDelayDifferentiable

/-- Displayed derivatives of a local response extension and its local group delay compute the
selected network group-delay dispersion on the branch-audited domain. -/
lemma frequencyGroupDelayDispersion_eq_of_extension_hasDerivAt (delays : Fin n → ℝ)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident)
    {angularFrequency : ℝ} {extension : ℝ → ℂ} {responseDerivative : ℂ}
    {dispersion : ℝ}
    (hInterior : angularFrequency ∈ interior (netlist.frequencyResponseDomain delays))
    (hExtension : ∀ frequency
      (hFrequency : frequency ∈ netlist.frequencyResponseDomain delays),
      extension frequency = netlist.frequencyResponse delays hFrequency output input)
    (hResponseDerivative : HasDerivAt extension responseDerivative angularFrequency)
    (hNonzero : extension angularFrequency ≠ 0)
    (hGroupDelayDerivative :
      HasDerivAt (localGroupDelay extension) dispersion angularFrequency) :
    netlist.frequencyGroupDelayDispersion delays output input angularFrequency =
      dispersion := by
  have hEventually := netlist.frequencyResponseEntry_eventuallyEq_of_extension
    delays output input extension hInterior hExtension
  rw [frequencyGroupDelayDispersion,
    localGroupDelayDispersion_eq_of_eventuallyEq hEventually]
  exact localGroupDelayDispersion_eq_of_hasDerivAt
    ⟨hResponseDerivative.differentiableAt, hNonzero⟩ hGroupDelayDerivative

end RationalNetlist

end

end Optics.DelayTransfer
