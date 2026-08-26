/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Evaluation

/-!
# Proof-gated frequency response of rational-delay networks

## i. Overview

For declared fixed real delays, `imaginaryFrequency` selects the imaginary-axis Laplace point
`s = I * ω`. Thus `frequencyDelayEvaluation` substitutes
`q_i = exp (-I * ω * τ_i)`. The one-delay point
`unitCirclePoint τ ω = exp (I * ω * τ)` is nonzero, lies on the unit circle, and has
reciprocal equal to the same formal delay value. This proves the selected
`q = exp (-s * τ) = z⁻¹` convention rather than merely naming it.

`RationalNetlist.frequencyResponseDomain` is the exact imaginary-axis preimage of N5F's
proof-gated Laplace response domain. `frequencyResponse` exists only with membership in that
domain. It is the N5F response at the exponential delay tuple, and in the one-delay case it
equals the reciprocal-Z response at `unitCirclePoint`.

## ii. Key results

- `imaginaryFrequency`: the embedding `ω ↦ I * ω`.
- `frequencyDelayEvaluation`: the delay tuple `q_i = exp (-I * ω * τ_i)`.
- `unitCirclePoint`: the reciprocal-Z coordinate `z = exp (I * ω * τ)`.
- `RationalNetlist.frequencyResponseDomain`: the proof-gated frequency domain.
- `RationalNetlist.frequencyResponse`: the reindexed N5F response on that domain.
- `RationalNetlist.frequencyResponse_eq_formalDelay`: the formal-delay response identity.
- `RationalNetlist.frequencyResponse_eq_reciprocalZ`: the unit-circle Z identity.

## iii. Table of contents

- A. Imaginary-axis and unit-circle evaluations
- B. Proof-gated network frequency response
- C. One-delay reciprocal-Z agreement

## iv. References

The substitution `laplaceEvaluation` is defined as `exp (-s * τ_i)` in
`Physlib/Optics/Systems/DelayTransfer/Basic.lean:225-227`. The exact N5F response-domain
preimage and response transport are
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:326-394`. The reciprocal-Z map and its
proof-gated transport are in that file at lines 396-495.

The response domain includes both retained-entry validity and network well-posedness; those gates
are independent as documented in
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:16-24`. This module does not claim a
response outside that domain. It does not claim rational dependence on physical frequency, nor
does it supply a dispersion model, positivity or dimensional interpretation of the real delay
data, or a bridge to the phasor layer's time convention. Imaginary-axis substitution alone
implies no time-domain causality. No passivity, resonance, group-delay, or dispersion result is
asserted. In particular, the requested Physlib extension concerning local logarithmic
derivatives is deferred to the later group-delay slice.

This module implements the requested “frequency response under the chosen
`q = exp (-s * τ) = z⁻¹` convention” from `goal.md:2279`.

-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-!

## A. Imaginary-axis and unit-circle evaluations

-/

/-- The complex Laplace point on the imaginary axis selected by angular frequency `ω`. -/
def imaginaryFrequency (angularFrequency : ℝ) : ℂ :=
  Complex.I * angularFrequency

/-- Evaluation of every formal delay at `q_i = exp (-I * ω * τ_i)`. -/
def frequencyDelayEvaluation {n : ℕ} (delays : Fin n → ℝ)
    (angularFrequency : ℝ) : DelayTuple n :=
  laplaceEvaluation delays (imaginaryFrequency angularFrequency)

/-- The frequency-delay substitution has the selected negative exponential sign. -/
lemma frequencyDelayEvaluation_apply {n : ℕ} (delays : Fin n → ℝ)
    (angularFrequency : ℝ) (i : Fin n) :
    frequencyDelayEvaluation delays angularFrequency i =
      Complex.exp (-Complex.I * ((angularFrequency * delays i : ℝ) : ℂ)) := by
  simp only [frequencyDelayEvaluation, laplaceEvaluation_apply, imaginaryFrequency]
  congr 1
  push_cast
  ring

/-- The reciprocal-Z unit-circle point `z = exp (I * ω * τ)`. -/
def unitCirclePoint (delay angularFrequency : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((angularFrequency * delay : ℝ) : ℂ))

/-- The selected reciprocal-Z point lies on the complex unit circle. -/
lemma norm_unitCirclePoint (delay angularFrequency : ℝ) :
    ‖unitCirclePoint delay angularFrequency‖ = 1 := by
  rw [unitCirclePoint]
  exact Complex.norm_exp_I_mul_ofReal (angularFrequency * delay)

/-- The selected reciprocal-Z point is never zero. -/
lemma unitCirclePoint_ne_zero (delay angularFrequency : ℝ) :
    unitCirclePoint delay angularFrequency ≠ 0 :=
  Complex.exp_ne_zero _

/-- For one delay, the unit-circle reciprocal and imaginary-axis substitutions agree exactly. -/
lemma zInverseEvaluation_unitCirclePoint (delay angularFrequency : ℝ) :
    zInverseEvaluation (unitCirclePoint delay angularFrequency) =
      frequencyDelayEvaluation (fun _ : Fin 1 ↦ delay) angularFrequency := by
  funext i
  rw [zInverseEvaluation_apply, frequencyDelayEvaluation_apply, unitCirclePoint,
    ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-!

## B. Proof-gated network frequency response

-/

namespace RationalNetlist

universe u v w x

variable {n : ℕ} (netlist : RationalNetlist.{u, v, w, x} n)

section Finite

variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on the original aggregate channels. -/
local instance frequencyChannelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- Classical equality on the original connected channels. -/
local instance frequencyConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel := Classical.decEq _

/-- External channels of the original finite netlist are finite. -/
local instance frequencyExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- Imaginary-axis reparameterization retains finite aggregate channels. -/
local instance frequencyLaplaceChannelFintype (delays : Fin n → ℝ) :
    Fintype (netlist.laplace delays).Channel :=
  inferInstanceAs (Fintype netlist.Channel)

/-- Imaginary-axis reparameterization retains finite connected channels. -/
local instance frequencyLaplaceConnectedChannelFintype (delays : Fin n → ℝ) :
    Fintype (netlist.laplace delays).ConnectedChannel :=
  inferInstanceAs (Fintype netlist.ConnectedChannel)

/-- Classical equality on imaginary-axis aggregate channels. -/
local instance frequencyLaplaceChannelDecidableEq (delays : Fin n → ℝ) :
    DecidableEq (netlist.laplace delays).Channel := Classical.decEq _

/-- Classical equality on imaginary-axis connected channels. -/
local instance frequencyLaplaceConnectedChannelDecidableEq (delays : Fin n → ℝ) :
    DecidableEq (netlist.laplace delays).ConnectedChannel := Classical.decEq _

/-- Imaginary-axis reparameterization retains finite external channels. -/
local instance frequencyLaplaceExternalChannelFintype (delays : Fin n → ℝ) :
    Fintype (netlist.laplace delays).ExternalChannel := by
  change Fintype netlist.ExternalChannel
  infer_instance

/-- Frequencies whose imaginary-axis Laplace points lie in the N5F response domain. -/
def frequencyResponseDomain (delays : Fin n → ℝ) : Set ℝ :=
  imaginaryFrequency ⁻¹' (netlist.laplace delays).responseDomain

/-- Frequency-domain membership is exactly formal-delay response-domain membership. -/
lemma mem_frequencyResponseDomain_iff (delays : Fin n → ℝ)
    (angularFrequency : ℝ) :
    angularFrequency ∈ netlist.frequencyResponseDomain delays ↔
      frequencyDelayEvaluation delays angularFrequency ∈ netlist.responseDomain := Iff.rfl

/-- The proof-gated N5F response on the imaginary-frequency axis.

The result is defined only with a witness that the retained entries are valid and the internal
network equations are well posed at this frequency.
-/
def frequencyResponse (delays : Fin n → ℝ) {angularFrequency : ℝ}
    (hFrequency : angularFrequency ∈ netlist.frequencyResponseDomain delays) :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing :=
  ((netlist.laplace delays).response hFrequency).reindex
    (Incident.relabelEquiv (netlist.laplaceExternalChannelEquiv delays))
    (Outgoing.relabelEquiv (netlist.laplaceExternalChannelEquiv delays))

/-- The proof-gated frequency response is N5F's response at the exponential delay tuple. -/
lemma frequencyResponse_eq_formalDelay (delays : Fin n → ℝ)
    {angularFrequency : ℝ}
    (hFrequency : angularFrequency ∈ netlist.frequencyResponseDomain delays) :
    netlist.frequencyResponse delays hFrequency =
      netlist.toParameterizedNetlist.response
        ((netlist.mem_frequencyResponseDomain_iff delays angularFrequency).mp hFrequency) :=
  netlist.response_laplace_reindex delays hFrequency

/-!

## C. One-delay reciprocal-Z agreement

-/

/-- Reciprocal-Z reparameterization retains finite aggregate channels. -/
local instance frequencyReciprocalZChannelFintype
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype oneDelayNetlist.Channel] :
    Fintype oneDelayNetlist.reciprocalZ.Channel :=
  inferInstanceAs (Fintype oneDelayNetlist.Channel)

/-- Reciprocal-Z reparameterization retains finite connected channels. -/
local instance frequencyReciprocalZConnectedChannelFintype
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype oneDelayNetlist.ConnectedChannel] :
    Fintype oneDelayNetlist.reciprocalZ.ConnectedChannel :=
  inferInstanceAs (Fintype oneDelayNetlist.ConnectedChannel)

/-- Classical equality on reciprocal-Z aggregate channels. -/
local instance frequencyReciprocalZChannelDecidableEq
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1) :
    DecidableEq oneDelayNetlist.reciprocalZ.Channel := Classical.decEq _

/-- Classical equality on reciprocal-Z connected channels. -/
local instance frequencyReciprocalZConnectedChannelDecidableEq
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1) :
    DecidableEq oneDelayNetlist.reciprocalZ.ConnectedChannel := Classical.decEq _

/-- Reciprocal-Z reparameterization retains finite external channels. -/
local instance frequencyReciprocalZExternalChannelFintype
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype oneDelayNetlist.Channel] [Fintype oneDelayNetlist.ConnectedChannel] :
    Fintype oneDelayNetlist.reciprocalZ.ExternalChannel := by
  change Fintype oneDelayNetlist.ExternalChannel
  classical
  infer_instance

/-- At the selected unit-circle point, reciprocal-Z domain membership is exactly frequency-domain
membership for the corresponding one-delay model. -/
lemma unitCirclePoint_mem_reciprocalZ_responseDomain_iff
    (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
    (delay angularFrequency : ℝ) :
    unitCirclePoint delay angularFrequency ∈ netlist.reciprocalZ.responseDomain ↔
      angularFrequency ∈ netlist.frequencyResponseDomain (fun _ ↦ delay) := by
  change zInverseEvaluation (unitCirclePoint delay angularFrequency) ∈
      netlist.responseDomain ↔
    frequencyDelayEvaluation (fun _ ↦ delay) angularFrequency ∈ netlist.responseDomain
  rw [zInverseEvaluation_unitCirclePoint]

/-- Frequency-domain membership supplies the corresponding reciprocal-Z domain witness. -/
lemma unitCirclePoint_mem_reciprocalZ_responseDomain
    (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
    {delay angularFrequency : ℝ}
    (hFrequency : angularFrequency ∈
      netlist.frequencyResponseDomain (fun _ ↦ delay)) :
    unitCirclePoint delay angularFrequency ∈ netlist.reciprocalZ.responseDomain :=
  (netlist.unitCirclePoint_mem_reciprocalZ_responseDomain_iff
    delay angularFrequency).mpr hFrequency

/-- On the proof-gated domain, the imaginary-axis response equals the reciprocal-Z response at
the selected nonzero unit-circle point. -/
lemma frequencyResponse_eq_reciprocalZ
    (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
    {delay angularFrequency : ℝ}
    (hFrequency : angularFrequency ∈
      netlist.frequencyResponseDomain (fun _ ↦ delay)) :
    netlist.frequencyResponse (fun _ ↦ delay) hFrequency =
      (netlist.reciprocalZ.response
        (netlist.unitCirclePoint_mem_reciprocalZ_responseDomain hFrequency)).reindex
          (Incident.relabelEquiv netlist.reciprocalZExternalChannelEquiv)
          (Outgoing.relabelEquiv netlist.reciprocalZExternalChannelEquiv) := by
  rw [netlist.frequencyResponse_eq_formalDelay]
  symm
  exact netlist.response_reciprocalZ_reindex_of_evaluation_eq
    (netlist.unitCirclePoint_mem_reciprocalZ_responseDomain hFrequency)
    (zInverseEvaluation_unitCirclePoint delay angularFrequency)
    ((netlist.mem_frequencyResponseDomain_iff _ _).mp hFrequency)

end Finite

end RationalNetlist

end

end Optics.DelayTransfer
