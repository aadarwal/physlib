/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Physlib.Optics.Systems.DelayTransfer.GroupDelay

/-!
# Regression tests for local group delay and dispersion

## i. Overview

The scalar response
`exp (-I * (delay * ω + dispersion * ω² / 2))` is nonzero everywhere. Its local group
delay is exactly `delay + dispersion * ω`, and its group-delay dispersion is exactly the
coefficient named `dispersion`. Exact rational instances test both the negative exponential sign
and a nonzero dispersion value. A separate zero-crossing fixture proves that differentiability
alone does not enter the logarithmic-derivative domain.

## ii. Key results

- `chirpedDelayResponse`: a nonvanishing response with quadratic local phase.
- `chirpedDelayResponse_localGroupDelay`: its exact affine group delay.
- `chirpedDelayResponse_localGroupDelayDispersion`: its exact constant dispersion.
- `pureDelay_groupDelay_three`: the negative-exponential sign anchor.
- `chirpedDelay_groupDelay_at_five`: a nonzero-dispersion value anchor.
- `zeroCrossing_not_mem_localLogDerivativeDomain`: the required zero guard.

## iii. Table of contents

- A. Quadratic-phase response
- B. Exact sign, dispersion, and zero-domain anchors

## iv. References and non-claims

The local logarithmic-derivative domains and totalized quantities are defined in
`Physlib/Optics/Systems/DelayTransfer/GroupDelay.lean:76-185`. This regression derives exact
values from a displayed scalar derivative and cancellation; it does not use `Complex.arg` or a
global phase branch.
The selected delay convention `q = exp (-I * ω * τ)` is defined in
`Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:81-94`.

No N5F network realization, material-dispersion law, rational-in-frequency result, time-domain
causality statement, passivity claim, units assignment, or source-parity claim is made. The
coefficient called dispersion is literally the derivative of the displayed local group delay.
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

end

end Optics.DelayTransfer
