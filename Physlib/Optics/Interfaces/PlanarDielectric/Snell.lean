/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.AngularGeometry

/-!
# Phase Snell law at a planar dielectric interface

## i. Overview

This file derives Snell's law for the real phase vectors of zero-attenuation complex-amplitude
plane waves. Electric phase matching first gives a material-independent identity: the incident and
transmitted tangential phase-vector norms agree, so each full phase-vector norm multiplied by the
sine of its label-relative phase angle agrees. Material dispersion and zero whole attenuation then
identify each phase-vector magnitude with angular frequency divided by material wave speed. The
common positive frequency cancels to give the wave-speed and relative-refractive-index forms of
Snell's law.

No phase-direction hypothesis is needed for these algebraic identities. The separately proved
acute-angle results supply the usual optical angle range when the phase vectors point into
their selected sides. These results neither construct nor select a transmitted branch. Unguarded
convention statement (review only): they assert no outgoing role. They assert no ray,
group-velocity, critical-angle, evanescent, Fresnel, irradiance, or power meaning either.

All results are label-level identities and remain valid when either electric amplitude vanishes;
they therefore do not assert an active optical field. The phase identity also permits zero phase
vectors with the total angle `π / 2`. By contrast, material dispersion together with zero whole
attenuation forces the phase-vector magnitudes in the speed and index forms to be nonzero.

## ii. Key results

- `IsElectricPhaseMatched.phaseSnellIdentity`: tangential phase matching in angle--magnitude form.
- `IsElectricPhaseMatched.snellLaw_waveSpeed`: `v₂ sin θᵢ = v₁ sin θₜ`.
- `IsElectricPhaseMatched.snellLaw_refractiveIndexRelativeTo`: `n₁ sin θᵢ = n₂ sin θₜ` for
  indices relative to any common homogeneous isotropic reference medium.

## iii. Table of contents

- A. Tangential phase identity
- B. Material wave-speed form
- C. Relative-refractive-index form

## iv. References

The proof specializes Physlib's complex phase-matching, side-relative angle, and homogeneous
isotropic material-dispersion APIs. No external formal-development source is copied or translated
here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space

noncomputable section

namespace PlanarDielectricWaveConfiguration
namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-!

## A. Tangential phase identity

-/

/-- Electric phase matching gives the phase Snell identity before any material-dispersion or
zero-attenuation hypothesis is imposed.

The identity is the equality of tangential phase-vector norms expressed through total
side-relative angles. It remains valid for zero electric amplitudes and zero phase vectors, and
assigns no active-field, propagation-direction, or material-branch meaning. -/
lemma phaseSnellIdentity (h : configuration.IsElectricPhaseMatched) :
    Real.sin configuration.incidentPhaseAngle *
        ‖configuration.incident.waveVector.phaseVector‖ =
      Real.sin configuration.transmittedPhaseAngle *
        ‖configuration.transmitted.waveVector.phaseVector‖ := by
  calc
    Real.sin configuration.incidentPhaseAngle *
          ‖configuration.incident.waveVector.phaseVector‖ =
        ‖configuration.interface.plane.tangentialProjection
          configuration.incident.waveVector.phaseVector‖ :=
      configuration.incident.waveVector.sin_phaseAngleToSide_mul_norm
        configuration.interface.plane .positive
    _ = ‖configuration.interface.plane.tangentialProjection
          configuration.transmitted.waveVector.phaseVector‖ := by
      exact congrArg norm h.transmitted_tangentialPhase_attenuation_eq_incident.1.symm
    _ = Real.sin configuration.transmittedPhaseAngle *
          ‖configuration.transmitted.waveVector.phaseVector‖ :=
      (configuration.transmitted.waveVector.sin_phaseAngleToSide_mul_norm
        configuration.interface.plane .positive).symm

/-!

## B. Material wave-speed form

-/

/-- Under zero attenuation and the respective material-dispersion hypotheses for the incident and
transmitted carriers, electric phase matching gives `v₂ sin θᵢ = v₁ sin θₜ`.

The zero-attenuation hypotheses concern the whole complex wave vectors, not only their tangential
projections. They are not consequences of phase matching. The equation remains a label-level
identity when either electric amplitude vanishes. -/
lemma snellLaw_waveSpeed
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hTransmittedAttenuation : configuration.transmitted.waveVector.attenuationVector = 0) :
    configuration.interface.positiveMedium.waveSpeed *
        Real.sin configuration.incidentPhaseAngle =
      configuration.interface.negativeMedium.waveSpeed *
        Real.sin configuration.transmittedPhaseAngle := by
  have hIncidentMagnitude :=
    hIncidentDispersion.phaseVector_norm_mul_waveSpeed hIncidentAttenuation
  have hTransmittedMagnitude :=
    hTransmittedDispersion.phaseVector_norm_mul_waveSpeed hTransmittedAttenuation
  apply mul_left_cancel₀ configuration.incident.angularFrequency_ne_zero
  calc
    configuration.incident.angularFrequency *
          (configuration.interface.positiveMedium.waveSpeed *
            Real.sin configuration.incidentPhaseAngle) =
        (‖configuration.incident.waveVector.phaseVector‖ *
            configuration.interface.negativeMedium.waveSpeed) *
          (configuration.interface.positiveMedium.waveSpeed *
            Real.sin configuration.incidentPhaseAngle) := by
      rw [hIncidentMagnitude]
    _ = (Real.sin configuration.incidentPhaseAngle *
          ‖configuration.incident.waveVector.phaseVector‖) *
        (configuration.interface.negativeMedium.waveSpeed *
          configuration.interface.positiveMedium.waveSpeed) := by ring
    _ = (Real.sin configuration.transmittedPhaseAngle *
          ‖configuration.transmitted.waveVector.phaseVector‖) *
        (configuration.interface.negativeMedium.waveSpeed *
          configuration.interface.positiveMedium.waveSpeed) := by
      rw [h.phaseSnellIdentity]
    _ = (‖configuration.transmitted.waveVector.phaseVector‖ *
          configuration.interface.positiveMedium.waveSpeed) *
        (configuration.interface.negativeMedium.waveSpeed *
          Real.sin configuration.transmittedPhaseAngle) := by ring
    _ = configuration.transmitted.angularFrequency *
        (configuration.interface.negativeMedium.waveSpeed *
          Real.sin configuration.transmittedPhaseAngle) := by
      rw [hTransmittedMagnitude]
    _ = configuration.incident.angularFrequency *
        (configuration.interface.negativeMedium.waveSpeed *
          Real.sin configuration.transmittedPhaseAngle) := by
      rw [h.1.1]

/-!

## C. Relative-refractive-index form

-/

/-- For zero-attenuation incident and transmitted carriers, electric phase matching gives
`n₁ sin θᵢ = n₂ sin θₜ` for refractive indices relative to any common homogeneous
isotropic reference medium. The equation remains a label-level identity when either electric
amplitude vanishes. -/
lemma snellLaw_refractiveIndexRelativeTo
    (h : configuration.IsElectricPhaseMatched)
    (reference : HomogeneousIsotropicMedium)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hTransmittedAttenuation : configuration.transmitted.waveVector.attenuationVector = 0) :
    configuration.interface.negativeMedium.refractiveIndexRelativeTo reference *
        Real.sin configuration.incidentPhaseAngle =
      configuration.interface.positiveMedium.refractiveIndexRelativeTo reference *
        Real.sin configuration.transmittedPhaseAngle := by
  have hSpeed := h.snellLaw_waveSpeed hIncidentDispersion hTransmittedDispersion
    hIncidentAttenuation hTransmittedAttenuation
  have hSineDiv :
      Real.sin configuration.incidentPhaseAngle /
          configuration.interface.negativeMedium.waveSpeed =
        Real.sin configuration.transmittedPhaseAngle /
          configuration.interface.positiveMedium.waveSpeed := by
    rw [div_eq_div_iff configuration.interface.negativeMedium.waveSpeed_ne_zero
      configuration.interface.positiveMedium.waveSpeed_ne_zero]
    simpa only [mul_comm] using hSpeed
  simp only [HomogeneousIsotropicMedium.refractiveIndexRelativeTo]
  calc
    (reference.waveSpeed / configuration.interface.negativeMedium.waveSpeed) *
          Real.sin configuration.incidentPhaseAngle =
        reference.waveSpeed *
          (Real.sin configuration.incidentPhaseAngle /
            configuration.interface.negativeMedium.waveSpeed) := by ring
    _ = reference.waveSpeed *
          (Real.sin configuration.transmittedPhaseAngle /
            configuration.interface.positiveMedium.waveSpeed) := by
      rw [hSineDiv]
    _ = (reference.waveSpeed / configuration.interface.positiveMedium.waveSpeed) *
          Real.sin configuration.transmittedPhaseAngle := by ring

end IsElectricPhaseMatched
end PlanarDielectricWaveConfiguration

end
end Optics
