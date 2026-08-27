/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.Snell

/-!
# Critical phase-angle geometry at a planar dielectric interface

## i. Overview

This file develops the material threshold behind critical-angle geometry for the existing
negative-to-positive planar dielectric convention. The critical sine ratio is the incident-medium
wave speed divided by the transmitted-medium wave speed, equivalently the transmitted refractive
index divided by the incident refractive index when both use one common reference. A strict
slower-to-faster wave-speed contrast places that ratio in `(0, 1)` and gives a proof-bearing
critical phase angle in `(0, π / 2)`.

The three incidence predicates are unconditional sine-threshold relations. In particular,
critical incidence also includes equal-speed grazing, where the ratio is one but no strictly
interior `criticalPhaseAngle` is available. Under strict contrast, sine-critical incidence can
still describe the supplementary obtuse total-angle branch until the incident angle is separately
placed in `[0, π / 2]`.

For an incident carrier satisfying negative-medium dispersion with zero whole attenuation, the
candidate transmitted normal radicand factors as the positive incident phase-magnitude square
times the difference between the squared critical sine ratio and squared incident-angle sine. This
factorization requires neither electric phase matching nor transmitted dispersion. It therefore
classifies the sign of a candidate expression only. Existing phase-matching results are needed to
identify that expression with the normal square of an actual transmitted-labelled candidate.

The results here remain label-level identities when electric amplitudes vanish. A positive
radicand constructs no transmitted wave and selects no real root; a negative radicand selects
neither imaginary root and is not by itself total internal reflection. Unguarded convention
statement (review only): no outgoing role follows. No ray, group-velocity, evanescent, Fresnel,
irradiance, or power conclusion is made.

## ii. Key results

- `PlanarDielectricInterface.criticalPhaseSineRatio`: the reference-free material threshold
  `v₁ / v₂`.
- `PlanarDielectricInterface.criticalPhaseAngle`: the proof-bearing angle `arcsin (v₁ / v₂)` in
  `(0, π / 2)` under the strict critical-angle contrast.
- `transmittedNormalRadicand_eq_incidentPhaseVectorNorm_sq_mul`: exact incident-angle
  factorization of the candidate transmitted normal radicand.
- `transmittedNormalRadicand_pos_iff_isSubcriticalPhaseIncidence` and its zero and negative
  companions: exact sign classification by the three sine-threshold incidence regimes.
- `IsElectricPhaseMatched.transmittedPhaseAngle_eq_pi_div_two_of_isCriticalPhaseIncidence`: a
  supplied phase-matched and dispersive critical candidate is phase-grazing on transmission.

## iii. Table of contents

- A. Critical-angle material data
- B. Incident-angle radicand factorization
- C. Sine-threshold sign classification
- D. Critical-angle interpretation
- E. Critical supplied-candidate grazing

## iv. References

The construction specializes Physlib's homogeneous-isotropic medium, complex material-dispersion,
and side-relative phase-angle APIs. No external formal-development source is copied or translated
here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space

noncomputable section

namespace PlanarDielectricInterface

/-!

## A. Critical-angle material data

-/

/-- The critical sine ratio for incidence from the negative-side medium into the positive-side
medium, defined as the incident-medium wave speed divided by the transmitted-medium wave speed.

This positive number exists for every interface. It lies below one only under a strict
slower-to-faster material contrast. -/
noncomputable def criticalPhaseSineRatio (interface : PlanarDielectricInterface) : ℝ :=
  interface.negativeMedium.waveSpeed / interface.positiveMedium.waveSpeed

/-- A planar dielectric interface has critical-angle contrast when its negative-side medium has
strictly lower wave speed than its positive-side medium. -/
def HasCriticalAngleContrast (interface : PlanarDielectricInterface) : Prop :=
  interface.negativeMedium.waveSpeed < interface.positiveMedium.waveSpeed

lemma criticalPhaseSineRatio_pos (interface : PlanarDielectricInterface) :
    0 < interface.criticalPhaseSineRatio :=
  div_pos interface.negativeMedium.waveSpeed_pos interface.positiveMedium.waveSpeed_pos

/-- The critical sine ratio is the positive-medium refractive index relative to the negative-side
incident medium. -/
lemma criticalPhaseSineRatio_eq_refractiveIndexRelativeTo
    (interface : PlanarDielectricInterface) :
    interface.criticalPhaseSineRatio =
      interface.positiveMedium.refractiveIndexRelativeTo interface.negativeMedium := rfl

/-- The squared critical sine ratio is the positive-to-negative ratio of the material coefficients
`epsilon * mu`. -/
lemma criticalPhaseSineRatio_sq (interface : PlanarDielectricInterface) :
    interface.criticalPhaseSineRatio ^ 2 =
      (interface.positiveMedium.ε * interface.positiveMedium.μ) /
        (interface.negativeMedium.ε * interface.negativeMedium.μ) := by
  rw [interface.criticalPhaseSineRatio_eq_refractiveIndexRelativeTo,
    interface.positiveMedium.refractiveIndexRelativeTo_sq]

/-- Relative to any one common reference medium, the critical sine ratio is the transmitted index
divided by the incident index. -/
lemma criticalPhaseSineRatio_eq_refractiveIndexRelativeTo_div
    (interface : PlanarDielectricInterface) (reference : HomogeneousIsotropicMedium) :
    interface.criticalPhaseSineRatio =
      interface.positiveMedium.refractiveIndexRelativeTo reference /
        interface.negativeMedium.refractiveIndexRelativeTo reference := by
  simp only [criticalPhaseSineRatio, HomogeneousIsotropicMedium.refractiveIndexRelativeTo]
  field_simp [reference.waveSpeed_ne_zero, interface.negativeMedium.waveSpeed_ne_zero,
    interface.positiveMedium.waveSpeed_ne_zero]

/-- Critical-angle contrast is equivalent to the critical sine ratio being below one. -/
lemma hasCriticalAngleContrast_iff_criticalPhaseSineRatio_lt_one
    (interface : PlanarDielectricInterface) :
    interface.HasCriticalAngleContrast ↔ interface.criticalPhaseSineRatio < 1 := by
  rw [HasCriticalAngleContrast, criticalPhaseSineRatio,
    div_lt_one interface.positiveMedium.waveSpeed_pos]

/-- Relative to any one common reference medium, critical-angle contrast is exactly the
transmitted refractive index being smaller than the incident refractive index. -/
lemma hasCriticalAngleContrast_iff_refractiveIndexRelativeTo_lt
    (interface : PlanarDielectricInterface) (reference : HomogeneousIsotropicMedium) :
    interface.HasCriticalAngleContrast ↔
      interface.positiveMedium.refractiveIndexRelativeTo reference <
        interface.negativeMedium.refractiveIndexRelativeTo reference := by
  rw [interface.hasCriticalAngleContrast_iff_criticalPhaseSineRatio_lt_one,
    interface.criticalPhaseSineRatio_eq_refractiveIndexRelativeTo_div,
    div_lt_one (interface.negativeMedium.refractiveIndexRelativeTo_pos reference)]

/-- Critical-angle contrast is exactly the positive-side material product `epsilon * mu` being
smaller than its negative-side counterpart. -/
lemma hasCriticalAngleContrast_iff_positive_epsilon_mu_lt_negative
    (interface : PlanarDielectricInterface) :
    interface.HasCriticalAngleContrast ↔
      interface.positiveMedium.ε * interface.positiveMedium.μ <
        interface.negativeMedium.ε * interface.negativeMedium.μ := by
  rw [interface.hasCriticalAngleContrast_iff_criticalPhaseSineRatio_lt_one]
  have hRatioPos := interface.criticalPhaseSineRatio_pos
  have hNegativeMaterialPos :=
    mul_pos interface.negativeMedium.ε_pos interface.negativeMedium.μ_pos
  constructor
  · intro hRatio
    have hRatioSq : interface.criticalPhaseSineRatio ^ 2 < 1 := by nlinarith
    rw [interface.criticalPhaseSineRatio_sq,
      div_lt_one hNegativeMaterialPos] at hRatioSq
    exact hRatioSq
  · intro hMaterial
    have hRatioSq : interface.criticalPhaseSineRatio ^ 2 < 1 := by
      rw [interface.criticalPhaseSineRatio_sq, div_lt_one hNegativeMaterialPos]
      exact hMaterial
    nlinarith

/-- Strict critical-angle contrast places the critical sine ratio in `(0, 1)`. -/
lemma criticalPhaseSineRatio_mem_Ioo (interface : PlanarDielectricInterface)
    (h : interface.HasCriticalAngleContrast) :
    interface.criticalPhaseSineRatio ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨interface.criticalPhaseSineRatio_pos,
    (interface.hasCriticalAngleContrast_iff_criticalPhaseSineRatio_lt_one).mp h⟩

/-- Under strict critical-angle contrast, the critical phase angle is `arcsin (v₁ / v₂)`,
bundled with its exact open-quadrant range. -/
noncomputable def criticalPhaseAngle (interface : PlanarDielectricInterface)
    (h : interface.HasCriticalAngleContrast) : Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  ⟨Real.arcsin interface.criticalPhaseSineRatio,
    Real.arcsin_pos.mpr interface.criticalPhaseSineRatio_pos,
    Real.arcsin_lt_pi_div_two.mpr
      ((interface.hasCriticalAngleContrast_iff_criticalPhaseSineRatio_lt_one).mp h)⟩

/-- The sine of the proof-bearing critical phase angle is the critical sine ratio. -/
@[simp]
lemma sin_criticalPhaseAngle (interface : PlanarDielectricInterface)
    (h : interface.HasCriticalAngleContrast) :
    Real.sin (interface.criticalPhaseAngle h : ℝ) = interface.criticalPhaseSineRatio := by
  rw [criticalPhaseAngle]
  apply Real.sin_arcsin
  · linarith [interface.criticalPhaseSineRatio_pos]
  · exact
      ((interface.hasCriticalAngleContrast_iff_criticalPhaseSineRatio_lt_one).mp h).le

end PlanarDielectricInterface

namespace PlanarDielectricWaveConfiguration

/-!

## B. Incident-angle radicand factorization

-/

/-- Negative-medium incident dispersion and zero whole incident attenuation factor the candidate
transmitted normal radicand into a positive phase-magnitude square and a pure angular threshold.

This identity uses neither electric phase matching nor transmitted dispersion, so it does not
identify the radicand with the normal square of the stored transmitted candidate. -/
lemma transmittedNormalRadicand_eq_incidentPhaseVectorNorm_sq_mul
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0) :
    configuration.transmittedNormalRadicand =
      ‖configuration.incident.waveVector.phaseVector‖ ^ 2 *
        (configuration.interface.criticalPhaseSineRatio ^ 2 -
          Real.sin configuration.incidentPhaseAngle ^ 2) := by
  have hMagnitude :=
    hIncidentDispersion.phaseVector_norm_mul_waveSpeed hIncidentAttenuation
  have hPositiveMaterial :
      configuration.interface.positiveMedium.ε *
            configuration.interface.positiveMedium.μ *
          configuration.incident.angularFrequency ^ 2 =
        (configuration.incident.angularFrequency /
          configuration.interface.positiveMedium.waveSpeed) ^ 2 := by
    rw [div_pow, configuration.interface.positiveMedium.waveSpeed_sq]
    field_simp [configuration.interface.positiveMedium.ε_ne_zero,
      configuration.interface.positiveMedium.μ_ne_zero]
  rw [transmittedNormalRadicand,
    ← configuration.incident.waveVector.sin_phaseAngleToSide_mul_norm
      configuration.interface.plane .positive,
    hPositiveMaterial, PlanarDielectricInterface.criticalPhaseSineRatio]
  calc
    (configuration.incident.angularFrequency /
          configuration.interface.positiveMedium.waveSpeed) ^ 2 -
        (Real.sin configuration.incidentPhaseAngle *
          ‖configuration.incident.waveVector.phaseVector‖) ^ 2 =
      ((‖configuration.incident.waveVector.phaseVector‖ *
            configuration.interface.negativeMedium.waveSpeed) /
          configuration.interface.positiveMedium.waveSpeed) ^ 2 -
        (Real.sin configuration.incidentPhaseAngle *
          ‖configuration.incident.waveVector.phaseVector‖) ^ 2 := by
      rw [hMagnitude]
    _ = ‖configuration.incident.waveVector.phaseVector‖ ^ 2 *
        ((configuration.interface.negativeMedium.waveSpeed /
              configuration.interface.positiveMedium.waveSpeed) ^ 2 -
          Real.sin configuration.incidentPhaseAngle ^ 2) := by ring

private lemma incidentPhaseVector_norm_pos
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0) :
    0 < ‖configuration.incident.waveVector.phaseVector‖ := by
  rw [hIncidentDispersion.phaseVector_norm_eq_angularFrequency_div_waveSpeed
    hIncidentAttenuation]
  exact div_pos configuration.incident.angularFrequency_pos
    configuration.interface.negativeMedium.waveSpeed_pos

private lemma sin_incidentPhaseAngle_nonneg
    (configuration : PlanarDielectricWaveConfiguration) :
    0 ≤ Real.sin configuration.incidentPhaseAngle := by
  change 0 ≤ Real.sin (InnerProductGeometry.angle
    configuration.incident.waveVector.phaseVector
      (configuration.interface.plane.sideNormalVector .positive))
  exact InnerProductGeometry.sin_angle_nonneg _ _

/-!

## C. Sine-threshold sign classification

-/

/-- The incident phase label is subcritical when the sine of its side-relative angle is below the
material critical-phase threshold.

This total-angle predicate agrees with ordinary angle ordering only when the incident phase angle
is known to lie in the acute-or-grazing interval. It asserts no transmitted-branch existence. -/
def IsSubcriticalPhaseIncidence (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  Real.sin configuration.incidentPhaseAngle <
    configuration.interface.criticalPhaseSineRatio

/-- The incident phase label is critical when the sine of its side-relative angle equals the
material critical-phase threshold.

This unconditional predicate does not imply strict critical-angle contrast: for equal wave speeds
it deliberately includes grazing incidence at sine one, although no interior critical phase angle
exists. Under strict contrast it agrees with equality to the critical phase angle only when the
incident phase angle is known to lie in the acute-or-grazing interval; otherwise the supplementary
obtuse total-angle branch has the same sine. -/
def IsCriticalPhaseIncidence (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  Real.sin configuration.incidentPhaseAngle =
    configuration.interface.criticalPhaseSineRatio

/-- The incident phase label is supercritical when the material critical-phase threshold is below
the sine of its side-relative angle.

This total-angle predicate agrees with ordinary angle ordering only when the incident phase angle
is known to lie in the acute-or-grazing interval. It does not by itself assert evanescence or total
internal reflection. -/
def IsSupercriticalPhaseIncidence (configuration : PlanarDielectricWaveConfiguration) : Prop :=
  configuration.interface.criticalPhaseSineRatio <
    Real.sin configuration.incidentPhaseAngle

/-- The candidate transmitted normal radicand is positive exactly when the incident phase-angle
sine is below the critical phase threshold.

This is an algebraic sign result and does not construct either available real normal root. -/
lemma transmittedNormalRadicand_pos_iff_isSubcriticalPhaseIncidence
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0) :
    0 < configuration.transmittedNormalRadicand ↔
      configuration.IsSubcriticalPhaseIncidence := by
  change 0 < configuration.transmittedNormalRadicand ↔
    Real.sin configuration.incidentPhaseAngle <
      configuration.interface.criticalPhaseSineRatio
  rw [configuration.transmittedNormalRadicand_eq_incidentPhaseVectorNorm_sq_mul
    hIncidentDispersion hIncidentAttenuation]
  have hNormSqPos :
      0 < ‖configuration.incident.waveVector.phaseVector‖ ^ 2 :=
    sq_pos_of_pos
      (incidentPhaseVector_norm_pos configuration hIncidentDispersion hIncidentAttenuation)
  have hRatio := configuration.interface.criticalPhaseSineRatio_pos
  have hSin := sin_incidentPhaseAngle_nonneg configuration
  rw [mul_pos_iff_of_pos_left hNormSqPos]
  constructor <;> intro h <;> nlinarith

/-- The candidate transmitted normal radicand vanishes exactly when the incident phase-angle sine
equals the critical phase threshold.

No incident phase-direction hypothesis is needed for this sine equality. -/
lemma transmittedNormalRadicand_eq_zero_iff_isCriticalPhaseIncidence
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0) :
    configuration.transmittedNormalRadicand = 0 ↔
      configuration.IsCriticalPhaseIncidence := by
  change configuration.transmittedNormalRadicand = 0 ↔
    Real.sin configuration.incidentPhaseAngle =
      configuration.interface.criticalPhaseSineRatio
  rw [configuration.transmittedNormalRadicand_eq_incidentPhaseVectorNorm_sq_mul
    hIncidentDispersion hIncidentAttenuation]
  have hNormSqPos :
      0 < ‖configuration.incident.waveVector.phaseVector‖ ^ 2 :=
    sq_pos_of_pos
      (incidentPhaseVector_norm_pos configuration hIncidentDispersion hIncidentAttenuation)
  have hRatio := configuration.interface.criticalPhaseSineRatio_pos
  have hSin := sin_incidentPhaseAngle_nonneg configuration
  constructor
  · intro h
    have hDifference :
        configuration.interface.criticalPhaseSineRatio ^ 2 -
            Real.sin configuration.incidentPhaseAngle ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt hNormSqPos)
    nlinarith
  · intro h
    apply mul_eq_zero.mpr
    right
    nlinarith

/-- The candidate transmitted normal radicand is negative exactly for supercritical phase
incidence.

This is an algebraic sign result and selects neither available imaginary normal root. -/
lemma transmittedNormalRadicand_lt_zero_iff_isSupercriticalPhaseIncidence
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0) :
    configuration.transmittedNormalRadicand < 0 ↔
      configuration.IsSupercriticalPhaseIncidence := by
  change configuration.transmittedNormalRadicand < 0 ↔
    configuration.interface.criticalPhaseSineRatio <
      Real.sin configuration.incidentPhaseAngle
  rw [configuration.transmittedNormalRadicand_eq_incidentPhaseVectorNorm_sq_mul
    hIncidentDispersion hIncidentAttenuation]
  have hNormSqPos :
      0 < ‖configuration.incident.waveVector.phaseVector‖ ^ 2 :=
    sq_pos_of_pos
      (incidentPhaseVector_norm_pos configuration hIncidentDispersion hIncidentAttenuation)
  have hRatio := configuration.interface.criticalPhaseSineRatio_pos
  have hSin := sin_incidentPhaseAngle_nonneg configuration
  constructor
  · intro h
    have hScaled :
        ‖configuration.incident.waveVector.phaseVector‖ ^ 2 *
            (configuration.interface.criticalPhaseSineRatio ^ 2 -
              Real.sin configuration.incidentPhaseAngle ^ 2) <
          ‖configuration.incident.waveVector.phaseVector‖ ^ 2 * 0 := by
      simpa using h
    have hDifference := (mul_lt_mul_iff_of_pos_left hNormSqPos).mp hScaled
    nlinarith
  · intro h
    have hDifference :
        configuration.interface.criticalPhaseSineRatio ^ 2 -
            Real.sin configuration.incidentPhaseAngle ^ 2 < 0 := by
      nlinarith
    have hScaled := (mul_lt_mul_iff_of_pos_left hNormSqPos).mpr hDifference
    simpa using hScaled

/-!

## D. Critical-angle interpretation

-/

/-- On the acute-or-grazing interval, subcritical phase incidence is exactly incidence below the
critical phase angle. -/
lemma isSubcriticalPhaseIncidence_iff_incidentPhaseAngle_lt_criticalPhaseAngle
    (configuration : PlanarDielectricWaveConfiguration)
    (hContrast : configuration.interface.HasCriticalAngleContrast)
    (hIncidentAngle : configuration.incidentPhaseAngle ∈ Set.Icc 0 (Real.pi / 2)) :
    configuration.IsSubcriticalPhaseIncidence ↔
      configuration.incidentPhaseAngle <
        (configuration.interface.criticalPhaseAngle hContrast : ℝ) := by
  change Real.sin configuration.incidentPhaseAngle <
      configuration.interface.criticalPhaseSineRatio ↔
    configuration.incidentPhaseAngle <
      Real.arcsin configuration.interface.criticalPhaseSineRatio
  have hAngleIcc :
      configuration.incidentPhaseAngle ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith [Real.pi_pos, hIncidentAngle.1], hIncidentAngle.2⟩
  have hRatioIoo := configuration.interface.criticalPhaseSineRatio_mem_Ioo hContrast
  exact (Real.lt_arcsin_iff_sin_lt hAngleIcc
    ⟨by linarith [hRatioIoo.1], hRatioIoo.2.le⟩).symm

/-- On the acute-or-grazing interval, critical phase incidence is exactly equality to the critical
phase angle. -/
lemma isCriticalPhaseIncidence_iff_incidentPhaseAngle_eq_criticalPhaseAngle
    (configuration : PlanarDielectricWaveConfiguration)
    (hContrast : configuration.interface.HasCriticalAngleContrast)
    (hIncidentAngle : configuration.incidentPhaseAngle ∈ Set.Icc 0 (Real.pi / 2)) :
    configuration.IsCriticalPhaseIncidence ↔
      configuration.incidentPhaseAngle =
        (configuration.interface.criticalPhaseAngle hContrast : ℝ) := by
  change Real.sin configuration.incidentPhaseAngle =
      configuration.interface.criticalPhaseSineRatio ↔
    configuration.incidentPhaseAngle =
      Real.arcsin configuration.interface.criticalPhaseSineRatio
  have hAngleIcc :
      configuration.incidentPhaseAngle ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith [Real.pi_pos, hIncidentAngle.1], hIncidentAngle.2⟩
  constructor
  · intro hSine
    calc
      configuration.incidentPhaseAngle =
          Real.arcsin (Real.sin configuration.incidentPhaseAngle) :=
        (Real.arcsin_sin hAngleIcc.1 hAngleIcc.2).symm
      _ = Real.arcsin configuration.interface.criticalPhaseSineRatio := by rw [hSine]
  · intro hAngle
    calc
      Real.sin configuration.incidentPhaseAngle =
          Real.sin (Real.arcsin configuration.interface.criticalPhaseSineRatio) := by rw [hAngle]
      _ = configuration.interface.criticalPhaseSineRatio :=
        configuration.interface.sin_criticalPhaseAngle hContrast

/-- On the acute-or-grazing interval, supercritical phase incidence is exactly incidence above the
critical phase angle. -/
lemma isSupercriticalPhaseIncidence_iff_criticalPhaseAngle_lt_incidentPhaseAngle
    (configuration : PlanarDielectricWaveConfiguration)
    (hContrast : configuration.interface.HasCriticalAngleContrast)
    (hIncidentAngle : configuration.incidentPhaseAngle ∈ Set.Icc 0 (Real.pi / 2)) :
    configuration.IsSupercriticalPhaseIncidence ↔
      (configuration.interface.criticalPhaseAngle hContrast : ℝ) <
        configuration.incidentPhaseAngle := by
  change configuration.interface.criticalPhaseSineRatio <
      Real.sin configuration.incidentPhaseAngle ↔
    Real.arcsin configuration.interface.criticalPhaseSineRatio <
      configuration.incidentPhaseAngle
  have hAngleIcc :
      configuration.incidentPhaseAngle ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith [Real.pi_pos, hIncidentAngle.1], hIncidentAngle.2⟩
  have hRatioIoo := configuration.interface.criticalPhaseSineRatio_mem_Ioo hContrast
  exact (Real.arcsin_lt_iff_lt_sin
    ⟨by linarith [hRatioIoo.1], hRatioIoo.2.le⟩
      hAngleIcc).symm

namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-!

## E. Critical supplied-candidate grazing

-/

/-- For a supplied electrically phase-matched candidate, critical incident phase data force the
unique zero transmitted normal root, zero whole transmitted attenuation, and zero transmitted
phase normal component.

Here critical incidence is the unconditional sine-threshold equality: it permits equal-speed
grazing and, without an incident-angle range, need not be the interior incoming critical angle.
This result does not construct the transmitted candidate or assert nonzero amplitude. Unguarded
convention statement (review only): it asserts no outgoing behavior. It asserts no evanescence,
total internal reflection, irradiance, or power either. -/
lemma transmitted_normalRoot_data_of_isCriticalPhaseIncidence
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hCritical : configuration.IsCriticalPhaseIncidence) :
    configuration.interface.plane.normalComponent
          configuration.transmitted.waveVector.phaseVector = 0 ∧
      configuration.transmitted.waveVector.attenuationVector = 0 ∧
      ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector = 0 := by
  have hRadicand : configuration.transmittedNormalRadicand = 0 :=
    (configuration.transmittedNormalRadicand_eq_zero_iff_isCriticalPhaseIncidence
      hIncidentDispersion hIncidentAttenuation).mpr hCritical
  have hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
          configuration.incident.waveVector.attenuationVector = 0 := by
    simp [hIncidentAttenuation, OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  exact h.transmitted_normalRoot_data_of_transmittedNormalRadicand_eq_zero
    hTransmittedDispersion hIncidentTangentialAttenuation hRadicand

/-- For a supplied electrically phase-matched and dispersive candidate, sine-threshold critical
incident phase data force the transmitted phase vector to be tangent to the interface.

Transmitted dispersion and the derived zero attenuation exclude a zero transmitted phase vector,
so this is genuine tangency. The result still asserts no nonzero electric amplitude. Unguarded
convention statement (review only): it asserts no outgoing behavior, irradiance, or power. -/
lemma transmittedPhaseAngle_eq_pi_div_two_of_isCriticalPhaseIncidence
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hCritical : configuration.IsCriticalPhaseIncidence) :
    configuration.transmittedPhaseAngle = Real.pi / 2 := by
  have hData := h.transmitted_normalRoot_data_of_isCriticalPhaseIncidence
    hIncidentDispersion hTransmittedDispersion hIncidentAttenuation hCritical
  change configuration.interface.plane.angleToSide .positive
    configuration.transmitted.waveVector.phaseVector = Real.pi / 2
  exact (configuration.interface.plane.angleToSide_eq_pi_div_two_iff_normalComponent_eq_zero
    .positive configuration.transmitted.waveVector.phaseVector).mpr hData.1

end IsElectricPhaseMatched

end PlanarDielectricWaveConfiguration

end
end Optics
