/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.MagneticFixedFrequency
public import Physlib.Optics.Polarization.ReferencedMaterialWave

/-!
# Jones equations for a planar dielectric boundary

## i. Overview

This file expresses the stored-point-referenced tangential electric- and magnetic-amplitude
equalities of a planar dielectric configuration in one common plane-normal polarization frame.
Each active wave is represented by full-vector Jones electric data in a propagation frame whose
first axis agrees with the common plane frame. The reflected wave retains the existing zero-field
branch with arbitrary dummy carrier labels.

The common frame uses `u₁ = n × u₀`, fixing the sign that relates its second axis to every
propagation frame. Writing `chi = n dot k-hat` for each signed normal propagation component and
`Y = Z⁻¹` for intrinsic material admittance, the two vector equalities give four scalar equations
without division:

```text
T₀ = I₀ + R₀
chi_t T₁ = chi_i I₁ + chi_r R₁
Y₂ chi_t T₀ = Y₁ chi_i I₀ + Y₁ chi_r R₀
Y₂ T₁ = Y₁ I₁ + Y₁ R₁.
```

The signs are carried by `chi`; in particular a direction into the negative side has negative
`chi` relative to the stored normal, while the reflected label alone proves no such direction.
Axis zero becomes the usual `s` axis and axis one the
full-vector `p` axis when the frames come from non-normal incidence geometry, but the results also
retain caller-selected frames at normal incidence and the grazing case `chi = 0`.

These boundary equations are not yet solved. No coefficient division, nonzero amplitude,
non-grazing condition, angle identification, reflection law, Snell law, Fresnel formula,
observable, irradiance, or power statement is made here. The normal-displacement entry of the
joint electric balance is not asserted redundant by these projection results. The four lemmas
assume only the two stated referenced amplitude equalities, the Jones connector conditions, and
the frame-axis equalities; they do not assume common frequency or electric phase matching.

## ii. Key results

- `HasReferencedJointElectricBalance.jones_component_zero`: the first electric equation.
- `HasReferencedJointElectricBalance.jones_component_one`: the signed-normal second electric
  equation.
- `HasReferencedTangentialMagneticFieldStrengthBalance.jones_component_zero`: the admittance and
  signed-normal first Jones equation.
- `HasReferencedTangentialMagneticFieldStrengthBalance.jones_component_one`: the admittance second
  Jones equation.

## iii. Table of contents

- A. Tangential electric equations
- B. Tangential magnetic equations

## iv. References

The result connects Physlib's existing fixed-frequency boundary reduction, referenced material
Jones connector, and planar-frame projection algebra. No external formal development is copied or
translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space
  InnerProductSpace
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

variable {configuration : PlanarDielectricWaveConfiguration}
  {incidentDirection reflectedDirection transmittedDirection : Space.Direction 3}
  {incidentFrame : PolarizationFrame incidentDirection}
  {reflectedFrame : PolarizationFrame reflectedDirection}
  {transmittedFrame : PolarizationFrame transmittedDirection}
  {incidentJones reflectedJones transmittedJones : JonesVector}

/-!

## A. Tangential electric equations

-/

namespace HasReferencedJointElectricBalance

/-- The first common-plane-frame coordinate of tangential electric balance is
`T₀ = I₀ + R₀`. -/
lemma jones_component_zero (h : configuration.HasReferencedJointElectricBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0) :
    transmittedJones.components 0 =
      incidentJones.components 0 + reflectedJones.components 0 := by
  have hAmplitude := congrArg Prod.fst h
  simp only [Prod.fst_add] at hAmplitude
  rw [hTransmitted.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      planeFrame hTransmittedAlign,
    hIncident.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      planeFrame hIncidentAlign,
    hReflected.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      planeFrame hReflectedAlign] at hAmplitude
  have hCoordinate := congrArg
    (fun v ↦ ⟪planeFrame.complexAxis 0, v⟫_ℂ) hAmplitude
  simpa [inner_add_right, PolarizationFrame.inner_complexAxis_embedJones] using hCoordinate

/-- The second common-plane-frame coordinate of tangential electric balance retains each signed
normal propagation component. -/
lemma jones_component_one (h : configuration.HasReferencedJointElectricBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0) :
    (configuration.interface.plane.normalComponent
        transmittedFrame.propagationVector : ℂ) * transmittedJones.components 1 =
      (configuration.interface.plane.normalComponent
          incidentFrame.propagationVector : ℂ) * incidentJones.components 1 +
        (configuration.interface.plane.normalComponent
          reflectedFrame.propagationVector : ℂ) * reflectedJones.components 1 := by
  have hAmplitude := congrArg Prod.fst h
  simp only [Prod.fst_add] at hAmplitude
  rw [hTransmitted.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      planeFrame hTransmittedAlign,
    hIncident.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      planeFrame hIncidentAlign,
    hReflected.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      planeFrame hReflectedAlign] at hAmplitude
  have hCoordinate := congrArg
    (fun v ↦ ⟪planeFrame.complexAxis 1, v⟫_ℂ) hAmplitude
  simpa [inner_add_right, PolarizationFrame.inner_complexAxis_embedJones] using hCoordinate

end HasReferencedJointElectricBalance

/-!

## B. Tangential magnetic equations

-/

namespace HasReferencedTangentialMagneticFieldStrengthBalance

/-- The tangential magnetic equation carried by the original first Jones coordinate retains
material admittance and each signed normal propagation component. -/
lemma jones_component_zero
    (h : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0) :
    ((configuration.interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
        (configuration.interface.plane.normalComponent
          transmittedFrame.propagationVector : ℂ) * transmittedJones.components 0 =
      ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ) * incidentJones.components 0 +
        ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          (configuration.interface.plane.normalComponent
            reflectedFrame.propagationVector : ℂ) * reflectedJones.components 0 := by
  change
    referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted =
      referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident +
        referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected at h
  rw [hTransmitted.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      planeFrame hTransmittedAlign,
    hIncident.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      planeFrame hIncidentAlign,
    hReflected.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      planeFrame hReflectedAlign] at h
  have hCoordinate := congrArg
    (fun v ↦ ⟪planeFrame.complexAxis 1, v⟫_ℂ) h
  simpa [inner_add_right, inner_smul_right,
    PolarizationFrame.inner_complexAxis_embedJones, mul_assoc] using hCoordinate

/-- The tangential magnetic equation carried by the original second Jones coordinate is the
admittance-weighted balance `Y₂ T₁ = Y₁ I₁ + Y₁ R₁`. -/
lemma jones_component_one
    (h : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0) :
    ((configuration.interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
        transmittedJones.components 1 =
      ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          incidentJones.components 1 +
        ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          reflectedJones.components 1 := by
  change
    referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted =
      referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident +
        referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected at h
  rw [hTransmitted.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      planeFrame hTransmittedAlign,
    hIncident.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      planeFrame hIncidentAlign,
    hReflected.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      planeFrame hReflectedAlign] at h
  have hCoordinate := congrArg
    (fun v ↦ ⟪planeFrame.complexAxis 0, v⟫_ℂ) h
  have hNegated :
      -((configuration.interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          transmittedJones.components 1 =
        -((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
            incidentJones.components 1 +
          -((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
            reflectedJones.components 1 := by
    simpa [inner_add_right, inner_smul_right,
      PolarizationFrame.inner_complexAxis_embedJones] using hCoordinate
  linear_combination -hNegated

end HasReferencedTangentialMagneticFieldStrengthBalance

end PlanarDielectricWaveConfiguration

end

end Optics
