/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.NormalFlux
public import Physlib.Optics.HarmonicFlux.PolarizerModePower

/-!
# Flux normalization regression for material Jones modes

## i. Overview

This file constructs a nonvacuous singleton normalization fixture for the P5b modal Malus bridge.
The medium has relative parameters `ε = 4` and `μ = 1`, hence wave impedance `1 / 2`. A unit Jones
linear-polarization state therefore has unit irradiance. Its carrier propagates along coordinate
zero through oppositely oriented input and output planes.

Direct actual-field integration gives signed normal fluxes `-1` and `1`, pinned by
`polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux` and
`polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux`. The incident and outgoing
role assignments are pinned by
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal` and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`, whose proofs use those
computations rather than a modal-power assumption.

## ii. Key results

- `polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal`: input normalization.
- `polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`: output normalization.

## iii. Table of contents

- A. Exact material and geometry
- B. Signed unit-flux computations
- C. Incident and outgoing normalization

## iv. References

Counting measure gives one discrete profile weight; it is not claimed to be geometric aperture
area. The singleton normalization supplies no modal completeness or physical polarizer model.

-/

@[expose] public section

namespace Optics
open Electromagnetism Electromagnetism.ThreeDimension
open MeasureTheory Space Time
open scoped Interval Real
noncomputable section
/-!
## A. Exact material and geometry

-/

/-- The exact medium whose wave impedance is one half. -/
def polarizerModeNormalizationRegressionMedium : HomogeneousIsotropicMedium where
  ε := 4
  μ := 1
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The exact regression medium has wave impedance one half. -/
lemma polarizerModeNormalizationRegressionMedium_waveImpedance :
    polarizerModeNormalizationRegressionMedium.waveImpedance = 1 / 2 := by
  norm_num [HomogeneousIsotropicMedium.waveImpedance,
    polarizerModeNormalizationRegressionMedium]
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

/-- The positive coordinate-zero propagation direction. -/
def polarizerModeNormalizationRegressionDirection : Space.Direction 3 where
  unit := Space.basis 0
  norm := by simp

/-- The coordinate polarization frame with transverse axes one and two. -/
def polarizerModeNormalizationRegressionFrame :
    PolarizationFrame polarizerModeNormalizationRegressionDirection where
  axis := fun i => EuclideanSpace.single i.succ 1
  orthonormal_axis :=
    EuclideanSpace.orthonormal_single.comp Fin.succ (Fin.succ_injective 2)
  orientation := by
    ext i
    fin_cases i <;> simp [crossProduct, polarizerModeNormalizationRegressionDirection]

/-- The output plane has outward normal along propagation, with its outgoing flux sign pinned by
`polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux` and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`. -/
def polarizerModeNormalizationRegressionOutputPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := polarizerModeNormalizationRegressionDirection

/-- The input plane has outward normal opposite propagation, with its incident flux sign pinned by
`polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux` and
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal`. -/
def polarizerModeNormalizationRegressionInputPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := ⟨-Space.basis 0, by simp⟩

/-- The singleton profile samples the spatial origin. -/
def polarizerModeNormalizationRegressionPoint : Unit → Space := fun _ => 0

/-!

## B. Signed unit-flux computations

-/

/-- Every linear axis has directly computed outgoing integrated normal flux one, pinned by
`polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux` and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`. -/
lemma polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux
    (axis : Real.Angle) :
    HarmonicFieldProfile.integratedMeanNormalFlux Measure.count
      polarizerModeNormalizationRegressionOutputPlane
      ((MaterialJonesMode.linearPolarizationFamily axis
        polarizerModeNormalizationRegressionMedium
        polarizerModeNormalizationRegressionFrame 1 (by norm_num)).modeProfile
          polarizerModeNormalizationRegressionPoint ()) = 1 := by
  rw [← (MaterialJonesMode.linearPolarizationFamily axis
    polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
    (by norm_num)).integral_intervalAverage_normalFlux_eq_integratedMeanNormalFlux Measure.count
      polarizerModeNormalizationRegressionOutputPlane
      polarizerModeNormalizationRegressionPoint () (0 : Time)]
  simp only [MeasureTheory.integral_count, Fintype.sum_unique,
    MaterialJonesMode.linearPolarizationFamily, MaterialJonesMode.family]
  rw [ComplexMonochromaticPlaneWave.ofReal_electricField,
    ComplexMonochromaticPlaneWave.ofReal_magneticFieldStrength,
    JonesVector.normalComponent_toMaterialPlaneWave_intervalAverage_poyntingVector,
    JonesVector.materialPlaneWaveIrradiance, JonesVector.intensity_linearPolarization,
    polarizerModeNormalizationRegressionMedium_waveImpedance]
  norm_num [polarizerModeNormalizationRegressionOutputPlane,
    polarizerModeNormalizationRegressionFrame,
    polarizerModeNormalizationRegressionDirection, PolarizationFrame.propagationVector,
    OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- Every linear axis has directly computed incident integrated normal flux minus one, pinned by
`polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux` and
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal`. -/
lemma polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux
    (axis : Real.Angle) :
    HarmonicFieldProfile.integratedMeanNormalFlux Measure.count
      polarizerModeNormalizationRegressionInputPlane
      ((MaterialJonesMode.linearPolarizationFamily axis
        polarizerModeNormalizationRegressionMedium
        polarizerModeNormalizationRegressionFrame 1 (by norm_num)).modeProfile
          polarizerModeNormalizationRegressionPoint ()) = -1 := by
  rw [← (MaterialJonesMode.linearPolarizationFamily axis
    polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
    (by norm_num)).integral_intervalAverage_normalFlux_eq_integratedMeanNormalFlux Measure.count
      polarizerModeNormalizationRegressionInputPlane
      polarizerModeNormalizationRegressionPoint () (0 : Time)]
  simp only [MeasureTheory.integral_count, Fintype.sum_unique,
    MaterialJonesMode.linearPolarizationFamily, MaterialJonesMode.family]
  rw [ComplexMonochromaticPlaneWave.ofReal_electricField,
    ComplexMonochromaticPlaneWave.ofReal_magneticFieldStrength,
    JonesVector.normalComponent_toMaterialPlaneWave_intervalAverage_poyntingVector,
    JonesVector.materialPlaneWaveIrradiance, JonesVector.intensity_linearPolarization,
    polarizerModeNormalizationRegressionMedium_waveImpedance]
  norm_num [polarizerModeNormalizationRegressionInputPlane,
    polarizerModeNormalizationRegressionFrame,
    polarizerModeNormalizationRegressionDirection, PolarizationFrame.propagationVector,
    OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-!

## C. Incident and outgoing normalization

-/

/-- Every linear axis in the fixture is outgoing flux normalized at the output plane (sentinel:
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`). -/
lemma polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal
    (axis : Real.Angle) :
    HarmonicFieldProfile.IsApertureFluxOrthonormal Measure.count
      polarizerModeNormalizationRegressionOutputPlane .outgoing
      ((MaterialJonesMode.linearPolarizationFamily axis
        polarizerModeNormalizationRegressionMedium
        polarizerModeNormalizationRegressionFrame 1 (by norm_num)).modeProfile
          polarizerModeNormalizationRegressionPoint) := by
  refine ⟨fun _ _ => Integrable.of_finite, ?_, ?_⟩
  · intro i
    cases i
    exact polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux axis
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-- Every linear axis in the fixture is incident flux normalized at the input plane (sentinel:
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal`). -/
lemma polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal
    (axis : Real.Angle) :
    HarmonicFieldProfile.IsApertureFluxOrthonormal Measure.count
      polarizerModeNormalizationRegressionInputPlane .incident
      ((MaterialJonesMode.linearPolarizationFamily axis
        polarizerModeNormalizationRegressionMedium
        polarizerModeNormalizationRegressionFrame 1 (by norm_num)).modeProfile
          polarizerModeNormalizationRegressionPoint) := by
  refine ⟨fun _ _ => Integrable.of_finite, ?_, ?_⟩
  · intro i
    cases i
    exact polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux axis
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

end

end Optics
