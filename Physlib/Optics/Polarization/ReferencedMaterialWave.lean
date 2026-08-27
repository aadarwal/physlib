/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryAmplitude
public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryMagnetic
public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwell
public import Physlib.Optics.Polarization.MaterialWave
public import Physlib.Optics.Polarization.PlanarFrame

/-!
# Plane-referenced complex material Jones waves

## i. Overview

This file connects a propagating framed Jones amplitude to the complex-carrier plane-wave API at
the stored point of an oriented affine plane. A referenced material Jones wave has real wave
vector `(omega / v) k` and has the supplied framed Jones vector as its complete electric phasor
after multiplication by the stored-point spatial factor.

Those two conditions determine the corresponding referenced magnetic-induction amplitude, scaled
by inverse wave speed. The material identity `mu * v = Z` then converts its tangential
magnetic-field-strength amplitude to the inverse-impedance-scaled propagation quarter-turn.
Consequently both tangential electric and magnetic-field-strength amplitudes can be projected by
the common planar-frame formulas while preserving the affine-point carrier phase.

This is a propagating, positive-frequency, homogeneous-isotropic material connector. It permits
the zero Jones vector and either sign of the propagation direction's plane-normal component. It
does not cover a complex attenuating propagation vector, impose a boundary law, solve a Fresnel
equation, or state an observable or power result. Unguarded convention statement (review only):
it assigns no incident, reflected, or transmitted role.

## ii. Key results

- `IsReferencedMaterialJonesWave`: the connected material wave-vector and referenced-electric-
  phasor conditions.
- `IsZeroOrReferencedMaterialJonesWave`: the role-neutral guarded form that retains an arbitrary
  dummy carrier when both the electric amplitude and Jones data vanish.
- `IsZeroOrReferencedMaterialJonesWave.components_eq_zero_of_electricAmplitude_eq_zero`: a zero
  electric amplitude forces zero Jones data in either guarded branch.
- `IsZeroOrReferencedMaterialJonesWave.reframe_of_electricAmplitude_eq_zero`: proved-zero Jones
  data may be represented in any propagation frame without constraining the dummy carrier.
- `JonesVector.isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave`: the canonical existing
  real material-wave construction satisfies the connector with its Jones data rephased to the
  plane point.
- `IsReferencedMaterialJonesWave.isPhaseDirectedInto_iff`: strict phase direction is exactly the
  corresponding signed propagation-frame normal condition.
- `IsReferencedMaterialJonesWave.propagationVector_eq_vectorReflection_of_waveVector_eq`: complex
  wave-vector reflection descends to reflection of the real frame propagation vector.
- `PolarizationFrame.complexCross_propagationVector_embedJones`: the complex propagation
  quarter-turn.
- `IsReferencedMaterialJonesWave.isTransverse` and `.isDispersionMatched`: the material-shell
  results.
- `IsReferencedMaterialJonesWave.referencedMagneticAmplitude`: the referenced magnetic-induction
  phasor.
- `IsReferencedMaterialJonesWave.referencedMediumJointElectricTraceAmplitude_fst`: the exact
  referenced tangential electric amplitude.
- `IsReferencedMaterialJonesWave.referencedMediumJointElectricTraceAmplitude_snd`: the exact
  referenced normal electric-displacement amplitude.
- `IsReferencedMaterialJonesWave.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq`:
  the exact inverse-impedance tangential magnetic amplitude.
- `IsReferencedMaterialJonesWave.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame`
  and `.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame`: their common
  planar-frame coordinate forms.

## iii. Table of contents

- A. Referenced material Jones data
- B. Complex frame algebra
- C. Propagation direction and reflection
- D. Material-shell results
- E. Referenced boundary amplitudes

## iv. References

The construction is derived from the imported Physlib complex-carrier, material, boundary-
amplitude, and polarization-frame APIs. No external formal development is copied or translated
here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Matrix
  InnerProductSpace PolarizationFrame
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

/-!

## A. Referenced material Jones data

-/

/-- A complex plane-wave candidate whose propagating material wave vector and electric phasor at
an oriented plane's stored point are represented by a polarization frame and Jones vector.

The Jones vector is a full-vector electric amplitude in the frame, not an interface-tangent
normalized coefficient. -/
structure IsReferencedMaterialJonesWave
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (J : JonesVector) : Prop where
  /-- The real propagating wave vector has material magnitude `omega / v`. -/
  waveVector_eq : wave.waveVector =
    ComplexWaveVector.ofReal
      ((wave.angularFrequency / medium.waveSpeed) • frame.propagationVector)
  /-- The stored-point-referenced electric amplitude is the framed Jones phasor. -/
  referencedElectricAmplitude_eq :
    wave.waveVector.spatialFactor plane.point • wave.electricAmplitude = frame.embedJones J

/-- Either a candidate and its Jones data are both electrically zero, leaving carrier labels
arbitrary, or they satisfy the complete referenced propagating material Jones connector. -/
def IsZeroOrReferencedMaterialJonesWave
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (J : JonesVector) : Prop :=
  (wave.electricAmplitude = 0 ∧ J.components = 0) ∨
    IsReferencedMaterialJonesWave plane medium wave frame J

namespace JonesVector

/-- Embedding the existing framed real material wave as complex carrier data gives the expected
real material wave vector. -/
lemma ofReal_toMaterialPlaneWave_waveVector (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hFrequency : 0 < angularFrequency) :
    (ComplexMonochromaticPlaneWave.ofReal
      (J.toMaterialPlaneWave medium frame angularFrequency hFrequency)).waveVector =
        ComplexWaveVector.ofReal
          ((angularFrequency / medium.waveSpeed) • frame.propagationVector) := by
  rw [ComplexMonochromaticPlaneWave.ofReal_waveVector]
  rfl

/-- Embedding the existing framed real material wave as complex carrier data recovers the framed
Jones electric amplitude. -/
lemma ofReal_toMaterialPlaneWave_electricAmplitude (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hFrequency : 0 < angularFrequency) :
    (ComplexMonochromaticPlaneWave.ofReal
      (J.toMaterialPlaneWave medium frame angularFrequency hFrequency)).electricAmplitude =
        frame.embedJones J := by
  ext i
  change (frame.electricReal J i : ℂ) +
      Complex.I * (frame.electricImag J i : ℂ) = frame.embedJones J i
  rw [frame.embedJones_apply_eq_electricReal_add_electricImag_mul_I]
  ring

/-- The complex embedding of the existing framed material wave satisfies the referenced material
Jones connector. Its returned Jones data includes the exact stored-point spatial phase. -/
lemma isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave
    (J : JonesVector) (plane : OrientedAffineHyperplane 3)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hFrequency : 0 < angularFrequency) :
    IsReferencedMaterialJonesWave plane medium
      (ComplexMonochromaticPlaneWave.ofReal
        (J.toMaterialPlaneWave medium frame angularFrequency hFrequency)) frame
      (JonesVector.scale
        ((ComplexMonochromaticPlaneWave.ofReal
          (J.toMaterialPlaneWave medium frame angularFrequency hFrequency)).waveVector.spatialFactor
            plane.point) J) := by
  constructor
  · exact J.ofReal_toMaterialPlaneWave_waveVector medium frame angularFrequency hFrequency
  · rw [J.ofReal_toMaterialPlaneWave_electricAmplitude]
    exact (frame.embedJones_scale _ J).symm

end JonesVector

namespace PolarizationFrame

variable {direction : Space.Direction 3}

/-!

## B. Complex frame algebra

-/

private lemma complexAxis_eq_ofReal (frame : PolarizationFrame direction) (i : Fin 2) :
    frame.complexAxis i = ComplexWaveVector.ofReal (frame.axis i) := rfl

/-- Complex crossing by the frame propagation vector acts on embedded Jones data by the
propagation quarter-turn `(J₀, J₁) ↦ (-J₁, J₀)`. -/
lemma complexCross_propagationVector_embedJones (frame : PolarizationFrame direction)
    (J : JonesVector) :
    complexCross (ComplexWaveVector.ofReal frame.propagationVector) (frame.embedJones J) =
      frame.embedJones J.propagationCross := by
  rw [embedJones, embedJones, Fin.sum_univ_two, Fin.sum_univ_two,
    complexAxis_eq_ofReal, complexAxis_eq_ofReal,
    complexCross_add_right, complexCross_smul_right, complexCross_smul_right,
    complexCross_ofReal, complexCross_ofReal,
    frame.propagationVector_cross_axis_zero,
    frame.propagationVector_cross_axis_one]
  ext i
  simp [JonesVector.propagationCross]
  ring

/-- The complex-bilinear pairing of the frame propagation vector with an embedded Jones
amplitude vanishes. -/
lemma bilinearDot_propagationVector_embedJones (frame : PolarizationFrame direction)
    (J : JonesVector) :
    ComplexWaveVector.bilinearDot (ComplexWaveVector.ofReal frame.propagationVector)
      (frame.embedJones J) = 0 := by
  rw [embedJones, Fin.sum_univ_two, complexAxis_eq_ofReal, complexAxis_eq_ofReal,
    ComplexWaveVector.bilinearDot_add_right,
    ComplexWaveVector.bilinearDot_smul_right,
    ComplexWaveVector.bilinearDot_smul_right,
    ComplexWaveVector.bilinearDot_ofReal,
    ComplexWaveVector.bilinearDot_ofReal,
    frame.inner_propagationVector_axis,
    frame.inner_propagationVector_axis]
  simp

end PolarizationFrame

namespace IsReferencedMaterialJonesWave

variable {plane : OrientedAffineHyperplane 3} {medium : HomogeneousIsotropicMedium}
  {wave : ComplexMonochromaticPlaneWave} {direction : Space.Direction 3}
  {frame : PolarizationFrame direction} {J : JonesVector}

/-!

## C. Propagation direction and reflection

-/

/-- A referenced propagating material wave is phase-directed into a geometric side exactly when
its real frame propagation vector has strictly positive side-signed normal component.

This translates a supplied geometric direction. Unguarded convention statement (review only): it
does not infer incident, reflected, outgoing, group-velocity, or power meaning from a wave label. -/
lemma isPhaseDirectedInto_iff
    (h : IsReferencedMaterialJonesWave plane medium wave frame J)
    (side : OrientedAffineHyperplane.Side) :
    wave.waveVector.IsPhaseDirectedInto plane side ↔
      0 < side.sign * plane.normalComponent frame.propagationVector := by
  rw [ComplexWaveVector.IsPhaseDirectedInto,
    ComplexWaveVector.hyperplaneNormalComponent_re, h.waveVector_eq,
    ComplexWaveVector.phaseVector_ofReal]
  simp only [OrientedAffineHyperplane.normalComponent, inner_smul_right]
  have hScale : 0 < wave.angularFrequency / medium.waveSpeed :=
    div_pos wave.angularFrequency_pos medium.waveSpeed_pos
  cases side
  · simp only [OrientedAffineHyperplane.Side.sign_negative, neg_one_mul, neg_pos]
    constructor
    · intro hNegative
      rcases (mul_neg_iff.mp hNegative) with hSigns | hSigns
      · exact hSigns.2
      · exact (not_lt_of_ge hScale.le hSigns.1).elim
    · exact mul_neg_of_pos_of_neg hScale
  · simp only [OrientedAffineHyperplane.Side.sign_positive, one_mul]
    exact mul_pos_iff_of_pos_left hScale

/-- Equal-frequency referenced waves whose complex wave vectors are related by hyperplane
reflection have real frame propagation vectors related by the same reflection.

The result is role-neutral: callers must separately prove the wave-vector equality and its
physical branch-selection meaning. -/
lemma propagationVector_eq_vectorReflection_of_waveVector_eq
    {incident reflected : ComplexMonochromaticPlaneWave}
    {incidentDirection reflectedDirection : Space.Direction 3}
    {incidentFrame : PolarizationFrame incidentDirection}
    {reflectedFrame : PolarizationFrame reflectedDirection}
    {incidentJones reflectedJones : JonesVector}
    (hIncident : IsReferencedMaterialJonesWave plane medium incident incidentFrame incidentJones)
    (hReflected : IsReferencedMaterialJonesWave plane medium reflected reflectedFrame
      reflectedJones)
    (hFrequency : reflected.angularFrequency = incident.angularFrequency)
    (hWaveVector : reflected.waveVector =
      ComplexWaveVector.hyperplaneReflection plane incident.waveVector) :
    reflectedFrame.propagationVector =
      plane.vectorReflection incidentFrame.propagationVector := by
  have hVector := congrArg ComplexWaveVector.phaseVector hWaveVector
  rw [hReflected.waveVector_eq, hIncident.waveVector_eq,
    ComplexWaveVector.phaseVector_ofReal,
    ComplexWaveVector.phaseVector_hyperplaneReflection_eq_vectorReflection,
    ComplexWaveVector.phaseVector_ofReal, hFrequency] at hVector
  have hScaleNe : incident.angularFrequency / medium.waveSpeed ≠ 0 :=
    ne_of_gt (div_pos incident.angularFrequency_pos medium.waveSpeed_pos)
  apply (smul_right_injective _ hScaleNe)
  change (incident.angularFrequency / medium.waveSpeed) • reflectedFrame.propagationVector =
    (incident.angularFrequency / medium.waveSpeed) •
      plane.vectorReflection incidentFrame.propagationVector
  rw [← plane.vectorReflection_smul]
  exact hVector

/-!

## D. Material-shell results

-/

/-- Referenced material Jones data is bilinearly transverse to its material wave vector. -/
lemma isTransverse (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    wave.IsTransverse := by
  rw [ComplexMonochromaticPlaneWave.IsTransverse, h.waveVector_eq,
    ComplexWaveVector.ofReal_smul, ComplexWaveVector.bilinearDot_smul_left]
  apply mul_eq_zero_of_right
  have hpair := congrArg
    (ComplexWaveVector.bilinearDot (ComplexWaveVector.ofReal frame.propagationVector))
    h.referencedElectricAmplitude_eq
  rw [ComplexWaveVector.bilinearDot_smul_right,
    frame.bilinearDot_propagationVector_embedJones] at hpair
  exact (mul_eq_zero.mp hpair).resolve_left
    (wave.waveVector.spatialFactor_ne_zero plane.point)

/-- Referenced material Jones data lies on the supplied homogeneous medium's propagating
dispersion shell. -/
lemma isDispersionMatched (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    wave.IsDispersionMatched medium := by
  have hscale :
      (wave.angularFrequency / medium.waveSpeed) *
          (wave.angularFrequency / medium.waveSpeed) =
        medium.ε * medium.μ * wave.angularFrequency ^ 2 := by
    rw [← pow_two, div_pow, medium.waveSpeed_sq]
    field_simp [medium.ε_ne_zero, medium.μ_ne_zero]
  rw [ComplexMonochromaticPlaneWave.IsDispersionMatched, h.waveVector_eq,
    ComplexWaveVector.bilinearDot_ofReal, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    frame.propagationVector_norm]
  norm_num
  exact_mod_cast hscale

/-- Referenced material Jones data gives a source-free macroscopic Maxwell solution in the
supplied homogeneous isotropic medium. -/
lemma isMacroscopicMaxwellSolution
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    medium.IsMacroscopicMaxwellSolution wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium) 0 0 :=
  wave.isMacroscopicMaxwellSolution medium h.isTransverse h.isDispersionMatched

/-!

## E. Referenced boundary amplitudes

-/

/-- The magnetic-induction phasor referenced to the plane's stored point is inverse wave speed
times the embedded propagation-quarter-turn Jones amplitude. -/
lemma referencedMagneticAmplitude
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    wave.waveVector.spatialFactor plane.point • wave.magneticAmplitude =
      (((medium.waveSpeed⁻¹ : ℝ) : ℂ) • frame.embedJones J.propagationCross) := by
  let spatialFactor := wave.waveVector.spatialFactor plane.point
  have hElectric : spatialFactor • wave.electricAmplitude = frame.embedJones J := by
    simpa only [spatialFactor] using h.referencedElectricAmplitude_eq
  change spatialFactor •
      ((wave.angularFrequency : ℂ)⁻¹ •
        complexCross wave.waveVector wave.electricAmplitude) = _
  rw [h.waveVector_eq, ComplexWaveVector.ofReal_smul,
    complexCross_smul_left]
  calc
    _ = ((wave.angularFrequency : ℂ)⁻¹ *
          (wave.angularFrequency / medium.waveSpeed : ℝ)) •
        complexCross (ComplexWaveVector.ofReal frame.propagationVector)
          (spatialFactor • wave.electricAmplitude) := by
      rw [complexCross_smul_right]
      module
    _ = ((wave.angularFrequency : ℂ)⁻¹ *
          (wave.angularFrequency / medium.waveSpeed : ℝ)) •
        frame.embedJones J.propagationCross := by
      rw [hElectric,
        frame.complexCross_propagationVector_embedJones]
    _ = ((medium.waveSpeed⁻¹ : ℝ) : ℂ) •
        frame.embedJones J.propagationCross := by
      congr 1
      push_cast
      field_simp [wave.angularFrequency_ne_zero, medium.waveSpeed_ne_zero]

/-- The first entry of the stored-point-referenced joint electric trace is exactly tangential
projection of the framed Jones phasor. -/
lemma referencedMediumJointElectricTraceAmplitude_fst
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    (ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude
      plane medium wave).1 =
      ComplexWaveVector.hyperplaneTangentialProjection plane (frame.embedJones J) := by
  rw [ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude,
    ComplexMonochromaticPlaneWave.mediumJointElectricTraceAmplitude]
  simp only [Prod.smul_fst]
  rw [← ComplexWaveVector.hyperplaneTangentialProjection_smul,
    h.referencedElectricAmplitude_eq]

/-- The second entry of the stored-point-referenced joint electric trace is the medium
permittivity times the normal component of the framed Jones phasor. -/
lemma referencedMediumJointElectricTraceAmplitude_snd
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    (ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude
      plane medium wave).2 =
      (medium.ε : ℂ) *
        ComplexWaveVector.hyperplaneNormalComponent plane (frame.embedJones J) := by
  rw [ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude,
    ComplexMonochromaticPlaneWave.mediumJointElectricTraceAmplitude]
  simp only [Prod.smul_snd]
  change wave.waveVector.spatialFactor plane.point *
      ((medium.ε : ℂ) *
        ComplexWaveVector.hyperplaneNormalComponent plane wave.electricAmplitude) = _
  calc
    _ = (medium.ε : ℂ) *
        (wave.waveVector.spatialFactor plane.point *
          ComplexWaveVector.hyperplaneNormalComponent plane wave.electricAmplitude) := by ring
    _ = (medium.ε : ℂ) * ComplexWaveVector.hyperplaneNormalComponent plane
        (wave.waveVector.spatialFactor plane.point • wave.electricAmplitude) := by
      congr 1
      simp only [ComplexWaveVector.hyperplaneNormalComponent,
        ComplexWaveVector.bilinearDot_smul_right]
    _ = _ := by rw [h.referencedElectricAmplitude_eq]

/-- The stored-point-referenced tangential magnetic-field-strength amplitude is inverse
impedance times tangential projection of the propagation-quarter-turn Jones phasor. -/
lemma referencedMediumTangentialMagneticFieldStrengthAmplitude_eq
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    ComplexMonochromaticPlaneWave.referencedMediumTangentialMagneticFieldStrengthAmplitude
        plane medium wave =
      (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
        ComplexWaveVector.hyperplaneTangentialProjection plane
          (frame.embedJones J.propagationCross)) := by
  rw [ComplexMonochromaticPlaneWave.referencedMediumTangentialMagneticFieldStrengthAmplitude,
    ComplexMonochromaticPlaneWave.mediumTangentialMagneticFieldStrengthAmplitude]
  calc
    _ = ((medium.μ⁻¹ : ℝ) : ℂ) •
        ComplexWaveVector.hyperplaneTangentialProjection plane
          (wave.waveVector.spatialFactor plane.point • wave.magneticAmplitude) := by
      rw [ComplexWaveVector.hyperplaneTangentialProjection_smul]
      module
    _ = ((medium.μ⁻¹ : ℝ) : ℂ) •
        ComplexWaveVector.hyperplaneTangentialProjection plane
          (((medium.waveSpeed⁻¹ : ℝ) : ℂ) •
            frame.embedJones J.propagationCross) := by
      rw [h.referencedMagneticAmplitude]
    _ = (((medium.μ⁻¹ * medium.waveSpeed⁻¹ : ℝ) : ℂ) •
        ComplexWaveVector.hyperplaneTangentialProjection plane
          (frame.embedJones J.propagationCross)) := by
      rw [ComplexWaveVector.hyperplaneTangentialProjection_smul, smul_smul]
      congr 1
      norm_cast
    _ = (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
        ComplexWaveVector.hyperplaneTangentialProjection plane
          (frame.embedJones J.propagationCross)) := by
      have hCoefficient : medium.μ⁻¹ * medium.waveSpeed⁻¹ =
          medium.waveImpedance⁻¹ := by
        rw [← mul_inv, medium.μ_mul_waveSpeed]
      rw [hCoefficient]

/-- In an aligned common plane frame, the referenced tangential electric amplitude has
coordinates `(J₀, c J₁)`, where `c` is the signed normal propagation component. -/
lemma referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
    (h : IsReferencedMaterialJonesWave plane medium wave frame J)
    (planeFrame : PolarizationFrame plane.normal)
    (halign : frame.axis 0 = planeFrame.axis 0) :
    (ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude
      plane medium wave).1 =
      planeFrame.embedJones
        (JonesVector.ofComponents (J.components 0)
          ((plane.normalComponent frame.propagationVector : ℂ) * J.components 1)) := by
  rw [h.referencedMediumJointElectricTraceAmplitude_fst]
  exact hyperplaneTangentialProjection_embedJones_of_axis_zero_eq
    (direction := direction) plane planeFrame frame J halign

/-- In an aligned common plane frame, the referenced tangential magnetic-field-strength
amplitude has coordinates `Z⁻¹ (-J₁, c J₀)`. -/
lemma referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
    (h : IsReferencedMaterialJonesWave plane medium wave frame J)
    (planeFrame : PolarizationFrame plane.normal)
    (halign : frame.axis 0 = planeFrame.axis 0) :
    ComplexMonochromaticPlaneWave.referencedMediumTangentialMagneticFieldStrengthAmplitude
        plane medium wave =
      (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
        planeFrame.embedJones
          (JonesVector.ofComponents (-J.components 1)
            ((plane.normalComponent frame.propagationVector : ℂ) * J.components 0))) := by
  rw [h.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq]
  rw [hyperplaneTangentialProjection_embedJones_propagationCross_of_axis_zero_eq
      (direction := direction) plane planeFrame frame J halign]

end IsReferencedMaterialJonesWave

namespace IsZeroOrReferencedMaterialJonesWave

variable {plane : OrientedAffineHyperplane 3} {medium : HomogeneousIsotropicMedium}
  {wave : ComplexMonochromaticPlaneWave} {direction : Space.Direction 3}
  {frame : PolarizationFrame direction} {J : JonesVector}

/-- Under the zero-or-connected guard, a zero electric amplitude forces every Jones coordinate to
vanish, including in the connected material-wave branch. -/
lemma components_eq_zero_of_electricAmplitude_eq_zero
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J)
    (hElectric : wave.electricAmplitude = 0) :
    J.components = 0 := by
  rcases h with hZero | hMaterial
  · exact hZero.2
  · have hEmbed : frame.embedJones J = 0 := by
      rw [← hMaterial.referencedElectricAmplitude_eq, hElectric, smul_zero]
    ext i
    have hCoordinate := congrArg (fun v ↦ ⟪frame.complexAxis i, v⟫_ℂ) hEmbed
    simpa [PolarizationFrame.inner_complexAxis_embedJones] using hCoordinate

/-- Proved-zero guarded Jones data may be represented in any propagation frame.

Only the connector used by the proof is changed. The wave and its arbitrary dummy carrier data
remain unchanged. -/
lemma reframe_of_electricAmplitude_eq_zero
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J)
    {newDirection : Space.Direction 3} (newFrame : PolarizationFrame newDirection)
    (hElectric : wave.electricAmplitude = 0) :
    IsZeroOrReferencedMaterialJonesWave plane medium wave newFrame J := by
  exact Or.inl ⟨hElectric, h.components_eq_zero_of_electricAmplitude_eq_zero hElectric⟩

/-- The zero-or-connected guard gives the same planar-frame tangential electric formula while
preserving arbitrary carrier data in its zero branch. -/
lemma referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J)
    (planeFrame : PolarizationFrame plane.normal)
    (halign : frame.axis 0 = planeFrame.axis 0) :
    (ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude
      plane medium wave).1 =
      planeFrame.embedJones
        (JonesVector.ofComponents (J.components 0)
          ((plane.normalComponent frame.propagationVector : ℂ) * J.components 1)) := by
  rcases h with ⟨hElectric, hJones⟩ | hMaterial
  · have hReferenced :
        ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude
          plane medium wave = 0 :=
      (ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude_eq_zero_iff
        plane medium wave).mpr hElectric
    rw [hReferenced]
    simp [PolarizationFrame.embedJones, hJones]
  · exact hMaterial.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      planeFrame halign

/-- The zero-or-connected guard gives the same planar-frame tangential magnetic formula while
preserving arbitrary carrier data in its zero branch. -/
lemma referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J)
    (planeFrame : PolarizationFrame plane.normal)
    (halign : frame.axis 0 = planeFrame.axis 0) :
    ComplexMonochromaticPlaneWave.referencedMediumTangentialMagneticFieldStrengthAmplitude
        plane medium wave =
      (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
        planeFrame.embedJones
          (JonesVector.ofComponents (-J.components 1)
            ((plane.normalComponent frame.propagationVector : ℂ) * J.components 0))) := by
  rcases h with ⟨hElectric, hJones⟩ | hMaterial
  · have hMagneticZero :=
      referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_zero_of_electricAmplitude_eq_zero
        plane medium wave hElectric
    rw [hMagneticZero]
    simp [PolarizationFrame.embedJones, hJones]
  · exact hMaterial.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      planeFrame halign

end IsZeroOrReferencedMaterialJonesWave

end

end Optics
