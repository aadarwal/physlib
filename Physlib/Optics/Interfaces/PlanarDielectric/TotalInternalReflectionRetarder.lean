/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.WavePlate
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalFresnel
public import Physlib.Optics.Polarization.Mueller.Algebra

/-!
# Total-internal-reflection Jones retardance

## i. Overview

This file packages the two unit-modulus Fresnel reflection coefficients evaluated at the purely
imaginary transmitted normal factor `-I * decayRatio` as a diagonal Jones matrix in abstract
`s`/`p` coordinates. A strictly positive `decayRatio` gives the physical positive-normal-decay
branch; the algebraic results below state explicitly when only a positive incident factor is
needed. The file identifies the matrix, up to its common `s` reflection phase, with the existing
ideal linear-retarder component.

In Physlib's positive-time phasor convention the coefficient phases are `phi_s` and `phi_p`,
while a positive retarder parameter `rho` gives the relative eigenvalue `exp (-I * rho)`.
Consequently the induced retarder parameter is

```text
rho = phi_s - phi_p.
```

Matrix self-composition therefore adds this retarder parameter. It represents two physical
reflections only after a caller externally identifies the intermediate output and input `s`/`p`
coordinates.

## ii. Scope

The self-composition results below are component-level Jones statements, not typed frame maps.
They omit the geometry and coordinate transport between two distinct reflecting faces, the common
propagation phase between the faces, and the entrance and exit interfaces of a prism. They
therefore do not yet define or claim a complete Fresnel-rhomb model. The coefficients remain raw
electric-field amplitudes, not power-normalized modal amplitudes.

## iii. Key results

- `PlanarDielectricInterface.totalInternalReflectionJonesMatrix`: the diagonal reflected Jones
  transform in abstract `s`/`p` coordinates.
- `PlanarDielectricInterface.totalInternalReflectionJonesMatrix_eq_scaled_linearRetarder`: exact
  factorization into a common reflection phase and an ideal retarder.
- `PlanarDielectricInterface.totalInternalReflectionJonesMatrix_act_equalAmplitudeRelativePhase`:
  the induced named relative-phase shift on equal-amplitude Jones data.
- `PlanarDielectricInterface.totalInternalReflectionJonesMatrix_isUnitary`: unitarity of the
  one-bounce Jones transform on the positive-incident branch.
- `PlanarDielectricInterface.totalInternalReflectionJonesMatrix_comp_self_eq_scaled_linearRetarder`:
  retardance addition under matrix self-composition.
- `PlanarDielectricWaveConfiguration.reflectedJones_eq_totalInternalReflectionJonesMatrix_act`:
  connection to the boundary-selected reflected Jones data.

## iv. Table of contents

- A. The total-internal-reflection Jones transform
- B. Retarder factorization
- C. Matrix self-composition
- D. Boundary-selected reflected wave

## v. References

The result is derived from Physlib's complex Fresnel boundary solution and its existing retarder
phase convention. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open Matrix

noncomputable section

private lemma JonesMatrix.IsUnitary.scale_of_norm_eq_one {M : JonesMatrix} (hM : M.IsUnitary)
    {z : ℂ} (hz : ‖z‖ = 1) : (M.scale z).IsUnitary := by
  rw [JonesMatrix.IsUnitary, Matrix.mem_unitaryGroup_iff'] at hM ⊢
  have hMConj : M.entriesᴴ * M.entries = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hM
  rw [JonesMatrix.scale_entries, star_smul]
  have hzStar : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hz]
    norm_num
  calc
    (star z • M.entriesᴴ) * (z • M.entries) =
        (star z * z) • (M.entriesᴴ * M.entries) := by
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    _ = 1 := by rw [hzStar, one_smul, hMConj]

namespace PlanarDielectricInterface

/-!

## A. The total-internal-reflection Jones transform

-/

/-- The diagonal Jones transform of one total internal reflection in abstract `s`/`p` coordinates.

The first coordinate is multiplied by the full-vector `s` reflection coefficient and the second
by the full-vector `p` reflection coefficient. No propagation phase away from the interface
reference point is included. The connected wrapper below supplies the propagation-oriented frame
interpretation. -/
def totalInternalReflectionJonesMatrix (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) : JonesMatrix :=
  ⟨!![
    interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ)), 0;
    0, interface.complexPFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ))]⟩

/-- The entries of the one-bounce total-internal-reflection Jones transform. -/
@[simp]
lemma totalInternalReflectionJonesMatrix_entries (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).entries =
      !![
        interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ)), 0;
        0, interface.complexPFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ))] := rfl

/-- One total internal reflection acts diagonally on abstract `s`/`p` components. -/
lemma totalInternalReflectionJonesMatrix_act (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) (J : JonesVector) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).act J =
      JonesVector.ofComponents
        (interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ)) * J.components 0)
        (interface.complexPFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ)) * J.components 1) := by
  ext i
  fin_cases i <;>
    simp [JonesMatrix.act_components, totalInternalReflectionJonesMatrix, Fin.sum_univ_two]

/-!

## B. Retarder factorization

-/

/-- The reflected `p` phase relative to the reflected `s` phase. -/
def totalInternalReflectionRelativePhase (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) : Real.Angle :=
  interface.pTotalInternalReflectionPhaseShift chi_i decayRatio -
    interface.sTotalInternalReflectionPhaseShift chi_i decayRatio

/-- The ideal-retarder parameter induced by one total internal reflection.

It is the negative of the `p`-relative-to-`s` phase because `linearRetarderPhase rho` uses the
eigenvalue `exp (-I * rho)`. -/
def totalInternalReflectionRetardance (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) : Real.Angle :=
  interface.sTotalInternalReflectionPhaseShift chi_i decayRatio -
    interface.pTotalInternalReflectionPhaseShift chi_i decayRatio

/-- The total-internal-reflection retardance is the negative of the reflected `p-s` phase. -/
lemma totalInternalReflectionRetardance_eq_neg_relativePhase
    (interface : PlanarDielectricInterface) (chi_i decayRatio : ℝ) :
    interface.totalInternalReflectionRetardance chi_i decayRatio =
      -interface.totalInternalReflectionRelativePhase chi_i decayRatio := by
  simp [totalInternalReflectionRetardance, totalInternalReflectionRelativePhase]

/-- On the physical positive-factor branch, the reflected `p-s` phase is the difference of the
two closed arctangent phase formulas. -/
lemma totalInternalReflectionRelativePhase_eq_two_arctan_sub
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    interface.totalInternalReflectionRelativePhase chi_i decayRatio =
      2 • (Real.arctan
        ((interface.negativeMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.positiveMedium.waveImpedance⁻¹ * chi_i)) : Real.Angle) -
      2 • (Real.arctan
        ((interface.positiveMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.negativeMedium.waveImpedance⁻¹ * chi_i)) : Real.Angle) := by
  rw [totalInternalReflectionRelativePhase,
    interface.pTotalInternalReflectionPhaseShift_eq_two_arctan hIncident hDecay,
    interface.sTotalInternalReflectionPhaseShift_eq_two_arctan hIncident hDecay]

/-- On the physical positive-factor branch, the induced retarder parameter is the difference of
the two closed arctangent phase formulas. -/
lemma totalInternalReflectionRetardance_eq_two_arctan_sub
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    interface.totalInternalReflectionRetardance chi_i decayRatio =
      2 • (Real.arctan
        ((interface.positiveMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.negativeMedium.waveImpedance⁻¹ * chi_i)) : Real.Angle) -
      2 • (Real.arctan
        ((interface.negativeMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.positiveMedium.waveImpedance⁻¹ * chi_i)) : Real.Angle) := by
  rw [totalInternalReflectionRetardance,
    interface.sTotalInternalReflectionPhaseShift_eq_two_arctan hIncident hDecay,
    interface.pTotalInternalReflectionPhaseShift_eq_two_arctan hIncident hDecay]

/-- On the positive-incident branch, the `p` reflection coefficient is the `s`
coefficient times the named relative phase. -/
lemma complexPFresnelReflectionCoefficient_eq_s_mul_relativePhase
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    interface.complexPFresnelReflectionCoefficient (chi_i : ℂ)
        (-Complex.I * (decayRatio : ℂ)) =
      interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ)) *
        (interface.totalInternalReflectionRelativePhase chi_i decayRatio).toCircle := by
  rw [interface.complexSFresnelReflectionCoefficient_eq_phaseCircle_of_neg_I_mul hIncident,
    interface.complexPFresnelReflectionCoefficient_eq_phaseCircle_of_neg_I_mul hIncident]
  simp only [totalInternalReflectionRelativePhase, sub_eq_add_neg,
    Real.Angle.toCircle_add, Real.Angle.toCircle_neg, Circle.coe_mul, Circle.coe_inv]
  field_simp [Circle.coe_ne_zero]

/-- A total-internal-reflection Jones transform is an ideal zero-axis linear retarder multiplied
by the common `s` reflection phase. -/
lemma totalInternalReflectionJonesMatrix_eq_scaled_linearRetarder
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    interface.totalInternalReflectionJonesMatrix chi_i decayRatio =
      (JonesMatrix.linearRetarder 0
        (interface.totalInternalReflectionRetardance chi_i decayRatio)).scale
          (interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
            (-Complex.I * (decayRatio : ℂ))) := by
  apply JonesMatrix.ext
  rw [JonesMatrix.scale_entries, JonesMatrix.linearRetarder_zero_axis_entries]
  have hRelative :=
    interface.complexPFresnelReflectionCoefficient_eq_s_mul_relativePhase
      (decayRatio := decayRatio) hIncident
  ext i j
  fin_cases i <;> fin_cases j
  · simp [totalInternalReflectionJonesMatrix]
  · simp [totalInternalReflectionJonesMatrix]
  · simp [totalInternalReflectionJonesMatrix]
  · simpa [totalInternalReflectionJonesMatrix, JonesMatrix.linearRetarderPhase,
      totalInternalReflectionRetardance, totalInternalReflectionRelativePhase] using hRelative

/-- One total-internal-reflection matrix adds its named reflected `p-s` phase to equal-amplitude
Jones data, up to the common `s` reflection phase. -/
lemma totalInternalReflectionJonesMatrix_act_equalAmplitudeRelativePhase
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (inputPhase : Real.Angle) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).act
        (JonesVector.equalAmplitudeRelativePhase inputPhase) =
      JonesVector.scale
        (interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ)))
        (JonesVector.equalAmplitudeRelativePhase
          (inputPhase + interface.totalInternalReflectionRelativePhase chi_i decayRatio)) := by
  rw [interface.totalInternalReflectionJonesMatrix_eq_scaled_linearRetarder hIncident,
    JonesMatrix.scale_act,
    JonesMatrix.linearRetarder_zero_axis_act_equalAmplitudeRelativePhase,
    interface.totalInternalReflectionRetardance_eq_neg_relativePhase]
  simp

/-- The one-bounce total-internal-reflection Jones transform preserves raw Jones intensity on the
positive-incident branch. -/
lemma totalInternalReflectionJonesMatrix_act_intensity
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (J : JonesVector) :
    ((interface.totalInternalReflectionJonesMatrix chi_i decayRatio).act J).intensity =
      J.intensity := by
  rw [interface.totalInternalReflectionJonesMatrix_eq_scaled_linearRetarder hIncident,
    JonesMatrix.scale_act,
    JonesVector.intensity_scale_of_norm_eq_one
      (interface.complexSFresnelReflectionCoefficient_norm_of_neg_I_mul hIncident),
    JonesMatrix.linearRetarder_act_intensity]

/-- The one-bounce total-internal-reflection Jones transform is algebraically unitary in the raw
Jones `s`/`p` coordinate space on the positive-incident branch. -/
lemma totalInternalReflectionJonesMatrix_isUnitary
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).IsUnitary := by
  rw [interface.totalInternalReflectionJonesMatrix_eq_scaled_linearRetarder hIncident]
  exact (JonesMatrix.linearRetarder_isUnitary 0
    (interface.totalInternalReflectionRetardance chi_i decayRatio)).scale_of_norm_eq_one
      (interface.complexSFresnelReflectionCoefficient_norm_of_neg_I_mul hIncident)

/-- The Mueller action of one total internal reflection equals that of its induced ideal retarder;
the common unit-modulus reflection phase is unobservable in Stokes data. -/
lemma totalInternalReflectionJonesMatrix_mueller_eq_linearRetarder
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).mueller =
      (JonesMatrix.linearRetarder 0
        (interface.totalInternalReflectionRetardance chi_i decayRatio)).mueller := by
  rw [interface.totalInternalReflectionJonesMatrix_eq_scaled_linearRetarder hIncident]
  exact JonesMatrix.mueller_scale_of_norm_eq_one
    (interface.complexSFresnelReflectionCoefficient_norm_of_neg_I_mul hIncident) _

/-!

## C. Matrix self-composition

-/

/-- Self-composition of the total-internal-reflection Jones matrix adds its retardance.

The common scalar is the square of the one-copy `s` reflection coefficient. Interpreting this
self-composition as two physical reflections requires an external identification of the
intermediate coordinates; the statement supplies neither that identification nor propagation
phase between spatially distinct reflecting faces. -/
lemma totalInternalReflectionJonesMatrix_comp_self_eq_scaled_linearRetarder
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).comp
        (interface.totalInternalReflectionJonesMatrix chi_i decayRatio) =
      (JonesMatrix.linearRetarder 0
        (interface.totalInternalReflectionRetardance chi_i decayRatio +
          interface.totalInternalReflectionRetardance chi_i decayRatio)).scale
        ((interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ))) ^ 2) := by
  rw [interface.totalInternalReflectionJonesMatrix_eq_scaled_linearRetarder hIncident]
  apply JonesMatrix.ext
  simp only [JonesMatrix.comp, JonesMatrix.scale_entries]
  rw [JonesMatrix.linearRetarder_zero_axis_entries,
    JonesMatrix.linearRetarder_zero_axis_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two,
      JonesMatrix.linearRetarderPhase_add]
  all_goals ring

/-- If matrix self-composition accumulates quarter-wave retardance, it is a positive quarter-wave
plate up to a common unit phase. -/
lemma totalInternalReflectionJonesMatrix_comp_self_eq_scaled_quarterWavePlate
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i)
    (hQuarter : interface.totalInternalReflectionRetardance chi_i decayRatio +
        interface.totalInternalReflectionRetardance chi_i decayRatio =
      ((Real.pi / 2 : ℝ) : Real.Angle)) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).comp
        (interface.totalInternalReflectionJonesMatrix chi_i decayRatio) =
      (JonesMatrix.quarterWavePlate 0).scale
        ((interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ))) ^ 2) := by
  rw [interface.totalInternalReflectionJonesMatrix_comp_self_eq_scaled_linearRetarder
    hIncident, hQuarter]
  rfl

/-- If matrix self-composition accumulates negative quarter-wave retardance, it is a negative
quarter-wave plate up to a common unit phase. -/
lemma totalInternalReflectionJonesMatrix_comp_self_eq_scaled_negativeQuarterWavePlate
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i)
    (hQuarter : interface.totalInternalReflectionRetardance chi_i decayRatio +
        interface.totalInternalReflectionRetardance chi_i decayRatio =
      ((-Real.pi / 2 : ℝ) : Real.Angle)) :
    (interface.totalInternalReflectionJonesMatrix chi_i decayRatio).comp
        (interface.totalInternalReflectionJonesMatrix chi_i decayRatio) =
      (JonesMatrix.negativeQuarterWavePlate 0).scale
        ((interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
          (-Complex.I * (decayRatio : ℂ))) ^ 2) := by
  rw [interface.totalInternalReflectionJonesMatrix_comp_self_eq_scaled_linearRetarder
    hIncident, hQuarter]
  rfl

end PlanarDielectricInterface

namespace PlanarDielectricWaveConfiguration

open ClassicalMechanics Electromagnetism.ThreeDimension Space InnerProductSpace
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

/-!

## D. Boundary-selected reflected wave

-/

/-- The Jones data selected by the complex Fresnel boundary equations is exactly the action of
the total-internal-reflection Jones transform on the incident Jones data.

This is a coordinate equality from the incident propagation-oriented `s`/`p` frame to the
separately declared reflected propagation-oriented `s`/`p` frame. It does not identify their
underlying physical transverse spaces without the supplied frame-alignment hypotheses. When the
reflected field vanishes, the reflected frame may remain arbitrary dummy data and the result is
the corresponding zero-coordinate equality. -/
lemma reflectedJones_eq_totalInternalReflectionJonesMatrix_act
    {configuration : PlanarDielectricWaveConfiguration}
    {incidentDirection reflectedDirection : Space.Direction 3}
    {incidentFrame : PolarizationFrame incidentDirection}
    {reflectedFrame : PolarizationFrame reflectedDirection}
    {incidentJones reflectedJones transmittedRawJones : JonesVector}
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : configuration.reflected.electricAmplitude ≠ 0 →
      reflectedFrame.axis 0 =
        (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    reflectedJones =
      (configuration.interface.totalInternalReflectionJonesMatrix
        (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
        (Real.sqrt (-configuration.transmittedNormalRadicand) /
          (configuration.incident.angularFrequency /
            configuration.interface.positiveMedium.waveSpeed))).act incidentJones := by
  have hSolved := complexFresnel_components_of_referenced_balances hElectric hMagnetic
    hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hReflection
      hIncidentNormal
  rw [configuration.positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
    hRadicand] at hSolved
  rw [configuration.interface.totalInternalReflectionJonesMatrix_act]
  ext i
  fin_cases i
  · exact hSolved.1
  · exact hSolved.2.2.1

end PlanarDielectricWaveConfiguration

end

end Optics
