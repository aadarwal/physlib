/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.VectorCalculus
public import Physlib.Electromagnetism.ThreeDimension.MacroscopicMaxwellEquations
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Dispersion

/-!

# Maxwell equations for real monochromatic plane waves

## i. Overview

This module connects the real monochromatic carrier to the differential macroscopic Maxwell
equations. Exact time-derivative, divergence, and curl formulas expose the common travelling
profile derivative. They show that Gauss's magnetic law and Faraday's law hold for every
off-shell candidate because of the built-in magnetic induction, while Gauss's electric law
requires transversality and the Ampère--Maxwell law additionally requires material dispersion.

A transverse dispersion-matched candidate, including the zero-amplitude candidate, therefore
solves the source-free macroscopic Maxwell equations with the canonical constitutive fields
`D = ε E` and `H = B / μ`. The result does not claim that Maxwell equations derived the
cross-product definition of `B`.

The module does not address complex phasors, physical power, handedness, group velocity,
interfaces, evanescent modes, finite beams, potentials, or gauge reconstruction.

## ii. Key results

- `MonochromaticPlaneWave.gaussLawElectric`: transverse `D` is divergence-free.
- `MonochromaticPlaneWave.gaussLawMagnetic`: constructed `B` is divergence-free off shell.
- `MonochromaticPlaneWave.faradayLaw`: the constructed `E` and `B` obey Faraday's law off shell.
- `MonochromaticPlaneWave.ampereMaxwellLaw`: transverse matched fields obey the source-free
  Ampère--Maxwell law.
- `MonochromaticPlaneWave.isSourceFreeMacroscopicMaxwell`: all four source-free equations.
- `MonochromaticPlaneWave.isMacroscopicMaxwellSolution`: the fixed-medium solution.

## iii. Table of contents

- A. Exact differential identities
- B. Individual Maxwell laws
- C. Source-free fixed-medium solutions

## iv. References

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension
namespace MonochromaticPlaneWave

open Space Time InnerProductSpace Matrix ClassicalMechanics

/-!

## A. Exact differential identities

-/

private lemma electricProfile_differentiable (wave : MonochromaticPlaneWave) :
    Differentiable ℝ wave.electricProfile :=
  (wave.electricProfile_contDiff 1).differentiable (by norm_num)

private lemma magneticProfile_differentiable (wave : MonochromaticPlaneWave) :
    Differentiable ℝ wave.magneticProfile :=
  (wave.magneticProfile_contDiff 1).differentiable (by norm_num)

/-- Exact time derivative of the electric field through its travelling profile. -/
lemma electricField_timeDeriv (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    ∂ₜ (fun s => wave.electricField s x) t =
      -wave.phaseVelocity •
        fderiv ℝ wave.electricProfile
          (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1 := by
  have h := congrFun (planeWave_time_deriv (c := wave.phaseVelocity)
    (s := wave.direction) (x := x) wave.electricProfile_differentiable) t
  simpa [electricField, planeWave_eq] using h

/-- Exact time derivative of the magnetic induction through its travelling profile. -/
lemma magneticInduction_timeDeriv (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    ∂ₜ (fun s => wave.magneticInduction s x) t =
      -wave.phaseVelocity •
        fderiv ℝ wave.magneticProfile
          (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1 := by
  have h := congrFun (planeWave_time_deriv (c := wave.phaseVelocity)
    (s := wave.direction) (x := x) wave.magneticProfile_differentiable) t
  simpa [magneticInduction, planeWave_eq] using h

/-- Exact divergence of the electric field through its travelling profile. -/
lemma electricField_div (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    (∇ ⬝ wave.electricField t) x =
      ⟪wave.propagationVector,
        fderiv ℝ wave.electricProfile
          (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1⟫_ℝ := by
  rw [electricField, planeWave_div wave.electricProfile_differentiable]
  rfl

/-- Exact divergence of the magnetic induction through its travelling profile. -/
lemma magneticInduction_div (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    (∇ ⬝ wave.magneticInduction t) x =
      ⟪wave.propagationVector,
        fderiv ℝ wave.magneticProfile
          (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1⟫_ℝ := by
  rw [magneticInduction, planeWave_div wave.magneticProfile_differentiable]
  rfl

/-- Exact curl of the electric field through its travelling profile. -/
lemma electricField_curl (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    (∇ ⨯ wave.electricField t) x =
      wave.propagationVector ⨯ₑ₃
        fderiv ℝ wave.electricProfile
          (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1 := by
  rw [electricField, planeWave_curl wave.electricProfile_differentiable]
  rfl

/-- Exact curl of magnetic induction through its travelling profile. -/
lemma magneticInduction_curl (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    (∇ ⨯ wave.magneticInduction t) x =
      wave.propagationVector ⨯ₑ₃
        fderiv ℝ wave.magneticProfile
          (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1 := by
  rw [magneticInduction, planeWave_curl wave.magneticProfile_differentiable]
  rfl

/-- Exact divergence of the constitutive electric displacement. -/
lemma electricDisplacement_div (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (t : Time) (x : Space) :
    (∇ ⬝ wave.electricDisplacement medium t) x =
      medium.ε *
        ⟪wave.propagationVector,
          fderiv ℝ wave.electricProfile
            (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1⟫_ℝ := by
  change (∇ ⬝ (medium.ε • wave.electricField t)) x = _
  have hspace : Differentiable ℝ (wave.electricField t) :=
    (wave.electricField_contDiff 1).differentiable (by norm_num) |>.comp
      (f := fun x => (t, x)) (by fun_prop)
  rw [Space.div_smul _ _ hspace, Pi.smul_apply, wave.electricField_div]
  rfl

/-- Exact time derivative of the constitutive electric displacement. -/
lemma electricDisplacement_timeDeriv (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (t : Time) (x : Space) :
    ∂ₜ (fun s => wave.electricDisplacement medium s x) t =
      medium.ε •
        (-wave.phaseVelocity •
          fderiv ℝ wave.electricProfile
            (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1) := by
  change ∂ₜ (fun s => medium.ε • wave.electricField s x) t = _
  rw [Time.deriv_smul]
  · rw [wave.electricField_timeDeriv]
  · exact (wave.electricField_contDiff 1).differentiable (by norm_num) |>.comp
      (f := fun s => (s, x)) (by fun_prop)

/-- Exact curl of the constitutive magnetic field strength. -/
lemma magneticFieldStrength_curl (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (t : Time) (x : Space) :
    (∇ ⨯ wave.magneticFieldStrength medium t) x =
      medium.μ⁻¹ •
        (wave.propagationVector ⨯ₑ₃
          fderiv ℝ wave.magneticProfile
            (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1) := by
  change (∇ ⨯ (medium.μ⁻¹ • wave.magneticInduction t)) x = _
  have hspace : Differentiable ℝ (wave.magneticInduction t) :=
    (wave.magneticInduction_contDiff 1).differentiable (by norm_num) |>.comp
      (f := fun x => (t, x)) (by fun_prop)
  rw [Space.curl_smul _ _ hspace, Pi.smul_apply, wave.magneticInduction_curl]

private lemma IsDispersionMatched.ampereCoefficient
    {wave : MonochromaticPlaneWave} {medium : HomogeneousIsotropicMedium}
    (h : wave.IsDispersionMatched medium) :
    medium.μ⁻¹ * (wave.waveNumber / wave.angularFrequency) =
      medium.ε * wave.phaseVelocity := by
  rw [h.waveNumber_div_angularFrequency_eq_waveSpeed_inv,
    h.phaseVelocity_eq_waveSpeed]
  have hsquare := medium.waveSpeed_sq
  field_simp [medium.μ_ne_zero, medium.waveSpeed_ne_zero] at ⊢ hsquare
  nlinarith [hsquare]

/-!

## B. Individual Maxwell laws

-/

/-- The electric displacement has zero divergence when the electric amplitude is transverse. -/
lemma gaussLawElectric (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (hTransverse : wave.IsTransverse)
    (t : Time) (x : Space) :
    (∇ ⬝ wave.electricDisplacement medium t) x = 0 := by
  rw [wave.electricDisplacement_div,
    hTransverse.electricProfile_fderiv]
  simp

/-- The magnetic induction of the candidate always has zero divergence. -/
lemma gaussLawMagnetic (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    (∇ ⬝ wave.magneticInduction t) x = 0 := by
  rw [wave.magneticInduction_div, wave.magneticProfile_fderiv_transverse]

/-- The constructed electric and magnetic fields satisfy Faraday's law off shell. -/
lemma faradayLaw (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    (∇ ⨯ wave.electricField t) x =
      -∂ₜ (fun s => wave.magneticInduction s x) t := by
  rw [wave.electricField_curl, wave.magneticInduction_timeDeriv,
    wave.magneticProfile_fderiv_eq_cross_electricProfile_fderiv]
  simp only [smul_smul]
  rw [← neg_smul]
  have hcoefficient :
      -(-wave.phaseVelocity * (wave.waveNumber / wave.angularFrequency)) = 1 := by
    rw [phaseVelocity]
    field_simp [wave.waveNumber_ne_zero, wave.angularFrequency_ne_zero]
  rw [hcoefficient, one_smul]

/-- Under transversality and material dispersion, the constitutive fields satisfy the
Ampère--Maxwell law without free current. -/
lemma ampereMaxwellLaw (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (hTransverse : wave.IsTransverse)
    (hDispersion : wave.IsDispersionMatched medium) (t : Time) (x : Space) :
    (∇ ⨯ wave.magneticFieldStrength medium t) x =
      ∂ₜ (fun s => wave.electricDisplacement medium s x) t := by
  have hprofile : ⟪wave.propagationVector,
      fderiv ℝ wave.electricProfile
        (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) 1⟫_ℝ = 0 :=
    IsTransverse.electricProfile_fderiv wave hTransverse _
  rw [wave.magneticFieldStrength_curl, wave.electricDisplacement_timeDeriv,
    wave.magneticProfile_fderiv_eq_cross_electricProfile_fderiv,
    Space.cross_smul, wave.propagationVector_cross_cross _ hprofile]
  simp only [smul_smul]
  rw [hDispersion.ampereCoefficient]
  simp

/-!

## C. Source-free fixed-medium solutions

-/

/-- A transverse candidate satisfying material dispersion solves the source-free macroscopic
Maxwell equations with its canonical constitutive fields. Zero electric amplitude is allowed. -/
lemma isSourceFreeMacroscopicMaxwell (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (hTransverse : wave.IsTransverse)
    (hDispersion : wave.IsDispersionMatched medium) :
    IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium) := by
  refine ⟨(wave.electricField_contDiff 1).differentiable (by norm_num),
    (wave.electricDisplacement_contDiff medium 1).differentiable (by norm_num),
    (wave.magneticInduction_contDiff 1).differentiable (by norm_num),
    (wave.magneticFieldStrength_contDiff medium 1).differentiable (by norm_num),
    ?_, ?_, ?_, ?_⟩
  · exact wave.gaussLawElectric medium hTransverse
  · exact wave.gaussLawMagnetic
  · intro t x
    simpa using wave.ampereMaxwellLaw medium hTransverse hDispersion t x
  · exact wave.faradayLaw

/-- A transverse dispersion-matched candidate is a source-free solution of the supplied
homogeneous isotropic medium. -/
lemma isMacroscopicMaxwellSolution (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (hTransverse : wave.IsTransverse)
    (hDispersion : wave.IsDispersionMatched medium) :
    medium.IsMacroscopicMaxwellSolution wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium) 0 0 :=
  ⟨wave.isConstitutive medium,
    wave.isSourceFreeMacroscopicMaxwell medium hTransverse hDispersion⟩

end MonochromaticPlaneWave
end ThreeDimension
end Electromagnetism
