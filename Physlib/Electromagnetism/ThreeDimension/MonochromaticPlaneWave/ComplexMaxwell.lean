/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MacroscopicMaxwellEquations
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexCalculus
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersion

/-!
# Maxwell equations for complex-amplitude plane waves

## i. Overview

This module connects `ComplexMonochromaticPlaneWave` calculation data to the differential
macroscopic Maxwell equations for its ordinary real `E`, `D`, `B`, and `H` fields. Named exact
time-derivative, divergence, and curl identities specialize the shared carrier calculus to those
physical field roles.

Gauss's magnetic law and Faraday's law hold for every off-shell candidate because the magnetic
amplitude was constructed as `B0 = omega^-1 (K cross E0)`. Gauss's electric law requires
complex-bilinear electric transversality. The source-free Ampere--Maxwell law additionally uses
the complex-bilinear material shell `K dot K = epsilon * mu * omega ^ 2`.

A transverse dispersion-matched candidate, including the zero-electric-amplitude candidate,
therefore solves the source-free macroscopic equations with the canonical constitutive fields
`D = epsilon E` and `H = mu^-1 B`. This is a sufficient forward result: no converse or nonzero
electric-amplitude claim is made here.

The complex data remains a calculation device for ordinary real fields, not a second complex
Maxwell-field theory. This module selects no square-root or interface branch and makes no
outgoing, evanescent-wave, power, potential, or gauge claim.

## ii. Key results

- `ComplexMonochromaticPlaneWave.gaussLawElectric`: transverse `D` is divergence-free.
- `ComplexMonochromaticPlaneWave.gaussLawMagnetic`: constructed `B` is divergence-free off shell.
- `ComplexMonochromaticPlaneWave.faradayLaw`: constructed `E` and `B` obey Faraday's law off shell.
- `ComplexMonochromaticPlaneWave.ampereMaxwellLaw`: transverse matched fields obey the
  source-free Ampere--Maxwell law.
- `ComplexMonochromaticPlaneWave.isSourceFreeMacroscopicMaxwell`: all four source-free laws with
  their regularity hypotheses.
- `ComplexMonochromaticPlaneWave.isMacroscopicMaxwellSolution`: the fixed-medium solution.

## iii. Table of contents

- A. Exact field differential identities
- B. Individual Maxwell laws
- C. Source-free fixed-medium solutions

## iv. References

This file combines Physlib's complex-carrier calculus, material-dispersion algebra, and existing
macroscopic Maxwell predicate. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Exact field differential identities

-/

private lemma realFieldOfAmplitude_differentiable_time
    (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (x : Space) :
    Differentiable ℝ (fun t ↦ wave.realFieldOfAmplitude amplitude t x) :=
  (wave.realFieldOfAmplitude_contDiff amplitude 1).differentiable (by norm_num) |>.comp
    (f := fun t ↦ (t, x)) (by fun_prop)

private lemma realFieldOfAmplitude_differentiable_space
    (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (t : Time) :
    Differentiable ℝ (wave.realFieldOfAmplitude amplitude t) :=
  (wave.realFieldOfAmplitude_contDiff amplitude 1).differentiable (by norm_num) |>.comp
    (f := fun x ↦ (t, x)) (by fun_prop)

/-- The electric-field time derivative is the real field realized from `I * omega * E0`. -/
lemma electricField_timeDeriv (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) :
    ∂ₜ (fun s ↦ wave.electricField s x) t =
      wave.realFieldOfAmplitude
        ((Complex.I * (wave.angularFrequency : ℂ)) • wave.electricAmplitude) t x := by
  exact wave.realFieldOfAmplitude_timeDeriv wave.electricAmplitude t x

/-- The magnetic-induction time derivative is the real field realized from `I * omega * B0`. -/
lemma magneticInduction_timeDeriv (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) :
    ∂ₜ (fun s ↦ wave.magneticInduction s x) t =
      wave.realFieldOfAmplitude
        ((Complex.I * (wave.angularFrequency : ℂ)) • wave.magneticAmplitude) t x := by
  exact wave.realFieldOfAmplitude_timeDeriv wave.magneticAmplitude t x

/-- The electric-field divergence is controlled by the complex-bilinear pairing `K dot E0`. -/
lemma electricField_div (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) :
    (∇ ⬝ wave.electricField t) x =
      (-Complex.I * wave.carrier t x *
        ComplexWaveVector.bilinearDot wave.waveVector wave.electricAmplitude).re := by
  exact wave.realFieldOfAmplitude_div wave.electricAmplitude t x

/-- The magnetic-induction divergence is controlled by the complex-bilinear pairing `K dot B0`. -/
lemma magneticInduction_div (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) :
    (∇ ⬝ wave.magneticInduction t) x =
      (-Complex.I * wave.carrier t x *
        ComplexWaveVector.bilinearDot wave.waveVector wave.magneticAmplitude).re := by
  exact wave.realFieldOfAmplitude_div wave.magneticAmplitude t x

/-- The electric-field curl is the real field realized from `-I * (K cross E0)`. -/
lemma electricField_curl (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) :
    (∇ ⨯ wave.electricField t) x =
      wave.realFieldOfAmplitude
        ((-Complex.I) • complexCross wave.waveVector wave.electricAmplitude) t x := by
  exact wave.realFieldOfAmplitude_curl wave.electricAmplitude t x

/-- The magnetic-induction curl is the real field realized from `-I * (K cross B0)`. -/
lemma magneticInduction_curl (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) :
    (∇ ⨯ wave.magneticInduction t) x =
      wave.realFieldOfAmplitude
        ((-Complex.I) • complexCross wave.waveVector wave.magneticAmplitude) t x := by
  exact wave.realFieldOfAmplitude_curl wave.magneticAmplitude t x

/-- The electric-displacement divergence is `epsilon` times the electric-field divergence. -/
lemma electricDisplacement_div (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (t : Time) (x : Space) :
    (∇ ⬝ wave.electricDisplacement medium t) x =
      medium.ε *
        (-Complex.I * wave.carrier t x *
          ComplexWaveVector.bilinearDot wave.waveVector wave.electricAmplitude).re := by
  change (∇ ⬝ (medium.ε • wave.electricField t)) x = _
  have hspace : Differentiable ℝ (wave.electricField t) :=
    realFieldOfAmplitude_differentiable_space wave wave.electricAmplitude t
  rw [Space.div_smul _ _ hspace, Pi.smul_apply, wave.electricField_div]
  rfl

/-- The electric-displacement time derivative is `epsilon` times the electric-field derivative. -/
lemma electricDisplacement_timeDeriv (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (t : Time) (x : Space) :
    ∂ₜ (fun s ↦ wave.electricDisplacement medium s x) t =
      medium.ε • wave.realFieldOfAmplitude
        ((Complex.I * (wave.angularFrequency : ℂ)) • wave.electricAmplitude) t x := by
  change ∂ₜ (fun s ↦ medium.ε • wave.electricField s x) t = _
  rw [Time.deriv_smul]
  · rw [wave.electricField_timeDeriv]
  · exact realFieldOfAmplitude_differentiable_time wave wave.electricAmplitude x

/-- The magnetic-field-strength curl is `mu^-1` times the magnetic-induction curl. -/
lemma magneticFieldStrength_curl (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (t : Time) (x : Space) :
    (∇ ⨯ wave.magneticFieldStrength medium t) x =
      medium.μ⁻¹ • wave.realFieldOfAmplitude
        ((-Complex.I) • complexCross wave.waveVector wave.magneticAmplitude) t x := by
  change (∇ ⨯ (medium.μ⁻¹ • wave.magneticInduction t)) x = _
  have hspace : Differentiable ℝ (wave.magneticInduction t) :=
    realFieldOfAmplitude_differentiable_space wave wave.magneticAmplitude t
  rw [Space.curl_smul _ _ hspace, Pi.smul_apply, wave.magneticInduction_curl]

private lemma realFieldOfAmplitude_neg (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (t : Time) (x : Space) :
    wave.realFieldOfAmplitude (-amplitude) t x =
      -wave.realFieldOfAmplitude amplitude t x := by
  ext i
  simp [realFieldOfAmplitude_apply]

private lemma faradayAmplitude (wave : ComplexMonochromaticPlaneWave) :
    (-Complex.I) • complexCross wave.waveVector wave.electricAmplitude =
      -((Complex.I * (wave.angularFrequency : ℂ)) • wave.magneticAmplitude) := by
  rw [← wave.angularFrequency_smul_magneticAmplitude, smul_smul, ← neg_smul]
  congr 1
  ring

private lemma IsDispersionMatched.ampereAmplitude
    {wave : ComplexMonochromaticPlaneWave} {medium : HomogeneousIsotropicMedium}
    (h : wave.IsDispersionMatched medium) (hTransverse : wave.IsTransverse) :
    ((medium.μ⁻¹ : ℝ) : ℂ) •
        ((-Complex.I) • complexCross wave.waveVector wave.magneticAmplitude) =
      (medium.ε : ℂ) •
        ((Complex.I * (wave.angularFrequency : ℂ)) • wave.electricAmplitude) := by
  rw [h.waveVector_cross_magneticAmplitude hTransverse]
  simp only [smul_smul]
  congr 1
  push_cast
  field_simp [medium.μ_ne_zero]

/-!

## B. Individual Maxwell laws

-/

/-- The electric displacement has zero divergence when the electric amplitude is bilinearly
transverse. -/
lemma gaussLawElectric (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (hTransverse : wave.IsTransverse)
    (t : Time) (x : Space) :
    (∇ ⬝ wave.electricDisplacement medium t) x = 0 := by
  rw [wave.electricDisplacement_div, hTransverse]
  simp

/-- The magnetic induction of the constructed candidate always has zero divergence. -/
lemma gaussLawMagnetic (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) :
    (∇ ⬝ wave.magneticInduction t) x = 0 := by
  rw [wave.magneticInduction_div,
    wave.bilinearDot_waveVector_magneticAmplitude]
  simp

/-- The constructed ordinary real electric and magnetic fields satisfy Faraday's law off shell. -/
lemma faradayLaw (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    (∇ ⨯ wave.electricField t) x =
      -∂ₜ (fun s ↦ wave.magneticInduction s x) t := by
  rw [wave.electricField_curl, wave.magneticInduction_timeDeriv]
  rw [← wave.realFieldOfAmplitude_neg]
  rw [faradayAmplitude]

/-- Under bilinear transversality and material dispersion, the constitutive fields satisfy the
Ampere--Maxwell law without free current. -/
lemma ampereMaxwellLaw (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (hTransverse : wave.IsTransverse)
    (hDispersion : wave.IsDispersionMatched medium) (t : Time) (x : Space) :
    (∇ ⨯ wave.magneticFieldStrength medium t) x =
      ∂ₜ (fun s ↦ wave.electricDisplacement medium s x) t := by
  rw [wave.magneticFieldStrength_curl, wave.electricDisplacement_timeDeriv]
  ext i
  have hi := congrArg (fun v : EuclideanSpace ℂ (Fin 3) ↦ v i)
    (hDispersion.ampereAmplitude hTransverse)
  have hre := congrArg (fun z : ℂ ↦ (wave.carrier t x * z).re) hi
  simp [realFieldOfAmplitude_apply] at hre ⊢
  linear_combination hre

/-!

## C. Source-free fixed-medium solutions

-/

/-- A transverse candidate satisfying complex material dispersion solves the source-free
macroscopic Maxwell equations with its canonical constitutive fields. Zero electric amplitude is
allowed. -/
lemma isSourceFreeMacroscopicMaxwell (wave : ComplexMonochromaticPlaneWave)
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
lemma isMacroscopicMaxwellSolution (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (hTransverse : wave.IsTransverse)
    (hDispersion : wave.IsDispersionMatched medium) :
    medium.IsMacroscopicMaxwellSolution wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium) 0 0 :=
  ⟨wave.isConstitutive medium,
    wave.isSourceFreeMacroscopicMaxwell medium hTransverse hDispersion⟩

end ComplexMonochromaticPlaneWave
end
end ThreeDimension
end Electromagnetism
