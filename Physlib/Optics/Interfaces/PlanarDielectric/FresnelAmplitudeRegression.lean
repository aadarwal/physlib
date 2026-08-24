/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelAmplitude
public import Physlib.Optics.Interfaces.PlanarDielectric.JonesBoundaryRegression

/-!
# Fresnel-amplitude solution regressions

## i. Overview

This file checks the scalar Fresnel solution against the independently established exact Jones
boundary fixture and against four boundary cases of its hypotheses. The existing fixture's manual
linear proof remains in `JonesBoundaryRegression`, which does not import the general solution.
Here the same four boundary equations are passed through the general solution and compared with the
independently recorded coefficient tuple

```text
(r_s, t_s, r_p, t_p) = (5/11, 16/11, -1/5, 8/5).
```

At normal incidence the fixture media give `(1/3, 4/3, -1/3, 4/3)`, showing the sign change of
the propagation-oriented full-vector `p` reflection coefficient. In the scalar case
`chi_t = 0`, the same media give `(1, 2, 1, 4)`; the proof uses the quotient results and hence
checks that they require no division by `chi_t`. A matched-medium case uses a zero reflected
amplitude and deliberately sets `chi_r = chi_i`, testing the zero-reflection branch rather
than the active reflected-root equation. Finally, a different-medium homogeneous system with zero
incident amplitude is proved to have only zero reflected and transmitted amplitudes.

The boundary-case checks are scalar-system regressions. They do not construct phase-matched
wave configurations, select propagation branches, or assert irradiance or power laws.

## ii. Key results

- `jonesBoundaryRegression_fresnelCoefficients_of_balances`: the general solution applied to the
  existing connected boundary fixture.
- `jonesBoundaryRegression_fresnelCoefficient_values`: the four exact coefficient values.
- `fresnelAmplitudeRegression_normalIncidence`: the full-vector normal-incidence signs.
- `fresnelAmplitudeRegression_transmittedGrazing`: the zero-transmitted-normal case.
- `fresnelAmplitudeRegression_zeroReflection`: the arbitrary-reflected-normal zero-field branch.
- `fresnelAmplitudeRegression_zeroInput`: uniqueness of the zero output for zero input.

## iii. Table of contents

- A. Independent exact-fixture comparison
- B. Normal and grazing coefficient cases
- C. Zero-reflection and zero-input branches

## iv. References

The regressions use only the imported Physlib Jones boundary fixture and Fresnel scalar solution. No
external formal development is copied or translated here.
-/

@[expose] public section

namespace Optics

open Electromagnetism
open PlanarDielectricWaveConfiguration

noncomputable section

/-!

## A. Independent exact-fixture comparison

-/

/-- Applying the connected general solution to the existing Jones boundary fixture gives its four
Fresnel coefficients. The proof does not use the fixture's manual coefficient proof. -/
lemma jonesBoundaryRegression_fresnelCoefficients_of_balances {rS tS rP tP : ℂ}
    (hElectric :
      (jonesBoundaryRegressionConfiguration rS tS rP tP).HasReferencedJointElectricBalance)
    (hMagnetic :
      PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance
        (jonesBoundaryRegressionConfiguration rS tS rP tP)) :
    rS = (jonesBoundaryRegressionInterface.sFresnelReflectionCoefficient (4 / 5) (3 / 5) : ℂ) ∧
      tS = (jonesBoundaryRegressionInterface.sFresnelTransmissionCoefficient
        (4 / 5) (3 / 5) : ℂ) ∧
      rP = (jonesBoundaryRegressionInterface.pFresnelReflectionCoefficient
        (4 / 5) (3 / 5) : ℂ) ∧
      tP = (jonesBoundaryRegressionInterface.pFresnelTransmissionCoefficient
        (4 / 5) (3 / 5) : ℂ) := by
  have hSolved :=
    PlanarDielectricWaveConfiguration.fresnel_components_of_referenced_balances
      hElectric hMagnetic jonesBoundaryRegressionPlaneFrame
      (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
        jonesBoundaryRegressionIncidentJones)
      (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
        (jonesBoundaryRegressionReflectedJones rS rP)))
      (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
        (jonesBoundaryRegressionTransmittedJones tS tP))
      (by rfl) (by rfl) (by rfl)
      (Or.inr (by
        dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
        rw [jonesBoundaryRegression_incidentNormalComponent,
          jonesBoundaryRegression_reflectedNormalComponent]
        norm_num))
      (by
        dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
        rw [jonesBoundaryRegression_incidentNormalComponent,
          jonesBoundaryRegression_transmittedNormalComponent]
        exact jonesBoundaryRegressionInterface.sFresnelDenominator_ne_zero
          (by norm_num) (by norm_num))
      (by
        dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
        rw [jonesBoundaryRegression_incidentNormalComponent,
          jonesBoundaryRegression_transmittedNormalComponent]
        exact jonesBoundaryRegressionInterface.pFresnelDenominator_ne_zero
          (by norm_num) (by norm_num))
  simpa [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface,
    jonesBoundaryRegressionIncidentJones, jonesBoundaryRegressionReflectedJones,
    jonesBoundaryRegressionTransmittedJones,
    jonesBoundaryRegression_incidentNormalComponent,
    jonesBoundaryRegression_transmittedNormalComponent] using hSolved

/-- On the exact `3-4-5` Jones boundary fixture, the four general Fresnel coefficients equal the
independently recorded manual solution. -/
lemma jonesBoundaryRegression_fresnelCoefficient_values :
    jonesBoundaryRegressionInterface.sFresnelReflectionCoefficient (4 / 5) (3 / 5) = 5 / 11 ∧
      jonesBoundaryRegressionInterface.sFresnelTransmissionCoefficient (4 / 5) (3 / 5) =
        16 / 11 ∧
      jonesBoundaryRegressionInterface.pFresnelReflectionCoefficient (4 / 5) (3 / 5) =
        -1 / 5 ∧
      jonesBoundaryRegressionInterface.pFresnelTransmissionCoefficient (4 / 5) (3 / 5) =
        8 / 5 := by
  norm_num [PlanarDielectricInterface.sFresnelReflectionCoefficient,
    PlanarDielectricInterface.sFresnelTransmissionCoefficient,
    PlanarDielectricInterface.pFresnelReflectionCoefficient,
    PlanarDielectricInterface.pFresnelTransmissionCoefficient,
    PlanarDielectricInterface.sFresnelDenominator,
    PlanarDielectricInterface.pFresnelDenominator, jonesBoundaryRegressionInterface,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]

/-!

## B. Normal and grazing coefficient cases

-/

/-- With the regression media at normal incidence, the full-vector coefficients are
`(1/3, 4/3, -1/3, 4/3)`. -/
lemma fresnelAmplitudeRegression_normalIncidence :
    jonesBoundaryRegressionInterface.sFresnelReflectionCoefficient 1 1 = 1 / 3 ∧
      jonesBoundaryRegressionInterface.sFresnelTransmissionCoefficient 1 1 = 4 / 3 ∧
      jonesBoundaryRegressionInterface.pFresnelReflectionCoefficient 1 1 = -1 / 3 ∧
      jonesBoundaryRegressionInterface.pFresnelTransmissionCoefficient 1 1 = 4 / 3 := by
  norm_num [PlanarDielectricInterface.sFresnelReflectionCoefficient,
    PlanarDielectricInterface.sFresnelTransmissionCoefficient,
    PlanarDielectricInterface.pFresnelReflectionCoefficient,
    PlanarDielectricInterface.pFresnelTransmissionCoefficient,
    PlanarDielectricInterface.sFresnelDenominator,
    PlanarDielectricInterface.pFresnelDenominator, jonesBoundaryRegressionInterface,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]

/-- The quotient results include the scalar transmitted-grazing case `chi_t = 0`. For the
regression media and `chi_i = 1`, the coefficients are `(1, 2, 1, 4)`. -/
lemma fresnelAmplitudeRegression_transmittedGrazing :
    jonesBoundaryRegressionInterface.sFresnelReflectionCoefficient 1 0 = 1 ∧
      jonesBoundaryRegressionInterface.sFresnelTransmissionCoefficient 1 0 = 2 ∧
      jonesBoundaryRegressionInterface.pFresnelReflectionCoefficient 1 0 = 1 ∧
      jonesBoundaryRegressionInterface.pFresnelTransmissionCoefficient 1 0 = 4 := by
  have hSolvedS := jonesBoundaryRegressionInterface.solve_sFresnel
    (chi_i := 1) (chi_r := -1) (chi_t := 0) (I := 1) (R := 1) (T := 2)
    (by norm_num)
    (by
      simp only [jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
        jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
      norm_num)
    (Or.inr (by norm_num))
    (jonesBoundaryRegressionInterface.sFresnelDenominator_ne_zero (by norm_num) (by norm_num))
  have hSolvedP := jonesBoundaryRegressionInterface.solve_pFresnel
    (chi_i := 1) (chi_r := -1) (chi_t := 0) (I := 1) (R := 1) (T := 4)
    (by norm_num)
    (by
      simp only [jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
        jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
      norm_num)
    (Or.inr (by norm_num))
    (jonesBoundaryRegressionInterface.pFresnelDenominator_ne_zero (by norm_num) (by norm_num))
  rcases hSolvedS with ⟨hsR, hsT⟩
  rcases hSolvedP with ⟨hpR, hpT⟩
  simp only [mul_one] at hsR hsT hpR hpT
  constructor
  · exact_mod_cast hsR.symm
  constructor
  · exact_mod_cast hsT.symm
  constructor
  · exact_mod_cast hpR.symm
  · exact_mod_cast hpT.symm

/-!

## C. Zero-reflection and zero-input branches

-/

/-- An equal-medium interface used to test the zero-reflection solution branch. -/
def fresnelAmplitudeRegressionMatchedInterface : PlanarDielectricInterface where
  plane := jonesBoundaryRegressionPlane
  negativeMedium := jonesBoundaryRegressionNegativeMedium
  positiveMedium := jonesBoundaryRegressionNegativeMedium

/-- For a matched interface, the zero-reflection branch leaves the reflected normal component
unrestricted. This exact check uses `chi_r = chi_i = 1`, which is not the active reflected-root
relation `chi_r = -chi_i`, and gives `(0, 1, 0, 1)`. -/
lemma fresnelAmplitudeRegression_zeroReflection :
    (1 : ℝ) ≠ -1 ∧
      fresnelAmplitudeRegressionMatchedInterface.sFresnelReflectionCoefficient 1 1 = 0 ∧
      fresnelAmplitudeRegressionMatchedInterface.sFresnelTransmissionCoefficient 1 1 = 1 ∧
      fresnelAmplitudeRegressionMatchedInterface.pFresnelReflectionCoefficient 1 1 = 0 ∧
      fresnelAmplitudeRegressionMatchedInterface.pFresnelTransmissionCoefficient 1 1 = 1 := by
  have hSolvedS := fresnelAmplitudeRegressionMatchedInterface.solve_sFresnel
    (chi_i := 1) (chi_r := 1) (chi_t := 1) (I := 1) (R := 0) (T := 1)
    (by norm_num)
    (by
      simp only [fresnelAmplitudeRegressionMatchedInterface]
      rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
      norm_num)
    (Or.inl rfl)
    (fresnelAmplitudeRegressionMatchedInterface.sFresnelDenominator_ne_zero
      (by norm_num) (by norm_num))
  have hSolvedP := fresnelAmplitudeRegressionMatchedInterface.solve_pFresnel
    (chi_i := 1) (chi_r := 1) (chi_t := 1) (I := 1) (R := 0) (T := 1)
    (by norm_num)
    (by
      simp only [fresnelAmplitudeRegressionMatchedInterface]
      rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv]
      norm_num)
    (Or.inl rfl)
    (fresnelAmplitudeRegressionMatchedInterface.pFresnelDenominator_ne_zero
      (by norm_num) (by norm_num))
  rcases hSolvedS with ⟨hsR, hsT⟩
  rcases hSolvedP with ⟨hpR, hpT⟩
  simp only [mul_one] at hsR hsT hpR hpT
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hsR.symm
  · exact_mod_cast hsT.symm
  · exact_mod_cast hpR.symm
  · exact_mod_cast hpT.symm

/-- For the different regression media at normal incidence, zero incident data and the active
reflected-root relation force all reflected and transmitted scalar amplitudes to vanish. -/
lemma fresnelAmplitudeRegression_zeroInput {rS tS rP tP : ℂ}
    (hElectricS : tS = rS)
    (hMagneticS : (5 / 4 : ℂ) * tS = -(5 / 2 : ℂ) * rS)
    (hElectricP : tP = -rP)
    (hMagneticP : (5 / 4 : ℂ) * tP = (5 / 2 : ℂ) * rP) :
    rS = 0 ∧ tS = 0 ∧ rP = 0 ∧ tP = 0 := by
  have hSolvedS := jonesBoundaryRegressionInterface.solve_sFresnel
    (chi_i := 1) (chi_r := -1) (chi_t := 1) (I := 0) (R := rS) (T := tS)
    (by simpa using hElectricS)
    (by
      simp only [jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
        jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
      norm_num
      linear_combination hMagneticS)
    (Or.inr (by norm_num))
    (jonesBoundaryRegressionInterface.sFresnelDenominator_ne_zero (by norm_num) (by norm_num))
  have hSolvedP := jonesBoundaryRegressionInterface.solve_pFresnel
    (chi_i := 1) (chi_r := -1) (chi_t := 1) (I := 0) (R := rP) (T := tP)
    (by simpa using hElectricP)
    (by
      simp only [jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
        jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
      norm_num
      linear_combination hMagneticP)
    (Or.inr (by norm_num))
    (jonesBoundaryRegressionInterface.pFresnelDenominator_ne_zero (by norm_num) (by norm_num))
  have hrS : rS = 0 := by simpa using hSolvedS.1
  have htS : tS = 0 := by simpa using hSolvedS.2
  have hrP : rP = 0 := by simpa using hSolvedP.1
  have htP : tP = 0 := by simpa using hSolvedP.2
  exact ⟨hrS, htS, hrP, htP⟩

end

end Optics
