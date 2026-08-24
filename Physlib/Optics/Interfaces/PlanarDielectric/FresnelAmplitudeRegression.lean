/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelAmplitude
public import Physlib.Optics.Interfaces.PlanarDielectric.JonesBoundaryRegression
public import Physlib.Optics.Polarization.IncidenceFrameRegression

/-!
# Fresnel-amplitude solution regressions

## i. Overview

This file checks the scalar Fresnel solution against the independently established exact Jones
boundary fixture and against boundary cases of its hypotheses. The existing fixture's manual
linear proof remains in `JonesBoundaryRegression`, which does not import the general solution.
Here the same four boundary equations are passed through the general solution and compared with the
independently recorded coefficient tuple

```text
(r_s, t_s, r_p, t_p) = (5/11, 16/11, -1/5, 8/5).
```

At normal incidence the fixture media give `(1/3, 4/3, -1/3, 4/3)`, showing the sign change of
the propagation-oriented full-vector `p` reflection coefficient. The selected-tangent frame
regression independently checks the corresponding complex electric and magnetic-field-strength
(`H`) vector balances and the fixed-plane tangential-`p` values `(1/3, 4/3)`. The oblique fixture
similarly converts the
full-vector `p` values `(-1/5, 8/5)` to fixed-plane values `(1/5, 6/5)`. In the scalar case
`chi_t = 0`, the same media give full-vector values `(1, 2, 1, 4)` and fixed-plane tangential-`p`
values `(-1, 0)`; the total coefficient definitions require no division by `chi_t`. At
`chi_i = 0`, their full-vector values are `(-1, 0)` and their tangential values are `(1, 2)`, while
the normal-ratio conversion is intentionally unavailable. A matched-medium scalar case uses a zero
reflected amplitude and deliberately sets `chi_r = chi_i`, testing the zero-reflection branch
rather than the active reflected-root equation. A connected matched normal-incidence fixture then
tests a zero reflected carrier with unrelated wave vector, frequency, and supplied frame. Finally,
a different-medium homogeneous system with zero incident amplitude is proved to have only zero
reflected and transmitted amplitudes.

Apart from the explicit normal complex-vector balance and the connected zero-field fixture, the
boundary-case checks are scalar-system regressions. They do not select physical propagation
branches or assert irradiance or power laws.

## ii. Key results

- `jonesBoundaryRegression_fresnelCoefficients_of_balances`: the general solution applied to the
  existing connected boundary fixture.
- `jonesBoundaryRegression_fresnelCoefficient_values`: the four exact coefficient values.
- `fresnelAmplitudeRegression_normalIncidence`: the full-vector normal-incidence signs.
- `fresnelAmplitudeRegression_normalIncidence_amplitudeBalances`: direct selected-frame electric
  and magnetic-field-strength amplitude balances at normal incidence.
- `jonesBoundaryRegression_tangentialPAmplitude_conversion`: exact oblique conversion of the
  independently solved full-vector amplitudes.
- `fresnelAmplitudeRegression_transmittedGrazing`: the zero-transmitted-normal case.
- `fresnelAmplitudeRegression_transmittedGrazing_tangentialP`: its fixed-plane `p` coefficients.
- `fresnelAmplitudeRegression_incidentGrazing_tangentialP`: the total incident-grazing values.
- `fresnelAmplitudeRegression_zeroReflection`: the arbitrary-reflected-normal zero-field branch.
- `fresnelAmplitudeRegression_zeroReflection_tangentialPGuard`: its tangential amplitude guard.
- `fresnelAmplitudeRegression_zeroReflection_selectedTangentWrapper`: a connected deliberately
  non-active carrier-and-frame zero branch.
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

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
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

/-- The unit two-component incident Jones data for the selected-tangent normal-incidence check. -/
def fresnelAmplitudeRegressionNormalIncidentJones : JonesVector :=
  JonesVector.ofComponents 1 1

/-- The full-vector reflected Jones data `(1/3, -1/3)` at normal incidence. -/
def fresnelAmplitudeRegressionNormalReflectedJones : JonesVector :=
  JonesVector.ofComponents (1 / 3) (-1 / 3)

/-- The full-vector transmitted Jones data `(4/3, 4/3)` at normal incidence. -/
def fresnelAmplitudeRegressionNormalTransmittedJones : JonesVector :=
  JonesVector.ofComponents (4 / 3) (4 / 3)

/-- The selected-tangent normal-incidence data directly satisfy both the complex electric and
admittance-weighted magnetic amplitude balances.

This calculation uses the exact forward and backward frame axes, independently of the Fresnel
solver. Both Jones components are nonzero, so it detects the reflected full-vector `p` sign. -/
lemma fresnelAmplitudeRegression_normalIncidence_amplitudeBalances :
    normalIncidenceRegressionForwardFrame.embedJones
        fresnelAmplitudeRegressionNormalTransmittedJones =
      normalIncidenceRegressionForwardFrame.embedJones
          fresnelAmplitudeRegressionNormalIncidentJones +
        normalIncidenceRegressionBackwardFrame.embedJones
          fresnelAmplitudeRegressionNormalReflectedJones ∧
    ((jonesBoundaryRegressionPositiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) •
        normalIncidenceRegressionForwardFrame.embedJones
          fresnelAmplitudeRegressionNormalTransmittedJones.propagationCross =
      ((jonesBoundaryRegressionNegativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) •
          normalIncidenceRegressionForwardFrame.embedJones
            fresnelAmplitudeRegressionNormalIncidentJones.propagationCross +
        ((jonesBoundaryRegressionNegativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) •
          normalIncidenceRegressionBackwardFrame.embedJones
            fresnelAmplitudeRegressionNormalReflectedJones.propagationCross := by
  constructor <;>
    ext i <;>
    fin_cases i <;>
    norm_num [fresnelAmplitudeRegressionNormalIncidentJones,
      fresnelAmplitudeRegressionNormalReflectedJones,
      fresnelAmplitudeRegressionNormalTransmittedJones, PolarizationFrame.embedJones,
      PolarizationFrame.complexAxis, normalIncidenceRegressionForwardFrame,
      normalIncidenceRegressionBackwardFrame, PolarizationFrame.ofAxisZero,
      normalIncidenceRegressionTangentAxis, incidenceRegressionNormal,
      normalIncidenceRegressionBackwardDirection, JonesVector.propagationCross,
      jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
      jonesBoundaryRegression_positiveMedium_waveImpedance_inv, crossProduct,
      Matrix.cons_val_two, Matrix.head_cons]

/-- The selected-tangent normal-incidence fixture reconciles the full-vector reflected sign with
equal fixed-plane `s` and tangential-`p` Fresnel coefficients. -/
lemma fresnelAmplitudeRegression_normalIncidence_tangentialP :
    jonesBoundaryRegressionInterface.tangentialPFresnelReflectionCoefficient 1 1 = 1 / 3 ∧
      jonesBoundaryRegressionInterface.tangentialPFresnelTransmissionCoefficient 1 1 = 4 / 3 ∧
      normalIncidenceRegressionBackwardFrame.normalScaledSecondComponent
          normalIncidenceRegressionPlane fresnelAmplitudeRegressionNormalReflectedJones =
        (1 / 3 : ℂ) *
          normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
            normalIncidenceRegressionPlane fresnelAmplitudeRegressionNormalIncidentJones ∧
      normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
          normalIncidenceRegressionPlane fresnelAmplitudeRegressionNormalTransmittedJones =
        (4 / 3 : ℂ) *
          normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
            normalIncidenceRegressionPlane fresnelAmplitudeRegressionNormalIncidentJones := by
  rcases fresnelAmplitudeRegression_normalIncidence with ⟨hRS, hTS, _, _⟩
  rw [jonesBoundaryRegressionInterface.tangentialPFresnelReflectionCoefficient_normalIncidence,
    jonesBoundaryRegressionInterface.tangentialPFresnelTransmissionCoefficient_normalIncidence,
    hRS, hTS]
  norm_num [normalIncidenceRegressionForwardFrame_normalScaledSecondComponent,
    normalIncidenceRegressionBackwardFrame_normalScaledSecondComponent,
    fresnelAmplitudeRegressionNormalIncidentJones,
    fresnelAmplitudeRegressionNormalReflectedJones,
    fresnelAmplitudeRegressionNormalTransmittedJones]

/-- The exact oblique fixture has fixed-plane `p` amplitudes `(4/5, 4/25, 24/25)` for its
incident, reflected, and transmitted Jones data. -/
lemma jonesBoundaryRegression_tangentialPComponents :
    jonesBoundaryRegressionIncidentFrame.normalScaledSecondComponent jonesBoundaryRegressionPlane
        jonesBoundaryRegressionIncidentJones = 4 / 5 ∧
      jonesBoundaryRegressionReflectedFrame.normalScaledSecondComponent jonesBoundaryRegressionPlane
          (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5)) = 4 / 25 ∧
      jonesBoundaryRegressionTransmittedFrame.normalScaledSecondComponent
          jonesBoundaryRegressionPlane
          (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5)) = 24 / 25 := by
  rw [PolarizationFrame.normalScaledSecondComponent,
    PolarizationFrame.normalScaledSecondComponent,
    PolarizationFrame.normalScaledSecondComponent, jonesBoundaryRegression_incidentNormalComponent,
    jonesBoundaryRegression_reflectedNormalComponent,
    jonesBoundaryRegression_transmittedNormalComponent]
  norm_num [jonesBoundaryRegressionIncidentJones, jonesBoundaryRegressionReflectedJones,
    jonesBoundaryRegressionTransmittedJones]

/-- The oblique fixture's full-vector values `(-1/5, 8/5)` convert to fixed-plane tangential-`p`
coefficients `(1/5, 6/5)`. -/
lemma jonesBoundaryRegression_tangentialPFresnelCoefficient_values :
    jonesBoundaryRegressionInterface.tangentialPFresnelReflectionCoefficient (4 / 5) (3 / 5) =
        1 / 5 ∧
      jonesBoundaryRegressionInterface.tangentialPFresnelTransmissionCoefficient
        (4 / 5) (3 / 5) = 6 / 5 := by
  have hFull := jonesBoundaryRegression_fresnelCoefficients_of_balances
    jonesBoundaryRegression_exact_hasReferencedJointElectricBalance
    jonesBoundaryRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
  have hRP : jonesBoundaryRegressionInterface.pFresnelReflectionCoefficient
      (4 / 5) (3 / 5) = -1 / 5 := by
    apply Complex.ofReal_injective
    simpa using hFull.2.2.1.symm
  have hTP : jonesBoundaryRegressionInterface.pFresnelTransmissionCoefficient
      (4 / 5) (3 / 5) = 8 / 5 := by
    apply Complex.ofReal_injective
    simpa using hFull.2.2.2.symm
  constructor
  · have hConversion := jonesBoundaryRegressionInterface
      |>.tangentialPFresnelReflectionCoefficient_eq_neg_pFresnelReflectionCoefficient
        (4 / 5) (3 / 5)
    rw [hConversion, hRP]
    norm_num
  · have hConversion := jonesBoundaryRegressionInterface
      |>.tangentialPFresnelTransmissionCoefficient_eq_normalRatio_mul
        (chi_i := 4 / 5) (chi_t := 3 / 5) (by norm_num)
    rw [hConversion, hTP]
    norm_num

/-- The independently balanced oblique Jones fixture obeys the named fixed-plane tangential-`p`
coefficient laws. This checks both the reflected sign and the transmitted normal-factor change. -/
lemma jonesBoundaryRegression_tangentialPAmplitude_conversion :
    jonesBoundaryRegressionReflectedFrame.normalScaledSecondComponent jonesBoundaryRegressionPlane
        (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5)) =
      (jonesBoundaryRegressionInterface.tangentialPFresnelReflectionCoefficient
        (4 / 5) (3 / 5) : ℂ) *
        jonesBoundaryRegressionIncidentFrame.normalScaledSecondComponent
          jonesBoundaryRegressionPlane
          jonesBoundaryRegressionIncidentJones ∧
    jonesBoundaryRegressionTransmittedFrame.normalScaledSecondComponent
        jonesBoundaryRegressionPlane
        (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5)) =
      (jonesBoundaryRegressionInterface.tangentialPFresnelTransmissionCoefficient
        (4 / 5) (3 / 5) : ℂ) *
        jonesBoundaryRegressionIncidentFrame.normalScaledSecondComponent
          jonesBoundaryRegressionPlane
          jonesBoundaryRegressionIncidentJones := by
  rcases jonesBoundaryRegression_tangentialPComponents with ⟨hI, hR, hT⟩
  rcases jonesBoundaryRegression_tangentialPFresnelCoefficient_values with ⟨hr, ht⟩
  rw [hI, hR, hT, hr, ht]
  norm_num

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

/-- At transmitted grazing, the fixed-plane reflected `p` coefficient is `-1`, while the
transmitted tangential `p` coefficient vanishes because the transmitted `p`-polarized electric
component is normal to the interface plane. -/
lemma fresnelAmplitudeRegression_transmittedGrazing_tangentialP :
    jonesBoundaryRegressionInterface.tangentialPFresnelReflectionCoefficient 1 0 = -1 ∧
      jonesBoundaryRegressionInterface.tangentialPFresnelTransmissionCoefficient 1 0 = 0 := by
  rcases fresnelAmplitudeRegression_transmittedGrazing with ⟨_, _, hReflection, _⟩
  rw [jonesBoundaryRegressionInterface
      |>.tangentialPFresnelReflectionCoefficient_eq_neg_pFresnelReflectionCoefficient,
    hReflection]
  norm_num [PlanarDielectricInterface.tangentialPFresnelTransmissionCoefficient]

/-- At incident grazing, the total full-vector `p` coefficients are `(-1, 0)` while the total
fixed-plane tangential coefficients are `(1, 2)`. The normal-ratio quotient conversion is
intentionally unavailable because `chi_i = 0`; the total coefficient definitions and the
cross-multiplied conversion remain meaningful without division by `chi_i`.

This is an algebraic boundary check, not an assertion that a grazing wave crosses the interface. -/
lemma fresnelAmplitudeRegression_incidentGrazing_tangentialP :
    jonesBoundaryRegressionInterface.pFresnelReflectionCoefficient 0 1 = -1 ∧
      jonesBoundaryRegressionInterface.pFresnelTransmissionCoefficient 0 1 = 0 ∧
      jonesBoundaryRegressionInterface.tangentialPFresnelReflectionCoefficient 0 1 = 1 ∧
      jonesBoundaryRegressionInterface.tangentialPFresnelTransmissionCoefficient 0 1 = 2 := by
  rw [PlanarDielectricInterface.pFresnelReflectionCoefficient,
    PlanarDielectricInterface.pFresnelTransmissionCoefficient,
    PlanarDielectricInterface.tangentialPFresnelReflectionCoefficient,
    PlanarDielectricInterface.tangentialPFresnelTransmissionCoefficient,
    PlanarDielectricInterface.pFresnelDenominator,
    jonesBoundaryRegressionInterface,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
  norm_num

/-!

## C. Zero-reflection and zero-input branches

-/

/-- An equal-medium interface used to test the zero-reflection solution branch. -/
def fresnelAmplitudeRegressionMatchedInterface : PlanarDielectricInterface where
  plane := jonesBoundaryRegressionPlane
  negativeMedium := jonesBoundaryRegressionNegativeMedium
  positiveMedium := jonesBoundaryRegressionNegativeMedium

/-- The matched regression media on the selected-tangent normal-incidence plane. -/
def fresnelAmplitudeRegressionNormalMatchedInterface : PlanarDielectricInterface where
  plane := normalIncidenceRegressionPlane
  negativeMedium := jonesBoundaryRegressionNegativeMedium
  positiveMedium := jonesBoundaryRegressionNegativeMedium

/-- A forward normal-incidence material wave at angular frequency one. Its reference plane passes
through the spatial origin, so its supplied Jones data are also its plane-referenced data. -/
def fresnelAmplitudeRegressionNormalMatchedWave (J : JonesVector) :
    ComplexMonochromaticPlaneWave :=
  ComplexMonochromaticPlaneWave.ofReal
    (J.toMaterialPlaneWave jonesBoundaryRegressionNegativeMedium
      normalIncidenceRegressionForwardFrame 1 (by norm_num))

/-- A zero reflected wave with deliberately unrelated frequency and wave vector. -/
def fresnelAmplitudeRegressionNormalZeroReflectedWave : ComplexMonochromaticPlaneWave where
  angularFrequency := 2
  angularFrequency_pos := by norm_num
  waveVector := 0
  electricAmplitude := 0

/-- A matched normal-incidence configuration whose reflected wave is a dummy zero carrier. -/
def fresnelAmplitudeRegressionNormalZeroConfiguration : PlanarDielectricWaveConfiguration where
  interface := fresnelAmplitudeRegressionNormalMatchedInterface
  incident := fresnelAmplitudeRegressionNormalMatchedWave
    fresnelAmplitudeRegressionNormalIncidentJones
  reflected := fresnelAmplitudeRegressionNormalZeroReflectedWave
  transmitted := fresnelAmplitudeRegressionNormalMatchedWave
    fresnelAmplitudeRegressionNormalIncidentJones

/-- The forward normal material wave is represented by its supplied Jones data at the origin. -/
lemma fresnelAmplitudeRegressionNormalMatchedWave_isReferencedMaterialJonesWave (J : JonesVector) :
    IsReferencedMaterialJonesWave normalIncidenceRegressionPlane
      jonesBoundaryRegressionNegativeMedium (fresnelAmplitudeRegressionNormalMatchedWave J)
      normalIncidenceRegressionForwardFrame J := by
  have h : IsReferencedMaterialJonesWave normalIncidenceRegressionPlane
      jonesBoundaryRegressionNegativeMedium (fresnelAmplitudeRegressionNormalMatchedWave J)
      normalIncidenceRegressionForwardFrame
      (JonesVector.scale
        ((fresnelAmplitudeRegressionNormalMatchedWave J).waveVector.spatialFactor
          normalIncidenceRegressionPlane.point) J) := by
    simpa only [fresnelAmplitudeRegressionNormalMatchedWave] using
      J.isReferencedMaterialJonesWave_ofReal_toMaterialPlaneWave
        normalIncidenceRegressionPlane jonesBoundaryRegressionNegativeMedium
          normalIncidenceRegressionForwardFrame 1 (by norm_num)
  have hSpatial :
      (fresnelAmplitudeRegressionNormalMatchedWave J).waveVector.spatialFactor
        normalIncidenceRegressionPlane.point = 1 := by
    simp [fresnelAmplitudeRegressionNormalMatchedWave, normalIncidenceRegressionPlane,
      ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing]
  have hJones : JonesVector.scale
      ((fresnelAmplitudeRegressionNormalMatchedWave J).waveVector.spatialFactor
        normalIncidenceRegressionPlane.point) J = J := by
    rw [hSpatial]
    ext i
    simp [JonesVector.scale]
  simpa only [hJones] using h

/-- The matched zero-reflection configuration satisfies the complete referenced electric
balance. -/
lemma fresnelAmplitudeRegressionNormalZeroConfiguration_hasElectricBalance :
    fresnelAmplitudeRegressionNormalZeroConfiguration.HasReferencedJointElectricBalance := by
  rw [PlanarDielectricWaveConfiguration.HasReferencedJointElectricBalance]
  change referencedMediumJointElectricTraceAmplitude normalIncidenceRegressionPlane
        jonesBoundaryRegressionNegativeMedium
        (fresnelAmplitudeRegressionNormalMatchedWave
          fresnelAmplitudeRegressionNormalIncidentJones) =
      referencedMediumJointElectricTraceAmplitude normalIncidenceRegressionPlane
          jonesBoundaryRegressionNegativeMedium
          (fresnelAmplitudeRegressionNormalMatchedWave
            fresnelAmplitudeRegressionNormalIncidentJones) +
        referencedMediumJointElectricTraceAmplitude normalIncidenceRegressionPlane
          jonesBoundaryRegressionNegativeMedium
          fresnelAmplitudeRegressionNormalZeroReflectedWave
  have hZero :=
    (ComplexMonochromaticPlaneWave.referencedMediumJointElectricTraceAmplitude_eq_zero_iff
      normalIncidenceRegressionPlane jonesBoundaryRegressionNegativeMedium
        fresnelAmplitudeRegressionNormalZeroReflectedWave).2 rfl
  rw [hZero]
  simp

/-- The matched zero-reflection configuration satisfies the referenced tangential
magnetic-field-strength balance. -/
lemma fresnelAmplitudeRegressionNormalZeroConfiguration_hasMagneticBalance :
    fresnelAmplitudeRegressionNormalZeroConfiguration
      |>.HasReferencedTangentialMagneticFieldStrengthBalance := by
  rw [PlanarDielectricWaveConfiguration.HasReferencedTangentialMagneticFieldStrengthBalance]
  change referencedMediumTangentialMagneticFieldStrengthAmplitude
        normalIncidenceRegressionPlane jonesBoundaryRegressionNegativeMedium
        (fresnelAmplitudeRegressionNormalMatchedWave
          fresnelAmplitudeRegressionNormalIncidentJones) =
      referencedMediumTangentialMagneticFieldStrengthAmplitude
          normalIncidenceRegressionPlane jonesBoundaryRegressionNegativeMedium
          (fresnelAmplitudeRegressionNormalMatchedWave
            fresnelAmplitudeRegressionNormalIncidentJones) +
        referencedMediumTangentialMagneticFieldStrengthAmplitude
          normalIncidenceRegressionPlane jonesBoundaryRegressionNegativeMedium
          fresnelAmplitudeRegressionNormalZeroReflectedWave
  have hZero :=
    referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_zero_of_electricAmplitude_eq_zero
      normalIncidenceRegressionPlane jonesBoundaryRegressionNegativeMedium
        fresnelAmplitudeRegressionNormalZeroReflectedWave rfl
  rw [hZero]
  simp

/-- The connected selected-tangent wrapper accepts a zero reflected carrier whose wave vector,
frequency, and supplied frame do not obey the active reflection data.

The last two conclusions are the reflected and transmitted fixed-plane tangential-`p` amplitude
laws returned by the connected boundary solver. -/
lemma fresnelAmplitudeRegression_zeroReflection_selectedTangentWrapper :
    fresnelAmplitudeRegressionNormalZeroConfiguration.reflected.waveVector = 0 ∧
      fresnelAmplitudeRegressionNormalZeroConfiguration.reflected.angularFrequency ≠
        fresnelAmplitudeRegressionNormalZeroConfiguration.incident.angularFrequency ∧
      ¬normalIncidenceRegressionForwardFrame.IsSelectedTangentNormalIncidence
        normalIncidenceRegressionPlane normalIncidenceRegressionForwardFrame .negative ∧
      normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
          normalIncidenceRegressionPlane (JonesVector.ofComponents 0 0) =
        (fresnelAmplitudeRegressionNormalMatchedInterface
          |>.tangentialPFresnelReflectionCoefficient 1 1 : ℂ) *
          normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
            normalIncidenceRegressionPlane fresnelAmplitudeRegressionNormalIncidentJones ∧
      normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
          normalIncidenceRegressionPlane fresnelAmplitudeRegressionNormalIncidentJones =
        (fresnelAmplitudeRegressionNormalMatchedInterface
          |>.tangentialPFresnelTransmissionCoefficient 1 1 : ℂ) *
          normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
            normalIncidenceRegressionPlane fresnelAmplitudeRegressionNormalIncidentJones := by
  have hIncident :=
    fresnelAmplitudeRegressionNormalMatchedWave_isReferencedMaterialJonesWave
      fresnelAmplitudeRegressionNormalIncidentJones
  have hTransmitted : IsReferencedMaterialJonesWave
      fresnelAmplitudeRegressionNormalZeroConfiguration.interface.plane
      fresnelAmplitudeRegressionNormalZeroConfiguration.interface.positiveMedium
      fresnelAmplitudeRegressionNormalZeroConfiguration.transmitted
      normalIncidenceRegressionForwardFrame fresnelAmplitudeRegressionNormalIncidentJones := by
    simpa [fresnelAmplitudeRegressionNormalZeroConfiguration,
      fresnelAmplitudeRegressionNormalMatchedInterface] using hIncident
  have hReflected : IsZeroOrReferencedMaterialJonesWave
      fresnelAmplitudeRegressionNormalZeroConfiguration.interface.plane
      fresnelAmplitudeRegressionNormalZeroConfiguration.interface.negativeMedium
      fresnelAmplitudeRegressionNormalZeroConfiguration.reflected
      normalIncidenceRegressionForwardFrame (JonesVector.ofComponents 0 0) := by
    left
    refine ⟨by
      simp [fresnelAmplitudeRegressionNormalZeroConfiguration,
        fresnelAmplitudeRegressionNormalZeroReflectedWave], ?_⟩
    ext i
    fin_cases i <;> rfl
  have hSolved :=
    fresnel_tangential_components_of_referenced_balances_of_selectedTangentNormalIncidence
      (configuration := fresnelAmplitudeRegressionNormalZeroConfiguration)
      (incidentFrame := normalIncidenceRegressionForwardFrame)
      (reflectedFrame := normalIncidenceRegressionForwardFrame)
      (transmittedFrame := normalIncidenceRegressionForwardFrame)
      (incidentJones := fresnelAmplitudeRegressionNormalIncidentJones)
      (reflectedJones := JonesVector.ofComponents 0 0)
      (transmittedJones := fresnelAmplitudeRegressionNormalIncidentJones)
      fresnelAmplitudeRegressionNormalZeroConfiguration_hasElectricBalance
      fresnelAmplitudeRegressionNormalZeroConfiguration_hasMagneticBalance
      normalIncidenceRegressionForwardFrame hIncident hReflected hTransmitted
      normalIncidenceRegressionForwardFrame_isSelectedTangentNormalIncidence
      normalIncidenceRegressionForwardFrame_isSelectedTangentNormalIncidence
      (fun hActive ↦ (hActive rfl).elim)
  refine ⟨rfl, ?_, ?_, hSolved.2.2⟩
  · norm_num [fresnelAmplitudeRegressionNormalZeroConfiguration,
      fresnelAmplitudeRegressionNormalZeroReflectedWave,
      fresnelAmplitudeRegressionNormalMatchedWave,
      ComplexMonochromaticPlaneWave.ofReal_angularFrequency,
      JonesVector.toMaterialPlaneWave_angularFrequency]
  · intro hNegative
    have hPositiveComponent :=
      normalIncidenceRegressionForwardFrame_isSelectedTangentNormalIncidence
        |>.normalComponent_propagationVector
    have hNegativeComponent := hNegative.normalComponent_propagationVector
    norm_num [Space.OrientedAffineHyperplane.Side.sign] at hPositiveComponent hNegativeComponent
    linarith

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

/-- The fixed-plane reflected `p` amplitude guard accepts a zero field with the deliberately
non-active reflected normal `chi_r = chi_i = 1`. -/
lemma fresnelAmplitudeRegression_zeroReflection_tangentialPGuard :
    (1 : ℝ) ≠ -1 ∧
      fresnelAmplitudeRegressionMatchedInterface.tangentialPFresnelReflectionCoefficient 1 1 =
        0 ∧
      ((1 : ℝ) : ℂ) * 0 =
        (fresnelAmplitudeRegressionMatchedInterface
          |>.tangentialPFresnelReflectionCoefficient 1 1 : ℂ) * (((1 : ℝ) : ℂ) * 1) := by
  rcases fresnelAmplitudeRegression_zeroReflection with ⟨hNormal, _, _, hReflection, _⟩
  have hAmplitude : (0 : ℂ) =
      (fresnelAmplitudeRegressionMatchedInterface.pFresnelReflectionCoefficient 1 1 : ℂ) * 1 := by
    rw [hReflection]
    norm_num
  have hGuard :=
    fresnelAmplitudeRegressionMatchedInterface.tangentialPFresnelReflectionAmplitude_of_guard
      (chi_i := 1) (chi_r := 1) (chi_t := 1) hAmplitude (Or.inl rfl)
  refine ⟨hNormal, ?_, hGuard⟩
  rw [fresnelAmplitudeRegressionMatchedInterface
      |>.tangentialPFresnelReflectionCoefficient_eq_neg_pFresnelReflectionCoefficient,
    hReflection]
  norm_num

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
