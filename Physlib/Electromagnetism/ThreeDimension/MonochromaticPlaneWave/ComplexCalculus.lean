/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBasic
public import Physlib.SpaceAndTime.Space.Derivatives.Curl

/-!
# Differential identities for complex-amplitude plane waves

## i. Overview

This file proves the regularity and exact differential identities of the ordinary real fields
constructed by `ComplexMonochromaticPlaneWave`. For the carrier convention

`C(t, x) = exp (I * omega * t) * exp (-I * (K dot x))`,

the scalar identities are `partial_t C = I * omega * C` and
`partial_j C = -I * K_j * C`. Consequently, for every constant complex amplitude `A`,

`div Re(C A) = Re(-I * C * (K dot A))`

and

`curl Re(C A) = Re(-I * C * (K cross A))`.

The pairing is complex-bilinear rather than Hermitian. These are calculus identities for an
off-shell carrier: they do not assume transversality or material dispersion, and they do not
assert a Maxwell equation, interface role, evanescent-wave role, or power normalization.

## ii. Key results

- `ComplexMonochromaticPlaneWave.carrier_contDiff`: joint smoothness of the complex carrier.
- `ComplexMonochromaticPlaneWave.realFieldOfAmplitude_contDiff`: joint smoothness of every
  ordinary real field constructed from a constant complex amplitude.
- `ComplexMonochromaticPlaneWave.carrier_timeDeriv`: the exact `I * omega` temporal factor.
- `ComplexMonochromaticPlaneWave.carrier_spaceDeriv`: the exact `-I * K_j` spatial factor.
- `ComplexMonochromaticPlaneWave.realFieldOfAmplitude_timeDeriv`: generic real-field time
  derivative.
- `ComplexMonochromaticPlaneWave.realFieldOfAmplitude_div`: generic real-field divergence.
- `ComplexMonochromaticPlaneWave.realFieldOfAmplitude_curl`: generic real-field curl.

## iii. Table of contents

- A. Regularity
- B. Carrier derivatives
- C. Real-field differential identities

## iv. References

These results differentiate the carrier convention defined in `ComplexBasic`. No external formal
development is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Regularity

-/

/-- The real-continuous-linear map represented by complex-bilinear pairing with a fixed complex
wave vector. -/
private def spatialPairingCLM (k : ComplexWaveVector 3) : Space →L[ℝ] ℂ :=
  ∑ i : Fin 3, k i • (Complex.ofRealCLM.comp (Space.coordCLM i))

private lemma spatialPairingCLM_apply (k : ComplexWaveVector 3) (x : Space) :
    spatialPairingCLM k x = k.spatialPairing x := by
  simp [spatialPairingCLM, ComplexWaveVector.spatialPairing,
    ComplexWaveVector.bilinearDot, Space.coordCLM_apply, Space.coord_apply]

private lemma spatialPairing_eq_clm (k : ComplexWaveVector 3) :
    k.spatialPairing = spatialPairingCLM k := by
  funext x
  exact (spatialPairingCLM_apply k x).symm

private lemma spatialPairing_contDiff (k : ComplexWaveVector 3) (n : WithTop ℕ∞) :
    ContDiff ℝ n k.spatialPairing := by
  rw [spatialPairing_eq_clm]
  fun_prop

/-- The complex carrier is jointly smooth in time and space to every requested order. -/
lemma carrier_contDiff (wave : ComplexMonochromaticPlaneWave) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿fun tx : Time × Space ↦ wave.carrier tx.1 tx.2 := by
  have htimeReal : ContDiff ℝ n fun tx : Time × Space ↦
      wave.angularFrequency * tx.1 := by
    fun_prop
  have htime : ContDiff ℝ n fun tx : Time × Space ↦
      ((wave.angularFrequency * tx.1 : ℝ) : ℂ) := by
    change ContDiff ℝ n fun tx : Time × Space ↦
      Complex.ofRealCLM (wave.angularFrequency * tx.1)
    exact Complex.ofRealCLM.contDiff.comp htimeReal
  have htemporal : ContDiff ℝ n fun tx : Time × Space ↦
      Complex.exp (((wave.angularFrequency * tx.1 : ℝ) : ℂ) * Complex.I) := by
    exact (htime.mul contDiff_const).cexp
  have hspatialPairing : ContDiff ℝ n fun tx : Time × Space ↦
      wave.waveVector.spatialPairing tx.2 := by
    exact (spatialPairing_contDiff wave.waveVector n).comp (by fun_prop)
  have hspatialFactor : ContDiff ℝ n fun tx : Time × Space ↦
      wave.waveVector.spatialFactor tx.2 := by
    unfold ComplexWaveVector.spatialFactor
    exact ((show ContDiff ℝ n fun _ : Time × Space ↦ -Complex.I from
      contDiff_const).mul hspatialPairing).cexp
  exact htemporal.mul hspatialFactor

/-- Every ordinary real field constructed from the carrier and a constant complex amplitude is
jointly smooth in time and space to every requested order. -/
lemma realFieldOfAmplitude_contDiff (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿(wave.realFieldOfAmplitude amplitude) := by
  rw [contDiff_euclidean]
  intro i
  have hproduct : ContDiff ℝ n fun tx : Time × Space ↦
      wave.carrier tx.1 tx.2 * amplitude i :=
    (wave.carrier_contDiff n).mul contDiff_const
  change ContDiff ℝ n fun tx : Time × Space ↦
    Complex.reCLM (wave.carrier tx.1 tx.2 * amplitude i)
  exact Complex.reCLM.contDiff.comp hproduct

/-- The ordinary real electric field is jointly smooth. -/
lemma electricField_contDiff (wave : ComplexMonochromaticPlaneWave) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿wave.electricField :=
  wave.realFieldOfAmplitude_contDiff wave.electricAmplitude n

/-- The ordinary real magnetic induction is jointly smooth. -/
lemma magneticInduction_contDiff (wave : ComplexMonochromaticPlaneWave) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿wave.magneticInduction :=
  wave.realFieldOfAmplitude_contDiff wave.magneticAmplitude n

/-- The ordinary real electric displacement in a fixed homogeneous medium is jointly smooth. -/
lemma electricDisplacement_contDiff (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿(wave.electricDisplacement medium) :=
  (wave.electricField_contDiff n).const_smul medium.ε

/-- The ordinary real magnetic field strength in a fixed homogeneous medium is jointly smooth. -/
lemma magneticFieldStrength_contDiff (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿(wave.magneticFieldStrength medium) :=
  (wave.magneticInduction_contDiff n).const_smul medium.μ⁻¹

private lemma realFieldOfAmplitude_differentiable_space
    (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (t : Time) :
    Differentiable ℝ (wave.realFieldOfAmplitude amplitude t) :=
  (wave.realFieldOfAmplitude_contDiff amplitude 1).differentiable (by norm_num) |>.comp
    (f := fun x ↦ (t, x)) (by fun_prop)

/-!

## B. Carrier derivatives

-/

/-- The time derivative of the carrier is its product with `I * omega`. -/
lemma carrier_timeDeriv (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    ∂ₜ (fun s ↦ wave.carrier s x) t =
      Complex.I * (wave.angularFrequency : ℂ) * wave.carrier t x := by
  unfold Time.deriv carrier
  rw [fderiv_mul_const (by fun_prop)]
  rw [(by fun_prop : DifferentiableAt ℝ
    (fun s : Time ↦ (((wave.angularFrequency * s : ℝ) : ℂ) *
      Complex.I)) t).hasFDerivAt.cexp.fderiv]
  rw [fderiv_mul_const (by fun_prop)]
  have hfrequency : (fun s : Time ↦ ((wave.angularFrequency * s : ℝ) : ℂ)) =
      Complex.ofRealCLM.comp (wave.angularFrequency • Time.toRealCLM) := by
    rfl
  rw [hfrequency, ContinuousLinearMap.fderiv]
  simp [Time.toRealCLM, mul_assoc, mul_comm]

private lemma spatialPairing_spaceDeriv (k : ComplexWaveVector 3)
    (j : Fin 3) (x : Space) :
    ∂[j] (fun y : Space ↦ k.spatialPairing y) x = k j := by
  change Space.deriv j k.spatialPairing x = k j
  rw [spatialPairing_eq_clm]
  unfold Space.deriv
  rw [ContinuousLinearMap.fderiv]
  fin_cases j <;>
    simp [spatialPairingCLM, Space.coordCLM_apply, Space.coord_apply,
      Space.basis_apply, Fin.sum_univ_three]

/-- The spatial coordinate derivative of the carrier is its product with `-I * K_j`. -/
lemma carrier_spaceDeriv (wave : ComplexMonochromaticPlaneWave)
    (j : Fin 3) (t : Time) (x : Space) :
    ∂[j] (fun y : Space ↦ wave.carrier t y) x =
      (-Complex.I * wave.waveVector j) * wave.carrier t x := by
  have hPairing : Differentiable ℝ wave.waveVector.spatialPairing := by
    rw [spatialPairing_eq_clm]
    fun_prop
  unfold Space.deriv carrier ComplexWaveVector.spatialFactor
  rw [fderiv_const_mul ((hPairing.const_mul (-Complex.I)).cexp.differentiableAt)]
  rw [(hPairing.const_mul (-Complex.I)).differentiableAt.hasFDerivAt.cexp.fderiv]
  rw [fderiv_const_mul hPairing.differentiableAt]
  have hderiv := spatialPairing_spaceDeriv wave.waveVector j x
  change (fderiv ℝ wave.waveVector.spatialPairing x) (Space.basis j) =
    wave.waveVector j at hderiv
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [hderiv]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-!

## C. Real-field differential identities

-/

/-- The time derivative of a realized real field is realization of the amplitude multiplied by
`I * omega`. -/
lemma realFieldOfAmplitude_timeDeriv (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (t : Time) (x : Space) :
    ∂ₜ (fun s ↦ wave.realFieldOfAmplitude amplitude s x) t =
      wave.realFieldOfAmplitude
        ((Complex.I * (wave.angularFrequency : ℂ)) • amplitude) t x := by
  have hcarrierDifferentiable : Differentiable ℝ (fun s ↦ wave.carrier s x) := by
    unfold carrier
    fun_prop
  have hfieldDifferentiable : Differentiable ℝ
      (fun s ↦ wave.realFieldOfAmplitude amplitude s x) := by
    apply Time.differentiable_euclid
    intro i
    change Differentiable ℝ (fun s ↦ (wave.carrier s x * amplitude i).re)
    fun_prop
  ext i
  rw [← Time.deriv_euclid hfieldDifferentiable]
  unfold Time.deriv
  change (fderiv ℝ
    (fun s : Time ↦ Complex.reCLM (wave.carrier s x * amplitude i)) t) 1 = _
  rw [fderiv_fun_comp t Complex.reCLM.differentiableAt
    (hcarrierDifferentiable.differentiableAt.mul_const _)]
  rw [fderiv_mul_const hcarrierDifferentiable.differentiableAt]
  have hcarrier := wave.carrier_timeDeriv t x
  change (fderiv ℝ (fun s ↦ wave.carrier s x) t) 1 =
    Complex.I * (wave.angularFrequency : ℂ) * wave.carrier t x at hcarrier
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    _root_.smul_apply, smul_eq_mul]
  rw [hcarrier]
  simp [realFieldOfAmplitude_apply, Complex.mul_re]
  ring

/-- A spatial coordinate derivative of a realized real field is realization of the amplitude
multiplied by `-I * K_j`. -/
lemma realFieldOfAmplitude_spaceDeriv (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (j : Fin 3) (t : Time) (x : Space) :
    ∂[j] (fun y : Space ↦ wave.realFieldOfAmplitude amplitude t y) x =
      wave.realFieldOfAmplitude
        ((-Complex.I * wave.waveVector j) • amplitude) t x := by
  have hcarrierDifferentiable : Differentiable ℝ (fun y ↦ wave.carrier t y) := by
    unfold carrier ComplexWaveVector.spatialFactor
    rw [spatialPairing_eq_clm]
    fun_prop
  have hfieldDifferentiable :=
    wave.realFieldOfAmplitude_differentiable_space amplitude t
  ext i
  rw [← Space.deriv_euclid hfieldDifferentiable]
  unfold Space.deriv
  change (fderiv ℝ
    (fun y : Space ↦ Complex.reCLM (wave.carrier t y * amplitude i)) x)
      (Space.basis j) = _
  rw [fderiv_fun_comp x Complex.reCLM.differentiableAt
    (hcarrierDifferentiable.differentiableAt.mul_const _)]
  rw [fderiv_mul_const hcarrierDifferentiable.differentiableAt]
  have hcarrier := wave.carrier_spaceDeriv j t x
  change (fderiv ℝ (fun y ↦ wave.carrier t y) x) (Space.basis j) =
    (-Complex.I * wave.waveVector j) * wave.carrier t x at hcarrier
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    _root_.smul_apply, smul_eq_mul]
  rw [hcarrier]
  simp [realFieldOfAmplitude_apply, Complex.mul_re]
  ring

/-- The divergence of a realized real field is the real part of the complex-bilinear
wave-vector--amplitude pairing multiplied by `-I` and the carrier. -/
lemma realFieldOfAmplitude_div (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (t : Time) (x : Space) :
    (∇ ⬝ wave.realFieldOfAmplitude amplitude t) x =
      (-Complex.I * wave.carrier t x *
        ComplexWaveVector.bilinearDot wave.waveVector amplitude).re := by
  have hfieldDifferentiable :=
    wave.realFieldOfAmplitude_differentiable_space amplitude t
  unfold Space.div
  rw [Fin.sum_univ_three]
  rw [Space.deriv_euclid hfieldDifferentiable,
    Space.deriv_euclid hfieldDifferentiable,
    Space.deriv_euclid hfieldDifferentiable]
  rw [wave.realFieldOfAmplitude_spaceDeriv,
    wave.realFieldOfAmplitude_spaceDeriv,
    wave.realFieldOfAmplitude_spaceDeriv]
  simp [realFieldOfAmplitude_apply, ComplexWaveVector.bilinearDot,
    Fin.sum_univ_three, Complex.mul_re]
  ring

/-- The curl of a realized real field is the componentwise real part of
`-I * C * (K cross A)`. -/
lemma realFieldOfAmplitude_curl (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (t : Time) (x : Space) :
    (∇ ⨯ wave.realFieldOfAmplitude amplitude t) x =
      wave.realFieldOfAmplitude
        ((-Complex.I) • complexCross wave.waveVector amplitude) t x := by
  have hfieldDifferentiable :=
    wave.realFieldOfAmplitude_differentiable_space amplitude t
  unfold Space.curl
  ext i
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceAdd]
    rw [Space.deriv_euclid hfieldDifferentiable,
      Space.deriv_euclid hfieldDifferentiable]
    rw [wave.realFieldOfAmplitude_spaceDeriv,
      wave.realFieldOfAmplitude_spaceDeriv]
    simp [realFieldOfAmplitude_apply, complexCross, crossProduct, Complex.mul_re]
    ring

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism
