/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelFlux
public import Physlib.Optics.Mode.Basic

/-!
# Power-normalized scalar Fresnel scattering kernels

## i. Overview

This file converts one real Fresnel reflection/transmission column into normalized modal
coordinates. The transmitted entry is multiplied by the square root of the transmitted-to-
incident normal-admittance ratio. A real symmetric two-side kernel completes that column with the
opposite reflection sign, and the existing `R + T = 1` law proves the resulting matrix lossless.

The completion is algebraic. It does not derive the second column from reverse incidence or
Maxwell boundary laws. It therefore precedes, but is not itself, the physical bidirectional
dielectric-interface scattering component required by E6.

## ii. Key results

- `powerNormalizedFresnelTransmissionCoefficient`: square-root flux normalization.
- `scalarFresnelScatteringKernel`: the real two-side algebraic kernel.
- `scalarFresnelScatteringKernel_isLossless`: its exact losslessness certificate.
- `sFresnelScatteringKernel_isLossless`: the real propagating s-column specialization.
- `pFresnelScatteringKernel_isLossless`: the real propagating p-column specialization.

## iii. Table of contents

- A. Square-root flux normalization
- B. Scalar two-side kernel
- C. Fresnel-column specializations

## iv. References

The coefficient and flux identities are derived in `FresnelAmplitude` and `FresnelFlux`. This
Physlib-original completion does not assert reverse-incidence physics, reciprocity, outgoing
semantics, reference-plane or polarization-frame transport, typed physical ports, modal
completeness, or electromagnetic mode normalization. Strictly positive incident and transmitted
normal components exclude grazing and critical channels. TIR evanescent transmission and lossy
media are outside this ordinary positive-power kernel.
-/

@[expose] public section

namespace Optics

open Electromagnetism Matrix

noncomputable section

namespace PlanarDielectricInterface

/-!
## A. Square-root flux normalization
-/

/-- A real electric-field transmission coefficient expressed in normalized power coordinates.

The multiplier is the square root of the transmitted-to-incident normal-admittance ratio. A
physical interpretation therefore requires a nonnegative ratio. -/
def powerNormalizedFresnelTransmissionCoefficient
    (fluxFactor transmissionCoefficient : ℝ) : ℝ :=
  Real.sqrt fluxFactor * transmissionCoefficient

/-- Squaring the power-normalized transmission coefficient recovers the weighted electric-field
coefficient when the flux factor is nonnegative. -/
lemma powerNormalizedFresnelTransmissionCoefficient_sq
    {fluxFactor transmissionCoefficient : ℝ} (hFactor : 0 ≤ fluxFactor) :
    powerNormalizedFresnelTransmissionCoefficient fluxFactor transmissionCoefficient ^ 2 =
      fluxFactor * transmissionCoefficient ^ 2 := by
  rw [powerNormalizedFresnelTransmissionCoefficient, mul_pow, Real.sq_sqrt hFactor]

/-!
## B. Scalar two-side kernel
-/

/-- The real two-side algebraic completion of one normalized Fresnel scattering column.

Coordinate `0` denotes the negative-side channel and coordinate `1` the positive-side channel.
The first column is the supplied left-incident reflection and normalized transmission. The second
column is its real symmetric unitary completion; this definition alone is not a reverse-incidence
derivation. -/
def scalarFresnelScatteringKernel (reflection transmission fluxFactor : ℝ) :
    ScatteringMatrix (Fin 2) where
  toModeTransform := !![
    (reflection : ℂ),
      (powerNormalizedFresnelTransmissionCoefficient fluxFactor transmission : ℂ);
    (powerNormalizedFresnelTransmissionCoefficient fluxFactor transmission : ℂ),
      -(reflection : ℂ)]

/-- The scalar kernel acts by the displayed reflection/transmission equations. -/
lemma scalarFresnelScatteringKernel_toLinearMap_apply
    (reflection transmission fluxFactor : ℝ) (input : ModeAmplitude (Fin 2)) :
    (scalarFresnelScatteringKernel reflection transmission fluxFactor).toModeTransform.toLinearMap
        input =
      WithLp.toLp 2 ![
        (reflection : ℂ) * input 0 +
          (powerNormalizedFresnelTransmissionCoefficient fluxFactor transmission : ℂ) * input 1,
        (powerNormalizedFresnelTransmissionCoefficient fluxFactor transmission : ℂ) * input 0 -
          (reflection : ℂ) * input 1] := by
  ext i
  fin_cases i <;>
    simp [scalarFresnelScatteringKernel, ModeTransform.toLinearMap, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

private lemma normSq_real_orthogonal_pair (reflection transmission : ℝ) (left right : ℂ) :
    Complex.normSq ((reflection : ℂ) * left + (transmission : ℂ) * right) +
        Complex.normSq ((transmission : ℂ) * left - (reflection : ℂ) * right) =
      (reflection ^ 2 + transmission ^ 2) *
        (Complex.normSq left + Complex.normSq right) := by
  simp [Complex.normSq_apply]
  ring

/-- A nonnegative flux factor and the scalar `R + T = 1` identity make the completed kernel
lossless in normalized modal coordinates. -/
lemma scalarFresnelScatteringKernel_isLossless
    {reflection transmission fluxFactor : ℝ} (hFactor : 0 ≤ fluxFactor)
    (hBalance : reflection ^ 2 + fluxFactor * transmission ^ 2 = 1) :
    (scalarFresnelScatteringKernel reflection transmission fluxFactor).IsLossless := by
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving]
  intro input
  rw [scalarFresnelScatteringKernel_toLinearMap_apply]
  rw [ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq, Fin.sum_univ_two,
    Fin.sum_univ_two]
  change
    Complex.normSq ((reflection : ℂ) * input 0 +
          (powerNormalizedFresnelTransmissionCoefficient fluxFactor transmission : ℂ) * input 1) +
        Complex.normSq
          ((powerNormalizedFresnelTransmissionCoefficient fluxFactor transmission : ℂ) * input 0 -
            (reflection : ℂ) * input 1) =
      Complex.normSq (input 0) + Complex.normSq (input 1)
  rw [normSq_real_orthogonal_pair,
    powerNormalizedFresnelTransmissionCoefficient_sq hFactor, hBalance, one_mul]

/-!
## C. Fresnel-column specializations
-/

/-- The normalized algebraic completion of the established left-incident full-vector s Fresnel
column. This is not yet a Maxwell-derived reverse-incidence interface component. -/
def sFresnelScatteringKernel (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ScatteringMatrix (Fin 2) :=
  scalarFresnelScatteringKernel
    (interface.sFresnelReflectionCoefficient chi_i chi_t)
    (interface.sFresnelTransmissionCoefficient chi_i chi_t)
    (interface.fresnelTransmissionFluxFactor chi_i chi_t)

/-- The normalized algebraic completion of the established left-incident full-vector p Fresnel
column. This is not yet a Maxwell-derived reverse-incidence interface component. -/
def pFresnelScatteringKernel (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ScatteringMatrix (Fin 2) :=
  scalarFresnelScatteringKernel
    (interface.pFresnelReflectionCoefficient chi_i chi_t)
    (interface.pFresnelTransmissionCoefficient chi_i chi_t)
    (interface.fresnelTransmissionFluxFactor chi_i chi_t)

/-- The s-polarized scalar completion is lossless for strictly propagating positive-normal
channels. -/
lemma sFresnelScatteringKernel_isLossless (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 < chi_t) :
    (interface.sFresnelScatteringKernel chi_i chi_t).IsLossless := by
  apply scalarFresnelScatteringKernel_isLossless
  · exact interface.fresnelTransmissionFluxFactor_nonneg hIncident hTransmitted.le
  · simpa [sFresnelReflectance, sFresnelTransmittance] using
      interface.sFresnelReflectance_add_transmittance hIncident hTransmitted.le

/-- The p-polarized scalar completion is lossless for strictly propagating positive-normal
channels. -/
lemma pFresnelScatteringKernel_isLossless (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 < chi_t) :
    (interface.pFresnelScatteringKernel chi_i chi_t).IsLossless := by
  apply scalarFresnelScatteringKernel_isLossless
  · exact interface.fresnelTransmissionFluxFactor_nonneg hIncident hTransmitted.le
  · simpa [pFresnelReflectance, pFresnelTransmittance] using
      interface.pFresnelReflectance_add_transmittance hIncident hTransmitted.le

end PlanarDielectricInterface

end

end Optics
