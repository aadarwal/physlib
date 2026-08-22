/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.Vacuum.HarmonicWave
public import Physlib.Optics.Polarization.Basic

/-!
# Jones realization of a harmonic electromagnetic wave

## i. Overview

This file connects the Optics Jones representation to Physlib's explicit real electromagnetic
solution `ElectromagneticPotential.harmonicWaveX` in three spatial dimensions. The wave propagates
in the positive first-coordinate direction, its ordered transverse Jones basis is the second and
third coordinate directions, and its carrier phase is `k * c * t - k * x 0`.

The bridge takes positive wave number `k`, so the angular frequency `k * c` is positive while the
propagation direction remains separate data. It identifies the complete electric and magnetic
fields of this purely harmonic solution from the same amplitude and component-phase data used to
build the Jones vector.

## ii. Scope

This module does not define an inverse amplitude-phase decomposition for arbitrary Jones vectors:
signed amplitudes mean such data is not unique. It also does not reconstruct an electromagnetic
potential, which would require a gauge choice, and it makes no claim that squared Jones intensity
is irradiance or modal power. The explicit `harmonicWaveX` source contains no arbitrary static
background, and this bridge does not extend to one. The magnetic result is for `B`, not `H`.

## iii. Main results

- `harmonicWaveX_electricField_transverse_eq_realize`: componentwise transverse realization.
- `harmonicWaveX_electricField_eq_realize`: realization of the complete electric field.
- `harmonicWaveX_magneticField_eq_realize`: realization of the compatible magnetic field.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ElectromagneticPotential Space Matrix

noncomputable section

/-! ## A. Carrier and fixed propagation frame -/

/-- The propagation direction of `harmonicWaveX` in three spatial dimensions.

This is the positive first coordinate direction. The transverse Jones coordinates are ordered as
the second and third coordinate directions. -/
def harmonicWaveXDirection : Space.Direction 3 :=
  ⟨Space.basis 0, by simp⟩

/-- The product `k * c` for `harmonicWaveX` in free space.

For positive wave number `k`, this is the positive physical angular frequency. -/
def harmonicWaveXAngularFrequency (F : FreeSpace) (k : ℝ) : ℝ :=
  k * F.c.val

/-- The carrier phase of `harmonicWaveX` before its component-dependent phases.

The phase origin is fixed at time zero and spatial origin. -/
def harmonicWaveXCarrierPhase (F : FreeSpace) (k : ℝ) (t : Time) (x : Space 3) : ℝ :=
  harmonicWaveXAngularFrequency F k * t.val - k * x 0

/-- Positive wave number gives positive angular frequency in free space. -/
lemma harmonicWaveXAngularFrequency_pos (F : FreeSpace) {k : ℝ} (hk : 0 < k) :
    0 < harmonicWaveXAngularFrequency F k := by
  exact mul_pos hk (SpeedOfLight.val_pos F.c)

/-- Realize a Jones vector in the fixed three-dimensional `harmonicWaveX` frame.

The longitudinal coordinate is zero and the two Jones coordinates are the ordered transverse
coordinates. -/
def JonesVector.realizeHarmonicWaveXFrame (J : JonesVector) (θ : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, J.realize θ 0, J.realize θ 1]

/-- The longitudinal coordinate of a Jones realization in the `harmonicWaveX` frame is zero. -/
@[simp]
lemma JonesVector.realizeHarmonicWaveXFrame_zero (J : JonesVector) (θ : ℝ) :
    J.realizeHarmonicWaveXFrame θ 0 = 0 := by
  simp [JonesVector.realizeHarmonicWaveXFrame]

/-- The transverse coordinates of the fixed-frame realization are the Jones realization. -/
@[simp]
lemma JonesVector.realizeHarmonicWaveXFrame_succ
    (J : JonesVector) (θ : ℝ) (i : Fin 2) :
    J.realizeHarmonicWaveXFrame θ i.succ = J.realize θ i := by
  fin_cases i <;> simp [JonesVector.realizeHarmonicWaveXFrame]

/-- Realize the magnetic field compatible with a Jones electric field in the fixed free-space
frame.

This is `c⁻¹` times the cross product of the unit propagation direction with the realized
electric field. -/
def JonesVector.realizeMagneticHarmonicWaveXFrame (F : FreeSpace) (J : JonesVector)
    (θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (1 / F.c.val) •
    (Space.basis.repr harmonicWaveXDirection.unit ⨯ₑ₃ J.realizeHarmonicWaveXFrame θ)

/-- The compatible magnetic realization has the expected fixed-frame coordinates. -/
lemma JonesVector.realizeMagneticHarmonicWaveXFrame_eq
    (F : FreeSpace) (J : JonesVector) (θ : ℝ) :
    J.realizeMagneticHarmonicWaveXFrame F θ =
      WithLp.toLp 2 ![0, -J.realize θ 1 / F.c.val, J.realize θ 0 / F.c.val] := by
  ext i
  fin_cases i <;>
    simp [JonesVector.realizeMagneticHarmonicWaveXFrame, harmonicWaveXDirection,
      JonesVector.realizeHarmonicWaveXFrame, crossProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, div_eq_mul_inv] <;>
    ring

/-! ## B. Plane-wave and electric-field bridge -/

/-- The positive-wave-number harmonic solution is a plane wave in the named propagation
direction. -/
lemma harmonicWaveX_isPlaneWave_direction
    (F : FreeSpace) {k : ℝ} (hk : 0 < k) (amplitude phaseOffset : Fin 2 → ℝ) :
    IsPlaneWave F (harmonicWaveX F k amplitude phaseOffset)
      harmonicWaveXDirection := by
  simpa [harmonicWaveXDirection] using
    harmonicWaveX_isPlaneWave F k hk.ne' amplitude phaseOffset

/-- Each transverse electric-field component of `harmonicWaveX` equals realization of the
corresponding Jones component at the common carrier phase. -/
lemma harmonicWaveX_electricField_transverse_eq_realize
    (F : FreeSpace) {k : ℝ} (hk : 0 < k) (amplitude phaseOffset : Fin 2 → ℝ)
    (t : Time) (x : Space 3) (i : Fin 2) :
    (harmonicWaveX F k amplitude phaseOffset).electricField F.c t x i.succ =
      (JonesVector.ofAmplitudePhase amplitude phaseOffset).realize
        (harmonicWaveXCarrierPhase F k t x) i := by
  rw [harmonicWaveX_electricField_succ F k hk.ne']
  symm
  simpa [harmonicWaveXCarrierPhase, harmonicWaveXAngularFrequency] using
    JonesVector.realize_ofAmplitudePhase_apply amplitude phaseOffset
      (harmonicWaveXCarrierPhase F k t x) i

/-- The complete electric field of `harmonicWaveX` equals the fixed-frame realization of its
Jones amplitude-phase data. -/
lemma harmonicWaveX_electricField_eq_realize
    (F : FreeSpace) {k : ℝ} (hk : 0 < k) (amplitude phaseOffset : Fin 2 → ℝ)
    (t : Time) (x : Space 3) :
    (harmonicWaveX F k amplitude phaseOffset).electricField F.c t x =
      (JonesVector.ofAmplitudePhase amplitude phaseOffset).realizeHarmonicWaveXFrame
        (harmonicWaveXCarrierPhase F k t x) := by
  ext i
  fin_cases i
  · simp [JonesVector.realizeHarmonicWaveXFrame, harmonicWaveX_electricField_zero]
  · simpa [JonesVector.realizeHarmonicWaveXFrame] using
      harmonicWaveX_electricField_transverse_eq_realize
        F hk amplitude phaseOffset t x (0 : Fin 2)
  · simpa [JonesVector.realizeHarmonicWaveXFrame] using
      harmonicWaveX_electricField_transverse_eq_realize
        F hk amplitude phaseOffset t x (1 : Fin 2)

/-! ## C. Magnetic-field bridge -/

/-- The magnetic field of `harmonicWaveX` equals the compatible fixed-frame realization of the
same Jones amplitude-phase data. -/
lemma harmonicWaveX_magneticField_eq_realize
    (F : FreeSpace) {k : ℝ} (hk : 0 < k) (amplitude phaseOffset : Fin 2 → ℝ)
    (t : Time) (x : Space 3) :
    (harmonicWaveX F k amplitude phaseOffset).magneticField F.c t x =
      (JonesVector.ofAmplitudePhase amplitude phaseOffset).realizeMagneticHarmonicWaveXFrame F
        (harmonicWaveXCarrierPhase F k t x) := by
  rw [magneticField_eq_magneticFieldMatrix _
    (harmonicWaveX_differentiable F k amplitude phaseOffset)]
  ext i
  rw [JonesVector.realizeMagneticHarmonicWaveXFrame_eq]
  fin_cases i
  · change -((harmonicWaveX F k amplitude phaseOffset).magneticFieldMatrix
      F.c t x ((0 : Fin 2).succ, (1 : Fin 2).succ)) = _
    rw [harmonicWaveX_magneticFieldMatrix_succ_succ
      F k amplitude phaseOffset t x (0 : Fin 2) (1 : Fin 2)]
    simp
  · change -((harmonicWaveX F k amplitude phaseOffset).magneticFieldMatrix
      F.c t x ((1 : Fin 2).succ, 0)) = _
    rw [harmonicWaveX_magneticFieldMatrix_succ_zero
      F k hk.ne' amplitude phaseOffset t x (1 : Fin 2)]
    simp [harmonicWaveXCarrierPhase, harmonicWaveXAngularFrequency, div_eq_mul_inv]
    rw [Phasor.realize_ofAmplitudePhase]
    ring_nf
  · change -((harmonicWaveX F k amplitude phaseOffset).magneticFieldMatrix
      F.c t x (0, (0 : Fin 2).succ)) = _
    rw [harmonicWaveX_magneticFieldMatrix_zero_succ
      F k hk.ne' amplitude phaseOffset t x (0 : Fin 2)]
    simp [harmonicWaveXCarrierPhase, harmonicWaveXAngularFrequency, div_eq_mul_inv]
    rw [Phasor.realize_ofAmplitudePhase]
    ring_nf

/-- The magnetic and electric fields of `harmonicWaveX` obey the fixed-frame plane-wave relation
`B = c⁻¹ k̂ × E`. -/
lemma harmonicWaveX_magneticField_eq_cross_electricField
    (F : FreeSpace) {k : ℝ} (hk : 0 < k) (amplitude phaseOffset : Fin 2 → ℝ)
    (t : Time) (x : Space 3) :
    (harmonicWaveX F k amplitude phaseOffset).magneticField F.c t x =
      (1 / F.c.val) • (Space.basis.repr harmonicWaveXDirection.unit ⨯ₑ₃
        (harmonicWaveX F k amplitude phaseOffset).electricField F.c t x) := by
  rw [harmonicWaveX_magneticField_eq_realize F hk,
    harmonicWaveX_electricField_eq_realize F hk]
  rfl

end

end Optics
