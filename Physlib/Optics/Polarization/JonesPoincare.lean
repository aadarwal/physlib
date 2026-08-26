/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Physlib.Optics.Polarization.JonesStokes
public import Physlib.Optics.Polarization.Poincare

/-!
# Unit Jones vectors on the Poincare sphere

## i. Overview

This file identifies unit-intensity Jones vectors modulo a common unit-complex phase with the
Poincare sphere. The forward map deliberately follows the existing connected chain from Jones
data, through pure unit-trace coherency and Stokes polarization, to the Poincare coordinates.
Here unit intensity means that the squared raw electric-field amplitude is one; it is not
irradiance or modal power without the later electromagnetic normalization bridge.

The result is only an algebraic equivalence of orbit sets. No topological equivalence or
continuously varying choice of representatives is asserted. The private proof uses one
algebraic formula on each side of a fixed boundary.

## ii. Key results

- `UnitJonesVector`: Jones vectors whose squared intensity is one.
- `UnitJonesVector.coherency`: their unit-trace pure coherency.
- `UnitJonesVector.toPoincareSphere`: their Stokes polarization on the Poincare sphere.
- `UnitJonesVector.toPoincareSphere_eq_iff_exists_phase`: the exact fiber characterization.
- `JonesPhaseClass`: the orbit quotient for the `Circle` action.
- `unitJonesPhasePoincareEquiv`: the algebraic orbit-set equivalence with the Poincare sphere.

## iii. Table of contents

- A. Unit Jones vectors and the circle action
- B. Pure coherency and the Poincare-sphere map
- C. Exact phase characterization
- D. Sphere representatives and the orbit-set equivalence
- E. Canonical-axis checks

## iv. References

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Unit Jones vectors and the circle action

-/

/-- A Jones vector whose squared Jones intensity is one. -/
abbrev UnitJonesVector := {J : JonesVector // J.intensity = 1}

namespace UnitJonesVector

/-- Multiply a unit Jones vector by a common unit-complex phase. -/
def phaseSMul (z : Circle) (J : UnitJonesVector) : UnitJonesVector :=
  ⟨JonesVector.scale (z : ℂ) J.val, by
    rw [JonesVector.intensity_scale_of_norm_eq_one (Circle.norm_coe z), J.property]⟩

/-- Unit-complex numbers act on unit Jones vectors by common complex scaling. -/
instance : SMul Circle UnitJonesVector := ⟨phaseSMul⟩

/-- The circle action is the underlying Jones-vector scaling operation. -/
@[simp]
lemma smul_val (z : Circle) (J : UnitJonesVector) :
    (z • J).val = JonesVector.scale (z : ℂ) J.val := rfl

/-- Common unit-complex scaling defines a multiplicative circle action. -/
instance : MulAction Circle UnitJonesVector where
  one_smul J := by
    apply Subtype.ext
    apply JonesVector.ext
    exact one_smul ℂ J.val.components
  mul_smul z w J := by
    apply Subtype.ext
    apply JonesVector.ext
    exact mul_smul (z : ℂ) (w : ℂ) J.val.components

/-- Apply a common real phase shift while preserving unit Jones intensity. -/
def phaseShift (phase : ℝ) (J : UnitJonesVector) : UnitJonesVector :=
  ⟨J.val.phaseShift phase, by rw [JonesVector.intensity_phaseShift, J.property]⟩

/-- The exponential circle action is the existing Jones phase-shift operation. -/
@[simp]
lemma circle_exp_smul (phase : ℝ) (J : UnitJonesVector) :
    Circle.exp phase • J = J.phaseShift phase := by
  apply Subtype.ext
  rfl

/-- The component vector of a unit Jones vector has norm one. -/
@[simp]
lemma components_norm (J : UnitJonesVector) : ‖J.val.components‖ = 1 := by
  have h := J.property
  rw [JonesVector.intensity] at h
  nlinarith [norm_nonneg J.val.components]

/-- The component vector of a unit Jones vector is nonzero. -/
lemma components_ne_zero (J : UnitJonesVector) : J.val.components ≠ 0 := by
  intro hzero
  have hnorm := J.components_norm
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-!

## B. Pure coherency and the Poincare-sphere map

-/

/-- The pure unit-trace coherency matrix determined by a unit Jones vector. -/
def coherency (J : UnitJonesVector) : UnitTracePolarizationCoherency :=
  ⟨J.val.coherency, by simpa using J.property⟩

/-- The underlying coherency of normalized Jones coherency is the Jones outer product. -/
@[simp]
lemma coherency_val (J : UnitJonesVector) : J.coherency.val = J.val.coherency := rfl

/-- A unit Jones vector has rank-one coherency. -/
lemma coherency_rank_eq_one (J : UnitJonesVector) : J.coherency.val.toMatrix.rank = 1 := by
  rw [Matrix.rank_eq_one_iff_ne_zero_and_det_eq_zero]
  refine ⟨?_, J.val.coherency_det_eq_zero⟩
  intro hzero
  have htrace := J.coherency.val.trace_eq_zero_iff_toMatrix_eq_zero.mpr hzero
  change J.val.coherency.trace = 0 at htrace
  rw [JonesVector.coherency_trace] at htrace
  rw [J.property] at htrace
  norm_num at htrace

/-- The Poincare-sphere point obtained through pure coherency and its Stokes polarization. -/
def toPoincareSphere (J : UnitJonesVector) : PoincareSphere :=
  ⟨(unitTraceCoherencyPoincareEquiv J.coherency).val,
    J.coherency.poincare_mem_sphere_iff_rank_eq_one.mpr J.coherency_rank_eq_one⟩

/-- The underlying sphere vector is the Jones-derived Stokes polarization. -/
@[simp]
lemma toPoincareSphere_val (J : UnitJonesVector) :
    J.toPoincareSphere.val = J.val.stokes.polarization := rfl

/-- Common unit phase leaves the Poincare-sphere point unchanged. -/
@[simp]
lemma toPoincareSphere_smul (z : Circle) (J : UnitJonesVector) :
    (z • J).toPoincareSphere = J.toPoincareSphere := by
  apply Subtype.ext
  simp only [toPoincareSphere_val, smul_val]
  rw [JonesVector.stokes_scale_of_norm_eq_one (Circle.norm_coe z)]

/-!

## C. Exact phase characterization

-/

/-- Every unit Jones vector has a nonzero component. -/
private lemma exists_component_ne_zero (J : UnitJonesVector) :
    ∃ i, J.val.components i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_ne_iff] at h
  have hzero : J.val.components = 0 := by
    ext i
    exact h i
  have hintensity : J.val.intensity = 0 := by
    simp [JonesVector.intensity, hzero]
  linarith [J.property]

/-- Two unit Jones vectors have the same pure coherency exactly when they differ by a unit phase. -/
lemma coherency_eq_iff_exists_phase (J K : UnitJonesVector) :
    J.coherency = K.coherency ↔ ∃ z : Circle, z • K = J := by
  constructor
  · intro hcoherency
    have hentry : ∀ i j,
        J.val.components i * starRingEnd ℂ (J.val.components j) =
          K.val.components i * starRingEnd ℂ (K.val.components j) := by
      intro i j
      exact congrFun₂ (congrArg (fun C => C.val.toMatrix) hcoherency) i j
    obtain ⟨k, hk⟩ := K.exists_component_ne_zero
    have hdiag := hentry k k
    rw [Complex.mul_conj, Complex.mul_conj] at hdiag
    have hnormSq : Complex.normSq (J.val.components k) =
        Complex.normSq (K.val.components k) := Complex.ofReal_injective hdiag
    let z : ℂ := J.val.components k / K.val.components k
    have hz_norm : ‖z‖ = 1 := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm]
      simp only [z, Complex.normSq_div, hnormSq]
      rw [div_self (fun hn => hk (Complex.normSq_eq_zero.mp hn))]
      norm_num
    refine ⟨⟨z, Metric.mem_sphere.mpr ?_⟩, ?_⟩
    · simpa only [dist_zero_right] using hz_norm
    · symm
      apply Subtype.ext
      apply JonesVector.ext
      ext i
      change J.val.components i = z * K.val.components i
      have hik := hentry i k
      rw [show J.val.components k = z * K.val.components k by simp [z, hk],
        starRingEnd_apply, star_mul] at hik
      have hcancel : J.val.components i * starRingEnd ℂ z = K.val.components i := by
        apply mul_right_cancel₀ (show starRingEnd ℂ (K.val.components k) ≠ 0 by simp [hk])
        simpa only [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc] using hik
      rw [← hcancel, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz_norm]
      simp
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    exact JonesVector.coherency_scale_of_norm_eq_one (Circle.norm_coe z) K.val

/-- Two unit Jones vectors determine the same sphere point exactly when they differ by unit
phase. -/
lemma toPoincareSphere_eq_iff_exists_phase (J K : UnitJonesVector) :
    J.toPoincareSphere = K.toPoincareSphere ↔ ∃ z : Circle, z • K = J := by
  rw [← coherency_eq_iff_exists_phase]
  constructor
  · intro hsphere
    apply unitTraceCoherencyPoincareEquiv.injective
    apply Subtype.ext
    change J.toPoincareSphere.val = K.toPoincareSphere.val
    exact congrArg Subtype.val hsphere
  · intro hcoherency
    apply Subtype.ext
    change (unitTraceCoherencyPoincareEquiv J.coherency).val =
      (unitTraceCoherencyPoincareEquiv K.coherency).val
    exact congrArg Subtype.val (congrArg unitTraceCoherencyPoincareEquiv hcoherency)

/-!

## D. Sphere representatives and the orbit-set equivalence

-/

private lemma poincareSphere_sum_sq (p : PoincareSphere) :
    p.val 0 ^ 2 + p.val 1 ^ 2 + p.val 2 ^ 2 = 1 := by
  have hnorm : ‖p.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  calc
    p.val 0 ^ 2 + p.val 1 ^ 2 + p.val 2 ^ 2 = ‖p.val‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs]
    _ = 1 := by rw [hnorm]; norm_num

/-- The first private algebraic chart used to choose a Jones representative. -/
private def northChartJones (x y z : ℝ) : JonesVector :=
  JonesVector.ofComponents (Real.sqrt ((1 + x) / 2))
    (((y : ℂ) + Complex.I * (z : ℂ)) / (2 * Real.sqrt ((1 + x) / 2)))

/-- The second private algebraic chart used to choose a Jones representative. -/
private def southChartJones (x y z : ℝ) : JonesVector :=
  JonesVector.ofComponents
    (((y : ℂ) - Complex.I * (z : ℂ)) / (2 * Real.sqrt ((1 - x) / 2)))
    (Real.sqrt ((1 - x) / 2))

private lemma normSq_plus_I (y z : ℝ) :
    Complex.normSq ((y : ℂ) + Complex.I * (z : ℂ)) = y ^ 2 + z ^ 2 := by
  rw [mul_comm Complex.I]
  exact Complex.normSq_add_mul_I y z

private lemma normSq_minus_I (y z : ℝ) :
    Complex.normSq ((y : ℂ) - Complex.I * (z : ℂ)) = y ^ 2 + z ^ 2 := by
  rw [show (y : ℂ) - Complex.I * (z : ℂ) =
    (y : ℂ) + ((-z : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.normSq_add_mul_I]
  ring

private lemma northChartJones_intensity (x y z : ℝ) (hx : 0 ≤ x)
    (hsphere : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (northChartJones x y z).intensity = 1 := by
  have ha : 0 < (1 + x) / 2 := by linarith
  rw [JonesVector.intensity_eq_sum_normSq, Fin.sum_univ_two]
  simp only [northChartJones, JonesVector.ofComponents_zero, JonesVector.ofComponents_one,
    Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_mul,
    Complex.normSq_ofNat, normSq_plus_I]
  rw [Real.mul_self_sqrt ha.le]
  field_simp [ne_of_gt ha]
  nlinarith

private lemma southChartJones_intensity (x y z : ℝ) (hx : x < 0)
    (hsphere : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (southChartJones x y z).intensity = 1 := by
  have ha : 0 < (1 - x) / 2 := by linarith
  have hden : 1 - x ≠ 0 := ne_of_gt (by linarith)
  rw [JonesVector.intensity_eq_sum_normSq, Fin.sum_univ_two]
  simp only [southChartJones, JonesVector.ofComponents_zero, JonesVector.ofComponents_one,
    Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_mul,
    Complex.normSq_ofNat, normSq_minus_I]
  rw [Real.mul_self_sqrt ha.le]
  field_simp [hden]
  nlinarith

private lemma northChartJones_stokes_zero (x y z : ℝ) (hx : 0 ≤ x)
    (hsphere : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (northChartJones x y z).stokes (Sum.inr 0) = x := by
  have ha : 0 < (1 + x) / 2 := by linarith
  rw [JonesVector.stokes_inr_zero]
  simp only [northChartJones, JonesVector.ofComponents_zero, JonesVector.ofComponents_one,
    Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_mul,
    Complex.normSq_ofNat, normSq_plus_I]
  rw [Real.mul_self_sqrt ha.le]
  field_simp [ne_of_gt ha]
  nlinarith

private lemma southChartJones_stokes_zero (x y z : ℝ) (hx : x < 0)
    (hsphere : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (southChartJones x y z).stokes (Sum.inr 0) = x := by
  have ha : 0 < (1 - x) / 2 := by linarith
  have hden : 1 - x ≠ 0 := ne_of_gt (by linarith)
  rw [JonesVector.stokes_inr_zero]
  simp only [southChartJones, JonesVector.ofComponents_zero, JonesVector.ofComponents_one,
    Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_mul,
    Complex.normSq_ofNat, normSq_minus_I]
  rw [Real.mul_self_sqrt ha.le]
  field_simp [hden]
  nlinarith

private lemma northChartJones_cross (x y z : ℝ) (hx : 0 ≤ x) :
    (northChartJones x y z).components 0 * star ((northChartJones x y z).components 1) =
      ((y : ℂ) - Complex.I * (z : ℂ)) / 2 := by
  have ha : 0 < (1 + x) / 2 := by linarith
  have hsqrt : (Real.sqrt ((1 + x) / 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 ha)
  simp only [northChartJones, JonesVector.ofComponents_zero, JonesVector.ofComponents_one,
    Complex.star_def, map_div₀, map_add, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  field_simp
  ring

private lemma southChartJones_cross (x y z : ℝ) (hx : x < 0) :
    (southChartJones x y z).components 0 * star ((southChartJones x y z).components 1) =
      ((y : ℂ) - Complex.I * (z : ℂ)) / 2 := by
  have ha : 0 < (1 - x) / 2 := by linarith
  have hsqrt : (Real.sqrt ((1 - x) / 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 ha)
  simp only [southChartJones, JonesVector.ofComponents_zero, JonesVector.ofComponents_one,
    Complex.star_def, Complex.conj_ofReal]
  field_simp

private lemma stokes_inr_one_eq_of_cross (J : JonesVector) (y z : ℝ)
    (hcross : J.components 0 * star (J.components 1) =
      ((y : ℂ) - Complex.I * (z : ℂ)) / 2) :
    J.stokes (Sum.inr 1) = y := by
  rw [JonesVector.stokes_inr_one, hcross]
  norm_num
  ring

private lemma stokes_inr_two_eq_of_cross (J : JonesVector) (y z : ℝ)
    (hcross : J.components 0 * star (J.components 1) =
      ((y : ℂ) - Complex.I * (z : ℂ)) / 2) :
    J.stokes (Sum.inr 2) = z := by
  rw [JonesVector.stokes_inr_two, hcross]
  norm_num
  ring

/-- A private choice of raw Jones representative using the two algebraic charts. -/
private def poincareJonesRepresentativeRaw (p : PoincareSphere) : JonesVector :=
  if 0 ≤ p.val 0 then northChartJones (p.val 0) (p.val 1) (p.val 2)
  else southChartJones (p.val 0) (p.val 1) (p.val 2)

private lemma poincareJonesRepresentativeRaw_intensity (p : PoincareSphere) :
    (poincareJonesRepresentativeRaw p).intensity = 1 := by
  by_cases h : 0 ≤ p.val 0
  · rw [poincareJonesRepresentativeRaw, if_pos h]
    exact northChartJones_intensity _ _ _ h (poincareSphere_sum_sq p)
  · rw [poincareJonesRepresentativeRaw, if_neg h]
    exact southChartJones_intensity _ _ _ (lt_of_not_ge h) (poincareSphere_sum_sq p)

/-- A private unit-intensity representative selected for a sphere point. -/
private def poincareJonesRepresentative (p : PoincareSphere) : UnitJonesVector :=
  ⟨poincareJonesRepresentativeRaw p, poincareJonesRepresentativeRaw_intensity p⟩

private lemma poincareJonesRepresentative_polarization (p : PoincareSphere) :
    (poincareJonesRepresentative p).val.stokes.polarization = p.val := by
  change (poincareJonesRepresentativeRaw p).stokes.polarization = p.val
  ext i
  rw [StokesVector.polarization_apply]
  fin_cases i
  · by_cases h : 0 ≤ p.val 0
    · rw [poincareJonesRepresentativeRaw, if_pos h]
      exact northChartJones_stokes_zero _ _ _ h (poincareSphere_sum_sq p)
    · rw [poincareJonesRepresentativeRaw, if_neg h]
      exact southChartJones_stokes_zero _ _ _ (lt_of_not_ge h) (poincareSphere_sum_sq p)
  · by_cases h : 0 ≤ p.val 0
    · rw [poincareJonesRepresentativeRaw, if_pos h]
      apply stokes_inr_one_eq_of_cross
      exact northChartJones_cross _ _ _ h
    · rw [poincareJonesRepresentativeRaw, if_neg h]
      apply stokes_inr_one_eq_of_cross
      exact southChartJones_cross _ _ _ (lt_of_not_ge h)
  · by_cases h : 0 ≤ p.val 0
    · rw [poincareJonesRepresentativeRaw, if_pos h]
      apply stokes_inr_two_eq_of_cross
      exact northChartJones_cross _ _ _ h
    · rw [poincareJonesRepresentativeRaw, if_neg h]
      apply stokes_inr_two_eq_of_cross
      exact southChartJones_cross _ _ _ (lt_of_not_ge h)

private lemma poincareJonesRepresentative_toPoincareSphere (p : PoincareSphere) :
    (poincareJonesRepresentative p).toPoincareSphere = p := by
  apply Subtype.ext
  exact poincareJonesRepresentative_polarization p

/-- Every Poincare-sphere point is represented by a unit Jones vector. -/
lemma toPoincareSphere_surjective : Function.Surjective toPoincareSphere := by
  intro p
  exact ⟨poincareJonesRepresentative p, poincareJonesRepresentative_toPoincareSphere p⟩

end UnitJonesVector

namespace UnitTracePolarizationCoherency

/-- A unit-trace coherency has rank one exactly when it is the pure coherency of a unit Jones
vector. -/
lemma rank_eq_one_iff_exists_unitJones_coherency (C : UnitTracePolarizationCoherency) :
    C.val.toMatrix.rank = 1 ↔ ∃ J : UnitJonesVector, C = J.coherency := by
  constructor
  · intro hrank
    let p : PoincareSphere :=
      ⟨(unitTraceCoherencyPoincareEquiv C).val,
        C.poincare_mem_sphere_iff_rank_eq_one.mpr hrank⟩
    obtain ⟨J, hJ⟩ := UnitJonesVector.toPoincareSphere_surjective p
    refine ⟨J, ?_⟩
    apply unitTraceCoherencyPoincareEquiv.injective
    apply Subtype.ext
    have hp := congrArg Subtype.val hJ
    change (unitTraceCoherencyPoincareEquiv J.coherency).val =
      (unitTraceCoherencyPoincareEquiv C).val at hp
    exact hp.symm
  · rintro ⟨J, rfl⟩
    exact J.coherency_rank_eq_one

end UnitTracePolarizationCoherency

/-- Unit Jones vectors modulo the orbit relation of common unit-complex phase. -/
abbrev JonesPhaseClass := MulAction.orbitRel.Quotient Circle UnitJonesVector

/-- Map a unit-Jones phase orbit to its common Poincare-sphere point. -/
def jonesPhasePoincareMap : JonesPhaseClass → PoincareSphere := fun q =>
  Quotient.liftOn' q UnitJonesVector.toPoincareSphere fun J K h => by
    rw [UnitJonesVector.toPoincareSphere_eq_iff_exists_phase]
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)

/-- The phase-orbit map sends the class of a unit Jones vector to its sphere point. -/
@[simp]
lemma jonesPhasePoincareMap_mk (J : UnitJonesVector) :
    jonesPhasePoincareMap (Quotient.mk'' J) = J.toPoincareSphere := rfl

/-- Common unit phase does not change the orbit class of a unit Jones vector. -/
lemma jonesPhaseClass_mk_smul (z : Circle) (J : UnitJonesVector) :
    (Quotient.mk'' (z • J) : JonesPhaseClass) = Quotient.mk'' J :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

/-- The map from unit-Jones phase classes to sphere points is bijective. -/
lemma jonesPhasePoincareMap_bijective : Function.Bijective jonesPhasePoincareMap := by
  constructor
  · intro q r h
    induction q using Quotient.inductionOn' with
    | _ J =>
        induction r using Quotient.inductionOn' with
        | _ K =>
            apply Quotient.sound
            change (MulAction.orbitRel Circle UnitJonesVector) J K
            rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
            exact (UnitJonesVector.toPoincareSphere_eq_iff_exists_phase J K).mp h
  · intro p
    obtain ⟨J, hJ⟩ := UnitJonesVector.toPoincareSphere_surjective p
    exact ⟨Quotient.mk'' J, hJ⟩

/-- Unit Jones vectors modulo common unit phase are algebraically equivalent to the Poincare
sphere. No topological equivalence or global continuous choice of representatives is asserted. -/
noncomputable def unitJonesPhasePoincareEquiv : JonesPhaseClass ≃ PoincareSphere :=
  Equiv.ofBijective jonesPhasePoincareMap jonesPhasePoincareMap_bijective

/-- The orbit-set equivalence sends a represented unit Jones vector to its sphere point. -/
@[simp]
lemma unitJonesPhasePoincareEquiv_apply_mk (J : UnitJonesVector) :
    unitJonesPhasePoincareEquiv (Quotient.mk'' J) = J.toPoincareSphere := rfl

/-!

## E. Canonical-axis checks

-/

namespace UnitJonesVector

/-- The normalized Jones vector in the first declared transverse coordinate. -/
def horizontal : UnitJonesVector :=
  ⟨JonesVector.horizontal, by
    rw [← JonesVector.stokes_intensity_eq_intensity]
    simp [StokesVector.intensity]⟩

/-- The normalized Jones vector in the second declared transverse coordinate. -/
def vertical : UnitJonesVector :=
  ⟨JonesVector.vertical, by
    rw [← JonesVector.stokes_intensity_eq_intensity]
    simp [StokesVector.intensity]⟩

/-- The normalized equal-component Jones vector with zero relative phase. -/
def diagonal : UnitJonesVector :=
  ⟨JonesVector.diagonal, by
    rw [← JonesVector.stokes_intensity_eq_intensity]
    simp [StokesVector.intensity]⟩

/-- The normalized equal-magnitude Jones vector with opposite real components. -/
def antidiagonal : UnitJonesVector :=
  ⟨JonesVector.antidiagonal, by
    rw [← JonesVector.stokes_intensity_eq_intensity]
    simp [StokesVector.intensity]⟩

/-- The normalized equal-magnitude Jones vector whose second component has positive `I` factor. -/
def plusIQuadrature : UnitJonesVector :=
  ⟨JonesVector.plusIQuadrature, by
    rw [← JonesVector.stokes_intensity_eq_intensity]
    simp [StokesVector.intensity]⟩

/-- The normalized equal-magnitude Jones vector whose second component has negative `I` factor. -/
def minusIQuadrature : UnitJonesVector :=
  ⟨JonesVector.minusIQuadrature, by
    rw [← JonesVector.stokes_intensity_eq_intensity]
    simp [StokesVector.intensity]⟩

/-- Horizontal unit Jones data maps to the positive first Poincare axis. -/
lemma toPoincareSphere_horizontal_val :
    horizontal.toPoincareSphere.val = EuclideanSpace.single 0 1 := by
  ext i
  rw [toPoincareSphere_val, StokesVector.polarization_apply]
  fin_cases i <;> simp [horizontal]

/-- Vertical unit Jones data maps to the negative first Poincare axis. -/
lemma toPoincareSphere_vertical_val :
    vertical.toPoincareSphere.val = -EuclideanSpace.single 0 1 := by
  ext i
  rw [toPoincareSphere_val, StokesVector.polarization_apply]
  fin_cases i <;> simp [vertical]

/-- Diagonal unit Jones data maps to the positive second Poincare axis. -/
lemma toPoincareSphere_diagonal_val :
    diagonal.toPoincareSphere.val = EuclideanSpace.single 1 1 := by
  ext i
  rw [toPoincareSphere_val, StokesVector.polarization_apply]
  fin_cases i <;> simp [diagonal]

/-- Antidiagonal unit Jones data maps to the negative second Poincare axis. -/
lemma toPoincareSphere_antidiagonal_val :
    antidiagonal.toPoincareSphere.val = -EuclideanSpace.single 1 1 := by
  ext i
  rw [toPoincareSphere_val, StokesVector.polarization_apply]
  fin_cases i <;> simp [antidiagonal]

/-- Positive-`I` quadrature unit Jones data maps to the positive third Poincare axis. -/
lemma toPoincareSphere_plusIQuadrature_val :
    plusIQuadrature.toPoincareSphere.val = EuclideanSpace.single 2 1 := by
  ext i
  rw [toPoincareSphere_val, StokesVector.polarization_apply]
  fin_cases i <;> simp [plusIQuadrature]

/-- Negative-`I` quadrature unit Jones data maps to the negative third Poincare axis. -/
lemma toPoincareSphere_minusIQuadrature_val :
    minusIQuadrature.toPoincareSphere.val = -EuclideanSpace.single 2 1 := by
  ext i
  rw [toPoincareSphere_val, StokesVector.polarization_apply]
  fin_cases i <;> simp [minusIQuadrature]

end UnitJonesVector

/-- The positive- and negative-`I` quadrature states represent distinct phase classes. -/
lemma plusIQuadrature_phaseClass_ne_minusIQuadrature :
    (Quotient.mk'' UnitJonesVector.plusIQuadrature : JonesPhaseClass) ≠
      Quotient.mk'' UnitJonesVector.minusIQuadrature := by
  intro h
  have hp := congrArg unitJonesPhasePoincareEquiv h
  rw [unitJonesPhasePoincareEquiv_apply_mk, unitJonesPhasePoincareEquiv_apply_mk] at hp
  have hval := congrArg Subtype.val hp
  rw [UnitJonesVector.toPoincareSphere_plusIQuadrature_val,
    UnitJonesVector.toPoincareSphere_minusIQuadrature_val] at hval
  have hcoord := congrArg (fun p : PoincareVector => p 2) hval
  norm_num at hcoord

end

end Optics
