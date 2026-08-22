/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Mueller.Algebra
public import Physlib.Optics.Polarization.Poincare

/-!
# Unitary Jones-induced Mueller transformations

This file proves the normalized consequences of algebraic Jones unitarity: coherency-trace and raw
Stokes-intensity preservation, fixation of the unpolarized axis, preservation of polarization
norm, an action on unit-intensity physical Stokes data, and preservation of the Poincare sphere.
These remain raw polarization-amplitude statements, not irradiance or Poynting-flux theorems.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace JonesMatrix

/-!
## A. Unitary Jones transformations
-/

/-- Unitary Jones congruence preserves the trace of every complex `2 × 2` matrix. -/
lemma IsUnitary.trace_congruence {M : JonesMatrix} (hM : M.IsUnitary)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (M.entries * A * M.entriesᴴ) = Matrix.trace A := by
  have hstar : M.entriesᴴ * M.entries = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hM
  rw [Matrix.trace_mul_cycle, hstar, one_mul]

/-- Unitary Jones congruence preserves the determinant of every complex `2 × 2` matrix. -/
lemma IsUnitary.det_congruence {M : JonesMatrix} (hM : M.IsUnitary)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (M.entries * A * M.entriesᴴ) = Matrix.det A := by
  rw [Matrix.det_mul_right_comm]
  have hstar : M.entries * M.entriesᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hM
  rw [hstar, one_mul]

/-- A unitary Jones matrix preserves coherency trace. -/
lemma IsUnitary.map_trace {M : JonesMatrix} (hM : M.IsUnitary)
    (C : PolarizationCoherency) :
    (C.map M.entries).trace = C.trace := by
  apply Complex.ofReal_injective
  rw [CoherencyMatrix.coe_trace, CoherencyMatrix.coe_trace,
    CoherencyMatrix.map_toMatrix, hM.trace_congruence]

/-- A unitary Jones-induced Mueller action preserves raw Stokes intensity. -/
lemma IsUnitary.mueller_intensity {M : JonesMatrix} (hM : M.IsUnitary)
    (S : StokesVector) :
    (M.mueller.act S).intensity = S.intensity := by
  apply Complex.ofReal_injective
  rw [StokesVector.coe_intensity_eq_trace_toSelfAdjoint,
    StokesVector.coe_intensity_eq_trace_toSelfAdjoint,
    M.mueller_act_toSelfAdjoint, hM.trace_congruence]

/-- A unitary Jones-induced Mueller action fixes every unpolarized Stokes vector. -/
lemma IsUnitary.mueller_unpolarized {M : JonesMatrix} (hM : M.IsUnitary) (s : ℝ) :
    M.mueller.act (StokesVector.ofIntensityPolarization s 0) =
      StokesVector.ofIntensityPolarization s 0 := by
  apply selfAdjointStokesEquiv.symm.injective
  apply Subtype.ext
  change (M.mueller.act (StokesVector.ofIntensityPolarization s 0)).toSelfAdjoint.val = _
  have hzero := StokesVector.toSelfAdjoint_ofIntensityPolarization_zero s
  rw [M.mueller_act_toSelfAdjoint, hzero]
  have hstar : M.entries * M.entriesᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hM
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hstar]
  exact hzero.symm

/-- A unitary Jones-induced Mueller action preserves the determinant of raw Stokes
reconstruction. -/
lemma IsUnitary.mueller_det {M : JonesMatrix} (hM : M.IsUnitary)
    (S : StokesVector) :
    Matrix.det (M.mueller.act S).toSelfAdjoint.val = Matrix.det S.toSelfAdjoint.val := by
  rw [M.mueller_act_toSelfAdjoint, hM.det_congruence]

/-- A unitary Jones-induced Mueller action preserves the norm of the polarization coordinates. -/
lemma IsUnitary.mueller_polarization_norm {M : JonesMatrix}
    (hM : M.IsUnitary) (S : StokesVector) :
    ‖(M.mueller.act S).polarization‖ = ‖S.polarization‖ := by
  have hdet := hM.mueller_det S
  rw [StokesVector.det_toSelfAdjoint, StokesVector.det_toSelfAdjoint,
    hM.mueller_intensity S] at hdet
  have hreal :
      (S.intensity ^ 2 - ‖(M.mueller.act S).polarization‖ ^ 2) / 4 =
        (S.intensity ^ 2 - ‖S.polarization‖ ^ 2) / 4 :=
    Complex.ofReal_injective hdet
  nlinarith [norm_nonneg (M.mueller.act S).polarization, norm_nonneg S.polarization]

/-- The unitary Jones action on unit-intensity physical Stokes data. -/
noncomputable def IsUnitary.actUnitIntensityStokes {M : JonesMatrix} (hM : M.IsUnitary)
    (S : UnitIntensityStokesVector) : UnitIntensityStokesVector :=
  ⟨M.actPhysicalStokes S.val, by
    simpa only [actPhysicalStokes_val, hM.mueller_intensity] using S.property⟩

/-- The raw Stokes vector underlying unit-intensity Jones action. -/
@[simp]
lemma IsUnitary.actUnitIntensityStokes_val {M : JonesMatrix} (hM : M.IsUnitary)
    (S : UnitIntensityStokesVector) :
    (hM.actUnitIntensityStokes S).val.val = M.mueller.act S.val.val := rfl

/-- Unitary Jones action preserves Poincare-sphere membership in both directions. -/
lemma IsUnitary.poincare_mem_sphere_iff {M : JonesMatrix} (hM : M.IsUnitary)
    (S : UnitIntensityStokesVector) :
    (unitIntensityStokesPoincareEquiv (hM.actUnitIntensityStokes S)).val ∈ PoincareSphere ↔
      (unitIntensityStokesPoincareEquiv S).val ∈ PoincareSphere := by
  rw [unitIntensityStokesPoincareEquiv_apply_val,
    unitIntensityStokesPoincareEquiv_apply_val, hM.actUnitIntensityStokes_val]
  simp only [Metric.mem_sphere, dist_zero_right, hM.mueller_polarization_norm]

/-- The map of the Poincare sphere induced by a unitary Jones matrix. -/
noncomputable def IsUnitary.poincareSphereMap {M : JonesMatrix} (hM : M.IsUnitary) :
    PoincareSphere → PoincareSphere := fun p =>
  ⟨(M.mueller.act (StokesVector.ofIntensityPolarization 1 p.val)).polarization, by
    rw [Metric.mem_sphere, dist_zero_right, hM.mueller_polarization_norm,
      StokesVector.polarization_ofIntensityPolarization]
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property⟩

/-- The value of the unitary Jones-induced Poincare-sphere map. -/
@[simp]
lemma IsUnitary.poincareSphereMap_val {M : JonesMatrix} (hM : M.IsUnitary)
    (p : PoincareSphere) :
    (hM.poincareSphereMap p).val =
      (M.mueller.act (StokesVector.ofIntensityPolarization 1 p.val)).polarization := rfl

end JonesMatrix

end

end Optics
