/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Basic

/-!
# Ray-transfer matrices, components, and ordered optical systems

## i. Overview

The named gap, refracting, and reflecting component matrices in this file are verified against
the relational component laws of `Physlib.Optics.Rays.Basic`. The pattern is that
`transferMatrix_rayBehavior` proves that the matrix action satisfies the component law, and
uniqueness upgrades this to an equivalence. The `prescribed` constructor is the deliberate
exception: its relation is specified by its matrix entries. The standalone `thinLensMatrix` is
also an algebraic target, then connected to a two-surface system by the lensmaker theorem.

An ordered optical system is a finite list of components in the order a ray meets them, together
with the gap the ray leaves through. A component is one homogeneous gap followed by one
interface. The two pieces of a system are carried as separate arguments throughout, so that every
system-level definition is a structural recursion on the component list and every system-level
theorem is an induction on it.

The system matrix folds the component matrices in the order that composes correctly on column
vectors: later components multiply on the left. `ParaxialSystem.rayBehavior_iff_matrix` is the
ray-transfer theorem for an arbitrary finite valid system, and
`ParaxialSystem.composedRayBehavior_iff_composedMatrix` is its analogue for a system built from
subsystems.

Reflection conventions. `Physlib.Optics.Rays.Basic` fixes the folded convention, in which the
axis is re-referenced to the new propagation direction after a mirror. Section D records a generic
output-angle coordinate reversal: its matrix is `Optics.angleReversal` multiplied on the left of
the component matrix. Siddique's table 3.1 already uses the folded mirror matrices. Identifying a
different source convention additionally requires an explicit axis and signed-radius map.

The determinant law. `ParaxialInterface.det_transferMatrix` gives `det = n₀ / n₁` for five of the
six constructors, and `ParaxialSystem.det_matrix` gives the telescoped form for a whole system.
The phase-conjugating mirror is the exception, with determinant `-1`: phase conjugation reverses
the wavefront and is not an ordinary ray-transfer operation. It is excluded by hypothesis and its
value stated separately, rather than weakening the law to a statement about `|det|`.

Explicit non-claims. These matrices carry no field, power, or polarization, and there is no
diffraction, aperture, or finite-beam content: a system that is geometrically well behaved here
may still be unusable physically. The thin- and thick-lens matrix identities are algebraic
consequences of the paraxial surface formulas. Their behavior-level corollaries separately require
positive indices, nonnegative thickness, and nonzero surface radii.

## ii. Key results

- `Optics.ParaxialInterface.rayBehavior_iff_transferMatrix`: the interface matrix is the unique
  realisation of the relational interface law.
- `Optics.ParaxialInterface.det_transferMatrix`: the index-ratio determinant law, with the
  phase-conjugate exception stated separately.
- `Optics.ParaxialSystem.rayBehavior_iff_matrix`: an arbitrary finite valid system transports a
  ray by the folded product of its component matrices.
- `Optics.ParaxialSystem.det_matrix`: the system determinant telescopes to
  `headIndex / exitGap.index`.
- `Optics.ParaxialSystem.composedRayBehavior_iff_composedMatrix`: the same for a system composed
  of subsystems.
- `Optics.thinLens_matrix`: the lensmaker's equation, obtained by composing two spherical
  refracting surfaces.
- `Optics.thickLens_matrix`: the same with a finite lens thickness.

## iii. Table of contents

- A. Ray-transfer matrices and their action
- B. Component matrices derived from component laws
- C. The determinant law
- D. Output-angle reversal
- E. Ordered optical systems
- F. The system ray-transfer theorem
- G. Composed systems
- H. Thin and thick lenses

## iv. References

- B. E. A. Saleh and M. C. Teich, *Fundamentals of Photonics*, 3rd edition, chapter 1, table
  1.4-1 for the component matrices and section 1.4 for the lensmaker's equation.
- M. U. Siddique, *Formal Analysis of Geometrical Optics using Theorem Proving*, PhD thesis,
  Concordia University, 2015, chapter 3, for the component and system results. Table 3.1 uses the
  folded mirror matrices; mapping its signed-radius vocabulary to Physlib remains a human check.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Ray-transfer matrices and their action

-/

/-- A ray-transfer, or `ABCD`, matrix acting on paraxial ray coordinates in the
`![height, angle]` column ordering fixed by `Optics.ParaxialRay.toVec`. -/
abbrev RayTransferMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- The action of a ray-transfer matrix on a paraxial ray coordinate, `(y₁, θ₁)ᵀ = M (y₀, θ₀)ᵀ`. -/
def rayTransfer (M : RayTransferMatrix) (r : ParaxialRay) : ParaxialRay :=
  ParaxialRay.ofVec (M.mulVec r.toVec)

@[simp]
lemma rayTransfer_height (M : RayTransferMatrix) (r : ParaxialRay) :
    (rayTransfer M r).height = M 0 0 * r.height + M 0 1 * r.angle := by
  simp [rayTransfer, Matrix.mulVec]

@[simp]
lemma rayTransfer_angle (M : RayTransferMatrix) (r : ParaxialRay) :
    (rayTransfer M r).angle = M 1 0 * r.height + M 1 1 * r.angle := by
  simp [rayTransfer, Matrix.mulVec]

/-- The action of an explicit `2 × 2` ray-transfer matrix, in the fixed coordinate ordering. -/
@[simp]
lemma rayTransfer_of_fin_two (a b c d : ℝ) (r : ParaxialRay) :
    rayTransfer !![a, b; c, d] r = ⟨a * r.height + b * r.angle, c * r.height + d * r.angle⟩ := by
  ext <;> simp

/-- Matrix multiplication is composition of ray transfers, with the later component on the
left. -/
lemma rayTransfer_mul (M N : RayTransferMatrix) (r : ParaxialRay) :
    rayTransfer (M * N) r = rayTransfer M (rayTransfer N r) := by
  simp only [rayTransfer, ParaxialRay.toVec_ofVec, Matrix.mulVec_mulVec]

@[simp]
lemma rayTransfer_one (r : ParaxialRay) : rayTransfer (1 : RayTransferMatrix) r = r := by
  simp only [rayTransfer, Matrix.one_mulVec, ParaxialRay.ofVec_toVec]

/-!

## B. Component matrices derived from component laws

-/

/-- The ray-transfer matrix of a homogeneous gap. -/
def ParaxialGap.transferMatrix (g : ParaxialGap) : RayTransferMatrix := !![1, g.length; 0, 1]

/-- The gap matrix realises the relational free-space law. -/
lemma ParaxialGap.transferMatrix_rayBehavior (g : ParaxialGap) (r₀ : ParaxialRay) :
    g.RayBehavior r₀ (rayTransfer g.transferMatrix r₀) := by
  refine ⟨?_, ?_⟩ <;> simp [ParaxialGap.transferMatrix]

/-- The gap matrix is the unique realisation of the relational free-space law. -/
lemma ParaxialGap.rayBehavior_iff_transferMatrix (g : ParaxialGap) (r₀ r₁ : ParaxialRay) :
    g.RayBehavior r₀ r₁ ↔ r₁ = rayTransfer g.transferMatrix r₀ := by
  constructor
  · intro hb
    exact g.rayBehavior_unique r₀ r₁ _ hb (g.transferMatrix_rayBehavior r₀)
  · rintro rfl
    exact g.transferMatrix_rayBehavior r₀

/-- The ray-transfer matrix of an interface carrying a ray from index `n₀` into index `n₁`.

The entries are those of Saleh and Teich table 1.4-1, in the folded reflection convention, so a
plane mirror is the identity and a mirror does not change the index.
-/
def ParaxialInterface.transferMatrix (n₀ n₁ : ℝ) : ParaxialInterface → RayTransferMatrix
  | planeRefracting => !![1, 0; 0, n₀ / n₁]
  | sphericalRefracting radius => !![1, 0; -(n₁ - n₀) / (n₁ * radius), n₀ / n₁]
  | planeMirror => 1
  | sphericalMirror radius => !![1, 0; -2 / radius, 1]
  | phaseConjugate => !![1, 0; 0, -1]
  | prescribed a b c d => !![a, b; c, d]

/-- The interface matrix realises the relational interface law.

This is the direction that has to be proved by computation; the converse is then uniqueness.
-/
lemma ParaxialInterface.transferMatrix_rayBehavior {n₀ n₁ : ℝ} {i : ParaxialInterface}
    (h : i.IsValid n₀ n₁) (r₀ : ParaxialRay) :
    i.RayBehavior n₀ n₁ r₀ (rayTransfer (i.transferMatrix n₀ n₁) r₀) := by
  have hn₁ : n₁ ≠ 0 := (ParaxialInterface.index_pos_right h).ne'
  cases i with
  | planeRefracting =>
      refine ⟨by simp [transferMatrix], ?_⟩
      simp only [transferMatrix, rayTransfer_of_fin_two]
      field_simp
      ring
  | sphericalRefracting radius =>
      have hr : radius ≠ 0 := h.2.2
      refine ⟨by simp [transferMatrix], ?_⟩
      simp only [transferMatrix, rayTransfer_of_fin_two]
      field_simp
      ring
  | planeMirror => exact ⟨by simp [transferMatrix], by simp [transferMatrix]⟩
  | sphericalMirror radius =>
      refine ⟨by simp [transferMatrix], ?_⟩
      simp only [transferMatrix, rayTransfer_of_fin_two]
      ring
  | phaseConjugate =>
      refine ⟨by simp [transferMatrix], ?_⟩
      simp [transferMatrix]
  | prescribed a b c d =>
      exact ⟨by simp [transferMatrix], by simp [transferMatrix]⟩

/-- The interface matrix is the unique realisation of the relational interface law.

For the named geometric constructors this extracts the matrix content of the independently stated
component behavior. For `prescribed`, the relation intentionally records the supplied entries.
-/
lemma ParaxialInterface.rayBehavior_iff_transferMatrix {n₀ n₁ : ℝ} {i : ParaxialInterface}
    (h : i.IsValid n₀ n₁) (r₀ r₁ : ParaxialRay) :
    i.RayBehavior n₀ n₁ r₀ r₁ ↔ r₁ = rayTransfer (i.transferMatrix n₀ n₁) r₀ := by
  constructor
  · intro hb
    exact ParaxialInterface.rayBehavior_unique h r₀ r₁ _ hb (transferMatrix_rayBehavior h r₀)
  · rintro rfl
    exact transferMatrix_rayBehavior h r₀

/-!

## C. The determinant law

-/

/-- A homogeneous gap has unit determinant: it does not change the refractive index. -/
@[simp]
lemma ParaxialGap.det_transferMatrix (g : ParaxialGap) : g.transferMatrix.det = 1 := by
  simp [ParaxialGap.transferMatrix, Matrix.det_fin_two_of]

/-- **The index-ratio determinant law.** A valid interface other than a phase-conjugating mirror
has determinant `n₀ / n₁`.

The phase-conjugating mirror is excluded because it genuinely fails the law; see
`Optics.ParaxialInterface.det_transferMatrix_phaseConjugate`.
-/
lemma ParaxialInterface.det_transferMatrix {n₀ n₁ : ℝ} {i : ParaxialInterface}
    (h : i.IsValid n₀ n₁) (hpc : i ≠ ParaxialInterface.phaseConjugate) :
    (i.transferMatrix n₀ n₁).det = n₀ / n₁ := by
  cases i with
  | planeRefracting => simp [transferMatrix, Matrix.det_fin_two_of]
  | sphericalRefracting radius => simp [transferMatrix, Matrix.det_fin_two_of]
  | planeMirror =>
      have hn : n₁ = n₀ := h.2
      simp [transferMatrix, hn, div_self h.1.ne']
  | sphericalMirror radius =>
      have hn : n₁ = n₀ := h.2.1
      simp [transferMatrix, Matrix.det_fin_two_of, hn, div_self h.1.ne']
  | phaseConjugate => exact absurd rfl hpc
  | prescribed a b c d =>
      rw [transferMatrix, Matrix.det_fin_two_of]
      exact h.2.2

/-- A phase-conjugating mirror has determinant `-1`, not the index ratio: it reverses the
wavefront, and is the one component here that is not an ordinary ray transfer. -/
@[simp]
lemma ParaxialInterface.det_transferMatrix_phaseConjugate (n₀ n₁ : ℝ) :
    (ParaxialInterface.phaseConjugate.transferMatrix n₀ n₁).det = -1 := by
  simp [transferMatrix, Matrix.det_fin_two_of]

/-!

## D. Output-angle reversal

-/

/-- The coordinate transform that preserves ray height and reverses the output angle. -/
def angleReversal : RayTransferMatrix := !![1, 0; 0, -1]

/-- Reversing the output-angle coordinate twice is the identity.

This is the guard against double-counting a reflection's direction reversal. A treatment that
keeps the reversal explicit as a coordinate operation, as this one does, must *not* also negate
the radii on the reversed leg: doing both applies the same physical reversal twice. See the
two-mirror round-trip regression in `Physlib.Optics.Rays.TransferRegression`.
-/
@[simp]
lemma angleReversal_mul_self : angleReversal * angleReversal = 1 := by
  rw [angleReversal, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

/-- The transfer matrix obtained by reversing the output-angle coordinate.

`Physlib.Optics.Rays.Basic` fixes the folded convention, in which a plane mirror is the identity.
Left multiplication by `angleReversal` changes only the reported outgoing angle. For a mirror it
can express a coordinate convention in which a plane mirror sends `θ` to `-θ`; applying it to an
arbitrary transmitting interface is only a coordinate operation, not a new physical component.
No particular source convention is claimed without a separate axis and signed-radius audit.
-/
def ParaxialInterface.outputAngleReversedTransferMatrix (n₀ n₁ : ℝ)
    (i : ParaxialInterface) :
    RayTransferMatrix :=
  angleReversal * i.transferMatrix n₀ n₁

/-- Reversing the output angle of the folded plane-mirror matrix gives `diag(1, -1)`. -/
lemma ParaxialInterface.outputAngleReversedTransferMatrix_planeMirror (n₀ n₁ : ℝ) :
    ParaxialInterface.planeMirror.outputAngleReversedTransferMatrix n₀ n₁ =
      !![1, 0; 0, -1] := by
  simp [outputAngleReversedTransferMatrix, transferMatrix, angleReversal]

/-- Reversing the output angle of the folded spherical-mirror matrix changes both entries in its
second row, giving `!![1, 0; 2 / radius, -1]`. -/
lemma ParaxialInterface.outputAngleReversedTransferMatrix_sphericalMirror
    (n₀ n₁ radius : ℝ) :
    (ParaxialInterface.sphericalMirror radius).outputAngleReversedTransferMatrix n₀ n₁ =
      !![1, 0; 2 / radius, -1] := by
  rw [outputAngleReversedTransferMatrix, transferMatrix, angleReversal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The transformed matrix is exactly the original transfer followed by output-angle reversal. -/
lemma rayTransfer_outputAngleReversedTransferMatrix
    (n₀ n₁ : ℝ) (i : ParaxialInterface) (r : ParaxialRay) :
    rayTransfer (i.outputAngleReversedTransferMatrix n₀ n₁) r =
      ⟨(rayTransfer (i.transferMatrix n₀ n₁) r).height,
        -(rayTransfer (i.transferMatrix n₀ n₁) r).angle⟩ := by
  rw [ParaxialInterface.outputAngleReversedTransferMatrix, rayTransfer_mul]
  ext <;> simp [angleReversal]

/-- Output-angle reversal multiplies the transfer-matrix determinant by `-1`. -/
lemma ParaxialInterface.det_outputAngleReversedTransferMatrix
    (n₀ n₁ : ℝ) (i : ParaxialInterface) :
    (i.outputAngleReversedTransferMatrix n₀ n₁).det =
      -(i.transferMatrix n₀ n₁).det := by
  rw [outputAngleReversedTransferMatrix, Matrix.det_mul, angleReversal,
    Matrix.det_fin_two_of]
  ring

/-!

## E. Ordered optical systems

-/

/-- A component of an optical system: a homogeneous gap, followed by the interface that ends it.

A ray meets the gap first and the interface second, so a system's leading gap is the distance
from the reference plane to its first surface.
-/
structure ParaxialComponent where
  /-- The homogeneous gap the ray traverses before reaching the interface. -/
  gap : ParaxialGap
  /-- The interface that terminates the gap. -/
  interface : ParaxialInterface

namespace ParaxialSystem

/-- The refractive index a ray has on entering a system given by the component list `cs` followed
by the gap `exitGap`. -/
def headIndex : List ParaxialComponent → ParaxialGap → ℝ
  | [], exitGap => exitGap.index
  | c :: _, _ => c.gap.index

/-- Validity of an ordered system: every gap is valid, and every interface is valid between the
index of the gap that precedes it and the index the ray enters the rest of the system with. -/
def IsValid : List ParaxialComponent → ParaxialGap → Prop
  | [], exitGap => exitGap.IsValid
  | c :: cs, exitGap =>
      c.gap.IsValid ∧ c.interface.IsValid c.gap.index (headIndex cs exitGap) ∧ IsValid cs exitGap

/-- The system ray-transfer matrix, folded so that later components multiply on the left, which
is the order in which they act on a column vector. -/
def matrix : List ParaxialComponent → ParaxialGap → RayTransferMatrix
  | [], exitGap => exitGap.transferMatrix
  | c :: cs, exitGap =>
      matrix cs exitGap * c.interface.transferMatrix c.gap.index (headIndex cs exitGap) *
        c.gap.transferMatrix

/-- The behaviour of a ray in an ordered system, stated relationally and componentwise: the ray
crosses each gap and each interface in turn, with the intermediate coordinates existentially
quantified rather than computed. -/
def RayBehavior : List ParaxialComponent → ParaxialGap → ParaxialRay → ParaxialRay → Prop
  | [], exitGap, r₀, r₁ => exitGap.RayBehavior r₀ r₁
  | c :: cs, exitGap, r₀, r₁ =>
      ∃ rGap rInterface,
        c.gap.RayBehavior r₀ rGap ∧
          c.interface.RayBehavior c.gap.index (headIndex cs exitGap) rGap rInterface ∧
          RayBehavior cs exitGap rInterface r₁

/-- A valid system is entered at a positive refractive index. -/
lemma headIndex_pos : ∀ (cs : List ParaxialComponent) (exitGap : ParaxialGap),
    IsValid cs exitGap → 0 < headIndex cs exitGap
  | [], _, h => h.index_pos
  | _ :: _, _, h => h.1.index_pos

/-!

## F. The system ray-transfer theorem

-/

/-- **Ray-transfer matrix for an optical system.** An arbitrary finite valid system transports a
ray coordinate by the folded product of its component matrices, and by nothing else.

This is the theorem that makes every later closed form a consequence of the component semantics
rather than of a stipulated matrix. Regression `R-01` of `goal.md` §I.3 is the order-sensitivity
of the fold, exercised in `Physlib.Optics.Rays.TransferRegression`.
-/
theorem rayBehavior_iff_matrix : ∀ (cs : List ParaxialComponent) (exitGap : ParaxialGap),
    IsValid cs exitGap → ∀ r₀ r₁ : ParaxialRay,
      (RayBehavior cs exitGap r₀ r₁ ↔ r₁ = rayTransfer (matrix cs exitGap) r₀) := by
  intro cs
  induction cs with
  | nil =>
      intro exitGap _ r₀ r₁
      exact exitGap.rayBehavior_iff_transferMatrix r₀ r₁
  | cons c cs ih =>
      intro exitGap hValid r₀ r₁
      obtain ⟨_, hInterface, hRest⟩ := hValid
      constructor
      · rintro ⟨rGap, rInterface, hGapBehavior, hInterfaceBehavior, hRestBehavior⟩
        rw [c.gap.rayBehavior_iff_transferMatrix] at hGapBehavior
        rw [ParaxialInterface.rayBehavior_iff_transferMatrix hInterface] at hInterfaceBehavior
        rw [ih exitGap hRest] at hRestBehavior
        subst hGapBehavior
        subst hInterfaceBehavior
        rw [hRestBehavior, matrix, rayTransfer_mul, rayTransfer_mul]
      · rintro rfl
        refine ⟨rayTransfer c.gap.transferMatrix r₀,
          rayTransfer (c.interface.transferMatrix c.gap.index (headIndex cs exitGap))
            (rayTransfer c.gap.transferMatrix r₀), c.gap.transferMatrix_rayBehavior r₀,
          ParaxialInterface.transferMatrix_rayBehavior hInterface _, ?_⟩
        rw [ih exitGap hRest, matrix, rayTransfer_mul, rayTransfer_mul]

/-- **The system determinant law.** The determinant of a valid system containing no
phase-conjugating mirror telescopes to the ratio of the entry index to the exit index. -/
lemma det_matrix : ∀ (cs : List ParaxialComponent) (exitGap : ParaxialGap),
    IsValid cs exitGap → (∀ c ∈ cs, c.interface ≠ ParaxialInterface.phaseConjugate) →
      (matrix cs exitGap).det = headIndex cs exitGap / exitGap.index := by
  intro cs
  induction cs with
  | nil =>
      intro exitGap hValid _
      rw [matrix, ParaxialGap.det_transferMatrix, headIndex, div_self hValid.index_pos.ne']
  | cons c cs ih =>
      intro exitGap hValid hpc
      obtain ⟨_, hInterface, hRest⟩ := hValid
      have hHead : headIndex cs exitGap ≠ 0 := (headIndex_pos cs exitGap hRest).ne'
      rw [matrix, Matrix.det_mul, Matrix.det_mul, ParaxialGap.det_transferMatrix,
        ih exitGap hRest (fun d hd => hpc d (List.mem_cons_of_mem c hd)),
        ParaxialInterface.det_transferMatrix hInterface (hpc c List.mem_cons_self), headIndex]
      field_simp

/-!

## G. Composed systems

-/

/-- The matrix of a composed system: a finite list of subsystems, each a component list with its
own exit gap, in the order the ray meets them. -/
def composedMatrix : List (List ParaxialComponent × ParaxialGap) → RayTransferMatrix
  | [] => 1
  | s :: rest => composedMatrix rest * matrix s.1 s.2

/-- Adjacent subsystems are index-compatible when each exit index is the next entry index. -/
def ComposedIndicesCompatible
    (subsystems : List (List ParaxialComponent × ParaxialGap)) : Prop :=
  subsystems.IsChain fun first second => first.2.index = headIndex second.1 second.2

/-- A composed system is valid when every subsystem is valid and adjacent subsystem indices
agree at their shared reference plane. -/
def ComposedIsValid (subsystems : List (List ParaxialComponent × ParaxialGap)) : Prop :=
  (∀ s ∈ subsystems, IsValid s.1 s.2) ∧ ComposedIndicesCompatible subsystems

/-- The behaviour of a ray in a composed system: the ray passes through each subsystem in turn,
with the coordinates between subsystems existentially quantified. -/
def ComposedRayBehavior :
    List (List ParaxialComponent × ParaxialGap) → ParaxialRay → ParaxialRay → Prop
  | [], r₀, r₁ => r₁ = r₀
  | s :: rest, r₀, r₁ => ∃ rMid, RayBehavior s.1 s.2 r₀ rMid ∧ ComposedRayBehavior rest rMid r₁

/-- **Ray-transfer matrix for a composed optical system.** A composed system transports a ray by
the folded product of its subsystem matrices. -/
theorem composedRayBehavior_iff_composedMatrix :
    ∀ (subsystems : List (List ParaxialComponent × ParaxialGap)), ComposedIsValid subsystems →
      ∀ r₀ r₁ : ParaxialRay,
        (ComposedRayBehavior subsystems r₀ r₁ ↔
          r₁ = rayTransfer (composedMatrix subsystems) r₀) := by
  intro subsystems
  induction subsystems with
  | nil =>
      intro _ r₀ r₁
      rw [ComposedRayBehavior, composedMatrix, rayTransfer_one]
  | cons s rest ih =>
      intro hValid r₀ r₁
      have hHead : IsValid s.1 s.2 := hValid.1 s List.mem_cons_self
      have hRest : ComposedIsValid rest :=
        ⟨fun t ht => hValid.1 t (List.mem_cons_of_mem s ht), hValid.2.of_cons⟩
      constructor
      · rintro ⟨rMid, hFirst, hRestBehavior⟩
        rw [rayBehavior_iff_matrix s.1 s.2 hHead] at hFirst
        rw [ih hRest] at hRestBehavior
        subst hFirst
        rw [hRestBehavior, composedMatrix, rayTransfer_mul]
      · rintro rfl
        refine ⟨rayTransfer (matrix s.1 s.2) r₀, ?_, ?_⟩
        · rw [rayBehavior_iff_matrix s.1 s.2 hHead]
        · rw [ih hRest, composedMatrix, rayTransfer_mul]

end ParaxialSystem

/-!

## H. Thin and thick lenses

-/

/-- The two-surface paraxial system used to model a thick lens.

The first spherical surface carries the ray from surrounding index `n` into lens index `nL`; the
second, after thickness `t`, carries it back to `n`.
-/
def thickLensSystem (n nL t R₁ R₂ : ℝ) : List ParaxialComponent :=
  [⟨⟨n, 0⟩, ParaxialInterface.sphericalRefracting R₁⟩,
    ⟨⟨nL, t⟩, ParaxialInterface.sphericalRefracting R₂⟩]

/-- The zero-thickness specialization of `Optics.thickLensSystem`. -/
def thinLensSystem (n nL R₁ R₂ : ℝ) : List ParaxialComponent :=
  thickLensSystem n nL 0 R₁ R₂

/-- Positive indices, nonnegative thickness, and nonzero radii make the thick-lens system valid. -/
lemma thickLensSystem_isValid {n nL t R₁ R₂ : ℝ} (hn : 0 < n) (hnL : 0 < nL)
    (ht : 0 ≤ t) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.IsValid (thickLensSystem n nL t R₁ R₂) ⟨n, 0⟩ := by
  refine ⟨⟨hn, by norm_num⟩, ⟨hn, hnL, hR₁⟩, ⟨hnL, ht⟩,
    ⟨hnL, hn, hR₂⟩, hn, by norm_num⟩

/-- Positive indices and nonzero radii make the zero-thickness lens system valid. -/
lemma thinLensSystem_isValid {n nL R₁ R₂ : ℝ} (hn : 0 < n) (hnL : 0 < nL)
    (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.IsValid (thinLensSystem n nL R₁ R₂) ⟨n, 0⟩ := by
  exact thickLensSystem_isValid hn hnL (by norm_num) hR₁ hR₂

/-- The algebraic ray-transfer matrix parameterized by a focal-length value `f`.

Physical focal-length statements must assume `f ≠ 0`. At `f = 0`, Lean's totalized division makes
this matrix the identity; no zero-focal-length optical interpretation is claimed.
-/
def thinLensMatrix (f : ℝ) : RayTransferMatrix := !![1, 0; -1 / f, 1]

/-- A thin lens has unit determinant. -/
@[simp]
lemma det_thinLensMatrix (f : ℝ) : (thinLensMatrix f).det = 1 := by
  simp [thinLensMatrix, Matrix.det_fin_two_of]

/-- **The thick-lens matrix.** Composing two spherical refracting surfaces of radii `R₁` and `R₂`
separated by a gap of length `t` in a medium of index `nL`, both immersed in a medium of index
`n`, gives the stated matrix.

This is an algebraic identity for the matrix of `thickLensSystem`. Under the positivity,
nonnegative-thickness, and nonzero-radius hypotheses of `thickLensSystem_isValid`, the subsequent
behavior theorem connects it to the independently stated surface laws.
-/
theorem thickLens_matrix (n nL t R₁ R₂ : ℝ) (hn : n ≠ 0) (hnL : nL ≠ 0) (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix (thickLensSystem n nL t R₁ R₂) ⟨n, 0⟩ =
      !![1 - t * (nL - n) / (nL * R₁), t * n / nL;
        -((nL / n - 1) * (1 / R₁ - 1 / R₂ + t * (nL - n) / (nL * R₁ * R₂))),
        1 + t * (nL - n) / (nL * R₂)] := by
  simp only [thickLensSystem, ParaxialSystem.matrix, ParaxialSystem.headIndex,
    ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- A physically valid thick-lens system satisfies the closed-form ray-transfer relation. -/
lemma thickLens_rayBehavior_iff_matrix {n nL t R₁ R₂ : ℝ} (hn : 0 < n) (hnL : 0 < nL)
    (ht : 0 ≤ t) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (r₀ r₁ : ParaxialRay) :
    ParaxialSystem.RayBehavior (thickLensSystem n nL t R₁ R₂) ⟨n, 0⟩ r₀ r₁ ↔
      r₁ = rayTransfer
        !![1 - t * (nL - n) / (nL * R₁), t * n / nL;
          -((nL / n - 1) * (1 / R₁ - 1 / R₂ + t * (nL - n) / (nL * R₁ * R₂))),
          1 + t * (nL - n) / (nL * R₂)] r₀ := by
  rw [ParaxialSystem.rayBehavior_iff_matrix _ _
    (thickLensSystem_isValid hn hnL ht hR₁ hR₂),
    thickLens_matrix n nL t R₁ R₂ hn.ne' hnL.ne' hR₁ hR₂]

/-- **The lensmaker's equation.** A thin lens is the zero-thickness case of `thickLens_matrix`,
and its lower-left entry is `-(nL / n - 1) (1 / R₁ - 1 / R₂)`. -/
theorem thinLens_matrix (n nL R₁ R₂ : ℝ) (hn : n ≠ 0) (hnL : nL ≠ 0) (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix (thinLensSystem n nL R₁ R₂) ⟨n, 0⟩ =
      !![1, 0; -((nL / n - 1) * (1 / R₁ - 1 / R₂)), 1] := by
  rw [thinLensSystem]
  rw [thickLens_matrix n nL 0 R₁ R₂ hn hnL hR₁ hR₂]
  norm_num

/-- A physically valid thin-lens system satisfies the lensmaker ray-transfer relation. -/
lemma thinLens_rayBehavior_iff_matrix {n nL R₁ R₂ : ℝ} (hn : 0 < n) (hnL : 0 < nL)
    (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (r₀ r₁ : ParaxialRay) :
    ParaxialSystem.RayBehavior (thinLensSystem n nL R₁ R₂) ⟨n, 0⟩ r₀ r₁ ↔
      r₁ = rayTransfer !![1, 0; -((nL / n - 1) * (1 / R₁ - 1 / R₂)), 1] r₀ := by
  rw [ParaxialSystem.rayBehavior_iff_matrix _ _
    (thinLensSystem_isValid hn hnL hR₁ hR₂),
    thinLens_matrix n nL R₁ R₂ hn.ne' hnL.ne' hR₁ hR₂]

/-- The thin lens obtained from two spherical surfaces is the thin-lens matrix of the focal
length given by the lensmaker's equation. -/
theorem thinLens_matrix_eq_thinLensMatrix (n nL R₁ R₂ f : ℝ) (hn : n ≠ 0) (hnL : nL ≠ 0)
    (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (hf : 1 / f = (nL / n - 1) * (1 / R₁ - 1 / R₂)) :
    ParaxialSystem.matrix (thinLensSystem n nL R₁ R₂) ⟨n, 0⟩ =
      thinLensMatrix f := by
  rw [thinLens_matrix n nL R₁ R₂ hn hnL hR₁ hR₂, thinLensMatrix, ← hf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

end

end Optics
