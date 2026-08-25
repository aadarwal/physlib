/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Physlib.Optics.Rays.Basic

/-!
# Ray-transfer matrices, components, and ordered optical systems

## i. Overview

Every ray-transfer matrix in this file is *derived* from the relational component law of
`Physlib.Optics.Rays.Basic`, never used to define one. The pattern is the same for each
component: `transferMatrix_rayBehavior` proves that the matrix action satisfies the component's
relational law, and the uniqueness result already proved for that law upgrades this to an
equivalence. A closed form obtained by multiplying matrices is therefore a theorem about the
component semantics, not a restatement of a definition.

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
axis is re-referenced to the new propagation direction after a mirror. Section D records the map
to the unfolded convention, in which a plane mirror sends `θ` to `-θ`: the unfolded matrix is the
folded one post-multiplied by `Optics.angleReversal`. Both are available so that a comparison
against a source using the other convention is an explicit theorem rather than a silent sign.

The determinant law. `ParaxialInterface.det_transferMatrix` gives `det = n₀ / n₁` for five of the
six constructors, and `ParaxialSystem.det_matrix` gives the telescoped form for a whole system.
The phase-conjugating mirror is the exception, with determinant `-1`: phase conjugation reverses
the wavefront and is not an ordinary ray-transfer operation. It is excluded by hypothesis and its
value stated separately, rather than weakening the law to a statement about `|det|`.

Explicit non-claims. These matrices carry no field, power, or polarization, and there is no
diffraction, aperture, or finite-beam content: a system that is geometrically well behaved here
may still be unusable physically. The thin- and thick-lens results are exact consequences of the
paraxial surface laws, so they inherit exactly the small-angle validity those laws carry, and
nothing more.

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
- D. The unfolded reflection convention
- E. Ordered optical systems
- F. The system ray-transfer theorem
- G. Composed systems
- H. Thin and thick lenses

## iv. References

- B. E. A. Saleh and M. C. Teich, *Fundamentals of Photonics*, 3rd edition, chapter 1, table
  1.4-1 for the component matrices and section 1.4 for the lensmaker's equation.
- M. U. Siddique, *Formal Analysis of Geometrical Optics using Theorem Proving*, PhD thesis,
  Concordia University, 2015, chapter 3, theorems 3.4 to 3.7, for the corresponding results in
  the unfolded reflection convention.

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

This is the component-level ray-transfer theorem: the matrix is not the definition of the
component, it is the extracted content of the component's behaviour.
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

## D. The unfolded reflection convention

-/

/-- The angle-reversal matrix relating the folded and unfolded reflection conventions. -/
def angleReversal : RayTransferMatrix := !![1, 0; 0, -1]

/-- The unfolded-convention matrix of an interface: the folded matrix followed by the reversal
that re-references the axis to the incoming propagation direction.

`Physlib.Optics.Rays.Basic` fixes the folded convention, in which a plane mirror is the identity.
Sources that keep the axis fixed across a mirror, and so send `θ` to `-θ`, use this matrix
instead. Recording the map explicitly means a comparison against such a source is a theorem
rather than an undocumented sign. Matching a particular source table entry by entry additionally
requires that source's radius-sign convention, which is a human-audit item and is not asserted
here.
-/
def ParaxialInterface.unfoldedTransferMatrix (n₀ n₁ : ℝ) (i : ParaxialInterface) :
    RayTransferMatrix :=
  angleReversal * i.transferMatrix n₀ n₁

/-- In the unfolded convention a plane mirror reverses the ray angle. -/
lemma ParaxialInterface.unfoldedTransferMatrix_planeMirror (n₀ n₁ : ℝ) :
    ParaxialInterface.planeMirror.unfoldedTransferMatrix n₀ n₁ = !![1, 0; 0, -1] := by
  simp [unfoldedTransferMatrix, transferMatrix, angleReversal]

/-- In the unfolded convention a spherical mirror of radius `radius` has the matrix
`!![1, 0; 2 / radius, -1]`. -/
lemma ParaxialInterface.unfoldedTransferMatrix_sphericalMirror (n₀ n₁ radius : ℝ) :
    (ParaxialInterface.sphericalMirror radius).unfoldedTransferMatrix n₀ n₁ =
      !![1, 0; 2 / radius, -1] := by
  rw [unfoldedTransferMatrix, transferMatrix, angleReversal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The unfolded convention is exactly the folded one with the outgoing angle reversed. -/
lemma rayTransfer_unfoldedTransferMatrix (n₀ n₁ : ℝ) (i : ParaxialInterface) (r : ParaxialRay) :
    rayTransfer (i.unfoldedTransferMatrix n₀ n₁) r =
      ⟨(rayTransfer (i.transferMatrix n₀ n₁) r).height,
        -(rayTransfer (i.transferMatrix n₀ n₁) r).angle⟩ := by
  rw [ParaxialInterface.unfoldedTransferMatrix, rayTransfer_mul]
  ext <;> simp [angleReversal]

/-- Reversing the angle multiplies the determinant by `-1`, so an unfolded reflecting component
has determinant `-(n₀ / n₁)` wherever the folded one has `n₀ / n₁`. -/
lemma ParaxialInterface.det_unfoldedTransferMatrix (n₀ n₁ : ℝ) (i : ParaxialInterface) :
    (i.unfoldedTransferMatrix n₀ n₁).det = -(i.transferMatrix n₀ n₁).det := by
  rw [unfoldedTransferMatrix, Matrix.det_mul, angleReversal, Matrix.det_fin_two_of]
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

/-- A composed system is valid when each of its subsystems is. -/
def ComposedIsValid (subsystems : List (List ParaxialComponent × ParaxialGap)) : Prop :=
  ∀ s ∈ subsystems, IsValid s.1 s.2

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
      have hHead : IsValid s.1 s.2 := hValid s List.mem_cons_self
      have hRest : ComposedIsValid rest := fun t ht => hValid t (List.mem_cons_of_mem s ht)
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

/-- The ray-transfer matrix of a thin lens of focal length `f`. -/
def thinLensMatrix (f : ℝ) : RayTransferMatrix := !![1, 0; -1 / f, 1]

/-- A thin lens has unit determinant. -/
@[simp]
lemma det_thinLensMatrix (f : ℝ) : (thinLensMatrix f).det = 1 := by
  simp [thinLensMatrix, Matrix.det_fin_two_of]

/-- **The thick-lens matrix.** Composing two spherical refracting surfaces of radii `R₁` and `R₂`
separated by a gap of length `t` in a medium of index `nL`, both immersed in a medium of index
`n`, gives the stated matrix.

Nothing here is stipulated: the matrix is the system matrix of a two-component system built from
the paraxial surface laws of `Physlib.Optics.Rays.Basic`, so its lower-left entry is a derived
lensmaker's equation with thickness, not a definition.
-/
theorem thickLens_matrix (n nL t R₁ R₂ : ℝ) (hn : n ≠ 0) (hnL : nL ≠ 0) (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix
        [⟨⟨n, 0⟩, ParaxialInterface.sphericalRefracting R₁⟩,
          ⟨⟨nL, t⟩, ParaxialInterface.sphericalRefracting R₂⟩] ⟨n, 0⟩ =
      !![1 - t * (nL - n) / (nL * R₁), t * n / nL;
        -((nL / n - 1) * (1 / R₁ - 1 / R₂ + t * (nL - n) / (nL * R₁ * R₂))),
        1 + t * (nL - n) / (nL * R₂)] := by
  simp only [ParaxialSystem.matrix, ParaxialSystem.headIndex, ParaxialInterface.transferMatrix,
    ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- **The lensmaker's equation.** A thin lens is the zero-thickness case of `thickLens_matrix`,
and its lower-left entry is `-(nL / n - 1) (1 / R₁ - 1 / R₂)`. -/
theorem thinLens_matrix (n nL R₁ R₂ : ℝ) (hn : n ≠ 0) (hnL : nL ≠ 0) (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix
        [⟨⟨n, 0⟩, ParaxialInterface.sphericalRefracting R₁⟩,
          ⟨⟨nL, 0⟩, ParaxialInterface.sphericalRefracting R₂⟩] ⟨n, 0⟩ =
      !![1, 0; -((nL / n - 1) * (1 / R₁ - 1 / R₂)), 1] := by
  rw [thickLens_matrix n nL 0 R₁ R₂ hn hnL hR₁ hR₂]
  norm_num

/-- The thin lens obtained from two spherical surfaces is the thin-lens matrix of the focal
length given by the lensmaker's equation. -/
theorem thinLens_matrix_eq_thinLensMatrix (n nL R₁ R₂ f : ℝ) (hn : n ≠ 0) (hnL : nL ≠ 0)
    (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (hf : 1 / f = (nL / n - 1) * (1 / R₁ - 1 / R₂)) :
    ParaxialSystem.matrix
        [⟨⟨n, 0⟩, ParaxialInterface.sphericalRefracting R₁⟩,
          ⟨⟨nL, 0⟩, ParaxialInterface.sphericalRefracting R₂⟩] ⟨n, 0⟩ =
      thinLensMatrix f := by
  rw [thinLens_matrix n nL R₁ R₂ hn hnL hR₁ hR₂, thinLensMatrix, ← hf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

end

end Optics
