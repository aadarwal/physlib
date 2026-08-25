/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Transfer

/-!
# Imaging and cardinal points

## i. Overview

Every cardinal point here follows the pattern *specification, definition, theorem*: a predicate
says what the point must do to rays, a formula in the system matrix entries is given, and a
theorem proves the formula meets the specification. Uniqueness is proved alongside, so the formula
is the only thing that meets it. No cardinal-point formula is a definition that is then
"verified" against itself.

Reference planes are moved by `Optics.shiftedMatrix zObject zImage M`, which prepends a
translation of length `zObject` and appends one of length `zImage`. A positive `zObject` places
the object plane *upstream* of the system entrance and a positive `zImage` places the image plane
*downstream* of the system exit. That single convention fixes the sign of every distance below;
it is not the only convention in use, and comparisons with a source must map it explicitly.

Translations are taken by `Optics.translationMatrix`, which is a gap matrix with the refractive
index forgotten. `Optics.translationMatrix_eq_transferMatrix` records that this loses nothing: a
gap's ray-transfer matrix does not depend on its index.

The nondegeneracy hypotheses are explicit throughout. Focal, principal, and nodal distances all
require `M 1 0 ≠ 0`, that is, a system with nonzero power. An afocal system has no cardinal
points at finite distance, and the theorems below say nothing about one rather than dividing by
zero silently.

Explicit non-claims. Nothing here is a claim about image quality: these are paraxial statements
about where rays go, with no aberration, diffraction, aperture, or finite-beam content. A pair of
planes can be conjugate in this sense while forming an unusable image. No field, irradiance, or
power is carried by a ray, so "image" here means a geometric conjugate plane and nothing more.

## ii. Key results

- `Optics.isConjugate_iff_entry_zero_one_eq_zero`: the imaging condition `B = 0` is equivalent to
  its behavioural specification.
- `Optics.transverseMagnification_mul_angularMagnification`: the Lagrange invariant, the product
  of the two magnifications is the determinant.
- `Optics.isBackFocalDistance_backFocalDistance` and
  `Optics.isFrontFocalDistance_frontFocalDistance`, with their uniqueness results.
- `Optics.arePrincipalDistances` and `Optics.areNodalDistances`, with uniqueness.
- `Optics.nodal_eq_principal_of_det_eq_one`: nodal and principal planes coincide exactly when the
  system does not change refractive index.
- `Optics.newton_imaging_equation`: `x x' = det M / C ^ 2`, which is `f ^ 2` for a system in a
  single medium.
- `Optics.thinLensMatrix_imaging_iff`: the thin-lens imaging equation `1 / s + 1 / s' = 1 / f`.
- `Optics.thickLens_principalDistances`: the thick-lens principal planes.
- `Optics.composedMatrix_objectImageFrame`: the object-image frame is an instance of the composed
  system of `Physlib.Optics.Rays.Transfer`, and its matrix is the shifted matrix.

## iii. Table of contents

- A. Translations and shifted reference planes
  - A.1. Translations
  - A.2. The object-image frame
- B. Conjugate planes and magnification
- C. Focal points
- D. Principal points
- E. Nodal points
- F. Newton and thin-lens imaging equations
- G. Thick-lens cardinal points

## iv. References

- B. E. A. Saleh and M. C. Teich, *Fundamentals of Photonics*, 3rd edition, chapter 1, for the
  imaging condition, magnifications, and the lens equations.
- M. U. Siddique, *Formal Analysis of Geometrical Optics using Theorem Proving*, PhD thesis,
  Concordia University, 2015, chapter 3, definitions 3.14 to 3.21 and theorems 3.9 to 3.12, for
  the specification-definition-theorem treatment of the cardinal points.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Translations and shifted reference planes

-/

/-!

### A.1. Translations

-/

/-- The ray-transfer matrix of a translation through axial distance `d`. -/
def translationMatrix (d : ℝ) : RayTransferMatrix := !![1, d; 0, 1]

@[simp]
lemma translationMatrix_zero_zero (d : ℝ) : translationMatrix d 0 0 = 1 := rfl

@[simp]
lemma translationMatrix_zero_one (d : ℝ) : translationMatrix d 0 1 = d := rfl

@[simp]
lemma translationMatrix_one_zero (d : ℝ) : translationMatrix d 1 0 = 0 := rfl

@[simp]
lemma translationMatrix_one_one (d : ℝ) : translationMatrix d 1 1 = 1 := rfl

/-- A gap's ray-transfer matrix is a translation through its length: it does not depend on the
gap's refractive index. This is why the distances below need no medium attached. -/
lemma translationMatrix_eq_transferMatrix (g : ParaxialGap) :
    translationMatrix g.length = g.transferMatrix := rfl

/-- The system matrix referred to an object plane a distance `zObject` upstream of the entrance
and an image plane a distance `zImage` downstream of the exit. -/
def shiftedMatrix (zObject zImage : ℝ) (M : RayTransferMatrix) : RayTransferMatrix :=
  translationMatrix zImage * M * translationMatrix zObject

@[simp]
lemma shiftedMatrix_zero_zero (zObject zImage : ℝ) (M : RayTransferMatrix) :
    shiftedMatrix zObject zImage M 0 0 = M 0 0 + zImage * M 1 0 := by
  simp only [shiftedMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    translationMatrix_zero_zero, translationMatrix_zero_one, translationMatrix_one_zero]
  ring

@[simp]
lemma shiftedMatrix_zero_one (zObject zImage : ℝ) (M : RayTransferMatrix) :
    shiftedMatrix zObject zImage M 0 1 =
      M 0 0 * zObject + M 0 1 + zImage * (M 1 0 * zObject + M 1 1) := by
  simp only [shiftedMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    translationMatrix_zero_zero, translationMatrix_zero_one, translationMatrix_one_one]
  ring

@[simp]
lemma shiftedMatrix_one_zero (zObject zImage : ℝ) (M : RayTransferMatrix) :
    shiftedMatrix zObject zImage M 1 0 = M 1 0 := by
  simp only [shiftedMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    translationMatrix_zero_zero, translationMatrix_one_zero, translationMatrix_one_one]
  ring

@[simp]
lemma shiftedMatrix_one_one (zObject zImage : ℝ) (M : RayTransferMatrix) :
    shiftedMatrix zObject zImage M 1 1 = M 1 0 * zObject + M 1 1 := by
  simp only [shiftedMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    translationMatrix_zero_one, translationMatrix_one_zero, translationMatrix_one_one]
  ring

/-- Moving the reference planes does not change the determinant, because a translation has unit
determinant. In particular it does not change the refractive-index ratio the system realises. -/
@[simp]
lemma det_shiftedMatrix (zObject zImage : ℝ) (M : RayTransferMatrix) :
    (shiftedMatrix zObject zImage M).det = M.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two M]
  simp only [shiftedMatrix_zero_zero, shiftedMatrix_zero_one, shiftedMatrix_one_zero,
    shiftedMatrix_one_one]
  ring

/-!

### A.2. The object-image frame

-/

/-- The shifted matrix is the system matrix bracketed by two homogeneous gaps: an object-side gap
and an image-side gap.

The refractive indices of the bracketing gaps do not enter the matrix, which is why the distances
of this file need no medium attached. They are still part of the frame, and
`Optics.composedIsValid_objectImageFrame` is where their positivity is used.
-/
lemma shiftedMatrix_eq_bracketed (objectGap imageGap : ParaxialGap) (M : RayTransferMatrix) :
    shiftedMatrix objectGap.length imageGap.length M =
      imageGap.transferMatrix * M * objectGap.transferMatrix := rfl

/-- **The object-image frame.** An object-side gap, an ordered system, and an image-side gap form
a composed system in the sense of `Physlib.Optics.Rays.Transfer`, and its composed matrix is the
system matrix referred to the object and image planes.

The frame therefore adds no new generality: it is the composed semantics specialised to a system
bracketed by free space, with the object and image planes as first-class parameters. Every result
below about `Optics.shiftedMatrix` is a result about this frame.
-/
theorem composedMatrix_objectImageFrame (objectGap imageGap : ParaxialGap)
    (cs : List ParaxialComponent) (exitGap : ParaxialGap) :
    ParaxialSystem.composedMatrix [([], objectGap), (cs, exitGap), ([], imageGap)] =
      shiftedMatrix objectGap.length imageGap.length (ParaxialSystem.matrix cs exitGap) := by
  simp only [ParaxialSystem.composedMatrix, ParaxialSystem.matrix, one_mul, shiftedMatrix,
    translationMatrix_eq_transferMatrix]

/-- The object-image frame is a valid composed system exactly when both bracketing gaps are valid
and the bracketed system is.

The positivity of the object-space and image-space refractive indices, which the source states as
explicit hypotheses of this frame, is exactly what `ParaxialGap.IsValid` carries for the two
bracketing gaps.
-/
theorem composedIsValid_objectImageFrame (objectGap imageGap : ParaxialGap)
    (cs : List ParaxialComponent) (exitGap : ParaxialGap) (hObject : objectGap.IsValid)
    (hSystem : ParaxialSystem.IsValid cs exitGap) (hImage : imageGap.IsValid) :
    ParaxialSystem.ComposedIsValid [([], objectGap), (cs, exitGap), ([], imageGap)] := by
  intro subsystem hMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember
  rcases hMember with rfl | rfl | rfl
  · exact hObject
  · exact hSystem
  · exact hImage

/-!

## B. Conjugate planes and magnification

-/

/-- **Specification of conjugate planes.** The reference planes of a system are conjugate when the
outgoing ray height depends only on the incoming height, and not on the incoming angle: every ray
leaving a point of the object plane arrives at one point of the image plane. -/
def IsConjugate (M : RayTransferMatrix) : Prop :=
  ∀ r₀ r₁ : ParaxialRay, r₀.height = r₁.height →
    (rayTransfer M r₀).height = (rayTransfer M r₁).height

/-- **The imaging condition.** The reference planes are conjugate exactly when the `B` entry of
the system matrix vanishes. -/
theorem isConjugate_iff_entry_zero_one_eq_zero (M : RayTransferMatrix) :
    IsConjugate M ↔ M 0 1 = 0 := by
  constructor
  · intro h
    have hzero := h ⟨0, 0⟩ ⟨0, 1⟩ rfl
    simpa using hzero.symm
  · intro hB r₀ r₁ hHeight
    simp [hB, hHeight]

/-- The transverse magnification of a system between conjugate planes. -/
def transverseMagnification (M : RayTransferMatrix) : ℝ := M 0 0

/-- The angular magnification of a system, for rays leaving the axial point of the object
plane. -/
def angularMagnification (M : RayTransferMatrix) : ℝ := M 1 1

/-- **Specification of the transverse magnification.** Between conjugate planes the outgoing
height is the transverse magnification times the incoming height. -/
theorem height_eq_transverseMagnification_mul (M : RayTransferMatrix) (h : IsConjugate M)
    (r : ParaxialRay) :
    (rayTransfer M r).height = transverseMagnification M * r.height := by
  rw [isConjugate_iff_entry_zero_one_eq_zero] at h
  simp [transverseMagnification, h]

/-- **Specification of the angular magnification.** A ray leaving the axial point of the object
plane has its angle multiplied by the angular magnification. This needs no conjugacy
hypothesis. -/
theorem angle_eq_angularMagnification_mul (M : RayTransferMatrix) (r : ParaxialRay)
    (h : r.height = 0) :
    (rayTransfer M r).angle = angularMagnification M * r.angle := by
  simp [angularMagnification, h]

/-- **The Lagrange invariant.** Between conjugate planes the product of the transverse and angular
magnifications is the determinant of the system matrix, which for a system free of
phase conjugation is the ratio of the entry index to the exit index. -/
theorem transverseMagnification_mul_angularMagnification (M : RayTransferMatrix)
    (h : IsConjugate M) :
    transverseMagnification M * angularMagnification M = M.det := by
  rw [isConjugate_iff_entry_zero_one_eq_zero] at h
  rw [Matrix.det_fin_two, transverseMagnification, angularMagnification, h]
  ring

/-!

## C. Focal points

-/

/-- The effective focal length of a system of nonzero power. -/
def effectiveFocalLength (M : RayTransferMatrix) : ℝ := -1 / M 1 0

/-- **Specification of the back focal distance.** Placing the image plane at this distance
downstream of the exit sends every incoming ray parallel to the axis onto the axis. -/
def IsBackFocalDistance (M : RayTransferMatrix) (z : ℝ) : Prop :=
  ∀ r : ParaxialRay, r.angle = 0 → (rayTransfer (shiftedMatrix 0 z M) r).height = 0

/-- The back focal distance of a system of nonzero power. -/
def backFocalDistance (M : RayTransferMatrix) : ℝ := -(M 0 0) / M 1 0

/-- The back focal distance meets its specification. -/
theorem isBackFocalDistance_backFocalDistance (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) :
    IsBackFocalDistance M (backFocalDistance M) := by
  intro r hAngle
  simp only [rayTransfer_height, shiftedMatrix_zero_zero, shiftedMatrix_zero_one,
    backFocalDistance, hAngle, mul_zero, add_zero]
  field_simp
  ring

/-- The back focal distance is the only distance meeting its specification. -/
theorem isBackFocalDistance_unique (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) (z : ℝ)
    (h : IsBackFocalDistance M z) : z = backFocalDistance M := by
  have h1 := h ⟨1, 0⟩ rfl
  simp only [rayTransfer_height, shiftedMatrix_zero_zero, shiftedMatrix_zero_one, mul_zero,
    add_zero, mul_one] at h1
  rw [backFocalDistance, eq_div_iff hC]
  linarith

/-- **Specification of the front focal distance.** Placing the object plane at this distance
upstream of the entrance sends every ray leaving its axial point out parallel to the axis. -/
def IsFrontFocalDistance (M : RayTransferMatrix) (z : ℝ) : Prop :=
  ∀ r : ParaxialRay, r.height = 0 → (rayTransfer (shiftedMatrix z 0 M) r).angle = 0

/-- The front focal distance of a system of nonzero power. -/
def frontFocalDistance (M : RayTransferMatrix) : ℝ := -(M 1 1) / M 1 0

/-- The front focal distance meets its specification. -/
theorem isFrontFocalDistance_frontFocalDistance (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) :
    IsFrontFocalDistance M (frontFocalDistance M) := by
  intro r hHeight
  simp only [rayTransfer_angle, shiftedMatrix_one_zero, shiftedMatrix_one_one, hHeight, mul_zero,
    zero_add, frontFocalDistance]
  field_simp
  ring

/-- The front focal distance is the only distance meeting its specification. -/
theorem isFrontFocalDistance_unique (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) (z : ℝ)
    (h : IsFrontFocalDistance M z) : z = frontFocalDistance M := by
  have h1 := h ⟨0, 1⟩ rfl
  simp only [rayTransfer_angle, shiftedMatrix_one_zero, shiftedMatrix_one_one, mul_zero, zero_add,
    mul_one] at h1
  rw [frontFocalDistance, eq_div_iff hC]
  linarith

/-!

## D. Principal points

-/

/-- **Specification of the principal planes.** Referring the system to these planes makes them a
pair of conjugate planes of unit transverse magnification. -/
def ArePrincipalDistances (M : RayTransferMatrix) (zObject zImage : ℝ) : Prop :=
  IsConjugate (shiftedMatrix zObject zImage M) ∧
    transverseMagnification (shiftedMatrix zObject zImage M) = 1

/-- The distance from the object-side principal plane to the entrance of a system of nonzero
power. -/
def objectPrincipalDistance (M : RayTransferMatrix) : ℝ := (M.det - M 1 1) / M 1 0

/-- The distance from the exit of a system of nonzero power to its image-side principal plane. -/
def imagePrincipalDistance (M : RayTransferMatrix) : ℝ := (1 - M 0 0) / M 1 0

/-- The principal distances meet their specification. -/
theorem arePrincipalDistances (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) :
    ArePrincipalDistances M (objectPrincipalDistance M) (imagePrincipalDistance M) := by
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
  constructor
  · rw [isConjugate_iff_entry_zero_one_eq_zero, shiftedMatrix_zero_one, objectPrincipalDistance,
      imagePrincipalDistance, hdet]
    field_simp
    ring
  · rw [transverseMagnification, shiftedMatrix_zero_zero, imagePrincipalDistance]
    field_simp
    ring

/-- The principal distances are the only pair meeting their specification. -/
theorem arePrincipalDistances_unique (M : RayTransferMatrix) (hC : M 1 0 ≠ 0)
    (zObject zImage : ℝ) (h : ArePrincipalDistances M zObject zImage) :
    zObject = objectPrincipalDistance M ∧ zImage = imagePrincipalDistance M := by
  obtain ⟨hConjugate, hMagnification⟩ := h
  rw [isConjugate_iff_entry_zero_one_eq_zero, shiftedMatrix_zero_one] at hConjugate
  rw [transverseMagnification, shiftedMatrix_zero_zero] at hMagnification
  have hz : zImage * M 1 0 = 1 - M 0 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [objectPrincipalDistance, Matrix.det_fin_two, eq_div_iff hC]
    linear_combination M 1 0 * hConjugate - (M 1 0 * zObject + M 1 1) * hz
  · rw [imagePrincipalDistance, eq_div_iff hC]
    linarith

/-!

## E. Nodal points

-/

/-- **Specification of the nodal planes.** Referring the system to these planes makes a ray
leaving the axial point of the object plane arrive at the axial point of the image plane with an
unchanged angle: the angular magnification is one and the planes are conjugate. -/
def AreNodalDistances (M : RayTransferMatrix) (zObject zImage : ℝ) : Prop :=
  IsConjugate (shiftedMatrix zObject zImage M) ∧
    angularMagnification (shiftedMatrix zObject zImage M) = 1

/-- The distance from the object-side nodal plane to the entrance of a system of nonzero power. -/
def objectNodalDistance (M : RayTransferMatrix) : ℝ := (1 - M 1 1) / M 1 0

/-- The distance from the exit of a system of nonzero power to its image-side nodal plane. -/
def imageNodalDistance (M : RayTransferMatrix) : ℝ := (M.det - M 0 0) / M 1 0

/-- The nodal distances meet their specification. -/
theorem areNodalDistances (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) :
    AreNodalDistances M (objectNodalDistance M) (imageNodalDistance M) := by
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
  constructor
  · rw [isConjugate_iff_entry_zero_one_eq_zero, shiftedMatrix_zero_one, objectNodalDistance,
      imageNodalDistance, hdet]
    field_simp
    ring
  · rw [angularMagnification, shiftedMatrix_one_one, objectNodalDistance]
    field_simp
    ring

/-- The nodal distances are the only pair meeting their specification. -/
theorem areNodalDistances_unique (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) (zObject zImage : ℝ)
    (h : AreNodalDistances M zObject zImage) :
    zObject = objectNodalDistance M ∧ zImage = imageNodalDistance M := by
  obtain ⟨hConjugate, hAngular⟩ := h
  rw [isConjugate_iff_entry_zero_one_eq_zero, shiftedMatrix_zero_one] at hConjugate
  rw [angularMagnification, shiftedMatrix_one_one] at hAngular
  refine ⟨?_, ?_⟩
  · rw [objectNodalDistance, eq_div_iff hC]
    linarith
  · rw [imageNodalDistance, Matrix.det_fin_two, eq_div_iff hC]
    linear_combination M 1 0 * hConjugate - (zImage * M 1 0 + M 0 0) * hAngular

/-- **Nodal planes coincide with principal planes exactly for a system in a single medium.**

The two pairs agree when the determinant is one, that is when the system does not change the
refractive index. For a system that does, they are genuinely different points.
-/
theorem nodal_eq_principal_of_det_eq_one (M : RayTransferMatrix) (h : M.det = 1) :
    objectNodalDistance M = objectPrincipalDistance M ∧
      imageNodalDistance M = imagePrincipalDistance M := by
  rw [objectNodalDistance, objectPrincipalDistance, imageNodalDistance, imagePrincipalDistance, h]
  exact ⟨rfl, rfl⟩

/-!

## F. Newton and thin-lens imaging equations

-/

/-- **Newton's imaging equation.** For conjugate planes, the object distance measured from the
front focal plane and the image distance measured from the back focal plane have product
`det M / C ^ 2`, which is the square of the effective focal length whenever the system does not
change the refractive index. -/
theorem newton_imaging_equation (M : RayTransferMatrix) (hC : M 1 0 ≠ 0) (zObject zImage : ℝ)
    (h : IsConjugate (shiftedMatrix zObject zImage M)) :
    (zObject - frontFocalDistance M) * (zImage - backFocalDistance M) = M.det / M 1 0 ^ 2 := by
  rw [isConjugate_iff_entry_zero_one_eq_zero, shiftedMatrix_zero_one] at h
  have key : (M 1 0 * zObject + M 1 1) * (M 1 0 * zImage + M 0 0) = M.det := by
    rw [Matrix.det_fin_two]
    linear_combination M 1 0 * h
  have hx : zObject - frontFocalDistance M = (M 1 0 * zObject + M 1 1) / M 1 0 := by
    rw [frontFocalDistance]
    field_simp
    ring
  have hx' : zImage - backFocalDistance M = (M 1 0 * zImage + M 0 0) / M 1 0 := by
    rw [backFocalDistance]
    field_simp
    ring
  rw [hx, hx', div_mul_div_comm, key, pow_two]

/-- Newton's equation for a system in a single medium, where the determinant is one. -/
theorem newton_imaging_equation_of_det_eq_one (M : RayTransferMatrix) (hC : M 1 0 ≠ 0)
    (hdet : M.det = 1) (zObject zImage : ℝ)
    (h : IsConjugate (shiftedMatrix zObject zImage M)) :
    (zObject - frontFocalDistance M) * (zImage - backFocalDistance M) =
      effectiveFocalLength M ^ 2 := by
  rw [newton_imaging_equation M hC zObject zImage h, hdet, effectiveFocalLength]
  field_simp

/-- **The thin-lens imaging condition.** An object plane a distance `s` in front of a thin lens
and an image plane a distance `s'` behind it are conjugate exactly when `f (s + s') = s s'`.

This is the cleared form, which needs only `f ≠ 0`. The familiar reciprocal form is
`Optics.thinLensMatrix_imaging_iff`.
-/
theorem thinLensMatrix_isConjugate_iff (f s s' : ℝ) (hf : f ≠ 0) :
    IsConjugate (shiftedMatrix s s' (thinLensMatrix f)) ↔ f * (s + s') = s * s' := by
  have hA : thinLensMatrix f 0 0 = 1 := rfl
  have hB : thinLensMatrix f 0 1 = 0 := rfl
  have hCentry : thinLensMatrix f 1 0 = -1 / f := rfl
  have hD : thinLensMatrix f 1 1 = 1 := rfl
  rw [isConjugate_iff_entry_zero_one_eq_zero, shiftedMatrix_zero_one, hA, hB, hCentry, hD]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- **The thin-lens imaging equation.** In reciprocal form, an object at distance `s` and an image
at distance `s'` are conjugate exactly when `1 / s + 1 / s' = 1 / f`. -/
theorem thinLensMatrix_imaging_iff (f s s' : ℝ) (hf : f ≠ 0) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    IsConjugate (shiftedMatrix s s' (thinLensMatrix f)) ↔ 1 / s + 1 / s' = 1 / f := by
  rw [thinLensMatrix_isConjugate_iff f s s' hf]
  rw [div_add_div _ _ hs hs', div_eq_div_iff (mul_ne_zero hs hs') hf]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- The transverse magnification of a thin lens between conjugate planes is `-s' / s`. -/
theorem thinLensMatrix_transverseMagnification (f s s' : ℝ) (hf : f ≠ 0) (hs : s ≠ 0)
    (h : IsConjugate (shiftedMatrix s s' (thinLensMatrix f))) :
    transverseMagnification (shiftedMatrix s s' (thinLensMatrix f)) = -s' / s := by
  rw [thinLensMatrix_isConjugate_iff f s s' hf] at h
  have hCentry : thinLensMatrix f 1 0 = -1 / f := rfl
  have hA : thinLensMatrix f 0 0 = 1 := rfl
  rw [transverseMagnification, shiftedMatrix_zero_zero, hA, hCentry]
  field_simp
  linarith

/-- A thin lens has both focal distances equal to its focal length. -/
theorem thinLensMatrix_focalDistances (f : ℝ) (hf : f ≠ 0) :
    backFocalDistance (thinLensMatrix f) = f ∧ frontFocalDistance (thinLensMatrix f) = f := by
  have hA : thinLensMatrix f 0 0 = 1 := rfl
  have hCentry : thinLensMatrix f 1 0 = -1 / f := rfl
  have hD : thinLensMatrix f 1 1 = 1 := rfl
  rw [backFocalDistance, frontFocalDistance, hA, hCentry, hD]
  refine ⟨?_, ?_⟩ <;> field_simp

/-- A thin lens has both principal planes at the lens itself. -/
theorem thinLensMatrix_principalDistances (f : ℝ) :
    objectPrincipalDistance (thinLensMatrix f) = 0 ∧
      imagePrincipalDistance (thinLensMatrix f) = 0 := by
  rw [objectPrincipalDistance, imagePrincipalDistance, det_thinLensMatrix]
  simp [thinLensMatrix]

/-!

## G. Thick-lens cardinal points

-/

/-- The image-side principal distance expressed through the effective focal length. -/
lemma imagePrincipalDistance_eq_effectiveFocalLength_mul (M : RayTransferMatrix)
    (hC : M 1 0 ≠ 0) :
    imagePrincipalDistance M = effectiveFocalLength M * (M 0 0 - 1) := by
  rw [imagePrincipalDistance, effectiveFocalLength]
  field_simp
  ring

/-- The object-side principal distance expressed through the effective focal length. -/
lemma objectPrincipalDistance_eq_effectiveFocalLength_mul (M : RayTransferMatrix)
    (hC : M 1 0 ≠ 0) :
    objectPrincipalDistance M = effectiveFocalLength M * (M 1 1 - M.det) := by
  rw [objectPrincipalDistance, effectiveFocalLength]
  field_simp
  ring

/-- **The principal planes of a thick lens**, expressed through its effective focal length.

The distances follow the sign convention fixed in the module documentation: the object-side value
is the distance from the principal plane to the first vertex, positive upstream, and the
image-side value is the distance from the second vertex to the principal plane, positive
downstream. At zero thickness both vanish, recovering
`Optics.thinLensMatrix_principalDistances`.
-/
theorem thickLens_principalDistances (n nL t R₁ R₂ : ℝ) (hn : n ≠ 0) (hnL : nL ≠ 0)
    (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (M : RayTransferMatrix)
    (hM : M = ParaxialSystem.matrix
      [⟨⟨n, 0⟩, ParaxialInterface.sphericalRefracting R₁⟩,
        ⟨⟨nL, t⟩, ParaxialInterface.sphericalRefracting R₂⟩] ⟨n, 0⟩)
    (hC : M 1 0 ≠ 0) :
    imagePrincipalDistance M = -effectiveFocalLength M * t * (nL - n) / (nL * R₁) ∧
      objectPrincipalDistance M = effectiveFocalLength M * t * (nL - n) / (nL * R₂) := by
  have hEntryA : M 0 0 = 1 - t * (nL - n) / (nL * R₁) := by
    rw [hM, thickLens_matrix n nL t R₁ R₂ hn hnL hR₁ hR₂]
    rfl
  have hEntryD : M 1 1 = 1 + t * (nL - n) / (nL * R₂) := by
    rw [hM, thickLens_matrix n nL t R₁ R₂ hn hnL hR₁ hR₂]
    rfl
  have hDet : M.det = 1 := by
    rw [hM, thickLens_matrix n nL t R₁ R₂ hn hnL hR₁ hR₂, Matrix.det_fin_two_of]
    field_simp
    ring
  constructor
  · rw [imagePrincipalDistance_eq_effectiveFocalLength_mul M hC, hEntryA]
    ring
  · rw [objectPrincipalDistance_eq_effectiveFocalLength_mul M hC, hEntryD, hDet]
    ring

end

end Optics
