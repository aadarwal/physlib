/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Imaging

/-!
# Regression tests for imaging and cardinal points

## i. Overview

This file carries regression `R-02` of `goal.md` §I.3, whose stated target is cardinal-point
formulas that are definitions dressed up as results.

The check has two halves. The positive half applies each cardinal-point formula to a concrete
system and shows it satisfies the behavioural specification. The negative half shows the
specification has teeth: a value that is close but wrong fails it. Without the negative half a
vacuous specification would pass.

The sharpest fixture is a single spherical refracting surface, whose nodal points both lie at its
centre of curvature while its principal points lie at the vertex. That configuration separates
the two notions, which coincide for every system in a single medium, and it checks the sign
convention of the distances at the same time: the object-side nodal distance comes out negative
because the point lies *downstream* of the entrance.

## ii. Key results

- `Optics.imagingRegression_thinLens_isBackFocalDistance` and
  `Optics.imagingRegression_thinLens_not_isBackFocalDistance`: the focal-distance specification is
  satisfied by the formula and refuted by a wrong value.
- `Optics.imagingRegression_sphericalSurface_nodal_at_centre`: the nodal points of a single
  refracting surface lie at its centre of curvature while its principal points lie at the vertex.
- `Optics.imagingRegression_sphericalSurface_nodal_ne_principal`: the two notions are genuinely
  different when the system changes refractive index.
- `Optics.imagingRegression_twoFocalLengths_magnification`: imaging at `2f` inverts with unit
  magnification.
- `Optics.imagingRegression_newton`: Newton's equation on the same configuration.

## iii. Table of contents

- A. Thin-lens cardinal points
- B. Imaging at twice the focal length
- C. A single spherical surface separates nodal from principal points
- D. The object-image frame

## iv. References

The fixtures use only the public declarations of `Physlib.Optics.Rays.Imaging`.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Thin-lens cardinal points

-/

/-- The unit-focal-length thin lens used throughout this file. -/
lemma imagingRegression_thinLensMatrix_entries :
    thinLensMatrix 1 0 0 = 1 ∧ thinLensMatrix 1 0 1 = 0 ∧ thinLensMatrix 1 1 0 = -1 ∧
      thinLensMatrix 1 1 1 = 1 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  norm_num [thinLensMatrix]

/-- A unit-focal-length thin lens has nonzero power. -/
lemma imagingRegression_thinLensMatrix_power : thinLensMatrix 1 1 0 ≠ 0 := by
  rw [imagingRegression_thinLensMatrix_entries.2.2.1]
  norm_num

/-- Both focal distances of a unit-focal-length thin lens are `1`. -/
lemma imagingRegression_thinLens_focalDistances :
    backFocalDistance (thinLensMatrix 1) = 1 ∧ frontFocalDistance (thinLensMatrix 1) = 1 :=
  thinLensMatrix_focalDistances 1 one_ne_zero

/-- **Regression R-02, positive half.** The back focal distance of a unit-focal-length thin lens
satisfies its behavioural specification: every incoming axis-parallel ray reaches the axis
there. -/
lemma imagingRegression_thinLens_isBackFocalDistance :
    IsBackFocalDistance (thinLensMatrix 1) 1 := by
  have h := isBackFocalDistance_backFocalDistance (thinLensMatrix 1)
    imagingRegression_thinLensMatrix_power
  rwa [imagingRegression_thinLens_focalDistances.1] at h

/-- **Regression R-02, negative half.** A wrong focal distance fails the specification, so the
specification is not vacuous. -/
lemma imagingRegression_thinLens_not_isBackFocalDistance :
    ¬ IsBackFocalDistance (thinLensMatrix 1) 2 := by
  intro h
  have h1 := h ⟨1, 0⟩ rfl
  obtain ⟨hA, -, hC, -⟩ := imagingRegression_thinLensMatrix_entries
  simp only [rayTransfer_height, shiftedMatrix_zero_zero, shiftedMatrix_zero_one, hA, hC] at h1
  norm_num at h1

/-- A thin lens has both principal planes and both nodal planes at the lens itself. -/
lemma imagingRegression_thinLens_cardinalPoints :
    objectPrincipalDistance (thinLensMatrix 1) = 0 ∧
      imagePrincipalDistance (thinLensMatrix 1) = 0 ∧
      objectNodalDistance (thinLensMatrix 1) = 0 ∧
      imageNodalDistance (thinLensMatrix 1) = 0 := by
  obtain ⟨hPrincipalObject, hPrincipalImage⟩ := thinLensMatrix_principalDistances 1
  obtain ⟨hNodalObject, hNodalImage⟩ :=
    nodal_eq_principal_of_det_eq_one (thinLensMatrix 1) (det_thinLensMatrix 1)
  exact ⟨hPrincipalObject, hPrincipalImage, hNodalObject.trans hPrincipalObject,
    hNodalImage.trans hPrincipalImage⟩

/-!

## B. Imaging at twice the focal length

-/

/-- An object and an image plane two focal lengths from a unit-focal-length thin lens are
conjugate. -/
lemma imagingRegression_twoFocalLengths_isConjugate :
    IsConjugate (shiftedMatrix 2 2 (thinLensMatrix 1)) := by
  rw [thinLensMatrix_imaging_iff 1 2 2 one_ne_zero two_ne_zero two_ne_zero]
  norm_num

/-- Imaging at twice the focal length inverts with unit magnification. -/
lemma imagingRegression_twoFocalLengths_magnification :
    transverseMagnification (shiftedMatrix 2 2 (thinLensMatrix 1)) = -1 := by
  rw [thinLensMatrix_transverseMagnification 1 2 2 one_ne_zero two_ne_zero
    imagingRegression_twoFocalLengths_isConjugate]
  norm_num

/-- **Newton's equation** on the same configuration: the object and image distances measured from
the focal planes are both `1`, and their product is the square of the focal length. -/
lemma imagingRegression_newton :
    (2 - frontFocalDistance (thinLensMatrix 1)) * (2 - backFocalDistance (thinLensMatrix 1)) =
      effectiveFocalLength (thinLensMatrix 1) ^ 2 := by
  refine newton_imaging_equation_of_det_eq_one (thinLensMatrix 1)
    imagingRegression_thinLensMatrix_power (det_thinLensMatrix 1) 2 2
    imagingRegression_twoFocalLengths_isConjugate

/-- The effective focal length of the regression lens is its focal length. -/
lemma imagingRegression_effectiveFocalLength :
    effectiveFocalLength (thinLensMatrix 1) = 1 := by
  rw [effectiveFocalLength, imagingRegression_thinLensMatrix_entries.2.2.1]
  norm_num

/-!

## C. A single spherical surface separates nodal from principal points

-/

/-- A single spherical refracting surface of radius `1` carrying a ray from index `1` into index
`2`. -/
def imagingRegressionSurface : RayTransferMatrix :=
  (ParaxialInterface.sphericalRefracting 1).transferMatrix 1 2

/-- The entries of the regression surface. -/
lemma imagingRegressionSurface_entries :
    imagingRegressionSurface 0 0 = 1 ∧ imagingRegressionSurface 0 1 = 0 ∧
      imagingRegressionSurface 1 0 = -(1 / 2) ∧ imagingRegressionSurface 1 1 = 1 / 2 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    norm_num [imagingRegressionSurface, ParaxialInterface.transferMatrix]

/-- The regression surface has nonzero power. -/
lemma imagingRegressionSurface_power : imagingRegressionSurface 1 0 ≠ 0 := by
  rw [imagingRegressionSurface_entries.2.2.1]
  norm_num

/-- The regression surface has determinant `1 / 2`, the ratio of its two refractive indices, so it
is not a system in a single medium. -/
lemma imagingRegressionSurface_det : imagingRegressionSurface.det = 1 / 2 := by
  obtain ⟨hA, hB, hC, hD⟩ := imagingRegressionSurface_entries
  rw [Matrix.det_fin_two, hA, hB, hC, hD]
  norm_num

/-- **The nodal points of a single refracting surface lie at its centre of curvature**, while its
principal points lie at the vertex.

The object-side nodal distance is `-1`, which under the sign convention of this file places that
plane one unit *downstream* of the entrance vertex, and the image-side nodal distance is `+1`,
one unit downstream of the exit vertex. The surface has zero thickness, so both are the same
point: the centre of curvature at radius `1`.
-/
lemma imagingRegression_sphericalSurface_nodal_at_centre :
    objectNodalDistance imagingRegressionSurface = -1 ∧
      imageNodalDistance imagingRegressionSurface = 1 ∧
      objectPrincipalDistance imagingRegressionSurface = 0 ∧
      imagePrincipalDistance imagingRegressionSurface = 0 := by
  obtain ⟨hA, -, hC, hD⟩ := imagingRegressionSurface_entries
  rw [objectNodalDistance, imageNodalDistance, objectPrincipalDistance, imagePrincipalDistance,
    imagingRegressionSurface_det, hA, hC, hD]
  norm_num

/-- The nodal and principal planes of the regression surface are different, because it changes
refractive index. Systems in a single medium cannot separate the two notions. -/
lemma imagingRegression_sphericalSurface_nodal_ne_principal :
    objectNodalDistance imagingRegressionSurface ≠
      objectPrincipalDistance imagingRegressionSurface := by
  obtain ⟨hNodal, -, hPrincipal, -⟩ := imagingRegression_sphericalSurface_nodal_at_centre
  rw [hNodal, hPrincipal]
  norm_num

/-- The nodal distances of the regression surface satisfy their behavioural specification. -/
lemma imagingRegression_sphericalSurface_areNodalDistances :
    AreNodalDistances imagingRegressionSurface (-1) 1 := by
  obtain ⟨hObject, hImage, -, -⟩ := imagingRegression_sphericalSurface_nodal_at_centre
  have h := areNodalDistances imagingRegressionSurface imagingRegressionSurface_power
  rwa [hObject, hImage] at h

/-!

## D. The object-image frame

-/

/-- The object-image frame of a unit-focal-length thin lens with both bracketing gaps of length
`2` in air is a valid composed system whose matrix is the shifted matrix. -/
lemma imagingRegression_objectImageFrame :
    ParaxialSystem.composedMatrix
        [([], (⟨1, 2⟩ : ParaxialGap)),
          ([⟨⟨1, 0⟩, ParaxialInterface.prescribed 1 0 (-1) 1⟩], (⟨1, 0⟩ : ParaxialGap)),
          ([], (⟨1, 2⟩ : ParaxialGap))] =
      shiftedMatrix 2 2
        (ParaxialSystem.matrix [⟨⟨1, 0⟩, ParaxialInterface.prescribed 1 0 (-1) 1⟩] ⟨1, 0⟩) :=
  composedMatrix_objectImageFrame ⟨1, 2⟩ ⟨1, 2⟩ _ _

/-- The bracketed frame is a valid composed system: both bracketing gaps have positive index and
nonnegative length, and the bracketed lens is a valid system. -/
lemma imagingRegression_objectImageFrame_isValid :
    ParaxialSystem.ComposedIsValid
      [([], (⟨1, 2⟩ : ParaxialGap)),
        ([⟨⟨1, 0⟩, ParaxialInterface.prescribed 1 0 (-1) 1⟩], (⟨1, 0⟩ : ParaxialGap)),
        ([], (⟨1, 2⟩ : ParaxialGap))] := by
  refine composedIsValid_objectImageFrame ⟨1, 2⟩ ⟨1, 2⟩ _ _ ⟨by norm_num, by norm_num⟩ ?_
    ⟨by norm_num, by norm_num⟩ rfl rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    norm_num [ParaxialSystem.headIndex, ParaxialInterface.IsValid]

end

end Optics
