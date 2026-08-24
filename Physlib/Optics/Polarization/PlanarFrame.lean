/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector.Hyperplane
public import Physlib.Optics.Polarization.Frame

/-!
# Polarization frames resolved on an oriented plane

## i. Overview

This file relates a propagation-oriented polarization frame to a common frame carried by an
oriented affine plane. The first axes are assumed exactly equal, fixing a common transverse gauge
rather than only a common unoriented line. The plane frame has second axis `u₁ = n × u₀`, not
`u₀ × n`. If `c` is the signed normal component of the propagation vector, tangential projection
then sends the propagation-frame axes `(e₀, e₁)` to `(u₀, c u₁)` in the plane frame.

For full-vector Jones coordinates this gives the interface-plane coordinates
`(J₀, c J₁)`. Applying the propagation quarter-turn first gives `(-J₁, c J₀)`, the
corresponding geometry needed for tangential magnetic-field amplitudes.

The signed factor is left explicit: it distinguishes propagation toward the positive and negative
sides of the plane and vanishes at grazing incidence. The results are purely geometric. They do
not assign incident, reflected, or transmitted roles; impose a material model or boundary law;
or state a Fresnel, observable, irradiance, or power result.

## ii. Key results

- `PolarizationFrame.tangentialProjection_axis_zero_of_axis_zero_eq`: the common first axis is
  fixed by tangential projection.
- `PolarizationFrame.tangentialProjection_axis_one_of_axis_zero_eq`: the second axis is multiplied
  by the signed normal factor.
- `PolarizationFrame.hyperplaneTangentialProjection_embedJones_of_axis_zero_eq`: the corresponding
  full-vector Jones-coordinate formula.
- `PolarizationFrame.hyperplaneTangentialProjection_embedJones_propagationCross_of_axis_zero_eq`:
  the propagation-cross formula.

## iii. Table of contents

- A. Real planar-frame geometry
- B. Complex Jones amplitudes

## iv. References

The construction is derived from the imported oriented-hyperplane, Euclidean cross-product, and
polarization-frame APIs. No external formal development is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Space Matrix InnerProductSpace

noncomputable section

namespace PolarizationFrame

variable {direction : Space.Direction 3}

/-!

## A. Real planar-frame geometry

-/

/-- If a propagation frame and a plane-normal frame have the same first axis, that axis is fixed
by tangential projection onto the plane. -/
lemma tangentialProjection_axis_zero_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (frame : PolarizationFrame direction) (halign : frame.axis 0 = planeFrame.axis 0) :
    plane.tangentialProjection (frame.axis 0) = planeFrame.axis 0 := by
  rw [← halign]
  apply plane.tangentialProjection_eq_self_of_isTangent
  change plane.normalComponent (frame.axis 0) = 0
  rw [OrientedAffineHyperplane.normalComponent, halign]
  change inner ℝ planeFrame.propagationVector (planeFrame.axis 0) = 0
  exact planeFrame.inner_propagationVector_axis 0

/-- If a propagation frame and a plane-normal frame have the same first axis, tangential
projection of the propagation frame's second axis is the plane frame's second axis multiplied by
the signed normal component of propagation. -/
lemma tangentialProjection_axis_one_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (frame : PolarizationFrame direction) (halign : frame.axis 0 = planeFrame.axis 0) :
    plane.tangentialProjection (frame.axis 1) =
      plane.normalComponent frame.propagationVector • planeFrame.axis 1 := by
  have htangent : inner ℝ plane.normalVector (frame.axis 0) = 0 := by
    rw [halign]
    change inner ℝ planeFrame.propagationVector (planeFrame.axis 0) = 0
    exact planeFrame.inner_propagationVector_axis 0
  have hnormal : inner ℝ frame.propagationVector plane.normalVector =
      plane.normalComponent frame.propagationVector := by
    rw [real_inner_comm]
    rfl
  have hcross : plane.normalVector ⨯ₑ₃
      (frame.propagationVector ⨯ₑ₃ frame.axis 0) =
        -plane.normalComponent frame.propagationVector • frame.axis 0 := by
    rw [Space.cross_cross_eq_smul_sub_smul', htangent, hnormal]
    simp
  calc
    plane.tangentialProjection (frame.axis 1) =
        -(plane.normalVector ⨯ₑ₃ (plane.normalVector ⨯ₑ₃ frame.axis 1)) := by
      rw [Space.cross_cross_eq_smul_sub_smul', plane.inner_normalVector_self]
      simp [OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent]
    _ = -(plane.normalVector ⨯ₑ₃
        (plane.normalVector ⨯ₑ₃
          (frame.propagationVector ⨯ₑ₃ frame.axis 0))) := by
      rw [frame.propagationVector_cross_axis_zero]
    _ = -(plane.normalVector ⨯ₑ₃
        (-plane.normalComponent frame.propagationVector • frame.axis 0)) := by
      rw [hcross]
    _ = plane.normalComponent frame.propagationVector •
        (plane.normalVector ⨯ₑ₃ planeFrame.axis 0) := by
      rw [Space.cross_smul, halign]
      simp
    _ = plane.normalComponent frame.propagationVector • planeFrame.axis 1 := by
      change _ • (planeFrame.propagationVector ⨯ₑ₃ planeFrame.axis 0) = _
      rw [planeFrame.propagationVector_cross_axis_zero]

/-!

## B. Normal cross products in aligned frames

-/

variable {direction₁ direction₂ : Space.Direction 3}

/-- The stored-normal component of the common first axis crossed with an aligned frame's second
axis is that frame's signed propagation normal. -/
lemma normalComponent_axis_zero_cross_axis_one_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (firstFrame : PolarizationFrame direction₁) (secondFrame : PolarizationFrame direction₂)
    (hFirstAlign : firstFrame.axis 0 = planeFrame.axis 0)
    (hSecondAlign : secondFrame.axis 0 = planeFrame.axis 0) :
    plane.normalComponent (firstFrame.axis 0 ⨯ₑ₃ secondFrame.axis 1) =
      plane.normalComponent secondFrame.propagationVector := by
  rw [hFirstAlign, ← hSecondAlign, secondFrame.orientation]
  rfl

/-- The stored-normal component of an aligned frame's second axis crossed with the common first
axis is minus that frame's signed propagation normal. -/
lemma normalComponent_axis_one_cross_axis_zero_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (firstFrame : PolarizationFrame direction₁) (secondFrame : PolarizationFrame direction₂)
    (hFirstAlign : firstFrame.axis 0 = planeFrame.axis 0)
    (hSecondAlign : secondFrame.axis 0 = planeFrame.axis 0) :
    plane.normalComponent (firstFrame.axis 1 ⨯ₑ₃ secondFrame.axis 0) =
      -plane.normalComponent firstFrame.propagationVector := by
  have hswap : firstFrame.axis 1 ⨯ₑ₃ secondFrame.axis 0 =
      -(secondFrame.axis 0 ⨯ₑ₃ firstFrame.axis 1) := by
    ext i
    fin_cases i <;> simp [crossProduct] <;> ring
  rw [hswap, OrientedAffineHyperplane.normalComponent, inner_neg_right,
    hSecondAlign, ← hFirstAlign, firstFrame.orientation]
  rfl

/-- The stored-normal component of the cross product of two aligned frames' second axes
vanishes. -/
lemma normalComponent_axis_one_cross_axis_one_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (firstFrame : PolarizationFrame direction₁) (secondFrame : PolarizationFrame direction₂)
    (hFirstAlign : firstFrame.axis 0 = planeFrame.axis 0)
    (hSecondAlign : secondFrame.axis 0 = planeFrame.axis 0) :
    plane.normalComponent (firstFrame.axis 1 ⨯ₑ₃ secondFrame.axis 1) = 0 := by
  have hFirstOrthogonal :
      inner ℝ (planeFrame.axis 0) (firstFrame.axis 1) = 0 := by
    rw [← hFirstAlign]
    simpa using
      (orthonormal_iff_ite.mp firstFrame.orthonormal_axis (0 : Fin 2) (1 : Fin 2))
  have hSecondOrthogonal :
      inner ℝ (planeFrame.axis 0) (secondFrame.axis 1) = 0 := by
    rw [← hSecondAlign]
    simpa using
      (orthonormal_iff_ite.mp secondFrame.orthonormal_axis (0 : Fin 2) (1 : Fin 2))
  change inner ℝ planeFrame.propagationVector
    (firstFrame.axis 1 ⨯ₑ₃ secondFrame.axis 1) = 0
  rw [show planeFrame.propagationVector =
      planeFrame.axis 0 ⨯ₑ₃ planeFrame.axis 1 from planeFrame.orientation.symm,
    Space.inner_cross_cross,
    hFirstOrthogonal, hSecondOrthogonal]
  ring

/-- The stored-normal component of a cross product between Jones fields in two frames aligned to
one plane frame, expressed in their scalar Jones realizations. -/
lemma normalComponent_cross_realizeJones_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (firstFrame : PolarizationFrame direction₁) (secondFrame : PolarizationFrame direction₂)
    (firstJones secondJones : JonesVector) (firstPhase secondPhase : ℝ)
    (hFirstAlign : firstFrame.axis 0 = planeFrame.axis 0)
    (hSecondAlign : secondFrame.axis 0 = planeFrame.axis 0) :
    plane.normalComponent
        (firstFrame.realizeJones firstJones firstPhase ⨯ₑ₃
          secondFrame.realizeJones secondJones secondPhase) =
      plane.normalComponent secondFrame.propagationVector *
          Phasor.realize (firstJones.components 0) firstPhase *
            Phasor.realize (secondJones.components 1) secondPhase -
        plane.normalComponent firstFrame.propagationVector *
          Phasor.realize (firstJones.components 1) firstPhase *
            Phasor.realize (secondJones.components 0) secondPhase := by
  have hZeroZero :
      plane.normalComponent (firstFrame.axis 0 ⨯ₑ₃ secondFrame.axis 0) = 0 := by
    rw [hFirstAlign, hSecondAlign]
    have hcross : planeFrame.axis 0 ⨯ₑ₃ planeFrame.axis 0 = 0 := by
      ext i
      fin_cases i <;> simp [crossProduct] <;> ring
    rw [hcross]
    simp [OrientedAffineHyperplane.normalComponent]
  rw [firstFrame.realizeJones_eq_sum, secondFrame.realizeJones_eq_sum,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Space.add_cross, Space.cross_add, Space.smul_cross, Space.cross_smul,
    OrientedAffineHyperplane.normalComponent, inner_add_right, inner_smul_right]
  rw [show inner ℝ plane.normalVector (firstFrame.axis 0 ⨯ₑ₃ secondFrame.axis 0) = 0
      from hZeroZero,
    show inner ℝ plane.normalVector (firstFrame.axis 0 ⨯ₑ₃ secondFrame.axis 1) =
        plane.normalComponent secondFrame.propagationVector from
      normalComponent_axis_zero_cross_axis_one_of_axis_zero_eq
        plane planeFrame firstFrame secondFrame hFirstAlign hSecondAlign,
    show inner ℝ plane.normalVector (firstFrame.axis 1 ⨯ₑ₃ secondFrame.axis 0) =
        -plane.normalComponent firstFrame.propagationVector from
      normalComponent_axis_one_cross_axis_zero_of_axis_zero_eq
        plane planeFrame firstFrame secondFrame hFirstAlign hSecondAlign,
    show inner ℝ plane.normalVector (firstFrame.axis 1 ⨯ₑ₃ secondFrame.axis 1) = 0 from
      normalComponent_axis_one_cross_axis_one_of_axis_zero_eq
        plane planeFrame firstFrame secondFrame hFirstAlign hSecondAlign]
  simp only [OrientedAffineHyperplane.normalComponent]
  ring

/-- The exact stored-normal interference between two instantaneous Jones realizations and their
propagation-quarter-turn realizations in aligned frames.

The two carrier phases are independent. The result is purely real frame geometry and does not
assign incident or reflected roles to either frame. -/
lemma normalComponent_cross_realizeJones_propagationCross_add_swap
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (firstFrame : PolarizationFrame direction₁) (secondFrame : PolarizationFrame direction₂)
    (firstJones secondJones : JonesVector) (firstPhase secondPhase : ℝ)
    (hFirstAlign : firstFrame.axis 0 = planeFrame.axis 0)
    (hSecondAlign : secondFrame.axis 0 = planeFrame.axis 0) :
    plane.normalComponent
        (firstFrame.realizeJones firstJones firstPhase ⨯ₑ₃
              secondFrame.realizeJones secondJones.propagationCross secondPhase +
          secondFrame.realizeJones secondJones secondPhase ⨯ₑ₃
              firstFrame.realizeJones firstJones.propagationCross firstPhase) =
      (plane.normalComponent firstFrame.propagationVector +
          plane.normalComponent secondFrame.propagationVector) *
        (Phasor.realize (firstJones.components 0) firstPhase *
            Phasor.realize (secondJones.components 0) secondPhase +
          Phasor.realize (firstJones.components 1) firstPhase *
            Phasor.realize (secondJones.components 1) secondPhase) := by
  rw [show plane.normalComponent
      (firstFrame.realizeJones firstJones firstPhase ⨯ₑ₃
            secondFrame.realizeJones secondJones.propagationCross secondPhase +
        secondFrame.realizeJones secondJones secondPhase ⨯ₑ₃
            firstFrame.realizeJones firstJones.propagationCross firstPhase) =
      plane.normalComponent
          (firstFrame.realizeJones firstJones firstPhase ⨯ₑ₃
            secondFrame.realizeJones secondJones.propagationCross secondPhase) +
        plane.normalComponent
          (secondFrame.realizeJones secondJones secondPhase ⨯ₑ₃
            firstFrame.realizeJones firstJones.propagationCross firstPhase) by
    simp [OrientedAffineHyperplane.normalComponent, inner_add_right]]
  rw [normalComponent_cross_realizeJones_of_axis_zero_eq
      plane planeFrame firstFrame secondFrame firstJones secondJones.propagationCross
        firstPhase secondPhase hFirstAlign hSecondAlign,
    normalComponent_cross_realizeJones_of_axis_zero_eq
      plane planeFrame secondFrame firstFrame secondJones firstJones.propagationCross
        secondPhase firstPhase hSecondAlign hFirstAlign]
  simp only [JonesVector.propagationCross_components_zero,
    JonesVector.propagationCross_components_one]
  simp [Phasor.realize]
  ring

/-- Opposite signed propagation normals make the aligned Jones normal-interference term vanish
for arbitrary Jones data and independent carrier phases. -/
lemma normalComponent_cross_realizeJones_propagationCross_add_swap_eq_zero
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (firstFrame : PolarizationFrame direction₁) (secondFrame : PolarizationFrame direction₂)
    (firstJones secondJones : JonesVector) (firstPhase secondPhase : ℝ)
    (hFirstAlign : firstFrame.axis 0 = planeFrame.axis 0)
    (hSecondAlign : secondFrame.axis 0 = planeFrame.axis 0)
    (hNormal : plane.normalComponent secondFrame.propagationVector =
      -plane.normalComponent firstFrame.propagationVector) :
    plane.normalComponent
        (firstFrame.realizeJones firstJones firstPhase ⨯ₑ₃
              secondFrame.realizeJones secondJones.propagationCross secondPhase +
          secondFrame.realizeJones secondJones secondPhase ⨯ₑ₃
              firstFrame.realizeJones firstJones.propagationCross firstPhase) = 0 := by
  rw [normalComponent_cross_realizeJones_propagationCross_add_swap
    plane planeFrame firstFrame secondFrame firstJones secondJones firstPhase secondPhase
      hFirstAlign hSecondAlign, hNormal]
  ring

/-!

## C. Complex Jones amplitudes

-/

private lemma complexAxis_eq_ofReal (frame : PolarizationFrame direction) (i : Fin 2) :
    frame.complexAxis i = ComplexWaveVector.ofReal (frame.axis i) := rfl

/-- Tangential projection expresses a full-vector Jones amplitude in the common plane frame as
`(J₀, c J₁)`, where `c` is the signed normal component of the propagation vector. -/
lemma hyperplaneTangentialProjection_embedJones_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (frame : PolarizationFrame direction) (J : JonesVector)
    (halign : frame.axis 0 = planeFrame.axis 0) :
    ComplexWaveVector.hyperplaneTangentialProjection plane (frame.embedJones J) =
      planeFrame.embedJones
        (JonesVector.ofComponents (J.components 0)
          ((plane.normalComponent frame.propagationVector : ℂ) * J.components 1)) := by
  rw [embedJones, embedJones, Fin.sum_univ_two, Fin.sum_univ_two,
    ComplexWaveVector.hyperplaneTangentialProjection_add,
    ComplexWaveVector.hyperplaneTangentialProjection_smul,
    ComplexWaveVector.hyperplaneTangentialProjection_smul, complexAxis_eq_ofReal,
    complexAxis_eq_ofReal, ComplexWaveVector.hyperplaneTangentialProjection_ofReal,
    ComplexWaveVector.hyperplaneTangentialProjection_ofReal,
    tangentialProjection_axis_zero_of_axis_zero_eq
      (direction := direction) plane planeFrame frame halign,
    tangentialProjection_axis_one_of_axis_zero_eq
      (direction := direction) plane planeFrame frame halign]
  simp [complexAxis_eq_ofReal, ComplexWaveVector.ofReal_smul]
  module

/-- Tangential projection after the propagation quarter-turn has common plane-frame coordinates
`(-J₁, c J₀)`, with the same signed normal factor `c`. -/
lemma hyperplaneTangentialProjection_embedJones_propagationCross_of_axis_zero_eq
    (plane : OrientedAffineHyperplane 3) (planeFrame : PolarizationFrame plane.normal)
    (frame : PolarizationFrame direction) (J : JonesVector)
    (halign : frame.axis 0 = planeFrame.axis 0) :
    ComplexWaveVector.hyperplaneTangentialProjection plane
        (frame.embedJones J.propagationCross) =
      planeFrame.embedJones
        (JonesVector.ofComponents (-J.components 1)
          ((plane.normalComponent frame.propagationVector : ℂ) * J.components 0)) := by
  simpa using hyperplaneTangentialProjection_embedJones_of_axis_zero_eq
    (direction := direction) plane planeFrame frame J.propagationCross halign

end PolarizationFrame

end

end Optics
