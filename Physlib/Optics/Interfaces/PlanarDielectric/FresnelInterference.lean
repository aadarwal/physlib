/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelFlux

/-!
# Incident-reflected normal Poynting interference

## i. Overview

This file identifies the normal Poynting interference between real propagating incident and
reflected material Jones waves. If their frames share the same first axis in one interface plane
frame, the two cross terms have stored-normal component

```text
Y (chi_i + chi_r) (S_i S_r + P_i P_r),
```

where `S_a` and `P_a` are the instantaneous real Jones-coordinate realizations. Thus the normal
interference vanishes pointwise when `chi_r = -chi_i`. No common frequency or common carrier phase
is needed for this cancellation. A zero reflected electric field also cancels the interference
while retaining arbitrary dummy reflected carrier data.

The resulting pointwise theorem identifies the stored-normal Poynting flux of the actual
incident-plus-reflected fields with the sum of their separate instantaneous normal fluxes at the
stored interface point. It does not assert additivity of the full Poynting vector: its tangential
interference may be nonzero.

Integrating the pointwise identity gives additivity over every common interval. Fixed-frequency
phase matching is used only afterward to replace the active reflected and transmitted periods by
the incident period. Combined with the separate-wave Fresnel result, this proves the normal-flux
balance for the actual superposed negative-side field.

## ii. Key results

- `PlanarDielectricWaveConfiguration.incidentReflected_normalPoynting_interference_eq_zero`:
  guarded pointwise cancellation for the actual wave fields.
- `PlanarDielectricWaveConfiguration.incidentReflected_normalComponent_poyntingVector_add`:
  pointwise additivity of actual stored-normal flux at the interface point.
- `incidentReflected_normalComponent_intervalAverage_poyntingVector_add`:
  the corresponding additivity over every common averaging interval.
- `PlanarDielectricWaveConfiguration.fresnel_superposedWave_normalFlux_balance`: the connected
  fixed-frequency Fresnel balance for the actual superposed fields.
- `PlanarDielectricWaveConfiguration.fresnel_superposedWave_normalFlux_balance_of_incidenceFrames`:
  the canonical non-normal-incidence endpoint with a derived common `s` axis and reflection guard.

## iii. Table of contents

- A. Actual incident-reflected wave fields
- B. Common-interval normal-flux averages
- C. Superposed-wave Fresnel balance

## iv. Scope

The cancellation and common-interval identities require no Fresnel coefficient formula,
denominator, nonzero incident field, common frequency, phase matching, or transmitted wave. The
final balance additionally uses the existing lossless Fresnel result and fixed-frequency electric
boundary. None of the results states a whole-plane, aperture-power, modal-power, TIR, lossy-medium,
or scattering law.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Matrix Space Time
open scoped Interval

noncomputable section

namespace PlanarDielectricWaveConfiguration

variable {configuration : PlanarDielectricWaveConfiguration}
  {incidentDirection reflectedDirection transmittedDirection : Space.Direction 3}
  {incidentFrame : PolarizationFrame incidentDirection}
  {reflectedFrame : PolarizationFrame reflectedDirection}
  {transmittedFrame : PolarizationFrame transmittedDirection}
  {incidentJones reflectedJones transmittedJones : JonesVector}

private lemma normalComponent_intervalAverage
    (plane : OrientedAffineHyperplane 3) (field : ℝ → EuclideanSpace ℝ (Fin 3))
    (startTime endTime : ℝ)
    (hField : IntervalIntegrable field MeasureTheory.volume startTime endTime) :
    plane.normalComponent (⨍ time in startTime..endTime, field time) =
      ⨍ time in startTime..endTime, plane.normalComponent (field time) := by
  rw [interval_average_eq, interval_average_eq]
  simp only [OrientedAffineHyperplane.normalComponent, inner_smul_right, smul_eq_mul]
  simpa only [innerSL_apply_apply] using
    congrArg (fun value : ℝ ↦ (endTime - startTime)⁻¹ * value)
    ((innerSL ℝ plane.normalVector).intervalIntegral_comp_comm hField).symm

private lemma continuous_cross
    (firstField secondField : ℝ → EuclideanSpace ℝ (Fin 3))
    (hFirst : Continuous firstField) (hSecond : Continuous secondField) :
    Continuous fun time ↦ firstField time ⨯ₑ₃ secondField time := by
  change Continuous fun time ↦ WithLp.toLp 2
    (crossProduct (WithLp.equiv 2 (Fin 3 → ℝ) (firstField time))
      (WithLp.equiv 2 (Fin 3 → ℝ) (secondField time)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hFirstComponent (j : Fin 3) : Continuous fun time ↦ firstField time j :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) j).comp hFirst
  have hSecondComponent (j : Fin 3) : Continuous fun time ↦ secondField time j :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) j).comp hSecond
  fin_cases i
  · exact (hFirstComponent 1).mul (hSecondComponent 2) |>.sub
      ((hFirstComponent 2).mul (hSecondComponent 1))
  · exact (hFirstComponent 2).mul (hSecondComponent 0) |>.sub
      ((hFirstComponent 0).mul (hSecondComponent 2))
  · exact (hFirstComponent 0).mul (hSecondComponent 1) |>.sub
      ((hFirstComponent 1).mul (hSecondComponent 0))

private lemma normalComponent_intervalAverage_add_of_pointwise
    (plane : OrientedAffineHyperplane 3)
    (totalField firstField secondField : ℝ → EuclideanSpace ℝ (Fin 3))
    (startTime endTime : ℝ) (hTotal : Continuous totalField)
    (hFirst : Continuous firstField) (hSecond : Continuous secondField)
    (hAdd : ∀ time, plane.normalComponent (totalField time) =
      plane.normalComponent (firstField time) + plane.normalComponent (secondField time)) :
    plane.normalComponent (⨍ time in startTime..endTime, totalField time) =
      plane.normalComponent (⨍ time in startTime..endTime, firstField time) +
        plane.normalComponent (⨍ time in startTime..endTime, secondField time) := by
  have hTotalIntegrable :
      IntervalIntegrable totalField MeasureTheory.volume startTime endTime :=
    hTotal.intervalIntegrable startTime endTime
  have hFirstIntegrable :
      IntervalIntegrable firstField MeasureTheory.volume startTime endTime :=
    hFirst.intervalIntegrable startTime endTime
  have hSecondIntegrable :
      IntervalIntegrable secondField MeasureTheory.volume startTime endTime :=
    hSecond.intervalIntegrable startTime endTime
  have hFirstNormal : Continuous fun time ↦ plane.normalComponent (firstField time) := by
    change Continuous fun time ↦ inner ℝ plane.normalVector (firstField time)
    exact continuous_const.inner hFirst
  have hSecondNormal : Continuous fun time ↦ plane.normalComponent (secondField time) := by
    change Continuous fun time ↦ inner ℝ plane.normalVector (secondField time)
    exact continuous_const.inner hSecond
  rw [normalComponent_intervalAverage _ _ _ _ hTotalIntegrable,
    normalComponent_intervalAverage _ _ _ _ hFirstIntegrable,
    normalComponent_intervalAverage _ _ _ _ hSecondIntegrable]
  calc
    (⨍ time in startTime..endTime, plane.normalComponent (totalField time)) =
        ⨍ time in startTime..endTime,
          plane.normalComponent (firstField time) + plane.normalComponent (secondField time) := by
      congr 1
      funext time
      exact hAdd time
    _ = _ := by
      rw [interval_average_eq, interval_average_eq, interval_average_eq,
        intervalIntegral.integral_add (hFirstNormal.intervalIntegrable startTime endTime)
          (hSecondNormal.intervalIntegrable startTime endTime), smul_add]

private lemma continuous_electricField_planePoint
    {plane : OrientedAffineHyperplane 3} {medium : HomogeneousIsotropicMedium}
    {wave : ComplexMonochromaticPlaneWave} {direction : Space.Direction 3}
    {frame : PolarizationFrame direction} {J : JonesVector}
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J) :
    Continuous fun time : ℝ ↦ wave.electricField (time : Time) plane.point := by
  rw [show (fun time : ℝ ↦ wave.electricField (time : Time) plane.point) =
    fun time ↦ frame.realizeJones J (wave.angularFrequency * time) by
    funext time
    exact h.electricField_planePoint (time : Time)]
  change Continuous fun time : ℝ ↦
    Phasor.realizeEuclidean (frame.embedJones J) (wave.angularFrequency * time)
  exact (Phasor.continuous_realizeEuclidean _).comp (by fun_prop)

private lemma continuous_magneticFieldStrength_planePoint
    {plane : OrientedAffineHyperplane 3} {medium : HomogeneousIsotropicMedium}
    {wave : ComplexMonochromaticPlaneWave} {direction : Space.Direction 3}
    {frame : PolarizationFrame direction} {J : JonesVector}
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J) :
    Continuous fun time : ℝ ↦
      wave.magneticFieldStrength medium (time : Time) plane.point := by
  rw [show (fun time : ℝ ↦ wave.magneticFieldStrength medium (time : Time) plane.point) =
    fun time ↦ medium.waveImpedance⁻¹ •
      frame.realizeJones J.propagationCross (wave.angularFrequency * time) by
    funext time
    exact h.magneticFieldStrength_planePoint (time : Time)]
  change Continuous fun time : ℝ ↦ medium.waveImpedance⁻¹ •
    Phasor.realizeEuclidean (frame.embedJones J.propagationCross)
      (wave.angularFrequency * time)
  have hPhase : Continuous fun time : ℝ ↦ wave.angularFrequency * time := by fun_prop
  have hRealize : Continuous fun time : ℝ ↦
      Phasor.realizeEuclidean (frame.embedJones J.propagationCross)
        (wave.angularFrequency * time) :=
    (Phasor.continuous_realizeEuclidean (frame.embedJones J.propagationCross)).comp hPhase
  exact hRealize.const_smul (medium.waveImpedance⁻¹ : ℝ)

/-!

## A. Actual incident-reflected wave fields

-/

/-- The normal incident-reflected Poynting interference of the actual wave fields vanishes
pointwise at the stored interface point.

The active reflected branch uses opposite signed propagation normals. In the zero-field branch,
the reflected carrier normal and frequency remain arbitrary; the common-axis hypothesis is retained
uniformly across both branches. -/
lemma incidentReflected_normalPoynting_interference_eq_zero
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (time : Time) :
    configuration.interface.plane.normalComponent
        (configuration.incident.electricField time configuration.interface.plane.point ⨯ₑ₃
              configuration.reflected.magneticFieldStrength
                configuration.interface.negativeMedium time configuration.interface.plane.point +
          configuration.reflected.electricField time configuration.interface.plane.point ⨯ₑ₃
              configuration.incident.magneticFieldStrength
                configuration.interface.negativeMedium time
                  configuration.interface.plane.point) = 0 := by
  rw [hIncident.electricField_planePoint, hReflected.magneticFieldStrength_planePoint,
    hReflected.electricField_planePoint, hIncident.magneticFieldStrength_planePoint,
    Space.cross_smul, Space.cross_smul, ← smul_add,
    OrientedAffineHyperplane.normalComponent, inner_smul_right]
  have hFrame : inner ℝ configuration.interface.plane.normalVector
        (incidentFrame.realizeJones incidentJones
                (configuration.incident.angularFrequency * (time : ℝ)) ⨯ₑ₃
              reflectedFrame.realizeJones reflectedJones.propagationCross
                (configuration.reflected.angularFrequency * (time : ℝ)) +
          reflectedFrame.realizeJones reflectedJones
                (configuration.reflected.angularFrequency * (time : ℝ)) ⨯ₑ₃
              incidentFrame.realizeJones incidentJones.propagationCross
                (configuration.incident.angularFrequency * (time : ℝ))) = 0 := by
    rcases hReflection with hZero | hNormal
    · have hJones : reflectedJones.components = 0 :=
        hReflected.components_eq_zero_of_electricAmplitude_eq_zero hZero
      calc
        _ = (configuration.interface.plane.normalComponent incidentFrame.propagationVector +
              configuration.interface.plane.normalComponent reflectedFrame.propagationVector) *
            (Phasor.realize (incidentJones.components 0)
                  (configuration.incident.angularFrequency * (time : ℝ)) *
                Phasor.realize (reflectedJones.components 0)
                  (configuration.reflected.angularFrequency * (time : ℝ)) +
              Phasor.realize (incidentJones.components 1)
                  (configuration.incident.angularFrequency * (time : ℝ)) *
                Phasor.realize (reflectedJones.components 1)
                  (configuration.reflected.angularFrequency * (time : ℝ))) :=
          PolarizationFrame.normalComponent_cross_realizeJones_propagationCross_add_swap
            configuration.interface.plane planeFrame incidentFrame reflectedFrame incidentJones
              reflectedJones
              (configuration.incident.angularFrequency * (time : ℝ))
              (configuration.reflected.angularFrequency * (time : ℝ))
              hIncidentAlign hReflectedAlign
        _ = 0 := by simp [hJones, Phasor.realize]
    · exact
        PolarizationFrame.normalComponent_cross_realizeJones_propagationCross_add_swap_eq_zero
          configuration.interface.plane planeFrame incidentFrame reflectedFrame incidentJones
            reflectedJones
            (configuration.incident.angularFrequency * (time : ℝ))
            (configuration.reflected.angularFrequency * (time : ℝ))
            hIncidentAlign hReflectedAlign hNormal
  rw [hFrame, mul_zero]

/-- At the stored interface point, the actual incident-plus-reflected field has instantaneous
stored-normal Poynting flux equal to the sum of the two waves' separate normal fluxes.

Only the normal component is additive; the full Poynting vector may retain tangential
interference. -/
lemma incidentReflected_normalComponent_poyntingVector_add
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (time : Time) :
    configuration.interface.plane.normalComponent
        (ThreeDimension.poyntingVector
          (configuration.incident.electricField + configuration.reflected.electricField)
          (configuration.incident.magneticFieldStrength configuration.interface.negativeMedium +
            configuration.reflected.magneticFieldStrength configuration.interface.negativeMedium)
          time configuration.interface.plane.point) =
      configuration.interface.plane.normalComponent
          (ThreeDimension.poyntingVector configuration.incident.electricField
            (configuration.incident.magneticFieldStrength
              configuration.interface.negativeMedium)
            time configuration.interface.plane.point) +
        configuration.interface.plane.normalComponent
          (ThreeDimension.poyntingVector configuration.reflected.electricField
            (configuration.reflected.magneticFieldStrength
              configuration.interface.negativeMedium)
            time configuration.interface.plane.point) := by
  have hInterference := incidentReflected_normalPoynting_interference_eq_zero
    planeFrame hIncident hReflected hIncidentAlign hReflectedAlign hReflection time
  change configuration.interface.plane.normalComponent
      ((configuration.incident.electricField time configuration.interface.plane.point +
          configuration.reflected.electricField time configuration.interface.plane.point) ⨯ₑ₃
        (configuration.incident.magneticFieldStrength configuration.interface.negativeMedium
            time configuration.interface.plane.point +
          configuration.reflected.magneticFieldStrength configuration.interface.negativeMedium
            time configuration.interface.plane.point)) =
    configuration.interface.plane.normalComponent
        (configuration.incident.electricField time configuration.interface.plane.point ⨯ₑ₃
          configuration.incident.magneticFieldStrength configuration.interface.negativeMedium
            time configuration.interface.plane.point) +
      configuration.interface.plane.normalComponent
        (configuration.reflected.electricField time configuration.interface.plane.point ⨯ₑ₃
          configuration.reflected.magneticFieldStrength configuration.interface.negativeMedium
            time configuration.interface.plane.point)
  rw [Space.add_cross, Space.cross_add, Space.cross_add]
  simp only [OrientedAffineHyperplane.normalComponent, inner_add_right] at hInterference ⊢
  linear_combination hInterference

/-!

## B. Common-interval normal-flux averages

-/

/-- Over every common real-time interval, the stored-normal mean Poynting flux of the actual
incident-plus-reflected fields equals the sum of their separate stored-normal mean fluxes at the
interface point.

This follows from pointwise normal-interference cancellation and requires no frequency matching.
The statement remains normal-only: it does not identify the full vector averages. -/
lemma incidentReflected_normalComponent_intervalAverage_poyntingVector_add
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (startTime endTime : ℝ) :
    configuration.interface.plane.normalComponent
        (⨍ time in startTime..endTime,
          ThreeDimension.poyntingVector
            (configuration.incident.electricField + configuration.reflected.electricField)
            (configuration.incident.magneticFieldStrength
                configuration.interface.negativeMedium +
              configuration.reflected.magneticFieldStrength
                configuration.interface.negativeMedium)
            (time : Time) configuration.interface.plane.point) =
      configuration.interface.plane.normalComponent
          (⨍ time in startTime..endTime,
            ThreeDimension.poyntingVector configuration.incident.electricField
              (configuration.incident.magneticFieldStrength
                configuration.interface.negativeMedium)
              (time : Time) configuration.interface.plane.point) +
        configuration.interface.plane.normalComponent
          (⨍ time in startTime..endTime,
            ThreeDimension.poyntingVector configuration.reflected.electricField
              (configuration.reflected.magneticFieldStrength
                configuration.interface.negativeMedium)
              (time : Time) configuration.interface.plane.point) := by
  have hIncidentGuarded : IsZeroOrReferencedMaterialJonesWave
      configuration.interface.plane configuration.interface.negativeMedium
        configuration.incident incidentFrame incidentJones :=
    Or.inr hIncident
  apply normalComponent_intervalAverage_add_of_pointwise
  · exact continuous_cross _ _
      ((continuous_electricField_planePoint hIncidentGuarded).add
        (continuous_electricField_planePoint hReflected))
      ((continuous_magneticFieldStrength_planePoint hIncidentGuarded).add
        (continuous_magneticFieldStrength_planePoint hReflected))
  · exact continuous_cross _ _ (continuous_electricField_planePoint hIncidentGuarded)
      (continuous_magneticFieldStrength_planePoint hIncidentGuarded)
  · exact continuous_cross _ _ (continuous_electricField_planePoint hReflected)
      (continuous_magneticFieldStrength_planePoint hReflected)
  · intro time
    exact incidentReflected_normalComponent_poyntingVector_add planeFrame hIncident hReflected
      hIncidentAlign hReflectedAlign hReflection (time : Time)

/-- Over one incident period, the stored-normal mean flux of the superposed negative-side fields
equals the incident own-period mean plus the reflected own-period mean.

An active reflected wave must share the incident frequency. An electrically zero reflected wave
retains arbitrary dummy frequency data. -/
lemma incidentReflected_normalComponent_intervalAverage_poyntingVector_add_ownPeriods
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hFrequency : configuration.reflected.electricAmplitude = 0 ∨
      configuration.reflected.angularFrequency = configuration.incident.angularFrequency)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (startTime : Time) :
    configuration.interface.plane.normalComponent
        (⨍ time in startTime.val..startTime.val +
            2 * Real.pi / configuration.incident.angularFrequency,
          ThreeDimension.poyntingVector
            (configuration.incident.electricField + configuration.reflected.electricField)
            (configuration.incident.magneticFieldStrength
                configuration.interface.negativeMedium +
              configuration.reflected.magneticFieldStrength
                configuration.interface.negativeMedium)
            (time : Time) configuration.interface.plane.point) =
      configuration.interface.plane.normalComponent
          (⨍ time in startTime.val..startTime.val +
              2 * Real.pi / configuration.incident.angularFrequency,
            ThreeDimension.poyntingVector configuration.incident.electricField
              (configuration.incident.magneticFieldStrength
                configuration.interface.negativeMedium)
              (time : Time) configuration.interface.plane.point) +
        configuration.interface.plane.normalComponent
          (⨍ time in startTime.val..startTime.val +
              2 * Real.pi / configuration.reflected.angularFrequency,
            ThreeDimension.poyntingVector configuration.reflected.electricField
              (configuration.reflected.magneticFieldStrength
                configuration.interface.negativeMedium)
              (time : Time) configuration.interface.plane.point) := by
  have hCommon := incidentReflected_normalComponent_intervalAverage_poyntingVector_add
    planeFrame hIncident hReflected hIncidentAlign hReflectedAlign hReflection startTime.val
      (startTime.val + 2 * Real.pi / configuration.incident.angularFrequency)
  rw [hReflected.normalComponent_intervalAverage_poyntingVector_planePoint_eq_ownPeriod
    configuration.incident.angularFrequency hFrequency startTime] at hCommon
  exact hCommon

/-!

## C. Superposed-wave Fresnel balance

-/

/-- Normal-flux balance between the actual superposed negative-side field and the transmitted
field, both averaged over the incident carrier period at the stored interface point. -/
def HasSuperposedWaveNormalFluxBalance (configuration : PlanarDielectricWaveConfiguration)
    (startTime : Time) : Prop :=
  configuration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / configuration.incident.angularFrequency,
        ThreeDimension.poyntingVector
          (configuration.incident.electricField + configuration.reflected.electricField)
          (configuration.incident.magneticFieldStrength configuration.interface.negativeMedium +
            configuration.reflected.magneticFieldStrength
              configuration.interface.negativeMedium)
          (time : Time) configuration.interface.plane.point) =
    configuration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / configuration.incident.angularFrequency,
        ThreeDimension.poyntingVector configuration.transmitted.electricField
          (configuration.transmitted.magneticFieldStrength
            configuration.interface.positiveMedium)
          (time : Time) configuration.interface.plane.point)

/-- The connected fixed-frequency Fresnel boundary satisfies normal-flux balance for the actual
superposed incident-plus-reflected field and the transmitted field at the stored interface point.

The proof reuses the separate-wave Fresnel balance. Fixed-frequency phase matching changes only
the reflected and transmitted period labels; normal interference already vanishes pointwise. -/
lemma fresnel_superposedWave_normalFlux_balance
    (hElectric : configuration.IsFixedFrequencyElectricBoundary)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hTransmittedNormal : 0 ≤
      configuration.interface.plane.normalComponent transmittedFrame.propagationVector)
    (startTime : Time) :
    configuration.HasSuperposedWaveNormalFluxBalance startTime := by
  have hTransmittedFrequency := hElectric.1.1.1
  have hReflectedFrequency : configuration.reflected.electricAmplitude = 0 ∨
      configuration.reflected.angularFrequency = configuration.incident.angularFrequency :=
    hElectric.1.2.imp id And.left
  have hCombined := incidentReflected_normalComponent_intervalAverage_poyntingVector_add_ownPeriods
    planeFrame hIncident hReflected hIncidentAlign hReflectedAlign hReflectedFrequency hReflection
      startTime
  have hSeparate := fresnel_separateWave_normalFlux_balance hElectric.2 hMagnetic planeFrame
    hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign hReflection
      hIncidentNormal hTransmittedNormal startTime
  rw [HasSuperposedWaveNormalFluxBalance, hCombined]
  rw [HasSeparateWaveNormalFluxBalance] at hSeparate
  simpa only [hTransmittedFrequency] using hSeparate

/-- A fixed-frequency boundary with canonical non-normal incidence frames satisfies normal-flux
balance for the actual superposed incident-plus-reflected field and the transmitted field.

The canonical-frame hypotheses and tangential phase matching give the common `s` axis. The
referenced connector data, phase matching, and explicit incident/reflected sign hypotheses give
the exact active reflected-normal equality required by the connected Fresnel endpoint. A zero
reflected field retains arbitrary dummy carrier and frame labels. -/
lemma fresnel_superposedWave_normalFlux_balance_of_incidenceFrames
    (hElectric : configuration.IsFixedFrequencyElectricBoundary)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentNonNormal : IsNonNormalIncidence incidentDirection
      configuration.interface.plane.normal)
    (hTransmittedNonNormal : IsNonNormalIncidence transmittedDirection
      configuration.interface.plane.normal)
    (hIncidentCanonical : incidentFrame = incidencePolarizationFrame incidentDirection
      configuration.interface.plane.normal hIncidentNonNormal)
    (hTransmittedCanonical : transmittedFrame = incidencePolarizationFrame transmittedDirection
      configuration.interface.plane.normal hTransmittedNonNormal)
    (hReflectedCanonical : configuration.reflected.electricAmplitude ≠ 0 →
      ∃ hReflectedNonNormal : IsNonNormalIncidence reflectedDirection
          configuration.interface.plane.normal,
        reflectedFrame = incidencePolarizationFrame reflectedDirection
          configuration.interface.plane.normal hReflectedNonNormal)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hReflectedNormal : configuration.reflected.electricAmplitude ≠ 0 →
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector < 0)
    (hTransmittedNormal : 0 ≤
      configuration.interface.plane.normalComponent transmittedFrame.propagationVector)
    (startTime : Time) :
    configuration.HasSuperposedWaveNormalFluxBalance startTime := by
  let planeFrame := incidencePlaneFrame configuration.interface.plane incidentDirection
    hIncidentNonNormal
  have hData := hElectric.1.canonicalIncidenceFrame_data hIncident hReflected hTransmitted
    hIncidentNonNormal hTransmittedNonNormal hIncidentCanonical hTransmittedCanonical
      hReflectedCanonical hIncidentNormal hReflectedNormal
  change incidentFrame.axis 0 = planeFrame.axis 0 ∧
    transmittedFrame.axis 0 = planeFrame.axis 0 ∧
      (configuration.reflected.electricAmplitude = 0 ∨
        reflectedFrame.axis 0 = planeFrame.axis 0 ∧
          reflectedFrame.propagationVector =
            configuration.interface.plane.vectorReflection incidentFrame.propagationVector) at hData
  rcases hData with ⟨hIncidentAlign, hTransmittedAlign, hReflectedData⟩
  by_cases hZero : configuration.reflected.electricAmplitude = 0
  · have hReflectedZero := hReflected.reframe_of_electricAmplitude_eq_zero planeFrame hZero
    exact fresnel_superposedWave_normalFlux_balance hElectric hMagnetic planeFrame hIncident
      hReflectedZero hTransmitted hIncidentAlign rfl hTransmittedAlign (Or.inl hZero)
        hIncidentNormal hTransmittedNormal startTime
  · rcases hReflectedData.resolve_left hZero with ⟨hReflectedAlign, hReflection⟩
    have hNormal : configuration.interface.plane.normalComponent
          reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector := by
      rw [hReflection, configuration.interface.plane.normalComponent_vectorReflection]
    exact fresnel_superposedWave_normalFlux_balance hElectric hMagnetic planeFrame hIncident
      hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign (Or.inr hNormal)
        hIncidentNormal hTransmittedNormal startTime

end PlanarDielectricWaveConfiguration

end

end Optics
