/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Conservation
public import Physlib.Optics.Network.FlatNetlistRephase

/-!
# Convention-free conservation for linear behaviors

## i. Overview

This file defines passivity and power preservation directly for a `LinearBehavior` between
separately typed input and output mode families. A relation has the property when every pair in
the relation satisfies the corresponding modal-power inequality or equality. The definition is
singular-safe: it asserts neither existence nor uniqueness of an output.

For a graph behavior, the relational predicates agree exactly with the existing rectangular
`ModeTransform.IsPassive` and `ModeTransform.IsPowerPreserving` predicates. Relabeling and
rephasing preserve both classifications without identifying the input and output types.

For a `FlatNetlist`, component passivity or power preservation lifts first to every complete
solution's exposed external readout and then to the singular-safe external behavior. A response
transform is compared with that behavior only under the existing named `FlatNetlist.IsWellPosed`
gate. Matched-gauge covariance uses `PortConnectionFamily.IsMatchedGauge` from
`ConnectionRoutingRephase.lean`; independent endpoint phases are not treated as a unit wire.

This discharges the `goal.md:1942-1943` item:
"convention-free port/network power, passivity, and losslessness predicates that do not require
time-reversal data;". Here the convention-free losslessness classification is called power
preservation, matching the rectangular transform API.

## ii. Key results

- `LinearBehavior.IsPassive` and `LinearBehavior.IsPowerPreserving`: singular-safe relational
  predicates on separately typed boundaries.
- `ModeTransform.toBehavior_isPassive_iff` and
  `ModeTransform.toBehavior_isPowerPreserving_iff`: exact agreement with rectangular transforms.
- `LinearBehavior.isPassive_reindex_iff` and `LinearBehavior.isPassive_rephase_iff`, with
  power-preserving analogues: covariance without an input/output pairing.
- `FlatNetlist.external_power_le_of_mem_solutionBehavior` and
  `FlatNetlist.external_power_eq_of_mem_solutionBehavior`: conservation at every complete
  solution, without well-posedness.
- `FlatNetlist.behavior_isPassive_of_scattering` and
  `FlatNetlist.behavior_isPowerPreserving_of_scattering`: singular-safe external classifications.
- `FlatNetlist.behavior_isPassive_iff_responseTransform_isPassive` and its power-preserving
  analogue: response agreement only under the named well-posedness gate.
- `FlatNetlist.rephasedBehavior_isPassive_iff` and its companion results: matched-gauge
  covariance of the actual netlist relation and gated response.

## iii. Table of contents

- A. Relational passivity and power preservation
- B. Agreement with rectangular transforms
- C. Relabeling and rephasing covariance
- D. Singular-safe flat-netlist lifts
- E. Matched-gauge netlist covariance

## iv. References

Every quantity here is `ModeAmplitude.power`, the squared `L²` norm of a finite family of
power-normalized modal amplitudes. This is amplitude-squared bookkeeping, not an electromagnetic
energy or power theorem. No statement supplies a flux normalization, time-reversal pairing,
scattering interpretation, physical-port pairing, reciprocity, reference plane, propagation law,
or physical losslessness claim.

The input and output types remain independent in every definition and lemma. Relabeling uses one
equivalence within each side, never an equivalence between the two boundaries. The raw
`FlatNetlist.solutionBehavior` is not itself called passive: its output is a complete internal
state, so the solution lemmas classify only the derived external readout.

The matched-gauge condition is the directed mate law of
`Physlib/Optics/Network/ConnectionRoutingRephase.lean`. It is structural coordinate covariance,
not time reversal or a claim that arbitrary independent endpoint rephasings preserve unit routing.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x

/-!
## A. Relational passivity and power preservation
-/

namespace LinearBehavior

variable {input : Type u} {output : Type v}

/-- A finite linear behavior is passive when every related output has no more normalized modal
power than its input. This property does not assert that an output exists or is unique. -/
def IsPassive [Fintype input] [Fintype output]
    (behavior : LinearBehavior input output) : Prop :=
  ∀ ⦃inputAmplitude outputAmplitude⦄,
    (inputAmplitude, outputAmplitude) ∈ behavior →
      outputAmplitude.power ≤ inputAmplitude.power

/-- A finite linear behavior is power-preserving when every related input/output pair has equal
normalized modal power. This property does not assert that an output exists or is unique. -/
def IsPowerPreserving [Fintype input] [Fintype output]
    (behavior : LinearBehavior input output) : Prop :=
  ∀ ⦃inputAmplitude outputAmplitude⦄,
    (inputAmplitude, outputAmplitude) ∈ behavior →
      outputAmplitude.power = inputAmplitude.power

/-- Every power-preserving linear behavior is passive. -/
lemma IsPowerPreserving.isPassive [Fintype input] [Fintype output]
    {behavior : LinearBehavior input output} (hPower : behavior.IsPowerPreserving) :
    behavior.IsPassive := by
  intro inputAmplitude outputAmplitude hMember
  exact le_of_eq (hPower hMember)

end LinearBehavior

/-!
## B. Agreement with rectangular transforms
-/

namespace ModeTransform

variable {input : Type u} {output : Type v}

/-- Relational passivity of a transform graph is exactly rectangular transform passivity. -/
lemma toBehavior_isPassive_iff [Fintype input] [DecidableEq input] [Fintype output]
    (transform : ModeTransform input output) :
    transform.toBehavior.IsPassive ↔ transform.IsPassive := by
  constructor
  · intro hBehavior inputAmplitude
    apply hBehavior
    exact (transform.mem_toBehavior_iff_toLinearMap inputAmplitude
      (transform.toLinearMap inputAmplitude)).mpr rfl
  · intro hTransform inputAmplitude outputAmplitude hMember
    rw [(transform.mem_toBehavior_iff_toLinearMap inputAmplitude outputAmplitude).mp hMember]
    exact hTransform inputAmplitude

/-- Relational power preservation of a transform graph is exactly rectangular transform power
preservation. -/
lemma toBehavior_isPowerPreserving_iff [Fintype input] [DecidableEq input] [Fintype output]
    (transform : ModeTransform input output) :
    transform.toBehavior.IsPowerPreserving ↔ transform.IsPowerPreserving := by
  constructor
  · intro hBehavior inputAmplitude
    apply hBehavior
    exact (transform.mem_toBehavior_iff_toLinearMap inputAmplitude
      (transform.toLinearMap inputAmplitude)).mpr rfl
  · intro hTransform inputAmplitude outputAmplitude hMember
    rw [(transform.mem_toBehavior_iff_toLinearMap inputAmplitude outputAmplitude).mp hMember]
    exact hTransform inputAmplitude

end ModeTransform

/-!
## C. Relabeling and rephasing covariance
-/

namespace LinearBehavior

variable {input : Type u} {output : Type v}
variable {newInput : Type w} {newOutput : Type x}

/-- Relabeling the input and output sides independently preserves and reflects relational
passivity. No equivalence between the two boundary types is used. -/
lemma isPassive_reindex_iff [Fintype input] [Fintype output]
    [Fintype newInput] [Fintype newOutput]
    (inputEquiv : input ≃ newInput) (outputEquiv : output ≃ newOutput)
    (behavior : LinearBehavior input output) :
    (behavior.reindex inputEquiv outputEquiv).IsPassive ↔ behavior.IsPassive := by
  constructor
  · intro hReindexed inputAmplitude outputAmplitude hMember
    have hTransported :
        (ModeAmplitude.reindex inputEquiv inputAmplitude,
            ModeAmplitude.reindex outputEquiv outputAmplitude) ∈
          behavior.reindex inputEquiv outputEquiv := by
      rw [LinearBehavior.mem_reindex_iff]
      simpa only [ModeAmplitude.reindex_symm_reindex] using hMember
    simpa only [ModeAmplitude.power_reindex] using hReindexed hTransported
  · intro hBehavior inputAmplitude outputAmplitude hMember
    rw [LinearBehavior.mem_reindex_iff] at hMember
    simpa only [ModeAmplitude.power_reindex] using hBehavior hMember

/-- Relabeling the input and output sides independently preserves and reflects relational power
preservation. -/
lemma isPowerPreserving_reindex_iff [Fintype input] [Fintype output]
    [Fintype newInput] [Fintype newOutput]
    (inputEquiv : input ≃ newInput) (outputEquiv : output ≃ newOutput)
    (behavior : LinearBehavior input output) :
    (behavior.reindex inputEquiv outputEquiv).IsPowerPreserving ↔
      behavior.IsPowerPreserving := by
  constructor
  · intro hReindexed inputAmplitude outputAmplitude hMember
    have hTransported :
        (ModeAmplitude.reindex inputEquiv inputAmplitude,
            ModeAmplitude.reindex outputEquiv outputAmplitude) ∈
          behavior.reindex inputEquiv outputEquiv := by
      rw [LinearBehavior.mem_reindex_iff]
      simpa only [ModeAmplitude.reindex_symm_reindex] using hMember
    simpa only [ModeAmplitude.power_reindex] using hReindexed hTransported
  · intro hBehavior inputAmplitude outputAmplitude hMember
    rw [LinearBehavior.mem_reindex_iff] at hMember
    simpa only [ModeAmplitude.power_reindex] using hBehavior hMember

/-- Independent unit-phase coordinate changes preserve and reflect relational passivity. -/
lemma isPassive_rephase_iff [Fintype input] [Fintype output]
    (inputGauge : ModePhaseGauge input) (outputGauge : ModePhaseGauge output)
    (behavior : LinearBehavior input output) :
    (behavior.rephase inputGauge outputGauge).IsPassive ↔ behavior.IsPassive := by
  constructor
  · intro hRephased inputAmplitude outputAmplitude hMember
    have hTransported :
        (ModeAmplitude.rephase inputGauge inputAmplitude,
            ModeAmplitude.rephase outputGauge outputAmplitude) ∈
          behavior.rephase inputGauge outputGauge := by
      rw [LinearBehavior.mem_rephase_iff]
      simpa only [ModeAmplitude.rephase_inv_rephase] using hMember
    simpa only [ModeAmplitude.power_rephase] using hRephased hTransported
  · intro hBehavior inputAmplitude outputAmplitude hMember
    rw [LinearBehavior.mem_rephase_iff] at hMember
    simpa only [ModeAmplitude.power_rephase] using hBehavior hMember

/-- Independent unit-phase coordinate changes preserve and reflect relational power
preservation. -/
lemma isPowerPreserving_rephase_iff [Fintype input] [Fintype output]
    (inputGauge : ModePhaseGauge input) (outputGauge : ModePhaseGauge output)
    (behavior : LinearBehavior input output) :
    (behavior.rephase inputGauge outputGauge).IsPowerPreserving ↔
      behavior.IsPowerPreserving := by
  constructor
  · intro hRephased inputAmplitude outputAmplitude hMember
    have hTransported :
        (ModeAmplitude.rephase inputGauge inputAmplitude,
            ModeAmplitude.rephase outputGauge outputAmplitude) ∈
          behavior.rephase inputGauge outputGauge := by
      rw [LinearBehavior.mem_rephase_iff]
      simpa only [ModeAmplitude.rephase_inv_rephase] using hMember
    simpa only [ModeAmplitude.power_rephase] using hRephased hTransported
  · intro hBehavior inputAmplitude outputAmplitude hMember
    rw [LinearBehavior.mem_rephase_iff] at hMember
    simpa only [ModeAmplitude.power_rephase] using hBehavior hMember

end LinearBehavior

/-!
## D. Singular-safe flat-netlist lifts
-/

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})
variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate channels, local to finite conservation statements. -/
local instance linearBehaviorConservationChannelDecidableEq :
    DecidableEq netlist.Channel :=
  Classical.decEq _

/-- Classical equality on connected channels, local to finite conservation statements. -/
local instance linearBehaviorConservationConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel :=
  Classical.decEq _

/-- The external complement of finite aggregate and connected channel families is finite. -/
local instance linearBehaviorConservationExternalChannelFintype :
    Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- Every complete solution of a netlist with a passive assembled component transform has an
external readout whose normalized modal power does not exceed the exposed input power.

This is unconditional in solver terms: `hSolution` supplies the particular complete solution, and
no existence, uniqueness, or well-posedness assumption is added. -/
lemma external_power_le_of_mem_solutionBehavior
    (hScattering : netlist.scatteringTransform.IsPassive)
    (inputAmplitude : ModeAmplitude netlist.ExternalIncident)
    (state : ModeAmplitude netlist.SolutionIndex)
    (hSolution : (inputAmplitude, state) ∈ netlist.solutionBehavior) :
    (netlist.outputReadout.toLinearMap state.restrictInr).power ≤ inputAmplitude.power := by
  classical
  have hDisplayed :
      (inputAmplitude, state.restrictInl.directSum state.restrictInr) ∈
        netlist.solutionBehavior := by
    simpa only [ModeAmplitude.directSum_restrict] using hSolution
  rcases (netlist.mem_solutionBehavior_directSum_iff inputAmplitude
    state.restrictInl state.restrictInr).mp hDisplayed with ⟨hComponent, hIncident⟩
  apply netlist.power_le_of_isPassive hScattering inputAmplitude _
  exact (netlist.mem_behavior_iff_componentBehavior inputAmplitude _).mpr
    ⟨state.restrictInl, state.restrictInr, hComponent, hIncident, rfl⟩

/-- Every complete solution of a netlist with a power-preserving assembled component transform has
an external readout with exactly the exposed input's normalized modal power.

The displayed complete solution is the only solver hypothesis. -/
lemma external_power_eq_of_mem_solutionBehavior
    (hScattering : netlist.scatteringTransform.IsPowerPreserving)
    (inputAmplitude : ModeAmplitude netlist.ExternalIncident)
    (state : ModeAmplitude netlist.SolutionIndex)
    (hSolution : (inputAmplitude, state) ∈ netlist.solutionBehavior) :
    (netlist.outputReadout.toLinearMap state.restrictInr).power = inputAmplitude.power := by
  classical
  have hDisplayed :
      (inputAmplitude, state.restrictInl.directSum state.restrictInr) ∈
        netlist.solutionBehavior := by
    simpa only [ModeAmplitude.directSum_restrict] using hSolution
  rcases (netlist.mem_solutionBehavior_directSum_iff inputAmplitude
    state.restrictInl state.restrictInr).mp hDisplayed with ⟨hComponent, hIncident⟩
  apply netlist.power_eq_of_isPowerPreserving hScattering inputAmplitude _
  exact (netlist.mem_behavior_iff_componentBehavior inputAmplitude _).mpr
    ⟨state.restrictInl, state.restrictInr, hComponent, hIncident, rfl⟩

/-- Passive assembled component scattering makes the singular-safe external relation passive. -/
lemma behavior_isPassive_of_scattering
    (hScattering : netlist.scatteringTransform.IsPassive) :
    netlist.behavior.IsPassive := by
  intro inputAmplitude outputAmplitude hBehavior
  exact netlist.power_le_of_isPassive hScattering inputAmplitude outputAmplitude hBehavior

/-- Power-preserving assembled component scattering makes the singular-safe external relation
power-preserving. -/
lemma behavior_isPowerPreserving_of_scattering
    (hScattering : netlist.scatteringTransform.IsPowerPreserving) :
    netlist.behavior.IsPowerPreserving := by
  intro inputAmplitude outputAmplitude hBehavior
  exact netlist.power_eq_of_isPowerPreserving hScattering inputAmplitude outputAmplitude hBehavior

/-- On the existing well-posed domain, relational passivity is exactly passivity of the extracted
response transform. -/
lemma behavior_isPassive_iff_responseTransform_isPassive
    (hWellPosed : netlist.IsWellPosed) :
    netlist.behavior.IsPassive ↔ (netlist.responseTransform hWellPosed).IsPassive := by
  simpa only [netlist.toBehavior_responseTransform hWellPosed] using
    ModeTransform.toBehavior_isPassive_iff (netlist.responseTransform hWellPosed)

/-- On the existing well-posed domain, relational power preservation is exactly power preservation
of the extracted response transform. -/
lemma behavior_isPowerPreserving_iff_responseTransform_isPowerPreserving
    (hWellPosed : netlist.IsWellPosed) :
    netlist.behavior.IsPowerPreserving ↔
      (netlist.responseTransform hWellPosed).IsPowerPreserving := by
  simpa only [netlist.toBehavior_responseTransform hWellPosed] using
    ModeTransform.toBehavior_isPowerPreserving_iff (netlist.responseTransform hWellPosed)

/-!
## E. Matched-gauge netlist covariance
-/

/-- Under the Slice 7 directed mate condition, passivity of the actually rephased singular-safe
netlist relation is equivalent to passivity of the original relation. -/
lemma rephasedBehavior_isPassive_iff
    (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge) :
    (netlist.rephasedBehavior gauge).IsPassive ↔ netlist.behavior.IsPassive := by
  rw [netlist.rephasedBehavior_eq gauge hMatched,
    LinearBehavior.isPassive_rephase_iff]

/-- Under the Slice 7 directed mate condition, power preservation of the actually rephased
singular-safe netlist relation is equivalent to power preservation of the original relation. -/
lemma rephasedBehavior_isPowerPreserving_iff
    (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge) :
    (netlist.rephasedBehavior gauge).IsPowerPreserving ↔
      netlist.behavior.IsPowerPreserving := by
  rw [netlist.rephasedBehavior_eq gauge hMatched,
    LinearBehavior.isPowerPreserving_rephase_iff]

/-- Under matched routing and the existing well-posedness gate, passivity of the response extracted
from the rephased netlist is equivalent to passivity of the original response. -/
lemma rephasedResponseTransform_isPassive_iff
    (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge)
    (hWellPosed : netlist.IsWellPosed) :
    (netlist.rephasedResponseTransform gauge hMatched hWellPosed).IsPassive ↔
      (netlist.responseTransform hWellPosed).IsPassive := by
  rw [netlist.rephasedResponseTransform_eq gauge hMatched hWellPosed,
    ModeTransform.isPassive_rephase_iff]

/-- Under matched routing and the existing well-posedness gate, power preservation of the response
extracted from the rephased netlist is equivalent to power preservation of the original response.
-/
lemma rephasedResponseTransform_isPowerPreserving_iff
    (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge)
    (hWellPosed : netlist.IsWellPosed) :
    (netlist.rephasedResponseTransform gauge hMatched hWellPosed).IsPowerPreserving ↔
      (netlist.responseTransform hWellPosed).IsPowerPreserving := by
  rw [netlist.rephasedResponseTransform_eq gauge hMatched hWellPosed,
    ModeTransform.isPowerPreserving_rephase_iff]

end FlatNetlist

end

end Optics
