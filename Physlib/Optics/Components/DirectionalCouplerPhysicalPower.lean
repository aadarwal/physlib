/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysical
public import Physlib.Optics.Components.DirectionalCouplerPower

/-!
# Modal power for the physical-port directional coupler

## i. Overview

This file transports the exact normalized-modal-power factor and the passive/lossless
classifications of `DirectionalCoupler` to its four owned physical ports. Relabeling changes only
coordinates, so it preserves the specification-level power identity and the scattering
classifications exactly.

These results assume Physlib's finite normalized-mode convention. Physical ownership supplies no
electromagnetic normalization, reciprocity, material, bandwidth, delay, or completeness theorem.

## ii. Key results

- `DirectionalCoupler.physicalBehavior_output_power`: exact physical specification power law.
- `DirectionalCoupler.physicalScattering_isPassive`: power-bounded physical scattering is passive.
- `DirectionalCoupler.physicalScattering_isLossless`: unitary physical scattering is lossless.

## iii. Table of contents

- A. Physical behavior power
- B. Physical scattering classification

## iv. References

These coordinate-transport results are Physlib-original and source-neutral.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DirectionalCoupler

/-! ## A. Physical behavior power -/

/-- Every physical behavior state obeys the same exact power-factor law as the raw component. -/
lemma physicalBehavior_output_power [Fintype ι] [DecidableEq ι] (p : Parameters)
    {incident : ModeAmplitude (Incident ((portFamily ι).Channel))}
    {outgoing : ModeAmplitude (Outgoing ((portFamily ι).Channel))}
    (hMember : (incident, outgoing) ∈ physicalBehavior p) :
    outgoing.power = p.powerFactor * incident.power := by
  have hRaw := (mem_physicalBehavior_iff p incident outgoing).mp hMember
  have hPower := behavior_output_power p hRaw
  simpa only [ModeAmplitude.power_reindex] using hPower

/-! ## B. Physical scattering classification -/

/-- Power-bounded parameters make the four-port physical scattering law passive. -/
lemma physicalScattering_isPassive [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsPowerBounded) : (physicalScattering p ι).toModeTransform.IsPassive := by
  change ((scattering p ι).toModeTransform.reindex
    (channelEquiv ι) (channelEquiv ι)).IsPassive
  exact (ModeTransform.isPassive_reindex_iff
    (channelEquiv ι) (channelEquiv ι) (scattering p ι).toModeTransform).mpr
      (scattering_isPassive p hp)

/-- Unitary parameters make the four-port physical scattering law lossless. -/
lemma physicalScattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitary) : (physicalScattering p ι).IsLossless := by
  exact (ScatteringMatrix.isLossless_reindex_iff
    (channelEquiv ι) (scattering p ι)).mpr (scattering_isLossless p hp)

end DirectionalCoupler

end

end Optics
