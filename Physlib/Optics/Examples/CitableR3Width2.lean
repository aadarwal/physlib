/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainFold
public import Physlib.Optics.Network.TwoPortSeries
public import Physlib.Optics.Components.DirectionalCoupler
public import Physlib.Optics.Components.MatchedPropagation
public import Physlib.Optics.Components.ReflectionlessTwoPort

/-!
# Citable R3 width-2 probe

## i. Overview

Structural admission only: elaboration does NOT show semantic correctness, physical validity, or
carrying-capacity. Sorried side-conditions are carrying-capacity grade and excluded.

Elevates the R3 reconnaissance finding: the cascade combinators are polymorphic in the channel
family and nothing fixes the width to one, so an interleaver stage instantiates at
`W := Unit ⊕ Unit` with no reindex and no bespoke module.

## ii. Key results

The five width-two cascade definitions elaborate. The opaque-`def` hazard R3 predicted is encoded
in section B as a compiler-checked negative control: the same first step, with `W` an opaque
`def`, fails instance resolution, and `#guard_msgs` pins the failure.

## iii. Table of contents

- A. Width-two structural probe
- B. Negative control: the opaque-def hazard

## iv. References

Elevated from the R3 reconnaissance probes (session record). Cited declarations at probe pin
cfaeef36: `DirectionalCoupler.behavior` (Components/DirectionalCoupler.lean:109),
`MatchedPropagation.transmission` (Components/MatchedPropagation.lean:108),
`ModeTransform.directSum` (Mode/Basic.lean:344), `ReflectionlessTwoPort.behavior`
(Components/ReflectionlessTwoPort.lean:109), `TwoPortScatteringBehavior.redhefferSeries`
(Network/TwoPortSeries.lean:74), `BackwardFirstTwoPortBehavior.seriesFold`
(Network/TwoPortChainFold.lean:69).
-/

@[expose] public section

namespace Optics.CitableR3

open Optics

noncomputable section

/-!
## A. Width-two structural probe
-/

/-- The two-waveguide channel family. `abbrev`, per R3's hazard note. -/
abbrev W := Unit ⊕ Unit

/-- Step 1 — coupler stage at `ι := Unit`; each side is already two channels wide. -/
def stageCoupler (p : DirectionalCoupler.Parameters) : TwoPortScatteringBehavior W W :=
  DirectionalCoupler.behavior (ι := Unit) p

/-- Step 2 — the asymmetric arm pair: two DIFFERENT scalar propagations, direct-summed.
This is the step R3 expected to be the obstruction and reported was not. -/
def arm (upper lower : MatchedPropagation.Parameters) : ModeTransform W W :=
  ModeTransform.directSum (MatchedPropagation.transmission upper Unit)
    (MatchedPropagation.transmission lower Unit)

/-- Step 3 — wrap the arm pair as a reflectionless two-port. -/
def stageDelay (upper lower : MatchedPropagation.Parameters) : TwoPortScatteringBehavior W W :=
  ReflectionlessTwoPort.behavior (arm upper lower) (arm upper lower)

/-- Step 4a — two stages composed by the Redheffer series at width two. -/
def twoStages (p : DirectionalCoupler.Parameters)
    (upper lower : MatchedPropagation.Parameters) : TwoPortScatteringBehavior W W :=
  TwoPortScatteringBehavior.redhefferSeries (stageCoupler p) (stageDelay upper lower)

/-- Step 4b — N stages by `seriesFold`, generic in the list, at width two. -/
def lattice (stages : List (BackwardFirstTwoPortBehavior W W)) :
    BackwardFirstTwoPortBehavior W W :=
  BackwardFirstTwoPortBehavior.seriesFold stages

end

end Optics.CitableR3

namespace Optics.CitableR3.NegativeControl

open Optics

noncomputable section

/-!
## B. Negative control: the opaque-def hazard
-/

/-- R3's predicted hazard, exercised: with the channel family an opaque `def` rather than an
`abbrev`, instance resolution cannot unfold it. The guard pins the failure so the build checks
the prediction; loosening or removing it defeats the control.

The precise mechanism: the failing step is not the first to need instances (step 1 needs two, on
the mode index, and they resolve) but the first to need an instance ON THE CHANNEL FAMILY ITSELF
(`Fintype WOpaque`). The hazard is exactly the boundary between definitional unfolding, which type
ascription performs, and instance search, which does not. The guarded declaration below cannot
be a named declaration: it is stated as an `example` so the failed elaboration leaves nothing
in the environment for downstream tooling, and the doc-comment slot above it is consumed by the
guard's expected message. -/
def WOpaque : Type := Unit ⊕ Unit

/-- Elaborates despite the opaque `def`: the instances needed here are on the mode index
(`Fintype Unit`), and the result type matches by definitional unification, which does unfold. -/
def stageCouplerOpaque (p : DirectionalCoupler.Parameters) :
    TwoPortScatteringBehavior WOpaque WOpaque :=
  DirectionalCoupler.behavior (ι := Unit) p

/-- Elaborates: `ModeTransform.directSum` carries no instance binders at all. -/
def armOpaque (upper lower : MatchedPropagation.Parameters) : ModeTransform WOpaque WOpaque :=
  ModeTransform.directSum (MatchedPropagation.transmission upper Unit)
    (MatchedPropagation.transmission lower Unit)

/--
error: failed to synthesize instance of type class
  Fintype WOpaque

Hint: Adding the command
`deriving instance Fintype for Optics.CitableR3.NegativeControl.WOpaque`
may allow Lean to derive the missing instance.
-/
#guard_msgs (whitespace := lax) in
example (upper lower : MatchedPropagation.Parameters) :
    TwoPortScatteringBehavior WOpaque WOpaque :=
  ReflectionlessTwoPort.behavior (armOpaque upper lower) (armOpaque upper lower)

end

end Optics.CitableR3.NegativeControl
