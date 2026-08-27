/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Examples.CROW

/-!
# Uniform fixture for the Table-1 comparison

## i. Overview

This additive fixture records the uniform, unit-amplitude domain required before any comparison.
End readout, phase conversion, and gauge transport remain explicit proof obligations.

## ii. Key results

The fixture proves uniformity, unit amplitude, zero phase, and the Pythagorean coupler identity.

## iii. Table of contents

- A. Uniform fixture and preconditions

## iv. References

Heebner et al., JOSA B 21 (2004), Table 1.
-/

@[expose] public section
namespace Optics.CROW

noncomputable section

/-!
## A. Uniform fixture and preconditions
-/
/-- Uniform bulk coupler parameters for the Table-1 domain. -/
def table1UniformParameters : Parameters 2 where
  coupler _ := { throughAmplitude := 3 / 5, crossAmplitude := 4 / 5 }
  forwardArc _ := { amplitudeTransmission := 1, carrierPathPhase := 0 }
  returnArc _ := { amplitudeTransmission := 1, carrierPathPhase := 0 }

/-- The uniform fixture satisfies the unit-amplitude propagation precondition. -/
lemma table1Uniform_forward_unit (i : Fin 2) :
    (table1UniformParameters.forwardArc i).amplitudeTransmission = 1 := by
  rfl

/-- The uniform fixture satisfies the return unit-amplitude propagation precondition. -/
lemma table1Uniform_return_unit (i : Fin 2) :
    (table1UniformParameters.returnArc i).amplitudeTransmission = 1 := by
  rfl

/-- Both directed arcs have zero carrier phase. -/
lemma table1Uniform_phase_zero (i : Fin 2) :
    (table1UniformParameters.forwardArc i).carrierPathPhase = 0 ∧
      (table1UniformParameters.returnArc i).carrierPathPhase = 0 := by
  constructor <;> rfl

/-- Every uniform coupler satisfies the Pythagorean identity. -/
lemma table1Uniform_coupler_pythagorean (i : Fin 3) :
    (table1UniformParameters.coupler i).throughAmplitude ^ 2 +
      (table1UniformParameters.coupler i).crossAmplitude ^ 2 = 1 := by
  norm_num [table1UniformParameters]

/-- The uniform fixture uses one coupler pair at every interface. -/
lemma table1Uniform_coupler_uniform (i j : Fin 3) :
    table1UniformParameters.coupler i = table1UniformParameters.coupler j := by
  rfl

end
end Optics.CROW
