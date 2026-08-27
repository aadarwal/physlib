/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
import Physlib.Optics.Network.ExactReferencesRegression

/-!
# Emit proof-carrying exact references

This executable transports the certified N6 exact-reference table to deterministic JSON. It may
print to standard output or write a caller-selected file. Mathematical trust remains in the sound
fields and named sound lemmas imported with the table, not in this emitter.
-/

open Optics

/-- Command-line usage for the exact-reference emitter. -/
def exactReferencesUsage : String :=
  "usage: lake exe exact_references <physlib-ref> [output-file]"

/-- Render the certified N6 manifest for a named Physlib commit. -/
def renderExactReferences (physlibRef : String) : String :=
  ExactReference.manifestString physlibRef n6ExactReferences

/-- Emit the proof-carrying N6 exact-reference manifest. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [physlibRef] =>
      IO.print (renderExactReferences physlibRef)
      return 0
  | [physlibRef, outputFile] =>
      IO.FS.writeFile ⟨outputFile⟩ (renderExactReferences physlibRef)
      return 0
  | _ =>
      IO.eprintln exactReferencesUsage
      return 2
