/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module
public import Physlib.Optics.Systems.Microring.SourceBridgeDate
public import Physlib.Optics.Systems.Microring.SourceBridgeSysCon
public import Physlib.Optics.Systems.Microring.SourceBridgeSfg

/-!
# Source bridges for microring transfer formulas

## i. Overview

This module re-exports the DATE'14, SysCon'15, and SFG-TR'14 microring source bridges. It
introduces no declarations or additional claims.

## ii. Key results

- `dateTwoPortChainMatrix_eq_gauged_n7Chain` and
  `dateFourPortChainMatrix_eq_reindexed_n5Response`.
- `sysConDropTransfer_eq_n5Response` and `sysConRejectionRatioInBase_eq_closedForm`.
- `sfgAddDropTransfer_eq_n5Response`.

## iii. Table of contents

- A. DATE'14 bridges, re-exported from `SourceBridgeDate`
- B. SysCon'15 bridges, re-exported from `SourceBridgeSysCon`
- C. SFG-TR'14 bridges, re-exported from `SourceBridgeSfg`

## iv. References

The imported modules give the source locations, parameter dictionaries, solve gates, and
respective non-claims. The SFG-TR section is catalogued at `HOL-CORPUS.md:335-349`, with Def. 35
and Thm. 7 at `HOL-CORPUS.md:345-346`.
-/
