/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Remark23.Library
public import ThreeSumApsp.RunningTimes.Sec3.Corollary15_16

/-!
# Remark 23 (3XOR): Corollary 16 for the reading of the note

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The note uses the paper's Corollary 16 unchanged (its §2 item 2): the lopsided triangle problems do
not depend on weights.  `xorModel` reads them as `lightModel` does, so the claim proved for
`lightModel` is the claim for `xorModel` (`xor_claim_corollary_16`).
-/

public section

namespace Light.Remark23

open ThreeSumApsp

/-- **Corollary 16** for the reading of the note. -/
theorem xor_claim_corollary_16 : Claim.Corollary_16 xorModel :=
  Light.Sec3.claim_corollary_16

example : Claim.Corollary_16 xorModel := Light.Sec3.claim_corollary_16

end Light.Remark23
