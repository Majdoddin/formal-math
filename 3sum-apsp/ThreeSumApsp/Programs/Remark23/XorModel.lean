/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Remark23.Tasks

/-!
# Remark 23 (3XOR): "is solved in time T" for the problems of the note

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The deductions between running-time claims (`TimeClaims/`) are made for an arbitrary reading
`M : DetTimeModel`.  `xorModel` reads them for the note: the fields for Exact Triangle,
Convolution-3SUM and 3SUM are read as Exact-XOR-Triangle (`xetTask`), Convolution-3XOR (`cxTask`)
and 3XOR (`x3Task`), solved by programs of the light language; all other fields are those of
`lightModel`.  So the claims about the lopsided triangle problems, which the note uses unchanged,
are the same propositions for both readings (`xorModel_lopCount`, `xorModel_lopDetect`).
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp

/-- The reading of "is solved in time T" for the note: the problems of 3SUM's chain are replaced by
their XOR versions, solved by programs of the light language. -/
noncomputable def xorModel : DetTimeModel :=
  { lightModel with
    exactTriangle := SolvedIn xetTask
    convolution3SUM := SolvedIn cxTask
    threeSum := SolvedIn x3Task }

/-- The counting problem of the lopsided triangles is read as for `lightModel`. -/
theorem xorModel_lopCount : xorModel.lopCount = lightModel.lopCount := rfl

/-- The detection problem of the lopsided triangles is read as for `lightModel`. -/
theorem xorModel_lopDetect : xorModel.lopDetect = lightModel.lopDetect := rfl

/-- The thin matrix product is read as for `lightModel`. -/
theorem xorModel_thinProduct : xorModel.thinProduct = lightModel.thinProduct := rfl

end Light.Remark23
