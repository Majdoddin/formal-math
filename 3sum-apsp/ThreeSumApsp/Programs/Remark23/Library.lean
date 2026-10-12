/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Remark23.Bits.Digits
public import ThreeSumApsp.Programs.Remark23.Bits.Numbers
public import ThreeSumApsp.Programs.Remark23.Bits.Rows
public import ThreeSumApsp.Programs.Remark23.Bits.XorTable
public import ThreeSumApsp.Programs.Remark23.XorModel

/-!
# Remark 23 (3XOR): the tasks, the reading `xorModel`, and the bit library

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The routines on vectors of `F^Λ` held as numbers or as rows of digits, each with its specification
and its time: xorNat and ipNat (`Bits/Numbers.lean`), vbits (`Bits/Digits.lean`), vxor, xor3Zero,
ipBit and ofBits (`Bits/Rows.lean`), xorTable (`Bits/XorTable.lean`); the tasks and `xorModel`.
The hosts of the note's reductions import what they use; this file keeps the whole library in the
build (`RunningTimes/Remark23/Corollary16.lean` imports it).
-/
