/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.int.associated
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Associated
import Mathlib.Data.Int.Units
import Mathlib.Data.Int.Basic
/-!
# Associated elements and the integers

This file contains some results on equality up to units in the integers.

## Main results

 * `Int.natAbs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/


theorem Int.natAbs_eq_iff_associated {a b : ℤ} : a.natAbs = b.natAbs ↔ Associated a b := by
  refine' Int.natAbs_eq_natAbs_iff.trans _
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1, by simp⟩
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
#align int.nat_abs_eq_iff_associated Int.natAbs_eq_iff_associated
