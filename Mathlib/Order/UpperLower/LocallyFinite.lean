/-
Copyright (c) 2023 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.upper_lower.locally_finite
! leanprover-community/mathlib commit 3e175454d8aa6a94734afcb2ae20a2f2b6660ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.LocallyFinite
import Mathlib.Order.UpperLower.Basic

/-!
# Upper and lower sets in a locally finite order

In this file we characterise the interaction of `UpperSet`/`LowerSet` and `LocallyFiniteOrder`.
-/


namespace Set

variable {α : Type _} [Preorder α] {s : Set α}

protected theorem Finite.upperClosure [LocallyFiniteOrderTop α] (hs : s.Finite) :
    (upperClosure s : Set α).Finite := by
  rw [coe_upperClosure]
  exact hs.biUnion fun _ _ => finite_Ici _
#align set.finite.upper_closure Set.Finite.upperClosure

protected theorem Finite.lowerClosure [LocallyFiniteOrderBot α] (hs : s.Finite) :
    (lowerClosure s : Set α).Finite := by
  rw [coe_lowerClosure]
  exact hs.biUnion fun _ _ => finite_Iic _
#align set.finite.lower_closure Set.Finite.lowerClosure

end Set
