/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module order.partial_sups
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Order.Hom.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The monotone sequence of partial supremums of a sequence

We define `partialSups : (ℕ → α) → ℕ →o α` inductively. For `f : ℕ → α`, `partialSups f` is
the sequence `f 0 `, `f 0 ⊔ f 1`, `f 0 ⊔ f 1 ⊔ f 2`, ... The point of this definition is that
* it doesn't need a `⨆`, as opposed to `⨆ (i ≤ n), f i` (which also means the wrong thing on
  `ConditionallyCompleteLattice`s).
* it doesn't need a `⊥`, as opposed to `(Finset.range (n + 1)).sup f`.
* it avoids needing to prove that `Finset.range (n + 1)` is nonempty to use `Finset.sup'`.

Equivalence with those definitions is shown by `partialSups_eq_biSup`, `partialSups_eq_sup_range`,
and `partialSups_eq_sup'_range` respectively.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because :
* Starting at `⊥` requires... having a bottom element.
* `fun f n ↦ (Finset.range n).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partialSups.gi`.

## TODO

One could generalize `partialSups` to any locally finite bot preorder domain, in place of `ℕ`.
Necessary for the TODO in the module docstring of `Order.disjointed`.
-/


variable {α : Type _}

section SemilatticeSup

variable [SemilatticeSup α]

/-- The monotone sequence whose value at `n` is the supremum of the `f m` where `m ≤ n`. -/
def partialSups (f : ℕ → α) : ℕ →o α :=
  ⟨@Nat.rec (fun _ => α) (f 0) fun (n : ℕ) (a : α) => a ⊔ f (n + 1),
    monotone_nat_of_le_succ fun _ => le_sup_left⟩
#align partial_sups partialSups

@[simp]
theorem partialSups_zero (f : ℕ → α) : partialSups f 0 = f 0 :=
  rfl
#align partial_sups_zero partialSups_zero

@[simp]
theorem partialSups_succ (f : ℕ → α) (n : ℕ) :
    partialSups f (n + 1) = partialSups f n ⊔ f (n + 1) :=
  rfl
#align partial_sups_succ partialSups_succ

theorem le_partialSups_of_le (f : ℕ → α) {m n : ℕ} (h : m ≤ n) : f m ≤ partialSups f n := by
  induction' n with n ih
  · rw [nonpos_iff_eq_zero.mp h, partialSups_zero]
  · cases' h with h h
    · exact le_sup_right
    · exact (ih h).trans le_sup_left
#align le_partial_sups_of_le le_partialSups_of_le

theorem le_partialSups (f : ℕ → α) : f ≤ partialSups f := fun _n => le_partialSups_of_le f le_rfl
#align le_partial_sups le_partialSups

theorem partialSups_le (f : ℕ → α) (n : ℕ) (a : α) (w : ∀ m, m ≤ n → f m ≤ a) :
    partialSups f n ≤ a := by
  induction' n with n ih
  · apply w 0 le_rfl
  · exact sup_le (ih fun m p => w m (Nat.le_succ_of_le p)) (w (n + 1) le_rfl)
#align partial_sups_le partialSups_le

@[simp]
theorem bddAbove_range_partialSups {f : ℕ → α} :
    BddAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f) := by
  apply exists_congr fun a => _
  intro a
  constructor
  · rintro h b ⟨i, rfl⟩
    exact (le_partialSups _ _).trans (h (Set.mem_range_self i))
  · rintro h b ⟨i, rfl⟩
    exact partialSups_le _ _ _ fun _ _ => h (Set.mem_range_self _)
#align bdd_above_range_partial_sups bddAbove_range_partialSups

theorem Monotone.partialSups_eq {f : ℕ → α} (hf : Monotone f) : (partialSups f : ℕ → α) = f := by
  ext n
  induction' n with n ih
  · rfl
  · rw [partialSups_succ, ih, sup_eq_right.2 (hf (Nat.le_succ _))]
#align monotone.partial_sups_eq Monotone.partialSups_eq

theorem partialSups_mono : Monotone (partialSups : (ℕ → α) → ℕ →o α) := by
  rintro f g h n
  induction' n with n ih
  · exact h 0
  · exact sup_le_sup ih (h _)
#align partial_sups_mono partialSups_mono

/-- `partialSups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
def partialSups.gi : GaloisInsertion (partialSups : (ℕ → α) → ℕ →o α) (↑) where
  choice f h :=
    ⟨f, by convert (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine' ⟨(le_partialSups f).trans, fun h => _⟩
    convert partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)
#align partial_sups.gi partialSups.gi

theorem partialSups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup' ⟨n, Finset.self_mem_range_succ n⟩ f := by
  induction' n with n ih
  · simp
  · dsimp [partialSups] at ih⊢
    simp_rw [@Finset.range_succ n.succ]
    rw [ih, Finset.sup'_insert, sup_comm]
#align partial_sups_eq_sup'_range partialSups_eq_sup'_range

end SemilatticeSup

theorem partialSups_eq_sup_range [SemilatticeSup α] [OrderBot α] (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup f := by
  induction' n with n ih
  · simp
  · dsimp [partialSups] at ih⊢
    rw [Finset.range_succ, Finset.sup_insert, sup_comm, ih]
#align partial_sups_eq_sup_range partialSups_eq_sup_range

/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
theorem partialSups_disjoint_of_disjoint [DistribLattice α] [OrderBot α] (f : ℕ → α)
    (h : Pairwise (Disjoint on f)) {m n : ℕ} (hmn : m < n) : Disjoint (partialSups f m) (f n) := by
  induction' m with m ih
  · exact h hmn.ne
  · rw [partialSups_succ, disjoint_sup_left]
    exact ⟨ih (Nat.lt_of_succ_lt hmn), h hmn.ne⟩
#align partial_sups_disjoint_of_disjoint partialSups_disjoint_of_disjoint

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

theorem partialSups_eq_ciSup_Iic (f : ℕ → α) (n : ℕ) : partialSups f n = ⨆ i : Set.Iic n, f i := by
  have : Set.Iio (n + 1) = Set.Iic n := Set.ext fun _ => Nat.lt_succ_iff
  rw [partialSups_eq_sup'_range, Finset.sup'_eq_csSup_image, Finset.coe_range, iSup, this]
  simp only [Set.range, Subtype.exists, Set.mem_Iic, exists_prop, (· '' ·)]
#align partial_sups_eq_csupr_Iic partialSups_eq_ciSup_Iic

@[simp]
theorem ciSup_partialSups_eq {f : ℕ → α} (h : BddAbove (Set.range f)) :
    (⨆ n, partialSups f n) = ⨆ n, f n := by
  refine' (ciSup_le fun n => _).antisymm (ciSup_mono _ <| le_partialSups f)
  · rw [partialSups_eq_ciSup_Iic]
    exact ciSup_le fun i => le_ciSup h _
  · rwa [bddAbove_range_partialSups]
#align csupr_partial_sups_eq ciSup_partialSups_eq

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

theorem partialSups_eq_biSup (f : ℕ → α) (n : ℕ) : partialSups f n = ⨆ i ≤ n, f i := by
  simpa only [iSup_subtype] using partialSups_eq_ciSup_Iic f n
#align partial_sups_eq_bsupr partialSups_eq_biSup

-- Porting note: simp can prove this @[simp]
theorem iSup_partialSups_eq (f : ℕ → α) : (⨆ n, partialSups f n) = ⨆ n, f n :=
  ciSup_partialSups_eq <| OrderTop.bddAbove _
#align supr_partial_sups_eq iSup_partialSups_eq

theorem iSup_le_iSup_of_partialSups_le_partialSups {f g : ℕ → α}
    (h : partialSups f ≤ partialSups g) : (⨆ n, f n) ≤ ⨆ n, g n := by
  rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g]
  exact iSup_mono h
#align supr_le_supr_of_partial_sups_le_partial_sups iSup_le_iSup_of_partialSups_le_partialSups

theorem iSup_eq_iSup_of_partialSups_eq_partialSups {f g : ℕ → α}
    (h : partialSups f = partialSups g) : (⨆ n, f n) = ⨆ n, g n := by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]
#align supr_eq_supr_of_partial_sups_eq_partial_sups iSup_eq_iSup_of_partialSups_eq_partialSups

end CompleteLattice
