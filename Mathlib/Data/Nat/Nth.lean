/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez

! This file was ported from Lean 3 source module data.nat.nth
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.List
import Mathlib.Order.OrderIsoNat

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisifies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `Nat.count`.

## Main definitions

* `nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `nth p n = 0`.

## Main results

* `Nat.nth_set_card`: For a fintely-often true `p`, gives the cardinality of the set of numbers
  satisfying `p` above particular values of `nth p`
* `Nat.count_nth_gc`: Establishes a Galois connection between `nth p` and `count p`.
* `Nat.nth_eq_orderIsoOfNat`: For an infinitely-ofter true predicate, `nth` agrees with the
  order-isomorphism of the subtype to the natural numbers.

There has been some discussion on the subject of whether both of `nth` and
`Nat.Subtype.orderIsoOfNat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/

open Finset

namespace Nat

variable (p : ℕ → Prop)

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. See also
`subtype.order_iso_of_nat` for the order isomorphism with ℕ when `p` is infinitely often true. -/
noncomputable def nth : ℕ → ℕ
  | n => infₛ { i : ℕ | p i ∧ ∀ k < n, nth k < i }
#align nat.nth Nat.nth

theorem nth_zero : nth p 0 = infₛ { i : ℕ | p i } := by
  rw [nth]
  simp
#align nat.nth_zero Nat.nth_zero

@[simp]
theorem nth_zero_of_zero (h : p 0) : nth p 0 = 0 := by simp [nth_zero, h]
#align nat.nth_zero_of_zero Nat.nth_zero_of_zero

theorem nth_zero_of_exists [DecidablePred p] (h : ∃ n, p n) : nth p 0 = Nat.find h := by
  rw [nth_zero]
  convert Nat.infₛ_def h
#align nat.nth_zero_of_exists Nat.nth_zero_of_exists

theorem nth_of_finite (hp : (setOf p).Finite) (n : ℕ) :
    nth p n = (hp.toFinset.sort (· ≤ ·)).getD n 0 := by
  obtain ⟨l, hlp, hls, hlp'⟩ :
    ∃ l : List ℕ, hp.toFinset.sort (· ≤ ·) = l ∧ l.Sorted (· < ·) ∧ p = (· ∈ l)
  · refine ⟨_, rfl, Finset.sort_sorted_lt _, funext fun k => ?_⟩
    rw [mem_sort, hp.mem_toFinset, Set.mem_setOf_eq]
  rw [hlp]; clear hlp hp; subst p
  induction' n using Nat.strongInductionOn with n ihn
  rw [nth]; simp (config := { contextual := true }) only [ihn]; clear ihn
  cases' lt_or_le n l.length with hn hn
  · rw [l.getD_eq_get _ hn]
    refine IsLeast.cinfₛ_eq ⟨⟨l.get_mem _ _, fun k hk => ?_⟩, fun k ⟨hkl, hk⟩ => ?_⟩
    · rw [l.getD_eq_get _ (hk.trans hn)]
      exact hls.rel_get_of_lt hk
    · rcases List.mem_iff_get.1 hkl with ⟨k, rfl⟩
      refine hls.le_of_lt.rel_get_of_le <| not_lt.mp fun hlt => ?_
      exact (hk k hlt).ne (l.getD_eq_get _ _)
  · rw [l.getD_eq_default _ hn, infₛ_eq_zero]
    refine .inr (Set.eq_empty_of_forall_not_mem fun k ⟨hkl, hk⟩ => ?_)
    rcases List.mem_iff_get.1 hkl with ⟨k, rfl⟩
    exact (hk k (k.2.trans_le hn)).ne (l.getD_eq_get _ _)

theorem nth_of_card_finite_le {n : ℕ} (hp : (setOf p).Finite) (hle : hp.toFinset.card ≤ n) :
    nth p n = 0 := by
  rw [nth_of_finite p hp, List.getD_eq_default]
  rwa [Finset.length_sort]

theorem nth_eq_orderEmbeddingOfSet (i : Infinite (setOf p)) [DecidablePred (· ∈ setOf p)] :
    nth p = Nat.orderEmbeddingOfSet (setOf p) := funext fun n => by
  let _ : DecidablePred p := ‹_›
  induction' n using Nat.strongInductionOn with n ihn
  rw [nth]
  refine IsLeast.cinfₛ_eq ⟨⟨(Subtype.ofNat _ n).2, fun k hk => ?_⟩, fun k ⟨hpk, hk⟩ => ?_⟩
  · rw [ihn k hk]
    exact (orderEmbeddingOfSet (setOf p)).strictMono hk
  · replace hk := fun m hm => (ihn m hm).symm.trans_lt (hk m hm)
    lift k to setOf p using hpk
    rw [orderEmbeddingOfSet_apply, Subtype.coe_le_coe]
    cases n
    case zero => exact bot_le
    case succ _ => exact Subtype.succ_le_of_lt <| hk _ (Nat.lt_succ_self _)

/-- When `p` is true infinitely often, `nth` agrees with `nat.subtype.order_iso_of_nat`. -/
theorem nth_eq_orderIsoOfNat (i : Infinite (setOf p)) (n : ℕ) :
    nth p n = Nat.Subtype.orderIsoOfNat (setOf p) n := by
  classical exact congr_fun (nth_eq_orderEmbeddingOfSet p i) n

theorem range_nth_of_finite (hp : (setOf p).Finite) : Set.range (nth p) = insert 0 (setOf p) := by
  have : nth p = fun n => (hp.toFinset.sort (· ≤ ·)).getD _ 0 := funext <| nth_of_finite p hp
  simp only [this, List.range_getD, Finset.mem_sort, hp.mem_toFinset, Set.setOf_mem_eq]

theorem range_nth_of_infinite (hp : (setOf p).Infinite) : Set.range (nth p) = setOf p :=
  have := hp.to_subtype
  by classical rw [nth_eq_orderEmbeddingOfSet, orderEmbeddingOfSet_range]

theorem exists_lt_card_finite_nth_eq {a : ℕ} (hp : (setOf p).Finite) (h : p a) :
    ∃ n < hp.toFinset.card, nth p n = a := by
  have : a ∈ hp.toFinset.sort (· ≤ ·) := by simpa
  rcases List.mem_iff_get.1 this with ⟨n, rfl⟩
  exact ⟨n, by simpa only [Finset.length_sort] using n.2,
    (nth_of_finite p hp n).trans (List.getD_eq_get _ _ _)⟩

theorem exists_nth_eq {a : ℕ} (h : p a) : ∃ n, nth p n = a := by
  by_cases hp : (setOf p).Finite
  · rw [← Set.mem_range, range_nth_of_finite p hp]
    exact .inr h
  · rwa [← Set.mem_range, range_nth_of_infinite p hp]

theorem nth_set_of_finite {n : ℕ} (hp : (setOf p).Finite) :
    { i : ℕ | p i ∧ ∀ t < n, nth p t < i } = { i | i ∈ (hp.toFinset.sort (· ≤ ·)).drop n } := by
  ext i
  have : i ∈ hp.toFinset.sort (· ≤ ·) ↔ p i := by simp
  simp_rw [Set.mem_setOf_eq, nth_of_finite p hp, ← this, List.mem_drop_iff_get, List.mem_iff_get]
  set l := hp.toFinset.sort (· ≤ ·)
  constructor
  · rintro ⟨⟨k, hnk, rfl⟩, hk⟩
    refine ⟨k, not_lt.mp fun hkn => ?_, rfl⟩
    exact (hk k hkn).ne (List.getD_eq_get _ _ _)
  · rintro ⟨k, hnk, rfl⟩
    refine ⟨⟨_, rfl⟩, fun m hm => ?_⟩
    rw [List.getD_eq_get _ _ (hm.trans (hnk.trans_lt k.isLt))]
    exact (Finset.sort_sorted_lt _).rel_get_of_lt (hm.trans_le hnk)

theorem nth_set_card {n : ℕ} (hp : (setOf p).Finite)
    (hp' : { i : ℕ | p i ∧ ∀ k < n, nth p k < i }.Finite) :
    hp'.toFinset.card = hp.toFinset.card - n := by
  let _ : Fintype { i | i ∈ (hp.toFinset.sort (· ≤ ·)).drop n } := List.Subtype.fintype _
  simp only [nth_set_of_finite p hp, Set.mem_setOf_eq]
  rw [Set.toFinset_toFinite, List.toFinset_subtype, List.toFinset_card_of_nodup, List.length_drop,
    Finset.length_sort]
  exact (Finset.sort_nodup _ _).sublist (List.drop_sublist _ _)
#align nat.nth_set_card Nat.nth_set_card
#align nat.nth_set_card_aux Nat.nth_set_cardₓ -- extra argument

theorem nth_set_nonempty_of_lt_card {n : ℕ} (hp : (setOf p).Finite) (hlt : n < hp.toFinset.card) :
    { i : ℕ | p i ∧ ∀ k < n, nth p k < i }.Nonempty := by
  have hp' : { i : ℕ | p i ∧ ∀ k : ℕ, k < n → nth p k < i }.Finite := hp.subset fun x hx => hx.1
  rw [← hp'.toFinset_nonempty, ← Finset.card_pos, nth_set_card p hp]
  exact Nat.sub_pos_of_lt hlt
#align nat.nth_set_nonempty_of_lt_card Nat.nth_set_nonempty_of_lt_card

theorem nth_mem_of_lt_card_finite_aux (n : ℕ) (hp : (setOf p).Finite) (hlt : n < hp.toFinset.card) :
    nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } := by
  rw [nth]
  apply cinfₛ_mem
  exact nth_set_nonempty_of_lt_card _ _ hlt
#align nat.nth_mem_of_lt_card_finite_aux Nat.nth_mem_of_lt_card_finite_aux

theorem nth_mem_of_lt_card_finite {n : ℕ} (hp : (setOf p).Finite) (hlt : n < hp.toFinset.card) :
    p (nth p n) :=
  (nth_mem_of_lt_card_finite_aux p n hp hlt).1
#align nat.nth_mem_of_lt_card_finite Nat.nth_mem_of_lt_card_finite

theorem nth_strictMono_of_finite {m n : ℕ} (hp : (setOf p).Finite) (hlt : n < hp.toFinset.card)
    (hmn : m < n) : nth p m < nth p n :=
  (nth_mem_of_lt_card_finite_aux p _ hp hlt).2 _ hmn
#align nat.nth_strict_mono_of_finite Nat.nth_strictMono_of_finite

#noalign nat.nth_mem_of_infinite_aux

theorem nth_mem_of_infinite (hp : (setOf p).Infinite) (n : ℕ) : p (nth p n) := by
  rw [nth_eq_orderIsoOfNat p hp.to_subtype]
  exact Subtype.prop _
#align nat.nth_mem_of_infinite Nat.nth_mem_of_infinite

theorem nth_strictMono (hp : (setOf p).Infinite) : StrictMono (nth p) := fun m n => by
  simpa only [nth_eq_orderIsoOfNat p hp.to_subtype, Subtype.coe_lt_coe, OrderIso.lt_iff_lt] using id
#align nat.nth_strict_mono Nat.nth_strictMono

theorem nth_injective_of_infinite (hp : (setOf p).Infinite) : Function.Injective (nth p) :=
  (nth_strictMono p hp).injective
#align nat.nth_injective_of_infinite Nat.nth_injective_of_infinite

theorem nth_monotone (hp : (setOf p).Infinite) : Monotone (nth p) :=
  (nth_strictMono p hp).monotone
#align nat.nth_monotone Nat.nth_monotone

theorem nth_mono_of_finite {a b : ℕ} (hp : (setOf p).Finite) (hb : b < hp.toFinset.card)
    (hab : a ≤ b) : nth p a ≤ nth p b := by
  obtain rfl | h := hab.eq_or_lt
  · exact le_rfl
  · exact (nth_strictMono_of_finite p hp hb h).le
#align nat.nth_mono_of_finite Nat.nth_mono_of_finite

theorem not_mem_of_between_nth {a n : ℕ} (h₁ : nth p n < a) (h₂ : a < nth p (n + 1)) : ¬p a := by
  intro ha
  by_cases hp : (setOf p).Finite
  · rcases exists_lt_card_finite_nth_eq p hp ha with ⟨m, hm, rfl⟩
    cases' lt_or_le n m with hnm hmn
    · exact h₂.not_le (nth_mono_of_finite p hp hm hnm)
    · cases' lt_or_le n hp.toFinset.card with hn hn
      · exact h₁.not_le (nth_mono_of_finite p hp hn hmn)
      · rw [nth_of_card_finite_le p hp (hn.trans n.le_succ)] at h₂
        exact h₂.not_le (zero_le _)
  · rcases exists_nth_eq p ha with ⟨m, rfl⟩
    rw [(nth_strictMono p hp).lt_iff_lt] at h₁ h₂
    exact h₁.not_le (le_of_lt_succ h₂)

-- porting note: removed unneeded assumptions
theorem le_nth_of_lt_nth_succ {k a : ℕ} (h : a < nth p k.succ) (ha : p a) : a ≤ nth p k :=
  not_lt.1 <| fun h' => not_mem_of_between_nth p h' h ha
#align nat.le_nth_of_lt_nth_succ_finite Nat.le_nth_of_lt_nth_succₓ
#align nat.le_nth_of_lt_nth_succ_infinite Nat.le_nth_of_lt_nth_succₓ

section Count

variable [DecidablePred p]

@[simp]
theorem count_nth_zero : count p (nth p 0) = 0 := by
  rw [count_eq_card_filter_range, Finset.card_eq_zero, nth_zero]
  ext a
  simp_rw [not_mem_empty, mem_filter, mem_range, iff_false_iff]
  rintro ⟨ha, hp⟩
  exact ha.not_le (Nat.infₛ_le hp)
#align nat.count_nth_zero Nat.count_nth_zero

theorem filter_range_nth_eq_insert_of_finite (hp : (setOf p).Finite) {k : ℕ}
    (hlt : k.succ < hp.toFinset.card) :
    Finset.filter p (Finset.range (nth p (k + 1))) =
      insert (nth p k) (Finset.filter p (Finset.range (nth p k))) := by
  ext a
  simp_rw [mem_insert, mem_filter, mem_range]
  constructor
  · rintro ⟨ha, hpa⟩
    refine' or_iff_not_imp_left.mpr fun h => ⟨lt_of_le_of_ne _ h, hpa⟩
    exact le_nth_of_lt_nth_succ p ha hpa
  · rintro (ha | ⟨ha, hpa⟩)
    · rw [ha]
      refine' ⟨nth_strictMono_of_finite p hp hlt (lt_add_one _), _⟩
      apply nth_mem_of_lt_card_finite p hp
      exact k.le_succ.trans_lt hlt
    refine' ⟨ha.trans _, hpa⟩
    exact nth_strictMono_of_finite p hp hlt (lt_add_one _)
#align nat.filter_range_nth_eq_insert_of_finite Nat.filter_range_nth_eq_insert_of_finite

theorem count_nth_of_lt_card_finite {n : ℕ} (hp : (setOf p).Finite) (hlt : n < hp.toFinset.card) :
    count p (nth p n) = n := by
  induction' n with k hk
  · exact count_nth_zero _
  · rw [count_eq_card_filter_range, filter_range_nth_eq_insert_of_finite p hp hlt,
      Finset.card_insert_of_not_mem, ← count_eq_card_filter_range, hk (lt_of_succ_lt hlt)]
    simp
#align nat.count_nth_of_lt_card_finite Nat.count_nth_of_lt_card_finite

theorem filter_range_nth_eq_insert_of_infinite (hp : (setOf p).Infinite) (k : ℕ) :
    (Finset.range (nth p (k + 1))).filter p =
      insert (nth p k) ((Finset.range (nth p k)).filter p) := by
  ext a
  simp_rw [mem_insert, mem_filter, mem_range]
  constructor
  · rintro ⟨ha, hpa⟩
    rw [nth] at ha
    refine' or_iff_not_imp_left.mpr fun hne => ⟨(le_of_not_lt fun h => _).lt_of_ne hne, hpa⟩
    exact
      ha.not_le (Nat.infₛ_le ⟨hpa, fun b hb => (nth_monotone p hp (le_of_lt_succ hb)).trans_lt h⟩)
  · rintro (rfl | ⟨ha, hpa⟩)
    · exact ⟨nth_strictMono p hp (lt_succ_self k), nth_mem_of_infinite p hp _⟩
    · exact ⟨ha.trans (nth_strictMono p hp (lt_succ_self k)), hpa⟩
#align nat.filter_range_nth_eq_insert_of_infinite Nat.filter_range_nth_eq_insert_of_infinite

theorem count_nth_of_infinite (hp : (setOf p).Infinite) (n : ℕ) : count p (nth p n) = n :=
  have := hp.to_subtype
  by classical simpa only [nth_eq_orderEmbeddingOfSet p this, orderEmbeddingOfSet_range]
    using (orderEmbeddingOfSet (setOf p)).count_apply n
#align nat.count_nth_of_infinite Nat.count_nth_of_infinite

@[simp]
theorem nth_count {n : ℕ} (hpn : p n) : nth p (count p n) = n := by
  obtain hp | hp := em (setOf p).Finite
  · refine' count_injective _ hpn _
    · apply nth_mem_of_lt_card_finite p hp
      exact count_lt_card hp hpn
    · exact count_nth_of_lt_card_finite _ _ (count_lt_card hp hpn)
  · apply count_injective (nth_mem_of_infinite _ hp _) hpn
    apply count_nth_of_infinite p hp
#align nat.nth_count Nat.nth_count

theorem nth_count_eq_infₛ {n : ℕ} : nth p (count p n) = infₛ { i : ℕ | p i ∧ n ≤ i } := by
  rw [nth]
  congr
  ext a
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro hpa
  refine' ⟨fun h => _, fun hn k hk => lt_of_lt_of_le _ hn⟩
  · by_contra ha
    simp only [not_le] at ha
    have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
    rwa [nth_count p hpa, lt_self_iff_false] at hn
  · apply (count_monotone p).reflect_lt
    convert hk
    obtain hp | hp : (setOf p).Finite ∨ (setOf p).Infinite := em (setOf p).Finite
    · rw [count_nth_of_lt_card_finite _ hp]
      exact hk.trans ((count_monotone _ hn).trans_lt (count_lt_card hp hpa))
    · apply count_nth_of_infinite p hp
#align nat.nth_count_eq_Inf Nat.nth_count_eq_infₛ

theorem count_nth_gc (hp : (setOf p).Infinite) : GaloisConnection (count p) (nth p) := fun x y => by
  classical
  have := hp.to_subtype
  simp_rw [nth_eq_orderEmbeddingOfSet p hp.to_subtype, ← OrderEmbedding.count_mem_range_le_iff,
    orderEmbeddingOfSet_range, Set.mem_setOf_eq]
#align nat.count_nth_gc Nat.count_nth_gc

theorem count_le_iff_le_nth (hp : (setOf p).Infinite) {a b : ℕ} : count p a ≤ b ↔ a ≤ nth p b :=
  count_nth_gc p hp _ _
#align nat.count_le_iff_le_nth Nat.count_le_iff_le_nth

/-- If the set `{ x | p x }` is infinite, then `Nat.count p` and `Nat.nth p` form a Galois
insertion. -/
noncomputable def count_nth_gi (hp : (setOf p).Infinite) : GaloisInsertion (count p) (nth p) :=
  (count_nth_gc p hp).toGaloisInsertion fun n => (count_nth_of_infinite p hp n).ge

theorem le_nth_count (hp : (setOf p).Infinite) (n : ℕ) : n ≤ nth p (count p n) :=
  (count_nth_gc _ hp).le_u_l  _
#align nat.nth_count_le Nat.le_nth_count

theorem lt_nth_iff_count_lt (hp : (setOf p).Infinite) {a b : ℕ} : a < count p b ↔ nth p a < b :=
  (count_nth_gc p hp).lt_iff_lt
#align nat.lt_nth_iff_count_lt Nat.lt_nth_iff_count_lt

theorem nth_lt_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k < n := by
  obtain hp | hp := em (setOf p).Finite
  · refine' (count_monotone p).reflect_lt _
    rwa [count_nth_of_lt_card_finite p hp]
    refine' h.trans_le _
    rw [count_eq_card_filter_range]
    exact Finset.card_le_of_subset fun x hx => hp.mem_toFinset.2 (mem_filter.1 hx).2
  · rwa [← lt_nth_iff_count_lt _ hp]
#align nat.nth_lt_of_lt_count Nat.nth_lt_of_lt_count

theorem count_le_of_le_nth (n k : ℕ) (h : n ≤ nth p k) : count p n ≤ k :=
  not_lt.1 <| (mt <| nth_lt_of_lt_count p n k) h.not_lt
#align nat.le_nth_of_count_le Nat.count_le_of_le_nth

theorem count_nth_le (n : ℕ) : count p (nth p n) ≤ n := count_le_of_le_nth p _ _ le_rfl

end Count

theorem nth_zero_of_nth_zero (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (ha : nth p a = 0) :
    nth p b = 0 := by
  rw [nth, infₛ_eq_zero] at ha ⊢
  cases' ha with ha ha
  · exact (h₀ ha.1).elim
  · refine' Or.inr (Set.eq_empty_of_subset_empty fun x hx => _)
    rw [← ha]
    exact ⟨hx.1, fun k hk => hx.2 k <| hk.trans_le hab⟩
#align nat.nth_zero_of_nth_zero Nat.nth_zero_of_nth_zero

end Nat
