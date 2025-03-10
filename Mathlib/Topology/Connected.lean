/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module topology.connected
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.BoolIndicator
import Mathlib.Order.SuccPred.Relation
import Mathlib.Topology.SubsetProperties

/-!
# Connected subsets of topological spaces

In this file we define connected subsets of a topological spaces and various other properties and
classes related to connectivity.

## Main definitions

We define the following properties for sets in a topological space:

* `IsConnected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
* `connectedComponent` is the connected component of an element in the space.
* `IsTotallyDisconnected`: all of its connected components are singletons.
* `IsTotallySeparated`: any two points can be separated by two disjoint opens that cover the set.

For each of these definitions, we also have a class stating that the whole space
satisfies that property:
`ConnectedSpace`, `TotallyDisconnectedSpace`, `TotallySeparatedSpace`.

## On the definition of connected sets/spaces

In informal mathematics, connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreconnected`.
In other words, the only difference is whether the empty space counts as connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/


open Set Function Topology TopologicalSpace Relation
open scoped Classical

universe u v

variable {α : Type u} {β : Type v} {ι : Type _} {π : ι → Type _} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

/-- A preconnected set is one where there is no non-trivial open partition. -/
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty
#align is_preconnected IsPreconnected

/-- A connected set is one that is nonempty and where there is no non-trivial open partition. -/
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
#align is_connected IsConnected

theorem IsConnected.nonempty {s : Set α} (h : IsConnected s) : s.Nonempty :=
  h.1
#align is_connected.nonempty IsConnected.nonempty

theorem IsConnected.isPreconnected {s : Set α} (h : IsConnected s) : IsPreconnected s :=
  h.2
#align is_connected.is_preconnected IsConnected.isPreconnected

theorem IsPreirreducible.isPreconnected {s : Set α} (H : IsPreirreducible s) : IsPreconnected s :=
  fun _ _ hu hv _ => H _ _ hu hv
#align is_preirreducible.is_preconnected IsPreirreducible.isPreconnected

theorem IsIrreducible.isConnected {s : Set α} (H : IsIrreducible s) : IsConnected s :=
  ⟨H.nonempty, H.isPreirreducible.isPreconnected⟩
#align is_irreducible.is_connected IsIrreducible.isConnected

theorem isPreconnected_empty : IsPreconnected (∅ : Set α) :=
  isPreirreducible_empty.isPreconnected
#align is_preconnected_empty isPreconnected_empty

theorem isConnected_singleton {x} : IsConnected ({x} : Set α) :=
  isIrreducible_singleton.isConnected
#align is_connected_singleton isConnected_singleton

theorem isPreconnected_singleton {x} : IsPreconnected ({x} : Set α) :=
  isConnected_singleton.isPreconnected
#align is_preconnected_singleton isPreconnected_singleton

theorem Set.Subsingleton.isPreconnected {s : Set α} (hs : s.Subsingleton) : IsPreconnected s :=
  hs.induction_on isPreconnected_empty fun _ => isPreconnected_singleton
#align set.subsingleton.is_preconnected Set.Subsingleton.isPreconnected

/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
theorem isPreconnected_of_forall {s : Set α} (x : α)
    (H : ∀ y ∈ s, ∃ t, t ⊆ s ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t) : IsPreconnected s := by
  rintro u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩
  have xs : x ∈ s := by
    rcases H y ys with ⟨t, ts, xt, -, -⟩
    exact ts xt
  -- porting note: todo: use `wlog xu : x ∈ u := hs xs using u v y z, v u z y`
  cases hs xs
  case inl xu =>
    rcases H y ys with ⟨t, ts, xt, yt, ht⟩
    have := ht u v hu hv (ts.trans hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩
    exact this.imp fun z hz => ⟨ts hz.1, hz.2⟩
  case inr xv =>
    rcases H z zs with ⟨t, ts, xt, zt, ht⟩
    have := ht v u hv hu (ts.trans <| by rwa [union_comm]) ⟨x, xt, xv⟩ ⟨z, zt, zu⟩
    exact this.imp fun _ h => ⟨ts h.1, h.2.2, h.2.1⟩
#align is_preconnected_of_forall isPreconnected_of_forall

/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
theorem isPreconnected_of_forall_pair {s : Set α}
    (H : ∀ x ∈ s, ∀ y ∈ s, ∃ t, t ⊆ s ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t) :
    IsPreconnected s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  exacts [isPreconnected_empty, isPreconnected_of_forall x fun y => H x hx y]
#align is_preconnected_of_forall_pair isPreconnected_of_forall_pair

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
theorem isPreconnected_sUnion (x : α) (c : Set (Set α)) (H1 : ∀ s ∈ c, x ∈ s)
    (H2 : ∀ s ∈ c, IsPreconnected s) : IsPreconnected (⋃₀ c) := by
  apply isPreconnected_of_forall x
  rintro y ⟨s, sc, ys⟩
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩
#align is_preconnected_sUnion isPreconnected_sUnion

theorem isPreconnected_iUnion {ι : Sort _} {s : ι → Set α} (h₁ : (⋂ i, s i).Nonempty)
    (h₂ : ∀ i, IsPreconnected (s i)) : IsPreconnected (⋃ i, s i) :=
  Exists.elim h₁ fun f hf => isPreconnected_sUnion f _ hf (forall_range_iff.2 h₂)
#align is_preconnected_Union isPreconnected_iUnion

theorem IsPreconnected.union (x : α) {s t : Set α} (H1 : x ∈ s) (H2 : x ∈ t) (H3 : IsPreconnected s)
    (H4 : IsPreconnected t) : IsPreconnected (s ∪ t) :=
  sUnion_pair s t ▸ isPreconnected_sUnion x {s, t} (by rintro r (rfl | rfl | h) <;> assumption)
    (by rintro r (rfl | rfl | h) <;> assumption)
#align is_preconnected.union IsPreconnected.union

theorem IsPreconnected.union' {s t : Set α} (H : (s ∩ t).Nonempty) (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ∪ t) := by
  rcases H with ⟨x, hxs, hxt⟩
  exact hs.union x hxs hxt ht
#align is_preconnected.union' IsPreconnected.union'

theorem IsConnected.union {s t : Set α} (H : (s ∩ t).Nonempty) (Hs : IsConnected s)
    (Ht : IsConnected t) : IsConnected (s ∪ t) := by
  rcases H with ⟨x, hx⟩
  refine' ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, _⟩
  exact Hs.isPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Ht.isPreconnected
#align is_connected.union IsConnected.union

/-- The directed sUnion of a set S of preconnected subsets is preconnected. -/
theorem IsPreconnected.sUnion_directed {S : Set (Set α)} (K : DirectedOn (· ⊆ ·) S)
    (H : ∀ s ∈ S, IsPreconnected s) : IsPreconnected (⋃₀ S) := by
  rintro u v hu hv Huv ⟨a, ⟨s, hsS, has⟩, hau⟩ ⟨b, ⟨t, htS, hbt⟩, hbv⟩
  obtain ⟨r, hrS, hsr, htr⟩ : ∃ r ∈ S, s ⊆ r ∧ t ⊆ r := K s hsS t htS
  have Hnuv : (r ∩ (u ∩ v)).Nonempty :=
    H _ hrS u v hu hv ((subset_sUnion_of_mem hrS).trans Huv) ⟨a, hsr has, hau⟩ ⟨b, htr hbt, hbv⟩
  have Kruv : r ∩ (u ∩ v) ⊆ ⋃₀ S ∩ (u ∩ v) := inter_subset_inter_left _ (subset_sUnion_of_mem hrS)
  exact Hnuv.mono Kruv
#align is_preconnected.sUnion_directed IsPreconnected.sUnion_directed

/-- The biUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
theorem IsPreconnected.biUnion_of_reflTransGen {ι : Type _} {t : Set ι} {s : ι → Set α}
    (H : ∀ i ∈ t, IsPreconnected (s i))
    (K : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen (fun i j => (s i ∩ s j).Nonempty ∧ i ∈ t) i j) :
    IsPreconnected (⋃ n ∈ t, s n) := by
  let R := fun i j : ι => (s i ∩ s j).Nonempty ∧ i ∈ t
  have P : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen R i j →
      ∃ p, p ⊆ t ∧ i ∈ p ∧ j ∈ p ∧ IsPreconnected (⋃ j ∈ p, s j) := fun i hi j hj h => by
    induction h
    case refl =>
      refine ⟨{i}, singleton_subset_iff.mpr hi, mem_singleton i, mem_singleton i, ?_⟩
      rw [biUnion_singleton]
      exact H i hi
    case tail j k _ hjk ih =>
      obtain ⟨p, hpt, hip, hjp, hp⟩ := ih hjk.2
      refine ⟨insert k p, insert_subset.mpr ⟨hj, hpt⟩, mem_insert_of_mem k hip, mem_insert k p, ?_⟩
      rw [biUnion_insert]
      refine (H k hj).union' (hjk.1.mono ?_) hp
      rw [inter_comm]
      exact inter_subset_inter_right _ (subset_biUnion_of_mem hjp)
  refine' isPreconnected_of_forall_pair _
  intro x hx y hy
  obtain ⟨i : ι, hi : i ∈ t, hxi : x ∈ s i⟩ := mem_iUnion₂.1 hx
  obtain ⟨j : ι, hj : j ∈ t, hyj : y ∈ s j⟩ := mem_iUnion₂.1 hy
  obtain ⟨p, hpt, hip, hjp, hp⟩ := P i hi j hj (K i hi j hj)
  exact ⟨⋃ j ∈ p, s j, biUnion_subset_biUnion_left hpt, mem_biUnion hip hxi,
    mem_biUnion hjp hyj, hp⟩
#align is_preconnected.bUnion_of_refl_trans_gen IsPreconnected.biUnion_of_reflTransGen

/-- The biUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
theorem IsConnected.biUnion_of_reflTransGen {ι : Type _} {t : Set ι} {s : ι → Set α}
    (ht : t.Nonempty) (H : ∀ i ∈ t, IsConnected (s i))
    (K : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty ∧ i ∈ t) i j) :
    IsConnected (⋃ n ∈ t, s n) :=
  ⟨nonempty_biUnion.2 <| ⟨ht.some, ht.some_mem, (H _ ht.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_reflTransGen (fun i hi => (H i hi).isPreconnected) K⟩
#align is_connected.bUnion_of_refl_trans_gen IsConnected.biUnion_of_reflTransGen

/-- Preconnectedness of the iUnion of a family of preconnected sets
indexed by the vertices of a preconnected graph,
where two vertices are joined when the corresponding sets intersect. -/
theorem IsPreconnected.iUnion_of_reflTransGen {ι : Type _} {s : ι → Set α}
    (H : ∀ i, IsPreconnected (s i))
    (K : ∀ i j, ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty) i j) :
    IsPreconnected (⋃ n, s n) := by
  rw [← biUnion_univ]
  exact IsPreconnected.biUnion_of_reflTransGen (fun i _ => H i) fun i _ j _ => by
    simpa [mem_univ] using K i j
#align is_preconnected.Union_of_refl_trans_gen IsPreconnected.iUnion_of_reflTransGen

theorem IsConnected.iUnion_of_reflTransGen {ι : Type _} [Nonempty ι] {s : ι → Set α}
    (H : ∀ i, IsConnected (s i))
    (K : ∀ i j, ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty) i j) : IsConnected (⋃ n, s n) :=
  ⟨nonempty_iUnion.2 <| Nonempty.elim ‹_› fun i : ι => ⟨i, (H _).nonempty⟩,
    IsPreconnected.iUnion_of_reflTransGen (fun i => (H i).isPreconnected) K⟩
#align is_connected.Union_of_refl_trans_gen IsConnected.iUnion_of_reflTransGen

section SuccOrder

open Order

variable [LinearOrder β] [SuccOrder β] [IsSuccArchimedean β]

/-- The iUnion of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is preconnected. -/
theorem IsPreconnected.iUnion_of_chain {s : β → Set α} (H : ∀ n, IsPreconnected (s n))
    (K : ∀ n, (s n ∩ s (succ n)).Nonempty) : IsPreconnected (⋃ n, s n) :=
  IsPreconnected.iUnion_of_reflTransGen H fun i j =>
    reflTransGen_of_succ _ (fun i _ => K i) fun i _ => by
      rw [inter_comm]
      exact K i
#align is_preconnected.Union_of_chain IsPreconnected.iUnion_of_chain

/-- The iUnion of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is connected. -/
theorem IsConnected.iUnion_of_chain [Nonempty β] {s : β → Set α} (H : ∀ n, IsConnected (s n))
    (K : ∀ n, (s n ∩ s (succ n)).Nonempty) : IsConnected (⋃ n, s n) :=
  IsConnected.iUnion_of_reflTransGen H fun i j =>
    reflTransGen_of_succ _ (fun i _ => K i) fun i _ => by
      rw [inter_comm]
      exact K i
#align is_connected.Union_of_chain IsConnected.iUnion_of_chain

/-- The iUnion of preconnected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
theorem IsPreconnected.biUnion_of_chain {s : β → Set α} {t : Set β} (ht : OrdConnected t)
    (H : ∀ n ∈ t, IsPreconnected (s n))
    (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).Nonempty) :
    IsPreconnected (⋃ n ∈ t, s n) := by
  have h1 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → k ∈ t := fun hi hj hk =>
    ht.out hi hj (Ico_subset_Icc_self hk)
  have h2 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → succ k ∈ t := fun hi hj hk =>
    ht.out hi hj ⟨hk.1.trans <| le_succ _, succ_le_of_lt hk.2⟩
  have h3 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → (s k ∩ s (succ k)).Nonempty :=
    fun hi hj hk => K _ (h1 hi hj hk) (h2 hi hj hk)
  refine' IsPreconnected.biUnion_of_reflTransGen H fun i hi j hj => _
  exact reflTransGen_of_succ _ (fun k hk => ⟨h3 hi hj hk, h1 hi hj hk⟩) fun k hk =>
      ⟨by rw [inter_comm]; exact h3 hj hi hk, h2 hj hi hk⟩
#align is_preconnected.bUnion_of_chain IsPreconnected.biUnion_of_chain

/-- The iUnion of connected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
theorem IsConnected.biUnion_of_chain {s : β → Set α} {t : Set β} (hnt : t.Nonempty)
    (ht : OrdConnected t) (H : ∀ n ∈ t, IsConnected (s n))
    (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).Nonempty) : IsConnected (⋃ n ∈ t, s n) :=
  ⟨nonempty_biUnion.2 <| ⟨hnt.some, hnt.some_mem, (H _ hnt.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_chain ht (fun i hi => (H i hi).isPreconnected) K⟩
#align is_connected.bUnion_of_chain IsConnected.biUnion_of_chain

end SuccOrder

/-- Theorem of bark and tree: if a set is within a preconnected set and its closure, then it is
preconnected as well. See also `IsConnected.subset_closure`. -/
protected theorem IsPreconnected.subset_closure {s : Set α} {t : Set α} (H : IsPreconnected s)
    (Kst : s ⊆ t) (Ktcs : t ⊆ closure s) : IsPreconnected t :=
  fun u v hu hv htuv ⟨_y, hyt, hyu⟩ ⟨_z, hzt, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv (Subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, Kst hrs, hruv⟩
#align is_preconnected.subset_closure IsPreconnected.subset_closure

/-- Theorem of bark and tree: if a set is within a connected set and its closure, then it is
connected as well. See also `IsPreconnected.subset_closure`. -/
protected theorem IsConnected.subset_closure {s : Set α} {t : Set α} (H : IsConnected s)
    (Kst : s ⊆ t) (Ktcs : t ⊆ closure s) : IsConnected t :=
  ⟨Nonempty.mono Kst H.left, IsPreconnected.subset_closure H.right Kst Ktcs⟩
#align is_connected.subset_closure IsConnected.subset_closure

/-- The closure of a preconnected set is preconnected as well. -/
protected theorem IsPreconnected.closure {s : Set α} (H : IsPreconnected s) :
    IsPreconnected (closure s) :=
  IsPreconnected.subset_closure H subset_closure Subset.rfl
#align is_preconnected.closure IsPreconnected.closure

/-- The closure of a connected set is connected as well. -/
protected theorem IsConnected.closure {s : Set α} (H : IsConnected s) : IsConnected (closure s) :=
  IsConnected.subset_closure H subset_closure <| Subset.rfl
#align is_connected.closure IsConnected.closure

/-- The image of a preconnected set is preconnected as well. -/
protected theorem IsPreconnected.image [TopologicalSpace β] {s : Set α} (H : IsPreconnected s)
    (f : α → β) (hf : ContinuousOn f s) : IsPreconnected (f '' s) := by
  -- Unfold/destruct definitions in hypotheses
  rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s ⊆ u' ∪ v'
  · rw [image_subset_iff, preimage_union] at huv
    replace huv := subset_inter huv Subset.rfl
    rw [inter_distrib_right, u'_eq, v'_eq, ← inter_distrib_right] at huv
    exact (subset_inter_iff.1 huv).1
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹IsPreconnected s›`
  obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).Nonempty := by
    refine H u' v' hu' hv' huv ⟨x, ?_⟩ ⟨y, ?_⟩ <;> rw [inter_comm]
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
  rw [← inter_self s, inter_assoc, inter_left_comm s u', ← inter_assoc, inter_comm s, inter_comm s,
    ← u'_eq, ← v'_eq] at hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩
#align is_preconnected.image IsPreconnected.image

/-- The image of a connected set is connected as well. -/
protected theorem IsConnected.image [TopologicalSpace β] {s : Set α} (H : IsConnected s) (f : α → β)
    (hf : ContinuousOn f s) : IsConnected (f '' s) :=
  ⟨nonempty_image_iff.mpr H.nonempty, H.isPreconnected.image f hf⟩
#align is_connected.image IsConnected.image

theorem isPreconnected_closed_iff {s : Set α} :
    IsPreconnected s ↔ ∀ t t', IsClosed t → IsClosed t' →
      s ⊆ t ∪ t' → (s ∩ t).Nonempty → (s ∩ t').Nonempty → (s ∩ (t ∩ t')).Nonempty :=
  ⟨by
      rintro h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩
      rw [← not_disjoint_iff_nonempty_inter, ← subset_compl_iff_disjoint_right, compl_inter]
      intro h'
      have xt' : x ∉ t' := (h' xs).resolve_left (absurd xt)
      have yt : y ∉ t := (h' ys).resolve_right (absurd yt')
      have := h _ _ ht.isOpen_compl ht'.isOpen_compl h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩
      rw [← compl_union] at this
      exact this.ne_empty htt'.disjoint_compl_right.inter_eq,
    by
      rintro h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩
      rw [← not_disjoint_iff_nonempty_inter, ← subset_compl_iff_disjoint_right, compl_inter]
      intro h'
      have xv : x ∉ v := (h' xs).elim (absurd xu) id
      have yu : y ∉ u := (h' ys).elim id (absurd yv)
      have := h _ _ hu.isClosed_compl hv.isClosed_compl h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩
      rw [← compl_union] at this
      exact this.ne_empty huv.disjoint_compl_right.inter_eq⟩
#align is_preconnected_closed_iff isPreconnected_closed_iff

theorem Inducing.isPreconnected_image [TopologicalSpace β] {s : Set α} {f : α → β}
    (hf : Inducing f) : IsPreconnected (f '' s) ↔ IsPreconnected s := by
  refine' ⟨fun h => _, fun h => h.image _ hf.continuous.continuousOn⟩
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  rcases hf.isOpen_iff.1 hu' with ⟨u, hu, rfl⟩
  rcases hf.isOpen_iff.1 hv' with ⟨v, hv, rfl⟩
  replace huv : f '' s ⊆ u ∪ v; · rwa [image_subset_iff]
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩ with
    ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩
  exact ⟨z, hzs, hzuv⟩
#align inducing.is_preconnected_image Inducing.isPreconnected_image

/- TODO: The following lemmas about connection of preimages hold more generally for strict maps
(the quotient and subspace topologies of the image agree) whose fibers are preconnected. -/
theorem IsPreconnected.preimage_of_open_map [TopologicalSpace β] {s : Set β} (hs : IsPreconnected s)
    {f : α → β} (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ range f) :
    IsPreconnected (f ⁻¹' s) := fun u v hu hv hsuv hsu hsv => by
  replace hsf : f '' (f ⁻¹' s) = s := image_preimage_eq_of_subset hsf
  obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s ∩ (f '' u ∩ f '' v)).Nonempty
  · refine hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
    · simpa only [hsf, image_union] using image_subset f hsuv
    · simpa only [image_preimage_inter] using hsu.image f
    · simpa only [image_preimage_inter] using hsv.image f
  · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩
#align is_preconnected.preimage_of_open_map IsPreconnected.preimage_of_open_map

theorem IsPreconnected.preimage_of_closed_map [TopologicalSpace β] {s : Set β}
    (hs : IsPreconnected s) {f : α → β} (hinj : Function.Injective f) (hf : IsClosedMap f)
    (hsf : s ⊆ range f) : IsPreconnected (f ⁻¹' s) :=
  isPreconnected_closed_iff.2 fun u v hu hv hsuv hsu hsv => by
    replace hsf : f '' (f ⁻¹' s) = s := image_preimage_eq_of_subset hsf
    obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s ∩ (f '' u ∩ f '' v)).Nonempty
    · refine isPreconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
      · simpa only [hsf, image_union] using image_subset f hsuv
      · simpa only [image_preimage_inter] using hsu.image f
      · simpa only [image_preimage_inter] using hsv.image f
    · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩
#align is_preconnected.preimage_of_closed_map IsPreconnected.preimage_of_closed_map

theorem IsConnected.preimage_of_openMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α → β} (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_open_map hinj hf hsf⟩
#align is_connected.preimage_of_open_map IsConnected.preimage_of_openMap

theorem IsConnected.preimage_of_closedMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α → β} (hinj : Function.Injective f) (hf : IsClosedMap f) (hsf : s ⊆ range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_closed_map hinj hf hsf⟩
#align is_connected.preimage_of_closed_map IsConnected.preimage_of_closedMap

theorem IsPreconnected.subset_or_subset (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hsuv : s ⊆ u ∪ v) (hs : IsPreconnected s) : s ⊆ u ∨ s ⊆ v := by
  specialize hs u v hu hv hsuv
  obtain hsu | hsu := (s ∩ u).eq_empty_or_nonempty
  · exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
  · replace hs := mt (hs hsu)
    simp_rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
      disjoint_iff_inter_eq_empty.1 huv] at hs
    exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)
#align is_preconnected.subset_or_subset IsPreconnected.subset_or_subset

theorem IsPreconnected.subset_left_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v) (hsu : (s ∩ u).Nonempty) (hs : IsPreconnected s) :
    s ⊆ u :=
  Disjoint.subset_left_of_subset_union hsuv
    (by
      by_contra hsv
      rw [not_disjoint_iff_nonempty_inter] at hsv
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv
      exact Set.disjoint_iff.1 huv hx)
#align is_preconnected.subset_left_of_subset_union IsPreconnected.subset_left_of_subset_union

theorem IsPreconnected.subset_right_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v) (hsv : (s ∩ v).Nonempty) (hs : IsPreconnected s) :
    s ⊆ v :=
  hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv
#align is_preconnected.subset_right_of_subset_union IsPreconnected.subset_right_of_subset_union

-- porting note: moved up
/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem IsPreconnected.subset_clopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
    (hne : (s ∩ t).Nonempty) : s ⊆ t :=
  hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne
#align is_preconnected.subset_clopen IsPreconnected.subset_clopen

/-- If a preconnected set `s` intersects an open set `u`, and limit points of `u` inside `s` are
contained in `u`, then the whole set `s` is contained in `u`. -/
theorem IsPreconnected.subset_of_closure_inter_subset (hs : IsPreconnected s) (hu : IsOpen u)
    (h'u : (s ∩ u).Nonempty) (h : closure u ∩ s ⊆ u) : s ⊆ u := by
  have A : s ⊆ u ∪ closure uᶜ := by
    intro x hx
    by_cases xu : x ∈ u
    · exact Or.inl xu
    · right
      intro h'x
      exact xu (h (mem_inter h'x hx))
  apply hs.subset_left_of_subset_union hu isClosed_closure.isOpen_compl _ A h'u
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)
#align is_preconnected.subset_of_closure_inter_subset IsPreconnected.subset_of_closure_inter_subset

theorem IsPreconnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ×ˢ t) := by
  apply isPreconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  refine' ⟨Prod.mk a₁ '' t ∪ flip Prod.mk b₂ '' s, _, .inl ⟨b₁, hb₁, rfl⟩, .inr ⟨a₂, ha₂, rfl⟩, _⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    exacts [⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
  · exact (ht.image _ (Continuous.Prod.mk _).continuousOn).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.image _ (continuous_id.prod_mk continuous_const).continuousOn)
#align is_preconnected.prod IsPreconnected.prod

theorem IsConnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConnected s)
    (ht : IsConnected t) : IsConnected (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
#align is_connected.prod IsConnected.prod

theorem isPreconnected_univ_pi [∀ i, TopologicalSpace (π i)] {s : ∀ i, Set (π i)}
    (hs : ∀ i, IsPreconnected (s i)) : IsPreconnected (pi univ s) := by
  rintro u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩
  induction' I using Finset.induction_on with i I _ ihI
  · refine' ⟨g, hgs, ⟨_, hgv⟩⟩
    simpa using hI
  · rw [Finset.piecewise_insert] at hI
    have := I.piecewise_mem_set_pi hfs hgs
    refine' (hsuv this).elim ihI fun h => _
    set S := update (I.piecewise f g) i '' s i
    have hsub : S ⊆ pi univ s := by
      refine' image_subset_iff.2 fun z hz => _
      rwa [update_preimage_univ_pi]
      exact fun j _ => this j trivial
    have hconn : IsPreconnected S :=
      (hs i).image _ (continuous_const.update i continuous_id).continuousOn
    have hSu : (S ∩ u).Nonempty := ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩
    have hSv : (S ∩ v).Nonempty := ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩
    refine' (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono _
    exact inter_subset_inter_left _ hsub
#align is_preconnected_univ_pi isPreconnected_univ_pi

@[simp]
theorem isConnected_univ_pi [∀ i, TopologicalSpace (π i)] {s : ∀ i, Set (π i)} :
    IsConnected (pi univ s) ↔ ∀ i, IsConnected (s i) := by
  simp only [IsConnected, ← univ_pi_nonempty_iff, forall_and, and_congr_right_iff]
  refine' fun hne => ⟨fun hc i => _, isPreconnected_univ_pi⟩
  rw [← eval_image_univ_pi hne]
  exact hc.image _ (continuous_apply _).continuousOn
#align is_connected_univ_pi isConnected_univ_pi

theorem Sigma.isConnected_iff [∀ i, TopologicalSpace (π i)] {s : Set (Σi, π i)} :
    IsConnected s ↔ ∃ i t, IsConnected t ∧ s = Sigma.mk i '' t := by
  refine' ⟨fun hs => _, _⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s ⊆ range (Sigma.mk i) :=
      hs.isPreconnected.subset_clopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_openMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn
#align sigma.is_connected_iff Sigma.isConnected_iff

theorem Sigma.isPreconnected_iff [hι : Nonempty ι] [∀ i, TopologicalSpace (π i)]
    {s : Set (Σi, π i)} : IsPreconnected s ↔ ∃ i t, IsPreconnected t ∧ s = Sigma.mk i '' t := by
  refine' ⟨fun hs => _, _⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      refine' ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn
#align sigma.is_preconnected_iff Sigma.isPreconnected_iff

theorem Sum.isConnected_iff [TopologicalSpace β] {s : Set (Sum α β)} :
    IsConnected s ↔
      (∃ t, IsConnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsConnected t ∧ s = Sum.inr '' t := by
  refine' ⟨fun hs => _, _⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s ⊆ range Sum.inl :=
        hs.isPreconnected.subset_clopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine' Or.inl ⟨Sum.inl ⁻¹' s, _, _⟩
      · exact hs.preimage_of_openMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s ⊆ range Sum.inr :=
        hs.isPreconnected.subset_clopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine' Or.inr ⟨Sum.inr ⁻¹' s, _, _⟩
      · exact hs.preimage_of_openMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn
#align sum.is_connected_iff Sum.isConnected_iff

theorem Sum.isPreconnected_iff [TopologicalSpace β] {s : Set (Sum α β)} :
    IsPreconnected s ↔
      (∃ t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsPreconnected t ∧ s = Sum.inr '' t := by
  refine' ⟨fun hs => _, _⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn
#align sum.is_preconnected_iff Sum.isPreconnected_iff

/-- The connected component of a point is the maximal connected set
that contains this point. -/
def connectedComponent (x : α) : Set α :=
  ⋃₀ { s : Set α | IsPreconnected s ∧ x ∈ s }
#align connected_component connectedComponent

/-- Given a set `F` in a topological space `α` and a point `x : α`, the connected
component of `x` in `F` is the connected component of `x` in the subtype `F` seen as
a set in `α`. This definition does not make sense if `x` is not in `F` so we return the
empty set in this case. -/
def connectedComponentIn (F : Set α) (x : α) : Set α :=
  if h : x ∈ F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅
#align connected_component_in connectedComponentIn

theorem connectedComponentIn_eq_image {F : Set α} {x : α} (h : x ∈ F) :
    connectedComponentIn F x = (↑) '' connectedComponent (⟨x, h⟩ : F) :=
  dif_pos h
#align connected_component_in_eq_image connectedComponentIn_eq_image

theorem connectedComponentIn_eq_empty {F : Set α} {x : α} (h : x ∉ F) :
    connectedComponentIn F x = ∅ :=
  dif_neg h
#align connected_component_in_eq_empty connectedComponentIn_eq_empty

theorem mem_connectedComponent {x : α} : x ∈ connectedComponent x :=
  mem_sUnion_of_mem (mem_singleton x) ⟨isPreconnected_singleton, mem_singleton x⟩
#align mem_connected_component mem_connectedComponent

theorem mem_connectedComponentIn {x : α} {F : Set α} (hx : x ∈ F) : x ∈ connectedComponentIn F x :=
  by simp [connectedComponentIn_eq_image hx, mem_connectedComponent, hx]
#align mem_connected_component_in mem_connectedComponentIn

theorem connectedComponent_nonempty {x : α} : (connectedComponent x).Nonempty :=
  ⟨x, mem_connectedComponent⟩
#align connected_component_nonempty connectedComponent_nonempty

theorem connectedComponentIn_nonempty_iff {x : α} {F : Set α} :
    (connectedComponentIn F x).Nonempty ↔ x ∈ F := by
  rw [connectedComponentIn]
  split_ifs <;> simp [connectedComponent_nonempty, *]
#align connected_component_in_nonempty_iff connectedComponentIn_nonempty_iff

theorem connectedComponentIn_subset (F : Set α) (x : α) : connectedComponentIn F x ⊆ F := by
  rw [connectedComponentIn]
  split_ifs <;> simp
#align connected_component_in_subset connectedComponentIn_subset

theorem isPreconnected_connectedComponent {x : α} : IsPreconnected (connectedComponent x) :=
  isPreconnected_sUnion x _ (fun _ => And.right) fun _ => And.left
#align is_preconnected_connected_component isPreconnected_connectedComponent

theorem isPreconnected_connectedComponentIn {x : α} {F : Set α} :
    IsPreconnected (connectedComponentIn F x) := by
  rw [connectedComponentIn]; split_ifs
  · exact inducing_subtype_val.isPreconnected_image.mpr isPreconnected_connectedComponent
  · exact isPreconnected_empty
#align is_preconnected_connected_component_in isPreconnected_connectedComponentIn

theorem isConnected_connectedComponent {x : α} : IsConnected (connectedComponent x) :=
  ⟨⟨x, mem_connectedComponent⟩, isPreconnected_connectedComponent⟩
#align is_connected_connected_component isConnected_connectedComponent

theorem isConnected_connectedComponentIn_iff {x : α} {F : Set α} :
    IsConnected (connectedComponentIn F x) ↔ x ∈ F := by
  simp_rw [← connectedComponentIn_nonempty_iff, IsConnected, isPreconnected_connectedComponentIn,
    and_true_iff]
#align is_connected_connected_component_in_iff isConnected_connectedComponentIn_iff

theorem IsPreconnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsPreconnected s)
    (H2 : x ∈ s) : s ⊆ connectedComponent x := fun _z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩
#align is_preconnected.subset_connected_component IsPreconnected.subset_connectedComponent

theorem IsPreconnected.subset_connectedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s)
    (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ connectedComponentIn F x := by
  have : IsPreconnected (((↑) : F → α) ⁻¹' s) := by
    refine' inducing_subtype_val.isPreconnected_image.mp _
    rwa [Subtype.image_preimage_coe, inter_eq_left_iff_subset.mpr hsF]
  have h2xs : (⟨x, hsF hxs⟩ : F) ∈ (↑) ⁻¹' s := by
    rw [mem_preimage]
    exact hxs
  have := this.subset_connectedComponent h2xs
  rw [connectedComponentIn_eq_image (hsF hxs)]
  refine' Subset.trans _ (image_subset _ this)
  rw [Subtype.image_preimage_coe, inter_eq_left_iff_subset.mpr hsF]
#align is_preconnected.subset_connected_component_in IsPreconnected.subset_connectedComponentIn

theorem IsConnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsConnected s)
    (H2 : x ∈ s) : s ⊆ connectedComponent x :=
  H1.2.subset_connectedComponent H2
#align is_connected.subset_connected_component IsConnected.subset_connectedComponent

theorem IsPreconnected.connectedComponentIn {x : α} {F : Set α} (h : IsPreconnected F)
    (hx : x ∈ F) : connectedComponentIn F x = F :=
  (connectedComponentIn_subset F x).antisymm (h.subset_connectedComponentIn hx subset_rfl)
#align is_preconnected.connected_component_in IsPreconnected.connectedComponentIn

theorem connectedComponent_eq {x y : α} (h : y ∈ connectedComponent x) :
    connectedComponent x = connectedComponent y :=
  eq_of_subset_of_subset (isConnected_connectedComponent.subset_connectedComponent h)
    (isConnected_connectedComponent.subset_connectedComponent
      (Set.mem_of_mem_of_subset mem_connectedComponent
        (isConnected_connectedComponent.subset_connectedComponent h)))
#align connected_component_eq connectedComponent_eq

theorem connectedComponent_eq_iff_mem {x y : α} :
    connectedComponent x = connectedComponent y ↔ x ∈ connectedComponent y :=
  ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩
#align connected_component_eq_iff_mem connectedComponent_eq_iff_mem

theorem connectedComponentIn_eq {x y : α} {F : Set α} (h : y ∈ connectedComponentIn F x) :
    connectedComponentIn F x = connectedComponentIn F y := by
  have hx : x ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, h⟩
  simp_rw [connectedComponentIn_eq_image hx] at h⊢
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h
  simp_rw [connectedComponentIn_eq_image hy, connectedComponent_eq h2y]
#align connected_component_in_eq connectedComponentIn_eq

theorem connectedComponentIn_univ (x : α) : connectedComponentIn univ x = connectedComponent x :=
  subset_antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent <|
      mem_connectedComponentIn trivial)
    (isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent <|
      subset_univ _)
#align connected_component_in_univ connectedComponentIn_univ

theorem connectedComponent_disjoint {x y : α} (h : connectedComponent x ≠ connectedComponent y) :
    Disjoint (connectedComponent x) (connectedComponent y) :=
  Set.disjoint_left.2 fun _ h1 h2 =>
    h ((connectedComponent_eq h1).trans (connectedComponent_eq h2).symm)
#align connected_component_disjoint connectedComponent_disjoint

theorem isClosed_connectedComponent {x : α} : IsClosed (connectedComponent x) :=
  closure_subset_iff_isClosed.1 <|
    isConnected_connectedComponent.closure.subset_connectedComponent <|
      subset_closure mem_connectedComponent
#align is_closed_connected_component isClosed_connectedComponent

theorem Continuous.image_connectedComponent_subset [TopologicalSpace β] {f : α → β}
    (h : Continuous f) (a : α) : f '' connectedComponent a ⊆ connectedComponent (f a) :=
  (isConnected_connectedComponent.image f h.continuousOn).subset_connectedComponent
    ((mem_image f (connectedComponent a) (f a)).2 ⟨a, mem_connectedComponent, rfl⟩)
#align continuous.image_connected_component_subset Continuous.image_connectedComponent_subset

theorem Continuous.mapsTo_connectedComponent [TopologicalSpace β] {f : α → β} (h : Continuous f)
    (a : α) : MapsTo f (connectedComponent a) (connectedComponent (f a)) :=
  mapsTo'.2 <| h.image_connectedComponent_subset a
#align continuous.maps_to_connected_component Continuous.mapsTo_connectedComponent

theorem irreducibleComponent_subset_connectedComponent {x : α} :
    irreducibleComponent x ⊆ connectedComponent x :=
  isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent
#align irreducible_component_subset_connected_component irreducibleComponent_subset_connectedComponent

@[mono]
theorem connectedComponentIn_mono (x : α) {F G : Set α} (h : F ⊆ G) :
    connectedComponentIn F x ⊆ connectedComponentIn G x := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image (h hx), ←
      show ((↑) : G → α) ∘ inclusion h = (↑) from rfl, image_comp]
    exact image_subset _ ((continuous_inclusion h).image_connectedComponent_subset ⟨x, hx⟩)
  · rw [connectedComponentIn_eq_empty hx]
    exact Set.empty_subset _
#align connected_component_in_mono connectedComponentIn_mono

/-- A preconnected space is one where there is no non-trivial open partition. -/
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a preconnected space is a preconnected set. -/
  isPreconnected_univ : IsPreconnected (univ : Set α)
#align preconnected_space PreconnectedSpace

export PreconnectedSpace (isPreconnected_univ)

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
class ConnectedSpace (α : Type u) [TopologicalSpace α] extends PreconnectedSpace α : Prop where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α
#align connected_space ConnectedSpace

attribute [instance 50] ConnectedSpace.toNonempty  -- see Note [lower instance priority]

-- see Note [lower instance priority]
theorem isConnected_univ [ConnectedSpace α] : IsConnected (univ : Set α) :=
  ⟨univ_nonempty, isPreconnected_univ⟩
#align is_connected_univ isConnected_univ

theorem isPreconnected_range [TopologicalSpace β] [PreconnectedSpace α] {f : α → β}
    (h : Continuous f) : IsPreconnected (range f) :=
  @image_univ _ _ f ▸ isPreconnected_univ.image _ h.continuousOn
#align is_preconnected_range isPreconnected_range

theorem isConnected_range [TopologicalSpace β] [ConnectedSpace α] {f : α → β} (h : Continuous f) :
    IsConnected (range f) :=
  ⟨range_nonempty f, isPreconnected_range h⟩
#align is_connected_range isConnected_range

theorem DenseRange.preconnectedSpace [TopologicalSpace β] [PreconnectedSpace α] {f : α → β}
    (hf : DenseRange f) (hc : Continuous f) : PreconnectedSpace β :=
  ⟨hf.closure_eq ▸ (isPreconnected_range hc).closure⟩
#align dense_range.preconnected_space DenseRange.preconnectedSpace

theorem connectedSpace_iff_connectedComponent :
    ConnectedSpace α ↔ ∃ x : α, connectedComponent x = univ := by
  constructor
  · rintro ⟨⟨x⟩⟩
    exact
      ⟨x, eq_univ_of_univ_subset <| isPreconnected_univ.subset_connectedComponent (mem_univ x)⟩
  · rintro ⟨x, h⟩
    haveI : PreconnectedSpace α :=
      ⟨by rw [← h]; exact isPreconnected_connectedComponent⟩
    exact ⟨⟨x⟩⟩
#align connected_space_iff_connected_component connectedSpace_iff_connectedComponent

theorem preconnectedSpace_iff_connectedComponent :
    PreconnectedSpace α ↔ ∀ x : α, connectedComponent x = univ := by
  constructor
  · intro h x
    exact eq_univ_of_univ_subset <| isPreconnected_univ.subset_connectedComponent (mem_univ x)
  · intro h
    cases' isEmpty_or_nonempty α with hα hα
    · exact ⟨by rw [univ_eq_empty_iff.mpr hα]; exact isPreconnected_empty⟩
    · exact ⟨by rw [← h (Classical.choice hα)]; exact isPreconnected_connectedComponent⟩
#align preconnected_space_iff_connected_component preconnectedSpace_iff_connectedComponent

@[simp]
theorem PreconnectedSpace.connectedComponent_eq_univ {X : Type _} [TopologicalSpace X]
    [h : PreconnectedSpace X] (x : X) : connectedComponent x = univ :=
  preconnectedSpace_iff_connectedComponent.mp h x
#align preconnected_space.connected_component_eq_univ PreconnectedSpace.connectedComponent_eq_univ

instance [TopologicalSpace β] [PreconnectedSpace α] [PreconnectedSpace β] :
    PreconnectedSpace (α × β) :=
  ⟨by
    rw [← univ_prod_univ]
    exact isPreconnected_univ.prod isPreconnected_univ⟩

instance [TopologicalSpace β] [ConnectedSpace α] [ConnectedSpace β] : ConnectedSpace (α × β) :=
  ⟨inferInstance⟩

instance [∀ i, TopologicalSpace (π i)] [∀ i, PreconnectedSpace (π i)] :
    PreconnectedSpace (∀ i, π i) :=
  ⟨by rw [← pi_univ univ]; exact isPreconnected_univ_pi fun i => isPreconnected_univ⟩

instance [∀ i, TopologicalSpace (π i)] [∀ i, ConnectedSpace (π i)] : ConnectedSpace (∀ i, π i) :=
  ⟨inferInstance⟩

-- see Note [lower instance priority]
instance (priority := 100) PreirreducibleSpace.preconnectedSpace (α : Type u) [TopologicalSpace α]
    [PreirreducibleSpace α] : PreconnectedSpace α :=
  ⟨isPreirreducible_univ.isPreconnected⟩
#align preirreducible_space.preconnected_space PreirreducibleSpace.preconnectedSpace

-- see Note [lower instance priority]
instance (priority := 100) IrreducibleSpace.connectedSpace (α : Type u) [TopologicalSpace α]
    [IrreducibleSpace α] : ConnectedSpace α where toNonempty := IrreducibleSpace.toNonempty
#align irreducible_space.connected_space IrreducibleSpace.connectedSpace

theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s ∪ t = univ → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t
#align nonempty_inter nonempty_inter

theorem isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s ≠ ∅ ∧ sᶜ ≠ ∅ :=
        ⟨mt Or.inl h,
          mt (fun h2 => Or.inr <| (by rw [← compl_compl s, h2, compl_empty] : s = univ)) h⟩
      let ⟨_, h2, h3⟩ :=
        nonempty_inter hs.1 hs.2.isOpen_compl (union_compl_self s) (nonempty_iff_ne_empty.2 h1.1)
          (nonempty_iff_ne_empty.2 h1.2)
      h3 h2,
    by rintro (rfl | rfl) <;> [exact isClopen_empty; exact isClopen_univ]⟩
#align is_clopen_iff isClopen_iff

theorem IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : s.Nonempty) :
    s = univ :=
  (isClopen_iff.mp h').resolve_left h.ne_empty
#align is_clopen.eq_univ IsClopen.eq_univ

theorem frontier_eq_empty_iff [PreconnectedSpace α] {s : Set α} :
    frontier s = ∅ ↔ s = ∅ ∨ s = univ :=
  isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff
#align frontier_eq_empty_iff frontier_eq_empty_iff

theorem nonempty_frontier_iff [PreconnectedSpace α] {s : Set α} :
    (frontier s).Nonempty ↔ s.Nonempty ∧ s ≠ univ := by
  simp only [nonempty_iff_ne_empty, Ne.def, frontier_eq_empty_iff, not_or]
#align nonempty_frontier_iff nonempty_frontier_iff

theorem Subtype.preconnectedSpace {s : Set α} (h : IsPreconnected s) : PreconnectedSpace s where
  isPreconnected_univ := by
    rwa [← inducing_subtype_val.isPreconnected_image, image_univ, Subtype.range_val]
#align subtype.preconnected_space Subtype.preconnectedSpace

theorem Subtype.connectedSpace {s : Set α} (h : IsConnected s) : ConnectedSpace s where
  toPreconnectedSpace := Subtype.preconnectedSpace h.isPreconnected
  toNonempty := h.nonempty.to_subtype
#align subtype.connected_space Subtype.connectedSpace

theorem isPreconnected_iff_preconnectedSpace {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s :=
  ⟨Subtype.preconnectedSpace, fun h => by
    simpa using isPreconnected_univ.image ((↑) : s → α) continuous_subtype_val.continuousOn⟩
#align is_preconnected_iff_preconnected_space isPreconnected_iff_preconnectedSpace

theorem isConnected_iff_connectedSpace {s : Set α} : IsConnected s ↔ ConnectedSpace s :=
  ⟨Subtype.connectedSpace, fun h =>
    ⟨nonempty_subtype.mp h.2, isPreconnected_iff_preconnectedSpace.mpr h.1⟩⟩
#align is_connected_iff_connected_space isConnected_iff_connectedSpace

/-- A set `s` is preconnected if and only if for every cover by two open sets that are disjoint on
`s`, it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_disjoint {s : Set α} :
    IsPreconnected s ↔
      ∀ u v, IsOpen u → IsOpen v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    rw [← nonempty_iff_ne_empty]
    simp [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    rw [nonempty_iff_ne_empty]
    intro H
    specialize h u v hu hv hs H
    contrapose H
    apply Nonempty.ne_empty
    cases' h with h h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩
#align is_preconnected_iff_subset_of_disjoint isPreconnected_iff_subset_of_disjoint

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
theorem isConnected_iff_sUnion_disjoint_open {s : Set α} :
    IsConnected s ↔
      ∀ U : Finset (Set α), (∀ u v : Set α, u ∈ U → v ∈ U → (s ∩ (u ∩ v)).Nonempty → u = v) →
        (∀ u ∈ U, IsOpen u) → (s ⊆ ⋃₀ ↑U) → ∃ u ∈ U, s ⊆ u := by
  rw [IsConnected, isPreconnected_iff_subset_of_disjoint]
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on
    case empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    case insert u U uU IH =>
      simp only [← ball_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}
#align is_connected_iff_sUnion_disjoint_open isConnected_iff_sUnion_disjoint_open

-- porting note: `IsPreconnected.subset_clopen` moved up from here

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem disjoint_or_subset_of_clopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) :
    Disjoint s t ∨ s ⊆ t :=
  (disjoint_or_nonempty_inter s t).imp_right <| hs.subset_clopen ht
#align disjoint_or_subset_of_clopen disjoint_or_subset_of_clopen

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_disjoint_closed :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    rw [← nonempty_iff_ne_empty]
    simp [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    rw [nonempty_iff_ne_empty]
    intro H
    specialize h u v hu hv hs H
    contrapose H
    apply Nonempty.ne_empty
    cases' h with h h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩
#align is_preconnected_iff_subset_of_disjoint_closed isPreconnected_iff_subset_of_disjoint_closed

/-- A closed set `s` is preconnected if and only if for every cover by two closed sets that are
disjoint, it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → Disjoint u v → s ⊆ u ∨ s ⊆ v := by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq, inter_empty]
  have H1 := H (u ∩ s) (v ∩ s)
  rw [subset_inter_iff, subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]
#align is_preconnected_iff_subset_of_fully_disjoint_closed isPreconnected_iff_subset_of_fully_disjoint_closed

theorem IsClopen.connectedComponent_subset {x} (hs : IsClopen s) (hx : x ∈ s) :
    connectedComponent x ⊆ s :=
  isPreconnected_connectedComponent.subset_clopen hs ⟨x, mem_connectedComponent, hx⟩
#align is_clopen.connected_component_subset IsClopen.connectedComponent_subset

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
theorem connectedComponent_subset_iInter_clopen {x : α} :
    connectedComponent x ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2
#align connected_component_subset_Inter_clopen connectedComponent_subset_iInter_clopen

/-- A clopen set is the union of its connected components. -/
theorem IsClopen.biUnion_connectedComponent_eq {Z : Set α} (h : IsClopen Z) :
    (⋃ x ∈ Z, connectedComponent x) = Z :=
  Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent
#align is_clopen.bUnion_connected_component_eq IsClopen.biUnion_connectedComponent_eq

/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
theorem preimage_connectedComponent_connected [TopologicalSpace β] {f : α → β}
    (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t}))
    (hcl : ∀ T : Set β, IsClosed T ↔ IsClosed (f ⁻¹' T)) (t : β) :
    IsConnected (f ⁻¹' connectedComponent t) := by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage connectedComponent_nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' connectedComponent t) :=
    (hcl (connectedComponent t)).1 isClosed_connectedComponent
  -- To show it's preconnected we decompose (f ⁻¹' connectedComponent t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose connectedComponent t into T₁ and T₂
  -- we will show that connectedComponent t is a subset of either and hence
  -- (f ⁻¹' connectedComponent t) is a subset of u or v
  let T₁ := { t' ∈ connectedComponent t | f ⁻¹' {t'} ⊆ u }
  let T₂ := { t' ∈ connectedComponent t | f ⁻¹' {t'} ⊆ v }
  have fiber_decomp : ∀ t' ∈ connectedComponent t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq, inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' connectedComponent t ∩ u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine' iUnion₂_subset fun t' ht' => subset_inter _ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' connectedComponent t ∩ v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine' iUnion₂_subset fun t' ht' => subset_inter _ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover connectedComponent t and are disjoint.
  have hT₁ : IsClosed T₁ := (hcl T₁).2 (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := (hcl T₂).2 (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : connectedComponent t ⊆ T₁ ∪ T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    cases' fiber_decomp t' ht' with htu htv
    · left
      exact ⟨ht', htu⟩
    right
    exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine' Disjoint.of_preimage hf _
    rw [T₁_u, T₂_v, disjoint_iff_inter_eq_empty, ← inter_inter_distrib_left, uv_disj.inter_eq,
      inter_empty]
  -- Now we do cases on whether (connectedComponent t) is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  cases' (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_connectedComponent).1
    isPreconnected_connectedComponent T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' connectedComponent t ⊆ f ⁻¹' T₁
      from (this.trans T₁_u.1).trans (inter_subset_right _ _)
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' connectedComponent t ⊆ f ⁻¹' T₂
      from (this.trans T₂_v.1).trans (inter_subset_right _ _)
    exact preimage_mono h
#align preimage_connected_component_connected preimage_connectedComponent_connected

theorem QuotientMap.preimage_connectedComponent [TopologicalSpace β] {f : α → β}
    (hf : QuotientMap f) (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f ⁻¹' connectedComponent (f a) = connectedComponent a :=
  ((preimage_connectedComponent_connected h_fibers (fun _ => hf.isClosed_preimage.symm)
      _).subset_connectedComponent mem_connectedComponent).antisymm
    (hf.continuous.mapsTo_connectedComponent a)
#align quotient_map.preimage_connected_component QuotientMap.preimage_connectedComponent

theorem QuotientMap.image_connectedComponent [TopologicalSpace β] {f : α → β} (hf : QuotientMap f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f '' connectedComponent a = connectedComponent (f a) := by
  rw [← hf.preimage_connectedComponent h_fibers, image_preimage_eq _ hf.surjective]
#align quotient_map.image_connected_component QuotientMap.image_connectedComponent

end Preconnected

section LocallyConnectedSpace

/-- A topological space is **locally connected** if each neighborhood filter admits a basis
of connected *open* sets. Note that it is equivalent to each point having a basis of connected
(non necessarily open) sets but in a non-trivial way, so we choose this definition and prove the
equivalence later in `locallyConnectedSpace_iff_connected_basis`. -/
class LocallyConnectedSpace (α : Type _) [TopologicalSpace α] : Prop where
  /-- Open connected neighborhoods form a basis of the neighborhoods filter. -/
  open_connected_basis : ∀ x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x ∈ s ∧ IsConnected s) id
#align locally_connected_space LocallyConnectedSpace

theorem locallyConnectedSpace_iff_open_connected_basis :
    LocallyConnectedSpace α ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x ∈ s ∧ IsConnected s) id :=
  ⟨@LocallyConnectedSpace.open_connected_basis _ _, LocallyConnectedSpace.mk⟩
#align locally_connected_space_iff_open_connected_basis locallyConnectedSpace_iff_open_connected_basis

theorem locallyConnectedSpace_iff_open_connected_subsets :
    LocallyConnectedSpace α ↔
      ∀ x, ∀ U ∈ 𝓝 x, ∃ V : Set α, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V := by
  simp_rw [locallyConnectedSpace_iff_open_connected_basis]
  refine forall_congr' fun _ => ?_
  constructor
  · intro h U hU
    rcases h.mem_iff.mp hU with ⟨V, hV, hVU⟩
    exact ⟨V, hVU, hV⟩
  · exact fun h => ⟨fun U => ⟨fun hU =>
      let ⟨V, hVU, hV⟩ := h U hU
      ⟨V, hV, hVU⟩, fun ⟨V, ⟨hV, hxV, _⟩, hVU⟩ => mem_nhds_iff.mpr ⟨V, hVU, hV, hxV⟩⟩⟩
#align locally_connected_space_iff_open_connected_subsets locallyConnectedSpace_iff_open_connected_subsets

/-- A space with discrete topology is a locally connected space. -/
instance (priority := 100) DiscreteTopology.toLocallyConnectedSpace (α) [TopologicalSpace α]
    [DiscreteTopology α] : LocallyConnectedSpace α :=
  locallyConnectedSpace_iff_open_connected_subsets.2 fun x _U hU =>
    ⟨{x}, singleton_subset_iff.2 <| mem_of_mem_nhds hU, isOpen_discrete _, rfl,
      isConnected_singleton⟩
#align discrete_topology.to_locally_connected_space DiscreteTopology.toLocallyConnectedSpace

theorem connectedComponentIn_mem_nhds [LocallyConnectedSpace α] {F : Set α} {x : α} (h : F ∈ 𝓝 x) :
    connectedComponentIn F x ∈ 𝓝 x := by
  rw [(LocallyConnectedSpace.open_connected_basis x).mem_iff] at h
  rcases h with ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩
  exact mem_nhds_iff.mpr ⟨s, h2s.isPreconnected.subset_connectedComponentIn hxs hsF, h1s, hxs⟩
#align connected_component_in_mem_nhds connectedComponentIn_mem_nhds

protected theorem IsOpen.connectedComponentIn [LocallyConnectedSpace α] {F : Set α} {x : α}
    (hF : IsOpen F) : IsOpen (connectedComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponentIn_eq hy]
  exact connectedComponentIn_mem_nhds (hF.mem_nhds <| connectedComponentIn_subset F x hy)
#align is_open.connected_component_in IsOpen.connectedComponentIn

theorem isOpen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsOpen (connectedComponent x) := by
  rw [← connectedComponentIn_univ]
  exact isOpen_univ.connectedComponentIn
#align is_open_connected_component isOpen_connectedComponent

theorem isClopen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsClopen (connectedComponent x) :=
  ⟨isOpen_connectedComponent, isClosed_connectedComponent⟩
#align is_clopen_connected_component isClopen_connectedComponent

theorem locallyConnectedSpace_iff_connectedComponentIn_open :
    LocallyConnectedSpace α ↔
      ∀ F : Set α, IsOpen F → ∀ x ∈ F, IsOpen (connectedComponentIn F x) := by
  constructor
  · intro h
    exact fun F hF x _ => hF.connectedComponentIn
  · intro h
    rw [locallyConnectedSpace_iff_open_connected_subsets]
    refine' fun x U hU =>
        ⟨connectedComponentIn (interior U) x,
          (connectedComponentIn_subset _ _).trans interior_subset, h _ isOpen_interior x _,
          mem_connectedComponentIn _, isConnected_connectedComponentIn_iff.mpr _⟩ <;>
      exact mem_interior_iff_mem_nhds.mpr hU
#align locally_connected_space_iff_connected_component_in_open locallyConnectedSpace_iff_connectedComponentIn_open

theorem locallyConnectedSpace_iff_connected_subsets :
    LocallyConnectedSpace α ↔ ∀ (x : α), ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPreconnected V ∧ V ⊆ U := by
  constructor
  · rw [locallyConnectedSpace_iff_open_connected_subsets]
    intro h x U hxU
    rcases h x U hxU with ⟨V, hVU, hV₁, hxV, hV₂⟩
    exact ⟨V, hV₁.mem_nhds hxV, hV₂.isPreconnected, hVU⟩
  · rw [locallyConnectedSpace_iff_connectedComponentIn_open]
    refine' fun h U hU x _ => isOpen_iff_mem_nhds.mpr fun y hy => _
    rw [connectedComponentIn_eq hy]
    rcases h y U (hU.mem_nhds <| (connectedComponentIn_subset _ _) hy) with ⟨V, hVy, hV, hVU⟩
    exact Filter.mem_of_superset hVy (hV.subset_connectedComponentIn (mem_of_mem_nhds hVy) hVU)
#align locally_connected_space_iff_connected_subsets locallyConnectedSpace_iff_connected_subsets

theorem locallyConnectedSpace_iff_connected_basis :
    LocallyConnectedSpace α ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set α => s ∈ 𝓝 x ∧ IsPreconnected s) id := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  exact forall_congr' <| fun x => Filter.hasBasis_self.symm
#align locally_connected_space_iff_connected_basis locallyConnectedSpace_iff_connected_basis

theorem locallyConnectedSpace_of_connected_bases {ι : Type _} (b : α → ι → Set α) (p : α → ι → Prop)
    (hbasis : ∀ x, (𝓝 x).HasBasis (p x) (b x))
    (hconnected : ∀ x i, p x i → IsPreconnected (b x i)) : LocallyConnectedSpace α := by
  rw [locallyConnectedSpace_iff_connected_basis]
  exact fun x =>
    (hbasis x).to_hasBasis
      (fun i hi => ⟨b x i, ⟨(hbasis x).mem_of_mem hi, hconnected x i hi⟩, subset_rfl⟩) fun s hs =>
      ⟨(hbasis x).index s hs.1, ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩
#align locally_connected_space_of_connected_bases locallyConnectedSpace_of_connected_bases

end LocallyConnectedSpace

section TotallyDisconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, ie either empty or a singleton.-/
def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.Subsingleton
#align is_totally_disconnected IsTotallyDisconnected

theorem isTotallyDisconnected_empty : IsTotallyDisconnected (∅ : Set α) := fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim
#align is_totally_disconnected_empty isTotallyDisconnected_empty

theorem isTotallyDisconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) := fun _ ht _ =>
  subsingleton_singleton.anti ht
#align is_totally_disconnected_singleton isTotallyDisconnected_singleton

/-- A space is totally disconnected if all of its connected components are singletons. -/
class TotallyDisconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally disconnected space is totally disconnected. -/
  isTotallyDisconnected_univ : IsTotallyDisconnected (univ : Set α)
#align totally_disconnected_space TotallyDisconnectedSpace

theorem IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α}
    (h : IsPreconnected s) : s.Subsingleton :=
  TotallyDisconnectedSpace.isTotallyDisconnected_univ s (subset_univ s) h
#align is_preconnected.subsingleton IsPreconnected.subsingleton

instance Pi.totallyDisconnectedSpace {α : Type _} {β : α → Type _}
    [∀ a, TopologicalSpace (β a)] [∀ a, TotallyDisconnectedSpace (β a)] :
    TotallyDisconnectedSpace (∀ a : α, β a) :=
  ⟨fun t _ h2 =>
    have this : ∀ a, IsPreconnected ((fun x : ∀ a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).continuousOn
    fun x x_in y y_in => funext fun a => (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩
#align pi.totally_disconnected_space Pi.totallyDisconnectedSpace

instance Prod.totallyDisconnectedSpace [TopologicalSpace β] [TotallyDisconnectedSpace α]
    [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β) :=
  ⟨fun t _ h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.continuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.continuousOn
    fun x hx y hy =>
    Prod.ext (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
      (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩
#align prod.totally_disconnected_space Prod.totallyDisconnectedSpace

instance [TopologicalSpace β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
    TotallyDisconnectedSpace (Sum α β) := by
  refine' ⟨fun s _ hs => _⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isPreconnected_iff.1 hs
  · exact ht.subsingleton.image _
  · exact ht.subsingleton.image _

instance [∀ i, TopologicalSpace (π i)] [∀ i, TotallyDisconnectedSpace (π i)] :
    TotallyDisconnectedSpace (Σi, π i) := by
  refine' ⟨fun s _ hs => _⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact subsingleton_empty
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
    exact ht.isPreconnected.subsingleton.image _

-- porting note: reformulated using `Pairwise`
/-- Let `X` be a topological space, and suppose that for all distinct `x,y ∈ X`, there
  is some clopen set `U` such that `x ∈ U` and `y ∉ U`. Then `X` is totally disconnected. -/
theorem isTotallyDisconnected_of_clopen_set {X : Type _} [TopologicalSpace X]
    (hX : Pairwise fun x y => ∃ (U : Set X), IsClopen U ∧ x ∈ U ∧ y ∉ U) :
    IsTotallyDisconnected (Set.univ : Set X) := by
  rintro S - hS
  unfold Set.Subsingleton
  by_contra' h_contra
  rcases h_contra with ⟨x, hx, y, hy, hxy⟩
  obtain ⟨U, h_clopen, hxU, hyU⟩ := hX hxy
  specialize
    hS U (Uᶜ) h_clopen.1 h_clopen.compl.1 (fun a _ => em (a ∈ U)) ⟨x, hx, hxU⟩ ⟨y, hy, hyU⟩
  rw [inter_compl_self, Set.inter_empty] at hS
  exact Set.not_nonempty_empty hS
#align is_totally_disconnected_of_clopen_set isTotallyDisconnected_of_clopen_set

/-- A space is totally disconnected iff its connected components are subsingletons. -/
theorem totallyDisconnectedSpace_iff_connectedComponent_subsingleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, (connectedComponent x).Subsingleton := by
  constructor
  · intro h x
    apply h.1
    · exact subset_univ _
    exact isPreconnected_connectedComponent
  intro h; constructor
  intro s s_sub hs
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, x_in⟩)
  · exact subsingleton_empty
  · exact (h x).anti (hs.subset_connectedComponent x_in)
#align totally_disconnected_space_iff_connected_component_subsingleton totallyDisconnectedSpace_iff_connectedComponent_subsingleton

/-- A space is totally disconnected iff its connected components are singletons. -/
theorem totallyDisconnectedSpace_iff_connectedComponent_singleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, connectedComponent x = {x} := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
  refine forall_congr' fun x => ?_
  rw [subsingleton_iff_singleton]
  exact mem_connectedComponent
#align totally_disconnected_space_iff_connected_component_singleton totallyDisconnectedSpace_iff_connectedComponent_singleton

@[simp] theorem connectedComponent_eq_singleton [TotallyDisconnectedSpace α] (x : α) :
    connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton.1 ‹_› x
#align connected_component_eq_singleton connectedComponent_eq_singleton

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp]
theorem Continuous.image_connectedComponent_eq_singleton {β : Type _} [TopologicalSpace β]
    [TotallyDisconnectedSpace β] {f : α → β} (h : Continuous f) (a : α) :
    f '' connectedComponent a = {f a} :=
  (Set.subsingleton_iff_singleton <| mem_image_of_mem f mem_connectedComponent).mp
    (isPreconnected_connectedComponent.image f h.continuousOn).subsingleton
#align continuous.image_connected_component_eq_singleton Continuous.image_connectedComponent_eq_singleton

theorem isTotallyDisconnected_of_totallyDisconnectedSpace [TotallyDisconnectedSpace α] (s : Set α) :
    IsTotallyDisconnected s := fun t _ ht =>
  TotallyDisconnectedSpace.isTotallyDisconnected_univ _ t.subset_univ ht
#align is_totally_disconnected_of_totally_disconnected_space isTotallyDisconnected_of_totallyDisconnectedSpace

theorem isTotallyDisconnected_of_image [TopologicalSpace β] {f : α → β} (hf : ContinuousOn f s)
    (hf' : Injective f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  fun _t hts ht _x x_in _y y_in =>
  hf' <|
    h _ (image_subset f hts) (ht.image f <| hf.mono hts) (mem_image_of_mem f x_in)
      (mem_image_of_mem f y_in)
#align is_totally_disconnected_of_image isTotallyDisconnected_of_image

theorem Embedding.isTotallyDisconnected [TopologicalSpace β] {f : α → β} (hf : Embedding f)
    {s : Set α} (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  isTotallyDisconnected_of_image hf.continuous.continuousOn hf.inj h
#align embedding.is_totally_disconnected Embedding.isTotallyDisconnected

instance Subtype.totallyDisconnectedSpace {α : Type _} {p : α → Prop} [TopologicalSpace α]
    [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Subtype p) :=
  ⟨embedding_subtype_val.isTotallyDisconnected
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
#align subtype.totally_disconnected_space Subtype.totallyDisconnectedSpace

end TotallyDisconnected

section TotallySeparated

-- todo: reformulate using `Set.Pairwise`
/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
def IsTotallySeparated (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ Disjoint u v
#align is_totally_separated IsTotallySeparated

theorem isTotallySeparated_empty : IsTotallySeparated (∅ : Set α) := fun _ => False.elim
#align is_totally_separated_empty isTotallySeparated_empty

theorem isTotallySeparated_singleton {x} : IsTotallySeparated ({x} : Set α) := fun _ hp _ hq hpq =>
  (hpq <| (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim
#align is_totally_separated_singleton isTotallySeparated_singleton

theorem isTotallyDisconnected_of_isTotallySeparated {s : Set α} (H : IsTotallySeparated s) :
    IsTotallyDisconnected s := by
  intro t hts ht x x_in y y_in
  by_contra h
  obtain
    ⟨u : Set α, v : Set α, hu : IsOpen u, hv : IsOpen v, hxu : x ∈ u, hyv : y ∈ v, hs : s ⊆ u ∪ v,
      huv⟩ :=
    H x (hts x_in) y (hts y_in) h
  refine' (ht _ _ hu hv (hts.trans hs) ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩).ne_empty _
  rw [huv.inter_eq, inter_empty]
#align is_totally_disconnected_of_is_totally_separated isTotallyDisconnected_of_isTotallySeparated

alias isTotallyDisconnected_of_isTotallySeparated ← IsTotallySeparated.isTotallyDisconnected
#align is_totally_separated.is_totally_disconnected IsTotallySeparated.isTotallyDisconnected

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
class TotallySeparatedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally separated space is totally separated. -/
  isTotallySeparated_univ : IsTotallySeparated (univ : Set α)
#align totally_separated_space TotallySeparatedSpace

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.totallyDisconnectedSpace (α : Type u)
    [TopologicalSpace α] [TotallySeparatedSpace α] : TotallyDisconnectedSpace α :=
  ⟨TotallySeparatedSpace.isTotallySeparated_univ.isTotallyDisconnected⟩
#align totally_separated_space.totally_disconnected_space TotallySeparatedSpace.totallyDisconnectedSpace

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.of_discrete (α : Type _) [TopologicalSpace α]
    [DiscreteTopology α] : TotallySeparatedSpace α :=
  ⟨fun _ _ b _ h => ⟨{b}ᶜ, {b}, isOpen_discrete _, isOpen_discrete _, h, rfl,
    (compl_union_self _).symm.subset, disjoint_compl_left⟩⟩
#align totally_separated_space.of_discrete TotallySeparatedSpace.of_discrete

theorem exists_clopen_of_totally_separated {α : Type _} [TopologicalSpace α]
    [TotallySeparatedSpace α] {x y : α} (hxy : x ≠ y) :
    ∃ U : Set α, IsClopen U ∧ x ∈ U ∧ y ∈ Uᶜ := by
  obtain ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ :=
    TotallySeparatedSpace.isTotallySeparated_univ x (Set.mem_univ x) y (Set.mem_univ y) hxy
  have clopen_U := isClopen_inter_of_disjoint_cover_clopen isClopen_univ f hU hV disj
  rw [univ_inter _] at clopen_U
  rw [← Set.subset_compl_iff_disjoint_right, subset_compl_comm] at disj
  exact ⟨U, clopen_U, Ux, disj Vy⟩
#align exists_clopen_of_totally_separated exists_clopen_of_totally_separated

end TotallySeparated

section connectedComponentSetoid

/-- The setoid of connected components of a topological space -/
def connectedComponentSetoid (α : Type _) [TopologicalSpace α] : Setoid α :=
  ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩
#align connected_component_setoid connectedComponentSetoid

/-- The quotient of a space by its connected components -/
def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotient (connectedComponentSetoid α)
#align connected_components ConnectedComponents

namespace ConnectedComponents

/-- Coercion from a topological space to the set of connected components of this space. -/
def mk : α → ConnectedComponents α := Quotient.mk''

instance : CoeTC α (ConnectedComponents α) := ⟨mk⟩

@[simp]
theorem coe_eq_coe {x y : α} :
    (x : ConnectedComponents α) = y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''
#align connected_components.coe_eq_coe ConnectedComponents.coe_eq_coe

theorem coe_ne_coe {x y : α} :
    (x : ConnectedComponents α) ≠ y ↔ connectedComponent x ≠ connectedComponent y :=
  coe_eq_coe.not
#align connected_components.coe_ne_coe ConnectedComponents.coe_ne_coe

theorem coe_eq_coe' {x y : α} : (x : ConnectedComponents α) = y ↔ x ∈ connectedComponent y :=
  coe_eq_coe.trans connectedComponent_eq_iff_mem
#align connected_components.coe_eq_coe' ConnectedComponents.coe_eq_coe'

instance [Inhabited α] : Inhabited (ConnectedComponents α) :=
  ⟨mk default⟩

instance : TopologicalSpace (ConnectedComponents α) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

theorem surjective_coe : Surjective (mk : α → ConnectedComponents α) :=
  surjective_quot_mk _
#align connected_components.surjective_coe ConnectedComponents.surjective_coe

theorem quotientMap_coe : QuotientMap (mk : α → ConnectedComponents α) :=
  quotientMap_quot_mk
#align connected_components.quotient_map_coe ConnectedComponents.quotientMap_coe

@[continuity]
theorem continuous_coe : Continuous (mk : α → ConnectedComponents α) :=
  quotientMap_coe.continuous
#align connected_components.continuous_coe ConnectedComponents.continuous_coe

@[simp]
theorem range_coe : range (mk : α → ConnectedComponents α) = univ :=
  surjective_coe.range_eq
#align connected_components.range_coe ConnectedComponents.range_coe

end ConnectedComponents

variable [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α → β}

theorem Continuous.image_eq_of_connectedComponent_eq (h : Continuous f) (a b : α)
    (hab : connectedComponent a = connectedComponent b) : f a = f b :=
  singleton_eq_singleton_iff.1 <|
    h.image_connectedComponent_eq_singleton a ▸
      h.image_connectedComponent_eq_singleton b ▸ hab ▸ rfl
#align continuous.image_eq_of_connected_component_eq Continuous.image_eq_of_connectedComponent_eq

/--
The lift to `connectedComponents α` of a continuous map from `α` to a totally disconnected space
-/
def Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponents α → β := fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq
#align continuous.connected_components_lift Continuous.connectedComponentsLift

@[continuity]
theorem Continuous.connectedComponentsLift_continuous (h : Continuous f) :
    Continuous h.connectedComponentsLift :=
  h.quotient_liftOn' <| by convert h.image_eq_of_connectedComponent_eq
#align continuous.connected_components_lift_continuous Continuous.connectedComponentsLift_continuous

@[simp]
theorem Continuous.connectedComponentsLift_apply_coe (h : Continuous f) (x : α) :
    h.connectedComponentsLift x = f x :=
  rfl
#align continuous.connected_components_lift_apply_coe Continuous.connectedComponentsLift_apply_coe

@[simp]
theorem Continuous.connectedComponentsLift_comp_coe (h : Continuous f) :
    h.connectedComponentsLift ∘ (↑) = f :=
  rfl
#align continuous.connected_components_lift_comp_coe Continuous.connectedComponentsLift_comp_coe

theorem connectedComponents_lift_unique' {β : Sort _} {g₁ g₂ : ConnectedComponents α → β}
    (hg : g₁ ∘ ((↑) : α → ConnectedComponents α) = g₂ ∘ (↑)) : g₁ = g₂ :=
  ConnectedComponents.surjective_coe.injective_comp_right hg
#align connected_components_lift_unique' connectedComponents_lift_unique'

theorem Continuous.connectedComponentsLift_unique (h : Continuous f) (g : ConnectedComponents α → β)
    (hg : g ∘ (↑) = f) : g = h.connectedComponentsLift :=
  connectedComponents_lift_unique' <| hg.trans h.connectedComponentsLift_comp_coe.symm
#align continuous.connected_components_lift_unique Continuous.connectedComponentsLift_unique

/-- The preimage of a singleton in `connectedComponents` is the connected component
of an element in the equivalence class. -/
theorem connectedComponents_preimage_singleton {x : α} :
    (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedComponent x := by
  ext y
  rw [mem_preimage, mem_singleton_iff, ConnectedComponents.coe_eq_coe']
#align connected_components_preimage_singleton connectedComponents_preimage_singleton

/-- The preimage of the image of a set under the quotient map to `connectedComponents α`
is the union of the connected components of the elements in it. -/
theorem connectedComponents_preimage_image (U : Set α) :
    (↑) ⁻¹' ((↑) '' U : Set (ConnectedComponents α)) = ⋃ x ∈ U, connectedComponent x := by
  simp only [connectedComponents_preimage_singleton, preimage_iUnion₂, image_eq_iUnion]
#align connected_components_preimage_image connectedComponents_preimage_image

instance ConnectedComponents.totallyDisconnectedSpace :
    TotallyDisconnectedSpace (ConnectedComponents α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  refine' ConnectedComponents.surjective_coe.forall.2 fun x => _
  rw [← ConnectedComponents.quotientMap_coe.image_connectedComponent, ←
    connectedComponents_preimage_singleton, image_preimage_eq _ ConnectedComponents.surjective_coe]
  refine' ConnectedComponents.surjective_coe.forall.2 fun y => _
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent
#align connected_components.totally_disconnected_space ConnectedComponents.totallyDisconnectedSpace

/-- Functoriality of `connectedComponents` -/
def Continuous.connectedComponentsMap {β : Type _} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : ConnectedComponents α → ConnectedComponents β :=
  Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)
#align continuous.connected_components_map Continuous.connectedComponentsMap

theorem Continuous.connectedComponentsMap_continuous {β : Type _} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : Continuous h.connectedComponentsMap :=
  Continuous.connectedComponentsLift_continuous (ConnectedComponents.continuous_coe.comp h)
#align continuous.connected_components_map_continuous Continuous.connectedComponentsMap_continuous

end connectedComponentSetoid

/-- A preconnected set `s` has the property that every map to a
discrete space that is continuous on `s` is constant on `s` -/
theorem IsPreconnected.constant {Y : Type _} [TopologicalSpace Y] [DiscreteTopology Y] {s : Set α}
    (hs : IsPreconnected s) {f : α → Y} (hf : ContinuousOn f s) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) : f x = f y :=
  (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)
#align is_preconnected.constant IsPreconnected.constant

/-- If every map to `Bool` (a discrete two-element space), that is
continuous on a set `s`, is constant on s, then s is preconnected -/
theorem isPreconnected_of_forall_constant {s : Set α}
    (hs : ∀ f : α → Bool, ContinuousOn f s → ∀ x ∈ s, ∀ y ∈ s, f x = f y) : IsPreconnected s := by
  unfold IsPreconnected
  by_contra'
  rcases this with ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩
  rw [not_nonempty_iff_eq_empty] at H
  have hy : y ∉ u := fun y_in_u => eq_empty_iff_forall_not_mem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩
  have : ContinuousOn u.boolIndicator s := by
    apply (continuousOn_boolIndicator_iff_clopen _ _).mpr ⟨_, _⟩
    · exact u_op.preimage continuous_subtype_val
    · rw [preimage_subtype_coe_eq_compl hsuv H]
      exact (v_op.preimage continuous_subtype_val).isClosed_compl
  simpa [(u.mem_iff_boolIndicator _).mp x_in_u, (u.not_mem_iff_boolIndicator _).mp hy] using
    hs _ this x x_in_s y y_in_s
#align is_preconnected_of_forall_constant isPreconnected_of_forall_constant

/-- A `PreconnectedSpace` version of `isPreconnected.constant` -/
theorem PreconnectedSpace.constant {Y : Type _} [TopologicalSpace Y] [DiscreteTopology Y]
    (hp : PreconnectedSpace α) {f : α → Y} (hf : Continuous f) {x y : α} : f x = f y :=
  IsPreconnected.constant hp.isPreconnected_univ (Continuous.continuousOn hf) trivial trivial
#align preconnected_space.constant PreconnectedSpace.constant

/-- A `PreconnectedSpace` version of `isPreconnected_of_forall_constant` -/
theorem preconnectedSpace_of_forall_constant
    (hs : ∀ f : α → Bool, Continuous f → ∀ x y, f x = f y) : PreconnectedSpace α :=
  ⟨isPreconnected_of_forall_constant fun f hf x _ y _ =>
      hs f (continuous_iff_continuousOn_univ.mpr hf) x y⟩
#align preconnected_space_of_forall_constant preconnectedSpace_of_forall_constant

/-- Refinement of `IsPreconnected.constant` only assuming the map factors through a
discrete subset of the target. -/
theorem IsPreconnected.constant_of_mapsTo [TopologicalSpace β] {S : Set α} (hS : IsPreconnected S)
    {T : Set β} [DiscreteTopology T] {f : α → β} (hc : ContinuousOn f S) (hTm : MapsTo f S T)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  let F : S → T := hTm.restrict f S T
  suffices F ⟨x, hx⟩ = F ⟨y, hy⟩ by rwa [← Subtype.coe_inj] at this
  exact (isPreconnected_iff_preconnectedSpace.mp hS).constant (hc.restrict_mapsTo _)
#align is_preconnected.constant_of_maps_to IsPreconnected.constant_of_mapsTo

/-- A version of `IsPreconnected.constant_of_mapsTo` that assumes that the codomain is nonempty and
proves that `f` is equal to `const α y` on `S` for some `y ∈ T`. -/
theorem IsPreconnected.eqOn_const_of_mapsTo [TopologicalSpace β] {S : Set α} (hS : IsPreconnected S)
    {T : Set β} [DiscreteTopology T] {f : α → β} (hc : ContinuousOn f S) (hTm : MapsTo f S T)
    (hne : T.Nonempty) : ∃ y ∈ T, EqOn f (const α y) S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
  · exact hne.imp fun _ hy => ⟨hy, eqOn_empty _ _⟩
  · exact ⟨f x, hTm hx, fun x' hx' => hS.constant_of_mapsTo hc hTm hx' hx⟩
