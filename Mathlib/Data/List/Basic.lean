/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

! This file was ported from Lean 3 source module data.list.basic
! leanprover-community/mathlib commit 9da1b3534b65d9661eb8f42443598a92bbb49211
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.List.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.List.Defs
import Mathlib.Init.Core
import Std.Data.List.Lemmas

/-!
# Basic properties of lists
-/

open Function

open Nat hiding one_pos

assert_not_exists Set.range

namespace List

universe u v w x

variable {ι : Type _} {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {l₁ l₂ : List α}

-- Porting note: Delete this attribute
-- attribute [inline] List.head!

/-- There is only one list of an empty type -/
instance uniqueOfIsEmpty [IsEmpty α] : Unique (List α) :=
  { instInhabitedList with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: _ => isEmptyElim a }
#align list.unique_of_is_empty List.uniqueOfIsEmpty

instance : IsLeftId (List α) Append.append [] :=
  ⟨nil_append⟩

instance : IsRightId (List α) Append.append [] :=
  ⟨append_nil⟩

instance : IsAssociative (List α) Append.append :=
  ⟨append_assoc⟩

#align list.cons_ne_nil List.cons_ne_nil
#align list.cons_ne_self List.cons_ne_self

#align list.head_eq_of_cons_eq List.head_eq_of_cons_eqₓ -- implicits order
#align list.tail_eq_of_cons_eq List.tail_eq_of_cons_eqₓ -- implicits order

@[simp] theorem cons_injective {a : α} : Injective (cons a) := fun _ _ => tail_eq_of_cons_eq
#align list.cons_injective List.cons_injective

#align list.cons_inj List.cons_inj

theorem cons_eq_cons {a b : α} {l l' : List α} : a :: l = b :: l' ↔ a = b ∧ l = l' :=
  ⟨List.cons.inj, fun h => h.1 ▸ h.2 ▸ rfl⟩
#align list.cons_eq_cons List.cons_eq_cons

theorem singleton_injective : Injective fun a : α => [a] := fun _ _ h => (cons_eq_cons.1 h).1
#align list.singleton_injective List.singleton_injective

theorem singleton_inj {a b : α} : [a] = [b] ↔ a = b :=
  singleton_injective.eq_iff
#align list.singleton_inj List.singleton_inj

#align list.exists_cons_of_ne_nil List.exists_cons_of_ne_nil

theorem set_of_mem_cons (l : List α) (a : α) : { x | x ∈ a :: l } = insert a { x | x ∈ l } :=
  Set.ext fun _ => mem_cons
#align list.set_of_mem_cons List.set_of_mem_cons

/-! ### mem -/

#align list.mem_singleton_self List.mem_singleton_self
#align list.eq_of_mem_singleton List.eq_of_mem_singleton
#align list.mem_singleton List.mem_singleton
#align list.mem_of_mem_cons_of_mem List.mem_of_mem_cons_of_mem

theorem _root_.Decidable.List.eq_or_ne_mem_of_mem [DecidableEq α]
    {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ a ≠ b ∧ a ∈ l := by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))
#align decidable.list.eq_or_ne_mem_of_mem Decidable.List.eq_or_ne_mem_of_mem

#align list.eq_or_ne_mem_of_mem List.eq_or_ne_mem_of_mem

-- porting note: from init.data.list.lemmas
alias mem_cons ↔ eq_or_mem_of_mem_cons _
#align list.eq_or_mem_of_mem_cons List.eq_or_mem_of_mem_cons

#align list.not_mem_append List.not_mem_append

#align list.ne_nil_of_mem List.ne_nil_of_mem

theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
  induction' l with b l ih; {cases h}; rcases h with (_ | ⟨_, h⟩)
  · exact ⟨[], l, rfl⟩
  · rcases ih h with ⟨s, t, rfl⟩
    exact ⟨b :: s, t, rfl⟩
#align list.mem_split List.mem_split

#align list.mem_of_ne_of_mem List.mem_of_ne_of_mem

#align list.ne_of_not_mem_cons List.ne_of_not_mem_cons

#align list.not_mem_of_not_mem_cons List.not_mem_of_not_mem_cons

#align list.not_mem_cons_of_ne_of_not_mem List.not_mem_cons_of_ne_of_not_mem

#align list.ne_and_not_mem_of_not_mem_cons List.ne_and_not_mem_of_not_mem_cons

#align list.mem_map List.mem_map

#align list.exists_of_mem_map List.exists_of_mem_map

#align list.mem_map_of_mem List.mem_map_of_memₓ -- implicits order

theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
    f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem _⟩
#align list.mem_map_of_injective List.mem_map_of_injective

@[simp]
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff {f : α → α}
    (hf : Function.Involutive f) (x : α) (l : List α) : (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩
#align function.involutive.exists_mem_and_apply_eq_iff Function.Involutive.exists_mem_and_apply_eq_iff

theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
    a ∈ map f l ↔ f a ∈ l := by rw [mem_map, hf.exists_mem_and_apply_eq_iff]
#align list.mem_map_of_involutive List.mem_map_of_involutive

#align list.forall_mem_map_iff List.forall_mem_map_iffₓ -- universe order

#align list.map_eq_nil List.map_eq_nilₓ -- universe order

attribute [simp] List.mem_join
#align list.mem_join List.mem_join

#align list.exists_of_mem_join List.exists_of_mem_join

#align list.mem_join_of_mem List.mem_join_of_memₓ -- implicits order

attribute [simp] List.mem_bind
#align list.mem_bind List.mem_bindₓ -- implicits order

-- Porting note: bExists in Lean3, And in Lean4
#align list.exists_of_mem_bind List.exists_of_mem_bindₓ -- implicits order

#align list.mem_bind_of_mem List.mem_bind_of_memₓ -- implicits order

#align list.bind_map List.bind_mapₓ -- implicits order

theorem map_bind (g : β → List γ) (f : α → β) :
    ∀ l : List α, (List.map f l).bind g = l.bind fun a => g (f a)
  | [] => rfl
  | a :: l => by simp only [cons_bind, map_cons, map_bind _ _ l]
#align list.map_bind List.map_bind

/-! ### length -/

#align list.length_eq_zero List.length_eq_zero

#align list.length_singleton List.length_singleton

#align list.length_pos_of_mem List.length_pos_of_mem

#align list.exists_mem_of_length_pos List.exists_mem_of_length_pos

#align list.length_pos_iff_exists_mem List.length_pos_iff_exists_mem

alias length_pos ↔ ne_nil_of_length_pos length_pos_of_ne_nil
#align list.ne_nil_of_length_pos List.ne_nil_of_length_pos
#align list.length_pos_of_ne_nil List.length_pos_of_ne_nil

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩
#align list.length_pos_iff_ne_nil List.length_pos_iff_ne_nil

#align list.exists_mem_of_ne_nil List.exists_mem_of_ne_nil

#align list.length_eq_one List.length_eq_one

theorem exists_of_length_succ {n} : ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
  | [], H => absurd H.symm <| succ_ne_zero n
  | h :: t, _ => ⟨h, t, rfl⟩
#align list.exists_of_length_succ List.exists_of_length_succ

@[simp] lemma length_injective_iff : Injective (List.length : List α → ℕ) ↔ Subsingleton α := by
  constructor
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intros hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    · next ih _ _ =>
      congr
      · exact Subsingleton.elim _ _
      · apply ih; simpa using hl
#align list.length_injective_iff List.length_injective_iff

@[simp default+1] -- Porting note: this used to be just @[simp]
lemma length_injective [Subsingleton α] : Injective (length : List α → ℕ) :=
  length_injective_iff.mpr inferInstance
#align list.length_injective List.length_injective

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩
#align list.length_eq_two List.length_eq_two

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩
#align list.length_eq_three List.length_eq_three

-- Porting note: Lean 3 core library had the name length_le_of_sublist
-- and data.list.basic the command `alias length_le_of_sublist ← sublist.length_le`,
-- but Std has the name Sublist.length_le instead.
alias Sublist.length_le ← length_le_of_sublist
#align list.length_le_of_sublist List.length_le_of_sublist
#align list.sublist.length_le List.Sublist.length_le

/-! ### set-theoretic notation of lists -/

-- ADHOC Porting note: instance from Lean3 core
instance : Singleton α (List α) := ⟨fun x => [x]⟩
#align list.has_singleton List.instSingletonList

-- ADHOC Porting note: instance from Lean3 core
instance [DecidableEq α] : Insert α (List α) := ⟨List.insert⟩

-- ADHOC Porting note: instance from Lean3 core
instance [DecidableEq α]: IsLawfulSingleton α (List α) :=
  { insert_emptyc_eq := fun x =>
      show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg (not_mem_nil _) }

#align list.empty_eq List.empty_eq

theorem singleton_eq (x : α) : ({x} : List α) = [x] :=
  rfl
#align list.singleton_eq List.singleton_eq

theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) : Insert.insert x l = x :: l :=
  if_neg h
#align list.insert_neg List.insert_neg

theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) : Insert.insert x l = l :=
  if_pos h
#align list.insert_pos List.insert_pos

theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y] := by
  rw [insert_neg, singleton_eq]
  rwa [singleton_eq, mem_singleton]
#align list.doubleton_eq List.doubleton_eq

/-! ### bounded quantifiers over lists -/

#align list.forall_mem_nil List.forall_mem_nil

#align list.forall_mem_cons List.forall_mem_cons

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∀ x ∈ a :: l, p x) :
    ∀ x ∈ l, p x := (forall_mem_cons.1 h).2
#align list.forall_mem_of_forall_mem_cons List.forall_mem_of_forall_mem_cons

#align list.forall_mem_singleton List.forall_mem_singleton

#align list.forall_mem_append List.forall_mem_append

theorem not_exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x :=
  fun.
#align list.not_exists_mem_nil List.not_exists_mem_nilₓ -- bExists change

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ x ∈ a :: l, p x :=
  ⟨a, mem_cons_self _ _, h⟩
#align list.exists_mem_cons_of List.exists_mem_cons_ofₓ -- bExists change

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ l, p x) →
    ∃ x ∈ a :: l, p x :=
  fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩
#align list.exists_mem_cons_of_exists List.exists_mem_cons_of_existsₓ -- bExists change

-- Porting note: bExists in Lean3 and And in Lean4
theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ a :: l, p x) →
    p a ∨ ∃ x ∈ l, p x :=
  fun ⟨x, xal, px⟩ =>
    Or.elim (eq_or_mem_of_mem_cons xal) (fun h : x = a => by rw [← h]; left; exact px)
      fun h : x ∈ l => Or.inr ⟨x, h, px⟩
#align list.or_exists_of_exists_mem_cons List.or_exists_of_exists_mem_consₓ -- bExists change

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  Iff.intro or_exists_of_exists_mem_cons fun h =>
    Or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists
#align list.exists_mem_cons_iff List.exists_mem_cons_iff

/-! ### list subset -/

instance : IsTrans (List α) Subset where
  trans := fun _ _ _ => List.Subset.trans

#align list.subset_def List.subset_def

#align list.subset_append_of_subset_left List.subset_append_of_subset_left

@[deprecated subset_append_of_subset_right]
theorem subset_append_of_subset_right' (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ :=
  subset_append_of_subset_right _
#align list.subset_append_of_subset_right List.subset_append_of_subset_right'

#align list.cons_subset List.cons_subset

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
  (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
cons_subset.2 ⟨ainm, lsubm⟩
#align list.cons_subset_of_subset_of_mem List.cons_subset_of_subset_of_mem

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
fun _ h ↦ (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)
#align list.append_subset_of_subset_of_subset List.append_subset_of_subset_of_subset

-- Porting note: in Std
#align list.append_subset_iff List.append_subset

alias subset_nil ↔ eq_nil_of_subset_nil _
#align list.eq_nil_of_subset_nil List.eq_nil_of_subset_nil

#align list.eq_nil_iff_forall_not_mem List.eq_nil_iff_forall_not_mem

#align list.map_subset List.map_subset

theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := by
  refine' ⟨_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'
#align list.map_subset_iff List.map_subset_iff

/-! ### append -/

theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl
#align list.append_eq_has_append List.append_eq_has_append

#align list.singleton_append List.singleton_append

#align list.append_ne_nil_of_ne_nil_left List.append_ne_nil_of_ne_nil_left

#align list.append_ne_nil_of_ne_nil_right List.append_ne_nil_of_ne_nil_right

#align list.append_eq_nil List.append_eq_nil

-- Porting note: in Std
#align list.nil_eq_append_iff List.nil_eq_append

theorem append_eq_cons_iff {a b c : List α} {x : α} :
    a ++ b = x :: c ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  cases a <;>
    simp only [and_assoc, @eq_comm _ c, nil_append, cons_append, cons.injEq, true_and_iff,
      false_and_iff, exists_false, false_or_iff, or_false_iff, exists_and_left, exists_eq_left']
#align list.append_eq_cons_iff List.append_eq_cons_iff

theorem cons_eq_append_iff {a b c : List α} {x : α} :
    (x :: c : List α) = a ++ b ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  rw [eq_comm, append_eq_cons_iff]
#align list.cons_eq_append_iff List.cons_eq_append_iff

#align list.append_eq_append_iff List.append_eq_append_iff

#align list.take_append_drop List.take_append_drop

#align list.append_inj List.append_inj

#align list.append_inj_right List.append_inj_rightₓ -- implicits order

#align list.append_inj_left List.append_inj_leftₓ -- implicits order

#align list.append_inj' List.append_inj'ₓ -- implicits order

#align list.append_inj_right' List.append_inj_right'ₓ -- implicits order

#align list.append_inj_left' List.append_inj_left'ₓ -- implicits order

theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  (append_right_inj _).1 h
#align list.append_left_cancel List.append_left_cancel

theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  (append_left_inj _).1 h
#align list.append_right_cancel List.append_right_cancel

theorem append_right_injective (s : List α) : Injective fun t ↦ s ++ t :=
fun _ _ ↦ append_left_cancel
#align list.append_right_injective List.append_right_injective

#align list.append_right_inj List.append_right_inj

theorem append_left_injective (t : List α) : Injective fun s ↦ s ++ t :=
fun _ _ ↦ append_right_cancel
#align list.append_left_injective List.append_left_injective

#align list.append_left_inj List.append_left_inj

#align list.map_eq_append_split List.map_eq_append_split

/-! ### replicate -/

attribute [simp] replicate_succ
#align list.replicate_succ List.replicate_succ

@[simp] lemma replicate_zero (a : α) : replicate 0 a = [] := rfl
#align list.replicate_zero List.replicate_zero

lemma replicate_one (a : α) : replicate 1 a = [a] := rfl
#align list.replicate_one List.replicate_one

theorem eq_replicate_length {a : α} : ∀ {l : List α}, l = replicate l.length a ↔ ∀ b ∈ l, b = a
  | [] => by simp
  | (b :: l) => by simp [eq_replicate_length]
#align list.eq_replicate_length List.eq_replicate_length

#align list.eq_replicate_of_mem List.eq_replicate_of_mem

#align list.eq_replicate List.eq_replicate

theorem replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ replicate n a := by
  induction m <;> simp [*, zero_add, succ_add, replicate]
#align list.replicate_add List.replicate_add

theorem replicate_succ' (n) (a : α) : replicate (n + 1) a = replicate n a ++ [a] :=
  replicate_add n 1 a
#align list.replicate_succ' List.replicate_succ'

theorem replicate_subset_singleton (n) (a : α) : replicate n a ⊆ [a] := fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)
#align list.replicate_subset_singleton List.replicate_subset_singleton

theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a := by
  simp only [eq_replicate, subset_def, mem_singleton, exists_eq_left']
#align list.subset_singleton_iff List.subset_singleton_iff

@[simp] theorem map_replicate (f : α → β) (n) (a : α) :
    map f (replicate n a) = replicate n (f a) := by
  induction n <;> [rfl; simp only [*, replicate, map]]
#align list.map_replicate List.map_replicate

@[simp] theorem tail_replicate (a : α) (n) :
    tail (replicate n a) = replicate (n - 1) a := by cases n <;> rfl
#align list.tail_replicate List.tail_replicate

@[simp] theorem join_replicate_nil (n : ℕ) : join (replicate n []) = @nil α := by
  induction n <;> [rfl; simp only [*, replicate, join, append_nil]]
#align list.join_replicate_nil List.join_replicate_nil

theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (@replicate α n) :=
  fun _ _ h => (eq_replicate.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩
#align list.replicate_right_injective List.replicate_right_injective

theorem replicate_right_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective hn).eq_iff
#align list.replicate_right_inj List.replicate_right_inj

@[simp] theorem replicate_right_inj' {a b : α} : ∀ {n},
    replicate n a = replicate n b ↔ n = 0 ∨ a = b
  | 0 => by simp
  | n + 1 => (replicate_right_inj n.succ_ne_zero).trans <| by simp only [n.succ_ne_zero, false_or]
#align list.replicate_right_inj' List.replicate_right_inj'

theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (length_replicate · a)
#align list.replicate_left_injective List.replicate_left_injective

@[simp] theorem replicate_left_inj {a : α} {n m : ℕ} : replicate n a = replicate m a ↔ n = m :=
  (replicate_left_injective a).eq_iff
#align list.replicate_left_inj List.replicate_left_inj

/-! ### pure -/

-- ADHOC Porting note: TODO this is from Lean3 core, so doesn't belong here
instance : Monad List := { pure := @List.ret, bind := @List.bind, map := @List.map }

-- Porting note: simp can prove this
-- @[simp]
theorem bind_singleton (f : α → List β) (x : α) : [x].bind f = f x :=
  append_nil (f x)
#align list.bind_singleton List.bind_singleton

@[simp] theorem bind_singleton' (l : List α) : (l.bind fun x => [x]) = l := by
  induction l <;> simp [*]
#align list.bind_singleton' List.bind_singleton'

theorem map_eq_bind {α β} (f : α → β) (l : List α) : map f l = l.bind fun x => [f x] := by
  simp_rw [←map_singleton]
  rw [← bind_singleton' l, bind_map, bind_singleton']
#align list.map_eq_bind List.map_eq_bind

theorem bind_assoc {α β} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.bind f).bind g = l.bind fun x => (f x).bind g := by induction l <;> simp [*]
#align list.bind_assoc List.bind_assoc

-- ADHOC Porting note: TODO this is from Lean3 core, so doesn't belong here
instance : LawfulMonad List := LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := List.bind_assoc)
  (bind_pure_comp := fun _ _ => (map_eq_bind _ _).symm)

@[simp]
theorem mem_pure {α} (x y : α) : x ∈ (pure y : List α) ↔ x = y :=
  show x ∈ [y] ↔ x = y by simp
#align list.mem_pure List.mem_pure

/-! ### bind -/

@[simp]
theorem bind_eq_bind {α β} (f : α → List β) (l : List α) : l >>= f = l.bind f :=
  rfl
#align list.bind_eq_bind List.bind_eq_bind

-- TODO: duplicate of a lemma in core
theorem bind_append (f : α → List β) (l₁ l₂ : List α) :
    (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f :=
  append_bind _ _ _
#align list.bind_append List.bind_append

/-! ### concat -/

theorem concat_nil (a : α) : concat [] a = [a] :=
  rfl
#align list.concat_nil List.concat_nil

theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl
#align list.concat_cons List.concat_cons

@[deprecated concat_eq_append]
theorem concat_eq_append' (a : α) (l : List α) : concat l a = l ++ [a] :=
  concat_eq_append l a
#align list.concat_eq_append List.concat_eq_append'

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ := by
  intro h
  rw [concat_eq_append, concat_eq_append] at h
  exact append_right_cancel h
#align list.init_eq_of_concat_eq List.init_eq_of_concat_eq

theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b := by
  intro h
  rw [concat_eq_append, concat_eq_append] at h
  exact head_eq_of_cons_eq (append_left_cancel h)
#align list.last_eq_of_concat_eq List.last_eq_of_concat_eq

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by simp
#align list.concat_ne_nil List.concat_ne_nil

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by simp
#align list.concat_append List.concat_append

@[deprecated length_concat]
theorem length_concat' (a : α) (l : List α) : length (concat l a) = succ (length l) := by
  simp only [concat_eq_append, length_append, length]
#align list.length_concat List.length_concat'

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by simp
#align list.append_concat List.append_concat

/-! ### reverse -/

#align list.reverse_nil List.reverse_nil

#align list.reverse_core List.reverseAux

-- Porting note: Do we need this?
attribute [local simp] reverseAux

#align list.reverse_cons List.reverse_cons

#align list.reverse_core_eq List.reverseAux_eq

theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]
#align list.reverse_cons' List.reverse_cons'

-- Porting note: simp can prove this
-- @[simp]
theorem reverse_singleton (a : α) : reverse [a] = [a] :=
  rfl
#align list.reverse_singleton List.reverse_singleton

#align list.reverse_append List.reverse_append
#align list.reverse_concat List.reverse_concat
#align list.reverse_reverse List.reverse_reverse

@[simp]
theorem reverse_involutive : Involutive (@reverse α) :=
  reverse_reverse
#align list.reverse_involutive List.reverse_involutive

@[simp]
theorem reverse_injective : Injective (@reverse α) :=
  reverse_involutive.injective
#align list.reverse_injective List.reverse_injective

theorem reverse_surjective : Surjective (@reverse α) :=
  reverse_involutive.surjective
#align list.reverse_surjective List.reverse_surjective

theorem reverse_bijective : Bijective (@reverse α) :=
  reverse_involutive.bijective
#align list.reverse_bijective List.reverse_bijective

@[simp]
theorem reverse_inj {l₁ l₂ : List α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
  reverse_injective.eq_iff
#align list.reverse_inj List.reverse_inj

theorem reverse_eq_iff {l l' : List α} : l.reverse = l' ↔ l = l'.reverse :=
  reverse_involutive.eq_iff
#align list.reverse_eq_iff List.reverse_eq_iff

@[simp]
theorem reverse_eq_nil {l : List α} : reverse l = [] ↔ l = [] :=
  @reverse_inj _ l []
#align list.reverse_eq_nil List.reverse_eq_nil

theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  simp only [concat_eq_append, reverse_cons, reverse_reverse]
#align list.concat_eq_reverse_cons List.concat_eq_reverse_cons

#align list.length_reverse List.length_reverse

-- Porting note: This one was @[simp] in mathlib 3,
-- but Std contains a competing simp lemma reverse_map.
-- For now we remove @[simp] to avoid simplification loops.
-- TODO: Change Std lemma to match mathlib 3?
theorem map_reverse (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) :=
  (reverse_map f l).symm
#align list.map_reverse List.map_reverse

theorem map_reverseAux (f : α → β) (l₁ l₂ : List α) :
    map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverseAux_eq, map_append, map_reverse]
#align list.map_reverse_core List.map_reverseAux

-- Porting TODO: Fix statement of `mem_reverse` in Std to match Lean3,
-- then deprecate/remove this one
theorem mem_reverse' {a : α} {l : List α} : a ∈ reverse l ↔ a ∈ l :=
  List.mem_reverse _ _
#align list.mem_reverse List.mem_reverse'

@[simp] theorem reverse_replicate (n) (a : α) : reverse (replicate n a) = replicate n a :=
  eq_replicate.2
    ⟨by rw [length_reverse, length_replicate],
     fun b h => eq_of_mem_replicate (mem_reverse'.1 h)⟩
#align list.reverse_replicate List.reverse_replicate

/-! ### empty -/

-- Porting note: this does not work as desired
-- attribute [simp] List.isEmpty

theorem isEmpty_iff_eq_nil {l : List α} : l.isEmpty ↔ l = [] := by cases l <;> simp [isEmpty]
#align list.empty_iff_eq_nil List.isEmpty_iff_eq_nil

/-! ### dropLast -/

@[simp]
theorem length_dropLast : ∀ l : List α, length l.dropLast = length l - 1
  | [] | [_] => rfl
  | a::b::l => by
    rw [dropLast, length_cons, length_cons, length_dropLast (b::l), succ_sub_one, length_cons,
      succ_sub_one]
    simp
#align list.length_init List.length_dropLast

-- Porting note: `rw [dropLast]` in Lean4 generates a goal `(b::l) ≠ []`
-- so we use this lemma instead
theorem dropLast_cons_cons (a b : α) (l : List α) : dropLast (a::b::l) = a::dropLast (b::l) := rfl

/-! ### getLast -/

@[simp]
theorem getLast_cons {a : α} {l : List α} :
    ∀ h : l ≠ nil, getLast (a :: l) (cons_ne_nil a l) = getLast l h := by
  induction l <;> intros
  contradiction
  rfl
#align list.last_cons List.getLast_cons

theorem getLast_append_singleton {a : α} (l : List α) :
    getLast (l ++ [a]) (append_ne_nil_of_ne_nil_right l _ (cons_ne_nil a _)) = a := by
  simp only [getLast_append]
#align list.last_append_singleton List.getLast_append_singleton

-- Porting note: name should be fixed upstream
theorem getLast_append' (l₁ l₂ : List α) (h : l₂ ≠ []) :
    getLast (l₁ ++ l₂) (append_ne_nil_of_ne_nil_right l₁ l₂ h) = getLast l₂ h := by
  induction' l₁ with _ _ ih
  · simp
  · simp only [cons_append]
    rw [List.getLast_cons]
    exact ih
#align list.last_append List.getLast_append'

theorem getLast_concat' {a : α} (l : List α) : getLast (concat l a) (concat_ne_nil a l) = a :=
  getLast_concat ..
#align list.last_concat List.getLast_concat'

@[simp]
theorem getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a := rfl
#align list.last_singleton List.getLast_singleton'

-- Porting note: simp can prove this
-- @[simp]
theorem getLast_cons_cons (a₁ a₂ : α) (l : List α) :
    getLast (a₁ :: a₂ :: l) (cons_ne_nil _ _) = getLast (a₂ :: l) (cons_ne_nil a₂ l) :=
  rfl
#align list.last_cons_cons List.getLast_cons_cons

theorem dropLast_append_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [a], h => rfl
  | a :: b :: l, h => by
    rw [dropLast_cons_cons, cons_append, getLast_cons (cons_ne_nil _ _)]
    congr
    exact dropLast_append_getLast (cons_ne_nil b l)
#align list.init_append_last List.dropLast_append_getLast

theorem getLast_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
    getLast l₁ h₁ = getLast l₂ h₂ := by subst l₁; rfl
#align list.last_congr List.getLast_congr

theorem getLast_mem : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ l
  | [], h => absurd rfl h
  | [a], _ => by simp only [getLast, mem_singleton]
  | a :: b :: l, h =>
    List.mem_cons.2 <| Or.inr <| by
        rw [getLast_cons_cons]
        exact getLast_mem (cons_ne_nil b l)
#align list.last_mem List.getLast_mem

theorem getLast_replicate_succ (m : ℕ) (a : α) :
    (replicate (m + 1) a).getLast (ne_nil_of_length_eq_succ (length_replicate _ _)) = a := by
  simp only [replicate_succ']
  exact getLast_append_singleton _
#align list.last_replicate_succ List.getLast_replicate_succ

/-! ### getLast? -/

-- Porting note: New lemma, since definition of getLast? is slightly different.
@[simp]
theorem getLast?_singleton (a : α) :
    getLast? [a] = a := rfl

-- Porting note: Moved earlier in file, for use in subsequent lemmas.
@[simp]
theorem getLast?_cons_cons (a b : α) (l : List α) :
    getLast? (a :: b :: l) = getLast? (b :: l) := rfl

@[simp]
theorem getLast?_isNone : ∀ {l : List α}, (getLast? l).isNone ↔ l = []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@getLast?_isNone (b :: l)]
#align list.last'_is_none List.getLast?_isNone

@[simp]
theorem getLast?_isSome : ∀ {l : List α}, l.getLast?.isSome ↔ l ≠ []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@getLast?_isSome (b :: l)]
#align list.last'_is_some List.getLast?_isSome

theorem mem_getLast?_eq_getLast : ∀ {l : List α} {x : α}, x ∈ l.getLast? → ∃ h, x = getLast l h
  | [], x, hx => False.elim <| by simp at hx
  | [a], x, hx =>
    have : a = x := by simpa using hx
    this ▸ ⟨cons_ne_nil a [], rfl⟩
  | a :: b :: l, x, hx => by
    rw [getLast?_cons_cons] at hx
    rcases mem_getLast?_eq_getLast hx with ⟨_, h₂⟩
    use cons_ne_nil _ _
    assumption
#align list.mem_last'_eq_last List.mem_getLast?_eq_getLast

theorem getLast?_eq_getLast_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.getLast? = some (l.getLast h)
  | [], h => (h rfl).elim
  | [_], _ => rfl
  | _ :: b :: l, _ => @getLast?_eq_getLast_of_ne_nil (b :: l) (cons_ne_nil _ _)
#align list.last'_eq_last_of_ne_nil List.getLast?_eq_getLast_of_ne_nil

theorem mem_getLast?_cons {x y : α} : ∀ {l : List α}, x ∈ l.getLast? → x ∈ (y :: l).getLast?
  | [], _ => by contradiction
  | _ :: _, h => h
#align list.mem_last'_cons List.mem_getLast?_cons

theorem mem_of_mem_getLast? {l : List α} {a : α} (ha : a ∈ l.getLast?) : a ∈ l :=
  let ⟨_, h₂⟩ := mem_getLast?_eq_getLast ha
  h₂.symm ▸ getLast_mem _
#align list.mem_of_mem_last' List.mem_of_mem_getLast?

theorem dropLast_append_getLast? : ∀ {l : List α}, ∀ a ∈ l.getLast?, dropLast l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [getLast?_cons_cons] at hc
    rw [dropLast_cons_cons, cons_append, dropLast_append_getLast? _ hc]
#align list.init_append_last' List.dropLast_append_getLast?

theorem getLastI_eq_getLast? [Inhabited α] : ∀ l : List α, l.getLastI = l.getLast?.iget
  | [] => by simp [getLastI, Inhabited.default]
  | [a] => rfl
  | [a, b] => rfl
  | [a, b, c] => rfl
  | _ :: _ :: c :: l => by simp [getLastI, getLastI_eq_getLast? (c :: l)]
#align list.ilast_eq_last' List.getLastI_eq_getLast?

@[simp]
theorem getLast?_append_cons :
    ∀ (l₁ : List α) (a : α) (l₂ : List α), getLast? (l₁ ++ a :: l₂) = getLast? (a :: l₂)
  | [], a, l₂ => rfl
  | [b], a, l₂ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, getLast?_cons_cons,
    ← cons_append, getLast?_append_cons (c :: l₁)]
#align list.last'_append_cons List.getLast?_append_cons

#align list.last'_cons_cons List.getLast?_cons_cons

theorem getLast?_append_of_ne_nil (l₁ : List α) :
    ∀ {l₂ : List α} (_ : l₂ ≠ []), getLast? (l₁ ++ l₂) = getLast? l₂
  | [], hl₂ => by contradiction
  | b :: l₂, _ => getLast?_append_cons l₁ b l₂
#align list.last'_append_of_ne_nil List.getLast?_append_of_ne_nil

theorem getLast?_append {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.getLast?) :
    x ∈ (l₁ ++ l₂).getLast? := by
  cases l₂
  · contradiction
  · rw [List.getLast?_append_cons]
    exact h
#align list.last'_append List.getLast?_append

/-! ### head(!?) and tail -/

theorem head!_eq_head? [Inhabited α] (l : List α) : head! l = (head? l).iget := by cases l <;> rfl
#align list.head_eq_head' List.head!_eq_head?

theorem surjective_head [Inhabited α] : Surjective (@head! α _) := fun x => ⟨[x], rfl⟩
#align list.surjective_head List.surjective_head

theorem surjective_head' : Surjective (@head? α) :=
  Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩
#align list.surjective_head' List.surjective_head'

theorem surjective_tail : Surjective (@tail α)
  | [] => ⟨[], rfl⟩
  | a :: l => ⟨a :: a :: l, rfl⟩
#align list.surjective_tail List.surjective_tail

theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: tail l
  | [], h => (Option.not_mem_none _ h).elim
  | a :: l, h => by
    simp only [head?, Option.mem_def, Option.some_inj] at h
    exact h ▸ rfl
#align list.eq_cons_of_mem_head' List.eq_cons_of_mem_head?

theorem mem_of_mem_head? {x : α} {l : List α} (h : x ∈ l.head?) : x ∈ l :=
  (eq_cons_of_mem_head? h).symm ▸ mem_cons_self _ _
#align list.mem_of_mem_head' List.mem_of_mem_head?

@[simp] theorem head!_cons [Inhabited α] (a : α) (l : List α) : head! (a :: l) = a := rfl
#align list.head_cons List.head!_cons

#align list.tail_nil List.tail_nil
#align list.tail_cons List.tail_cons

@[simp]
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
    head! (s ++ t) = head! s := by induction s; contradiction; rfl
#align list.head_append List.head!_append

theorem head?_append {s t : List α} {x : α} (h : x ∈ s.head?) : x ∈ (s ++ t).head? := by
  cases s; contradiction; exact h
#align list.head'_append List.head?_append

theorem head?_append_of_ne_nil :
    ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []), head? (l₁ ++ l₂) = head? l₁
  | _ :: _, _, _ => rfl
#align list.head'_append_of_ne_nil List.head?_append_of_ne_nil

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
    tail (l ++ [a]) = tail l ++ [a] := by
  induction l; contradiction; rw [tail, cons_append, tail]
#align list.tail_append_singleton_of_ne_nil List.tail_append_singleton_of_ne_nil

theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ head? l → a :: tail l = l
  | [], a, h => by contradiction
  | b :: l, a, h => by
    simp at h
    simp [h]
#align list.cons_head'_tail List.cons_head?_tail

theorem head!_mem_head? [Inhabited α] : ∀ {l : List α}, l ≠ [] → head! l ∈ head? l
  | [], h => by contradiction
  | a :: l, _ => rfl
#align list.head_mem_head' List.head!_mem_head?

theorem cons_head!_tail [Inhabited α] {l : List α} (h : l ≠ []) : head! l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)
#align list.cons_head_tail List.cons_head!_tail

theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  have h' := mem_cons_self l.head! l.tail
  rwa [cons_head!_tail h] at h'
#align list.head_mem_self List.head!_mem_self

@[simp]
theorem head?_map (f : α → β) (l) : head? (map f l) = (head? l).map f := by cases l <;> rfl
#align list.head'_map List.head?_map

theorem tail_append_of_ne_nil (l l' : List α) (h : l ≠ []) : (l ++ l').tail = l.tail ++ l' := by
  cases l
  · contradiction
  · simp
#align list.tail_append_of_ne_nil List.tail_append_of_ne_nil

section deprecated
set_option linter.deprecated false -- TODO(Mario): make replacements for theorems in this section

@[simp] theorem nthLe_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length := (by simpa [← lt_tsub_iff_right] using h)) :
    l.tail.nthLe i h = l.nthLe (i + 1) h' := by
  -- Porting note: cases l <;> [cases h; rfl] fails
  cases l
  · cases h
  · rfl
#align list.nth_le_tail List.nthLe_tail

theorem nthLe_cons_aux {l : List α} {a : α} {n} (hn : n ≠ 0) (h : n < (a :: l).length) :
    n - 1 < l.length := by
  contrapose! h
  rw [length_cons]
  convert succ_le_succ h
  exact (Nat.succ_pred_eq_of_pos hn.bot_lt).symm
#align list.nth_le_cons_aux List.nthLe_cons_aux

theorem nthLe_cons {l : List α} {a : α} {n} (hl) :
    (a :: l).nthLe n hl = if hn : n = 0 then a else l.nthLe (n - 1) (nthLe_cons_aux hn hl) := by
  split_ifs with h
  · simp [nthLe, h]
  cases l
  · rw [length_singleton, lt_succ_iff, nonpos_iff_eq_zero] at hl
    contradiction
  cases n
  · contradiction
  rfl
#align list.nth_le_cons List.nthLe_cons

end deprecated

-- Porting note: List.modifyHead has @[simp], and Lean 4 treats this as
-- an invitation to unfold modifyHead in any context,
-- not just use the equational lemmas.

-- @[simp]
@[simp 1100, nolint simpNF]
theorem modifyHead_modifyHead (l : List α) (f g : α → α) :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp
#align list.modify_head_modify_head List.modifyHead_modifyHead

/-! ### Induction from the right -/

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
def reverseRecOn {C : List α → Sort _} (l : List α) (H0 : C [])
    (H1 : ∀ (l : List α) (a : α), C l → C (l ++ [a])) : C l := by
  rw [← reverse_reverse l]
  match h:(reverse l) with
  | [] => exact H0
  | head :: tail =>
    have : tail.length < l.length := by
      rw [← length_reverse l, h, length_cons]
      simp [Nat.lt_succ]
    let ih := reverseRecOn (reverse tail) H0 H1
    rw [reverse_cons]
    exact H1 _ _ ih
termination_by _ _ l _ _ => l.length
#align list.reverse_rec_on List.reverseRecOn

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectionalRec {C : List α → Sort _} (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : ∀ l, C l
  | [] => H0
  | [a] => H1 a
  | a :: b :: l => by
    let l' := dropLast (b :: l)
    let b' := getLast (b :: l) (cons_ne_nil _ _)
    rw [← dropLast_append_getLast (cons_ne_nil b l)]
    have : C l' := bidirectionalRec H0 H1 Hn l'
    exact Hn a l' b' this
termination_by' measure List.length
#align list.bidirectional_rec List.bidirectionalRecₓ -- universe order

/-- Like `bidirectionalRec`, but with the list parameter placed first. -/
@[elab_as_elim]
def bidirectionalRecOn {C : List α → Sort _} (l : List α) (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
  bidirectionalRec H0 H1 Hn l
#align list.bidirectional_rec_on List.bidirectionalRecOn

/-! ### sublists -/

attribute [refl] List.Sublist.refl

#align list.nil_sublist List.nil_sublist
#align list.sublist.refl List.Sublist.refl
#align list.sublist.trans List.Sublist.trans
#align list.sublist_cons List.sublist_cons
#align list.sublist_of_cons_sublist List.sublist_of_cons_sublist

theorem Sublist.cons_cons {l₁ l₂ : List α} (a : α) (s : l₁ <+ l₂) : a :: l₁ <+ a :: l₂ :=
  Sublist.cons₂ _ s
#align list.sublist.cons_cons List.Sublist.cons_cons

#align list.sublist_append_left List.sublist_append_left
#align list.sublist_append_right List.sublist_append_right

theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ <+ a :: l₂ :=
  Sublist.cons _
#align list.sublist_cons_of_sublist List.sublist_cons_of_sublist

#align list.sublist_append_of_sublist_left List.sublist_append_of_sublist_left
#align list.sublist_append_of_sublist_right List.sublist_append_of_sublist_right

theorem sublist_of_cons_sublist_cons {l₁ l₂ : List α} : ∀ {a : α}, a :: l₁ <+ a :: l₂ → l₁ <+ l₂
  | _, Sublist.cons _ s => sublist_of_cons_sublist s
  | _, Sublist.cons₂ _ s => s
#align list.sublist_of_cons_sublist_cons List.sublist_of_cons_sublist_cons

theorem cons_sublist_cons_iff {l₁ l₂ : List α} {a : α} : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  ⟨sublist_of_cons_sublist_cons, Sublist.cons_cons _⟩
#align list.cons_sublist_cons_iff List.cons_sublist_cons_iff

#align list.append_sublist_append_left List.append_sublist_append_left
#align list.sublist.append_right List.Sublist.append_right
#align list.sublist_or_mem_of_sublist List.sublist_or_mem_of_sublist
#align list.sublist.reverse List.Sublist.reverse

#align list.reverse_sublist_iff List.reverse_sublist

#align list.append_sublist_append_right List.append_sublist_append_right
#align list.sublist.append List.Sublist.append
#align list.sublist.subset List.Sublist.subset

#align list.singleton_sublist List.singleton_sublist

theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil <| s.subset
#align list.eq_nil_of_sublist_nil List.eq_nil_of_sublist_nil

-- Porting note: this lemma seems to have been renamed on the occasion of its move to Std4
alias sublist_nil ← sublist_nil_iff_eq_nil
#align list.sublist_nil_iff_eq_nil List.sublist_nil_iff_eq_nil

#align list.replicate_sublist_replicate List.replicate_sublist_replicate

theorem sublist_replicate_iff {l : List α} {a : α} {n : ℕ} :
    l <+ replicate n a ↔ ∃ k ≤ n, l = replicate k a :=
  ⟨fun h =>
    ⟨l.length, h.length_le.trans_eq (length_replicate _ _),
      eq_replicate_length.mpr fun b hb => eq_of_mem_replicate (h.subset hb)⟩,
    by rintro ⟨k, h, rfl⟩; exact (replicate_sublist_replicate _).mpr h⟩
#align list.sublist_replicate_iff List.sublist_replicate_iff

#align list.sublist.eq_of_length List.Sublist.eq_of_length

#align list.sublist.eq_of_length_le List.Sublist.eq_of_length_le

theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le
#align list.sublist.antisymm List.Sublist.antisymm

instance decidableSublist [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+ l₂)
  | [], _ => isTrue <| nil_sublist _
  | _ :: _, [] => isFalse fun h => List.noConfusion <| eq_nil_of_sublist_nil h
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      @decidable_of_decidable_of_iff _ _ (decidableSublist l₁ l₂) <|
        h ▸ ⟨Sublist.cons_cons _, sublist_of_cons_sublist_cons⟩
    else
      @decidable_of_decidable_of_iff _ _ (decidableSublist (a :: l₁) l₂)
        ⟨sublist_cons_of_sublist _, fun s =>
          match a, l₁, s, h with
          | _, _, Sublist.cons _ s', h => s'
          | _, _, Sublist.cons₂ t _, h => absurd rfl h⟩
#align list.decidable_sublist List.decidableSublist

/-! ### indexOf -/

section IndexOf

variable [DecidableEq α]

-- Porting note: simp can prove this
-- @[simp]
theorem indexOf_nil (a : α) : indexOf a [] = 0 :=
  rfl
#align list.index_of_nil List.indexOf_nil

/-
  Porting note: The following proofs were simpler prior to the port. These proofs use the low-level
  `findIdx.go`.
  * `indexOf_cons_self`
  * `indexOf_cons_eq`
  * `indexOf_cons_ne`
  * `indexOf_cons`

  The ported versions of the earlier proofs are given in comments.
-/

-- Porting note: these lemmas recover the Lean 3 definition of `findIdx`
@[simp] theorem findIdx_nil {α : Type _} (p : α → Bool) :
  [].findIdx p = 0 := rfl

theorem findIdx_cons (p : α → Bool) (b : α) (l : List α) :
    (b :: l).findIdx p = bif p b then 0 else (l.findIdx p) + 1 := by
    cases H : p b with
      | true => simp [H, findIdx, findIdx.go]
      | false => simp [H, findIdx, findIdx.go, findIdx_go_succ]
  where
    findIdx_go_succ (p : α → Bool) (l : List α) (n : ℕ) :
        List.findIdx.go p l (n + 1) = (List.findIdx.go p l n) + 1 := by
      cases l with
      | nil => unfold List.findIdx.go; exact Nat.succ_eq_add_one n
      | cons head tail =>
        unfold List.findIdx.go
        cases p head <;> simp only [cond_false, cond_true]
        exact findIdx_go_succ p tail (n + 1)

-- indexOf_cons_eq _ rfl
@[simp]
theorem indexOf_cons_self (a : α) (l : List α) : indexOf a (a :: l) = 0 := by
  rw [indexOf, findIdx_cons, beq_self_eq_true, cond]
#align list.index_of_cons_self List.indexOf_cons_self

-- fun e => if_pos e
theorem indexOf_cons_eq {a b : α} (l : List α) : a = b → indexOf a (b :: l) = 0
  | e => by rw [e]; exact indexOf_cons_self b l
#align list.index_of_cons_eq List.indexOf_cons_eq

-- fun n => if_neg n
@[simp]
theorem indexOf_cons_ne {a b : α} (l : List α) : a ≠ b → indexOf a (b :: l) = succ (indexOf a l)
  | h => by simp only [indexOf, findIdx_cons, Bool.cond_eq_ite, beq_iff_eq, h, ite_false]
#align list.index_of_cons_ne List.indexOf_cons_ne

-- rfl
theorem indexOf_cons (a b : α) (l : List α) :
    indexOf a (b :: l) = if a = b then 0 else succ (indexOf a l) := by
  simp only [indexOf, findIdx_cons, Bool.cond_eq_ite, beq_iff_eq]
#align list.index_of_cons List.indexOf_cons

theorem indexOf_eq_length {a : α} {l : List α} : indexOf a l = length l ↔ a ∉ l := by
  induction' l with b l ih
  · exact iff_of_true rfl (not_mem_nil _)
  simp only [length, mem_cons, indexOf_cons]; split_ifs with h
  · exact iff_of_false (by rintro ⟨⟩) fun H => H <| Or.inl h
  · simp only [h, false_or_iff]
    rw [← ih]
    exact succ_inj'
#align list.index_of_eq_length List.indexOf_eq_length

@[simp]
theorem indexOf_of_not_mem {l : List α} {a : α} : a ∉ l → indexOf a l = length l :=
  indexOf_eq_length.2
#align list.index_of_of_not_mem List.indexOf_of_not_mem

theorem indexOf_le_length {a : α} {l : List α} : indexOf a l ≤ length l := by
  induction' l with b l ih; · rfl
  simp only [length, indexOf_cons]
  by_cases h : a = b;
  · rw [if_pos h]
    exact Nat.zero_le _
  rw [if_neg h]; exact succ_le_succ ih
#align list.index_of_le_length List.indexOf_le_length

theorem indexOf_lt_length {a} {l : List α} : indexOf a l < length l ↔ a ∈ l :=
  ⟨fun h => Decidable.by_contradiction fun al => Nat.ne_of_lt h <| indexOf_eq_length.2 al,
   fun al => (lt_of_le_of_ne indexOf_le_length) fun h => indexOf_eq_length.1 h al⟩
#align list.index_of_lt_length List.indexOf_lt_length

theorem indexOf_append_of_mem {a : α} (h : a ∈ l₁) : indexOf a (l₁ ++ l₂) = indexOf a l₁ := by
  induction' l₁ with d₁ t₁ ih
  · exfalso
    exact not_mem_nil a h
  rw [List.cons_append]
  by_cases hh : a = d₁
  · iterate 2 rw [indexOf_cons_eq _ hh]
  rw [indexOf_cons_ne _ hh, indexOf_cons_ne _ hh, ih (mem_of_ne_of_mem hh h)]
#align list.index_of_append_of_mem List.indexOf_append_of_mem

theorem indexOf_append_of_not_mem {a : α} (h : a ∉ l₁) :
    indexOf a (l₁ ++ l₂) = l₁.length + indexOf a l₂ := by
  induction' l₁ with d₁ t₁ ih
  · rw [List.nil_append, List.length, zero_add]
  rw [List.cons_append, indexOf_cons_ne _ (ne_of_not_mem_cons h), List.length,
    ih (not_mem_of_not_mem_cons h), Nat.succ_add]
#align list.index_of_append_of_not_mem List.indexOf_append_of_not_mem

end IndexOf

/-! ### nth element -/

section deprecated
set_option linter.deprecated false

@[deprecated get_of_mem]
theorem nthLe_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n h, nthLe l n h = a :=
  let ⟨i, h⟩ := get_of_mem h; ⟨i.1, i.2, h⟩
#align list.nth_le_of_mem List.nthLe_of_mem

@[deprecated get?_eq_get]
theorem nthLe_get? {l : List α} {n} (h) : get? l n = some (nthLe l n h) := get?_eq_get _
#align list.nth_le_nth List.nthLe_get?

#align list.nth_len_le List.get?_len_le

@[simp]
theorem get?_length (l : List α) : l.get? l.length = none := get?_len_le le_rfl
#align list.nth_length List.get?_length

@[deprecated get?_eq_some]
theorem get?_eq_some' {l : List α} {n a} : get? l n = some a ↔ ∃ h, nthLe l n h = a := get?_eq_some
#align list.nth_eq_some List.get?_eq_some'

#align list.nth_eq_none_iff List.get?_eq_none
#align list.nth_of_mem List.get?_of_mem

@[deprecated get_mem]
theorem nthLe_mem (l : List α) (n h) : nthLe l n h ∈ l := get_mem ..
#align list.nth_le_mem List.nthLe_mem

#align list.nth_mem List.get?_mem

@[deprecated mem_iff_get]
theorem mem_iff_nthLe {a} {l : List α} : a ∈ l ↔ ∃ n h, nthLe l n h = a :=
  mem_iff_get.trans ⟨fun ⟨⟨n, h⟩, e⟩ => ⟨n, h, e⟩, fun ⟨n, h, e⟩ => ⟨⟨n, h⟩, e⟩⟩
#align list.mem_iff_nth_le List.mem_iff_nthLe

#align list.mem_iff_nth List.mem_iff_get?
#align list.nth_zero List.get?_zero

-- Porting note: couldn't synthesize _ in cases h x _ rfl anymore, needed to be given explicitly
theorem get?_injective {α : Type u} {xs : List α} {i j : ℕ} (h₀ : i < xs.length) (h₁ : Nodup xs)
    (h₂ : xs.get? i = xs.get? j) : i = j := by
  induction xs generalizing i j with
  | nil => cases h₀
  | cons x xs tail_ih =>
    cases i <;> cases j
    case zero.zero => rfl
    case succ.succ =>
      congr; cases h₁
      apply tail_ih <;> solve_by_elim [lt_of_succ_lt_succ]
    all_goals ( dsimp at h₂; cases' h₁ with _ _ h h')
    · cases (h x (mem_iff_get?.mpr ⟨_, h₂.symm⟩) rfl)
    · cases (h x (mem_iff_get?.mpr ⟨_, h₂⟩) rfl)
#align list.nth_injective List.get?_injective

#align list.nth_map List.get?_map

@[deprecated get_map]
theorem nthLe_map (f : α → β) {l n} (H1 H2) : nthLe (map f l) n H1 = f (nthLe l n H2) := get_map ..
#align list.nth_le_map List.nthLe_map

/-- A version of `get_map` that can be used for rewriting. -/
theorem get_map_rev (f : α → β) {l n} :
    f (get l n) = get (map f l) ⟨n.1, (l.length_map f).symm ▸ n.2⟩ := Eq.symm (get_map _)

/-- A version of `nthLe_map` that can be used for rewriting. -/
@[deprecated get_map_rev]
theorem nthLe_map_rev (f : α → β) {l n} (H) :
    f (nthLe l n H) = nthLe (map f l) n ((l.length_map f).symm ▸ H) :=
  (nthLe_map f _ _).symm
#align list.nth_le_map_rev List.nthLe_map_rev

@[simp, deprecated get_map]
theorem nthLe_map' (f : α → β) {l n} (H) :
    nthLe (map f l) n H = f (nthLe l n (l.length_map f ▸ H)) := nthLe_map f _ _
#align list.nth_le_map' List.nthLe_map'

/-- If one has `nthLe L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
@[deprecated get_of_eq]
theorem nthLe_of_eq {L L' : List α} (h : L = L') {i : ℕ} (hi : i < L.length) :
    nthLe L i hi = nthLe L' i (h ▸ hi) := by congr
#align list.nth_le_of_eq List.nthLe_of_eq

@[simp, deprecated get_singleton]
theorem nthLe_singleton (a : α) {n : ℕ} (hn : n < 1) : nthLe [a] n hn = a := get_singleton ..
#align list.nth_le_singleton List.nthLe_singleton

@[deprecated] -- FIXME: replacement -- it's not `get_zero` and it's not `get?_zero`
theorem nthLe_zero [Inhabited α] {L : List α} (h : 0 < L.length) : List.nthLe L 0 h = L.head! := by
  cases L
  cases h
  simp [nthLe]
#align list.nth_le_zero List.nthLe_zero

@[deprecated get_append]
theorem nthLe_append {l₁ l₂ : List α} {n : ℕ} (hn₁) (hn₂) :
    (l₁ ++ l₂).nthLe n hn₁ = l₁.nthLe n hn₂ := get_append _ hn₂
#align list.nth_le_append List.nthLe_append

@[deprecated get_append_right']
theorem nthLe_append_right {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂) :
    (l₁ ++ l₂).nthLe n h₂ = l₂.nthLe (n - l₁.length) (get_append_right_aux h₁ h₂) :=
  get_append_right' h₁ h₂
#align list.nth_le_append_right_aux List.get_append_right_aux
#align list.nth_le_append_right List.nthLe_append_right

@[deprecated get_replicate]
theorem nthLe_replicate (a : α) {n m : ℕ} (h : m < (replicate n a).length) :
    (replicate n a).nthLe m h = a := get_replicate ..
#align list.nth_le_replicate List.nthLe_replicate

#align list.nth_append List.get?_append
#align list.nth_append_right List.get?_append_right

@[deprecated getLast_eq_get]
theorem getLast_eq_nthLe (l : List α) (h : l ≠ []) :
    getLast l h = l.nthLe (l.length - 1) (Nat.sub_lt (length_pos_of_ne_nil h) one_pos) :=
  getLast_eq_get ..
#align list.last_eq_nth_le List.getLast_eq_nthLe

theorem get_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.get ⟨l.length - 1, h⟩ = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
  (getLast_eq_get l _).symm

@[deprecated get_length_sub_one]
theorem nthLe_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.nthLe (l.length - 1) h = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
  get_length_sub_one _
#align list.nth_le_length_sub_one List.nthLe_length_sub_one

#align list.nth_concat_length List.get?_concat_length

@[deprecated get_cons_length]
theorem nthLe_cons_length : ∀ (x : α) (xs : List α) (n : ℕ) (h : n = xs.length),
    (x :: xs).nthLe n (by simp [h]) = (x :: xs).getLast (cons_ne_nil x xs) := get_cons_length
#align list.nth_le_cons_length List.nthLe_cons_length

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  induction' l with x l ih generalizing n
  · cases h
  · by_cases h₁ : l = []
    · subst h₁
      rw [get_singleton]
      simp [lt_succ_iff] at h
      subst h
      simp
    have h₂ := h
    rw [length_cons, Nat.lt_succ_iff, le_iff_eq_or_lt] at h₂
    cases n
    · simp [get]
    rw [drop, get]
    apply ih

@[deprecated take_one_drop_eq_of_lt_length]
theorem take_one_drop_eq_of_lt_length' {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.nthLe n h] := take_one_drop_eq_of_lt_length h
#align list.take_one_drop_eq_of_lt_length List.take_one_drop_eq_of_lt_length'

#align list.ext List.ext

@[deprecated ext_get]
theorem ext_nthLe {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ n h₁ h₂, nthLe l₁ n h₁ = nthLe l₂ n h₂) : l₁ = l₂ :=
  ext_get hl h
#align list.ext_le List.ext_nthLe

@[simp]
theorem indexOf_get [DecidableEq α] {a : α} : ∀ {l : List α} (h), get l ⟨indexOf a l, h⟩ = a
  | b :: l, h => by
    by_cases h' : a = b <;>
      simp only [h', if_pos, if_false, indexOf_cons, get, @indexOf_get _ _ l]

@[simp, deprecated indexOf_get]
theorem indexOf_nthLe [DecidableEq α] {a : α} : ∀ {l : List α} (h), nthLe l (indexOf a l) h = a :=
  indexOf_get
#align list.index_of_nth_le List.indexOf_nthLe

@[simp]
theorem indexOf_get? [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    get? l (indexOf a l) = some a := by rw [nthLe_get?, indexOf_nthLe (indexOf_lt_length.2 h)]
#align list.index_of_nth List.indexOf_get?

@[deprecated]
theorem get_reverse_aux₁ :
    ∀ (l r : List α) (i h1 h2), get (reverseAux l r) ⟨i + length l, h1⟩ = get r ⟨i, h2⟩
  | [], r, i => fun h1 _ => rfl
  | a :: l, r, i => by
    rw [show i + length (a :: l) = i + 1 + length l from add_right_comm i (length l) 1]
    exact fun h1 h2 => get_reverse_aux₁ l (a :: r) (i + 1) h1 (succ_lt_succ h2)
#align list.nth_le_reverse_aux1 List.get_reverse_aux₁

theorem indexOf_inj [DecidableEq α] {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    indexOf x l = indexOf y l ↔ x = y :=
  ⟨fun h => by
    have x_eq_y :
        get l ⟨indexOf x l, indexOf_lt_length.2 hx⟩ =
        get l ⟨indexOf y l, indexOf_lt_length.2 hy⟩ := by
      simp only [h]
    simp only [indexOf_get] at x_eq_y; exact x_eq_y, fun h => by subst h; rfl⟩
#align list.index_of_inj List.indexOf_inj

theorem get_reverse_aux₂ :
    ∀ (l r : List α) (i : Nat) (h1) (h2),
      get (reverseAux l r) ⟨length l - 1 - i, h1⟩ = get l ⟨i, h2⟩
  | [], r, i, h1, h2 => absurd h2 (Nat.not_lt_zero _)
  | a :: l, r, 0, h1, _ => by
    have aux := get_reverse_aux₁ l (a :: r) 0
    rw [zero_add] at aux
    exact aux _ (zero_lt_succ _)
  | a :: l, r, i + 1, h1, h2 => by
    have aux := get_reverse_aux₂ l (a :: r) i
    have heq :=
      calc
        length (a :: l) - 1 - (i + 1) = length l - (1 + i) := by rw [add_comm]; rfl
        _ = length l - 1 - i := by rw [← tsub_add_eq_tsub_tsub]
    rw [← heq] at aux
    apply aux
#align list.nth_le_reverse_aux2 List.get_reverse_aux₂

@[simp] theorem get_reverse (l : List α) (i : Nat) (h1 h2) :
    get (reverse l) ⟨length l - 1 - i, h1⟩ = get l ⟨i, h2⟩ :=
  get_reverse_aux₂ _ _ _ _ _

@[simp, deprecated get_reverse]
theorem nthLe_reverse (l : List α) (i : Nat) (h1 h2) :
    nthLe (reverse l) (length l - 1 - i) h1 = nthLe l i h2 :=
  get_reverse ..
#align list.nth_le_reverse List.nthLe_reverse

theorem nthLe_reverse' (l : List α) (n : ℕ) (hn : n < l.reverse.length) (hn') :
    l.reverse.nthLe n hn = l.nthLe (l.length - 1 - n) hn' := by
  rw [eq_comm]
  convert nthLe_reverse l.reverse n (by simpa) hn using 1
  simp
#align list.nth_le_reverse' List.nthLe_reverse'

theorem get_reverse' (l : List α) (n) (hn') :
    l.reverse.get n = l.get ⟨l.length - 1 - n, hn'⟩ := nthLe_reverse' ..

-- FIXME: prove it the other way around
attribute [deprecated get_reverse'] nthLe_reverse'

theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) :
    l = [l.nthLe 0 (h.symm ▸ zero_lt_one)] := by
  refine' ext_get (by convert h) fun n h₁ h₂ => _
  simp only [get_singleton]
  congr
  exact eq_bot_iff.mpr (Nat.lt_succ_iff.mp h₂)
#align list.eq_cons_of_length_one List.eq_cons_of_length_one

theorem get_eq_iff {l : List α} {n : Fin l.length} {x : α} : l.get n = x ↔ l.get? n.1 = some x := by
  rw [get?_eq_some]
  simp [n.2]

@[deprecated get_eq_iff]
theorem nthLe_eq_iff {l : List α} {n : ℕ} {x : α} {h} : l.nthLe n h = x ↔ l.get? n = some x :=
  get_eq_iff
#align list.nth_le_eq_iff List.nthLe_eq_iff

@[deprecated get?_eq_get]
theorem some_nthLe_eq {l : List α} {n : ℕ} {h} : some (l.nthLe n h) = l.get? n :=
  (get?_eq_get _).symm
#align list.some_nth_le_eq List.some_nthLe_eq

end deprecated

theorem modifyNthTail_modifyNthTail {f g : List α → List α} (m : ℕ) :
    ∀ (n) (l : List α),
      (l.modifyNthTail f n).modifyNthTail g (m + n) =
        l.modifyNthTail (fun l => (f l).modifyNthTail g m) n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => congr_arg (List.cons a) (modifyNthTail_modifyNthTail m n l)
#align list.modify_nth_tail_modify_nth_tail List.modifyNthTail_modifyNthTail

theorem modifyNthTail_modifyNthTail_le {f g : List α → List α} (m n : ℕ) (l : List α)
    (h : n ≤ m) :
    (l.modifyNthTail f n).modifyNthTail g m =
      l.modifyNthTail (fun l => (f l).modifyNthTail g (m - n)) n := by
  rcases exists_add_of_le h with ⟨m, rfl⟩
  rw [@add_tsub_cancel_left, add_comm, modifyNthTail_modifyNthTail]
#align list.modify_nth_tail_modify_nth_tail_le List.modifyNthTail_modifyNthTail_le

theorem modifyNthTail_modifyNthTail_same {f g : List α → List α} (n : ℕ) (l : List α) :
    (l.modifyNthTail f n).modifyNthTail g n = l.modifyNthTail (g ∘ f) n := by
  rw [modifyNthTail_modifyNthTail_le n n l (le_refl n), tsub_self]; rfl
#align list.modify_nth_tail_modify_nth_tail_same List.modifyNthTail_modifyNthTail_same

#align list.modify_nth_tail_id List.modifyNthTail_id

theorem removeNth_eq_nthTail : ∀ (n) (l : List α), removeNth l n = modifyNthTail tail n l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (cons _) (removeNth_eq_nthTail _ _)
#align list.remove_nth_eq_nth_tail List.removeNth_eq_nthTail

#align list.update_nth_eq_modify_nth List.set_eq_modifyNth

theorem modifyNth_eq_set (f : α → α) :
    ∀ (n) (l : List α), modifyNth f n l = ((fun a => set l n (f a)) <$> get? l n).getD l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, b :: l =>
    (congr_arg (cons b) (modifyNth_eq_set f n l)).trans <| by cases get? l n <;> rfl
#align list.modify_nth_eq_update_nth List.modifyNth_eq_set

#align list.nth_modify_nth List.get?_modifyNth

theorem length_modifyNthTail (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyNthTail f n l) = length l
  | 0, _ => H _
  | _ + 1, [] => rfl
  | _ + 1, _ :: _ => @congr_arg _ _ _ _ (· + 1) (length_modifyNthTail _ H _ _)
#align list.modify_nth_tail_length List.length_modifyNthTail

-- Porting note: Duplicate of `modify_get?_length`
-- (but with a substantially better name?)
-- @[simp]
theorem length_modifyNth (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  modify_get?_length f
#align list.modify_nth_length List.length_modifyNth

#align list.update_nth_length List.length_set

#align list.nth_modify_nth_eq List.get?_modifyNth_eq
#align list.nth_modify_nth_ne List.get?_modifyNth_ne
#align list.nth_update_nth_eq List.get?_set_eq
#align list.nth_update_nth_of_lt List.get?_set_eq_of_lt
#align list.nth_update_nth_ne List.get?_set_ne
#align list.update_nth_nil List.set_nil
#align list.update_nth_succ List.set_succ
#align list.update_nth_comm List.set_comm

@[simp, deprecated get_set_eq]
theorem nthLe_set_eq (l : List α) (i : ℕ) (a : α) (h : i < (l.set i a).length) :
    (l.set i a).nthLe i h = a := get_set_eq ..
#align list.nth_le_update_nth_eq List.nthLe_set_eq

@[simp]
theorem get_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simpa using hj⟩ := by
  rw [← Option.some_inj, ← List.get?_eq_get, List.get?_set_ne _ _ h, List.get?_eq_get]

@[simp, deprecated get_set_of_ne]
theorem nthLe_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).nthLe j hj = l.nthLe j (by simpa using hj) :=
  get_set_of_ne h _ hj
#align list.nth_le_update_nth_of_ne List.nthLe_set_of_ne

#align list.mem_or_eq_of_mem_update_nth List.mem_or_eq_of_mem_set

section InsertNth

variable {a : α}

@[simp]
theorem insertNth_zero (s : List α) (x : α) : insertNth 0 x s = x :: s :=
  rfl
#align list.insert_nth_zero List.insertNth_zero

@[simp]
theorem insertNth_succ_nil (n : ℕ) (a : α) : insertNth (n + 1) a [] = [] :=
  rfl
#align list.insert_nth_succ_nil List.insertNth_succ_nil

@[simp]
theorem insertNth_succ_cons (s : List α) (hd x : α) (n : ℕ) :
    insertNth (n + 1) x (hd :: s) = hd :: insertNth n x s :=
  rfl
#align list.insert_nth_succ_cons List.insertNth_succ_cons

theorem length_insertNth : ∀ n as, n ≤ length as → length (insertNth n a as) = length as + 1
  | 0, _, _ => rfl
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, _ :: as, h => congr_arg Nat.succ <| length_insertNth n as (Nat.le_of_succ_le_succ h)
#align list.length_insert_nth List.length_insertNth

theorem removeNth_insertNth (n : ℕ) (l : List α) : (l.insertNth n a).removeNth n = l := by
  rw [removeNth_eq_nth_tail, insertNth, modifyNthTail_modifyNthTail_same]
  exact modifyNthTail_id _ _
#align list.remove_nth_insert_nth List.removeNth_insertNth

theorem insertNth_removeNth_of_ge :
    ∀ n m as,
      n < length as → n ≤ m → insertNth m a (as.removeNth n) = (as.insertNth (m + 1) a).removeNth n
  | 0, 0, [], has, _ => (lt_irrefl _ has).elim
  | 0, 0, _ :: as, _, _ => by simp [removeNth, insertNth]
  | 0, m + 1, a :: as, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertNth_removeNth_of_ge n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_ge List.insertNth_removeNth_of_ge

theorem insertNth_removeNth_of_le :
    ∀ n m as,
      n < length as → m ≤ n → insertNth m a (as.removeNth n) = (as.insertNth m a).removeNth (n + 1)
  | _, 0, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertNth_removeNth_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_le List.insertNth_removeNth_of_le

theorem insertNth_comm (a b : α) :
    ∀ (i j : ℕ) (l : List α) (_ : i ≤ j) (_ : j ≤ length l),
      (l.insertNth i a).insertNth (j + 1) b = (l.insertNth j b).insertNth i a
  | 0, j, l => by simp [insertNth]
  | i + 1, 0, l => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp [insertNth]
    exact insertNth_comm a b i j l (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)
#align list.insert_nth_comm List.insertNth_comm

theorem mem_insertNth {a b : α} :
    ∀ {n : ℕ} {l : List α} (_ : n ≤ l.length), a ∈ l.insertNth n b ↔ a = b ∨ a ∈ l
  | 0, as, _ => by simp
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    rw [List.insertNth_succ_cons, mem_cons, mem_insertNth (Nat.le_of_succ_le_succ h),
      ← or_assoc, @or_comm (a = a'), or_assoc, mem_cons]
#align list.mem_insert_nth List.mem_insertNth

theorem insertNth_of_length_lt (l : List α) (x : α) (n : ℕ) (h : l.length < n) :
    insertNth n x l = l := by
  induction' l with hd tl IH generalizing n
  · cases n
    · simp at h
    · simp
  · cases n
    · simp at h
    · simp only [Nat.succ_lt_succ_iff, length] at h
      simpa using IH _ h
#align list.insert_nth_of_length_lt List.insertNth_of_length_lt

@[simp]
theorem insertNth_length_self (l : List α) (x : α) : insertNth l.length x l = l ++ [x] := by
  induction' l with hd tl IH
  · simp
  · simpa using IH
#align list.insert_nth_length_self List.insertNth_length_self

theorem length_le_length_insertNth (l : List α) (x : α) (n : ℕ) :
    l.length ≤ (insertNth n x l).length := by
  cases' le_or_lt n l.length with hn hn
  · rw [length_insertNth _ _ hn]
    exact (Nat.lt_succ_self _).le
  · rw [insertNth_of_length_lt _ _ _ hn]
#align list.length_le_length_insert_nth List.length_le_length_insertNth

theorem length_insertNth_le_succ (l : List α) (x : α) (n : ℕ) :
    (insertNth n x l).length ≤ l.length + 1 := by
  cases' le_or_lt n l.length with hn hn
  · rw [length_insertNth _ _ hn]
  · rw [insertNth_of_length_lt _ _ _ hn]
    exact (Nat.lt_succ_self _).le
#align list.length_insert_nth_le_succ List.length_insertNth_le_succ

theorem get_insertNth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)) :
    (insertNth n x l).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  induction' n with n IH generalizing k l
  · simp at hn
  · cases' l with hd tl
    · simp
    · cases k
      · simp [get]
      · rw [Nat.succ_lt_succ_iff] at hn
        simpa using IH _ _ hn _

@[deprecated get_insertNth_of_lt]
theorem nthLe_insertNth_of_lt : ∀ (l : List α) (x : α) (n k : ℕ), k < n → ∀ (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)),
    (insertNth n x l).nthLe k hk' = l.nthLe k hk := @get_insertNth_of_lt _
#align list.nth_le_insert_nth_of_lt List.nthLe_insertNth_of_lt

@[simp]
theorem get_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
    (insertNth n x l).get ⟨n, hn'⟩ = x := by
  induction' l with hd tl IH generalizing n
  · simp only [length, nonpos_iff_eq_zero] at hn
    cases hn
    simp only [insertNth_zero, get_singleton]
  · cases n
    · simp
    · simp only [Nat.succ_le_succ_iff, length] at hn
      simpa using IH _ hn

@[simp, deprecated get_insertNth_self]
theorem nthLe_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
    (insertNth n x l).nthLe n hn' = x := get_insertNth_self _ _ _ hn
#align list.nth_le_insert_nth_self List.nthLe_insertNth_self

theorem get_insertNth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      -- Porting note: the original proof fails
      -- rwa [length_insertNth _ _ (le_self_add.trans hk'.le), Nat.succ_lt_succ_iff]
      rw [length_insertNth _ _ (le_self_add.trans hk'.le)]; exact Nat.succ_lt_succ_iff.2 hk')) :
    (insertNth n x l).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  induction' l with hd tl IH generalizing n k
  · simp at hk'
  · cases n
    · simp
    · simpa [succ_add] using IH _ _ _

set_option linter.deprecated false in
@[deprecated get_insertNth_add_succ]
theorem nthLe_insertNth_add_succ : ∀ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      -- Porting note: the original proof fails
      -- rwa [length_insertNth _ _ (le_self_add.trans hk'.le), Nat.succ_lt_succ_iff]
      rw [length_insertNth _ _ (le_self_add.trans hk'.le)]; exact Nat.succ_lt_succ_iff.2 hk')),
    (insertNth n x l).nthLe (n + k + 1) hk = nthLe l (n + k) hk' :=
  @get_insertNth_add_succ _
#align list.nth_le_insert_nth_add_succ List.nthLe_insertNth_add_succ

set_option linter.unnecessarySimpa false in
theorem insertNth_injective (n : ℕ) (x : α) : Function.Injective (insertNth n x) := by
  induction' n with n IH
  · have : insertNth 0 x = cons x := funext fun _ => rfl
    simp [this]
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> simpa [IH.eq_iff] using h
#align list.insert_nth_injective List.insertNth_injective

end InsertNth

/-! ### map -/

#align list.map_nil List.map_nil

theorem map_eq_foldr (f : α → β) (l : List α) : map f l = foldr (fun a bs => f a :: bs) [] l := by
  induction l <;> simp [*]
#align list.map_eq_foldr List.map_eq_foldr

theorem map_congr {f g : α → β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]
#align list.map_congr List.map_congr

theorem map_eq_map_iff {f g : α → β} {l : List α} : map f l = map g l ↔ ∀ x ∈ l, f x = g x := by
  refine' ⟨_, map_congr⟩; intro h x hx
  rw [mem_iff_get] at hx; rcases hx with ⟨n, hn, rfl⟩
  rw [get_map_rev f, get_map_rev g]
  congr!
#align list.map_eq_map_iff List.map_eq_map_iff

theorem map_concat (f : α → β) (a : α) (l : List α) :
    map f (concat l a) = concat (map f l) (f a) := by
  induction l <;> [rfl; simp only [*, concat_eq_append, cons_append, map, map_append]]
#align list.map_concat List.map_concat

@[simp]
theorem map_id'' (l : List α) : map (fun x => x) l = l :=
  map_id _
#align list.map_id'' List.map_id''

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : List α) : map f l = l := by
  simp [show f = id from funext h]
#align list.map_id' List.map_id'

theorem eq_nil_of_map_eq_nil {f : α → β} {l : List α} (h : map f l = nil) : l = nil :=
  eq_nil_of_length_eq_zero <| by rw [← length_map l f, h]; rfl
#align list.eq_nil_of_map_eq_nil List.eq_nil_of_map_eq_nil

@[simp]
theorem map_join (f : α → β) (L : List (List α)) : map f (join L) = join (map (map f) L) := by
  induction L <;> [rfl; simp only [*, join, map, map_append]]
#align list.map_join List.map_join

theorem bind_ret_eq_map (f : α → β) (l : List α) : l.bind (List.ret ∘ f) = map f l := by
  unfold List.bind
  induction l <;> simp [map, join, List.ret, cons_append, nil_append, *] at *
  assumption
#align list.bind_ret_eq_map List.bind_ret_eq_map

theorem bind_congr {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    List.bind l f = List.bind l g :=
  (congr_arg List.join <| map_congr h : _)
#align list.bind_congr List.bind_congr

@[simp]
theorem map_eq_map {α β} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl
#align list.map_eq_map List.map_eq_map

@[simp]
theorem map_tail (f : α → β) (l) : map f (tail l) = tail (map f l) := by cases l <;> rfl
#align list.map_tail List.map_tail

@[simp]
theorem map_injective_iff {f : α → β} : Injective (map f) ↔ Injective f := by
  constructor <;> intro h x y hxy
  · suffices [x] = [y] by simpa using this
    apply h
    simp [hxy]
  · induction' y with yh yt y_ih generalizing x
    · simpa using hxy
    cases x
    · simp at hxy
    · simp only [map, cons.injEq] at hxy
      simp [y_ih hxy.2, h hxy.1]
#align list.map_injective_iff List.map_injective_iff

/-- A single `List.map` of a composition of functions is equal to
composing a `List.map` with another `List.map`, fully applied.
This is the reverse direction of `List.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  (map_map _ _ _).symm
#align list.comp_map List.comp_map

/-- Composing a `List.map` with another `List.map` is equal to
a single `List.map` of composed functions.
-/
@[simp]
theorem map_comp_map (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) := by
  ext l; rw [comp_map, Function.comp_apply]
#align list.map_comp_map List.map_comp_map

theorem map_filter_eq_foldr (f : α → β) (p : α → Bool) (as : List α) :
    map f (filter p as) = foldr (fun a bs => bif p a then f a :: bs else bs) [] as := by
  induction' as with head tail
  · rfl
  · simp only [foldr]
    cases hp : p head <;> simp [filter, *]
#align list.map_filter_eq_foldr List.map_filter_eq_foldr

theorem getLast_map (f : α → β) {l : List α} (hl : l ≠ []) :
    (l.map f).getLast (mt eq_nil_of_map_eq_nil hl) = f (l.getLast hl) := by
  induction' l with l_hd l_tl l_ih
  · apply (hl rfl).elim
  · cases l_tl
    · simp
    · simpa using l_ih _
#align list.last_map List.getLast_map

theorem map_eq_replicate_iff {l : List α} {f : α → β} {b : β} :
    l.map f = replicate l.length b ↔ ∀ x ∈ l, f x = b := by
  simp [eq_replicate]
#align list.map_eq_replicate_iff List.map_eq_replicate_iff

@[simp] theorem map_const (l : List α) (b : β) : map (const α b) l = replicate l.length b :=
  map_eq_replicate_iff.mpr fun _ _ => rfl
#align list.map_const List.map_const

@[simp] theorem map_const' (l : List α) (b : β) : map (fun _ => b) l = replicate l.length b :=
  map_const l b
#align list.map_const' List.map_const'

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (const α b₂) l) :
    b₁ = b₂ := by rw [map_const] at h; exact eq_of_mem_replicate h
#align list.eq_of_mem_map_const List.eq_of_mem_map_const

/-! ### zipWith -/

theorem nil_zipWith (f : α → β → γ) (l : List β) : zipWith f [] l = [] := by cases l <;> rfl
#align list.nil_map₂ List.nil_zipWith

theorem zipWith_nil (f : α → β → γ) (l : List α) : zipWith f l [] = [] := by cases l <;> rfl
#align list.map₂_nil List.zipWith_nil

@[simp]
theorem zipWith_flip (f : α → β → γ) : ∀ as bs, zipWith (flip f) bs as = zipWith f as bs
  | [], [] => rfl
  | [], b :: bs => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => by
    simp! [zipWith_flip]
    rfl
#align list.map₂_flip List.zipWith_flip

/-! ### take, drop -/

@[simp]
theorem take_zero (l : List α) : take 0 l = [] :=
  rfl
#align list.take_zero List.take_zero

@[simp]
theorem take_nil : ∀ n, take n [] = ([] : List α)
  | 0 | _ + 1 => rfl
#align list.take_nil List.take_nil

theorem take_cons (n) (a : α) (l : List α) : take (succ n) (a :: l) = a :: take n l :=
  rfl
#align list.take_cons List.take_cons

#align list.take_length List.take_length

theorem take_all_of_le : ∀ {n} {l : List α}, length l ≤ n → take n l = l
  | 0, [], _ => rfl
  | 0, a :: l, h => absurd h (not_le_of_gt (zero_lt_succ _))
  | n + 1, [], _ => rfl
  | n + 1, a :: l, h => by
    change a :: take n l = a :: l
    rw [take_all_of_le (le_of_succ_le_succ h)]
#align list.take_all_of_le List.take_all_of_le

@[simp]
theorem take_left : ∀ l₁ l₂ : List α, take (length l₁) (l₁ ++ l₂) = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congr_arg (cons a) (take_left l₁ l₂)
#align list.take_left List.take_left

theorem take_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left
#align list.take_left' List.take_left'

theorem take_take : ∀ (n m) (l : List α), take n (take m l) = take (min n m) l
  | n, 0, l => by rw [min_zero, take_zero, take_nil]
  | 0, m, l => by rw [zero_min, take_zero, take_zero]
  | succ n, succ m, nil => by simp only [take_nil]
  | succ n, succ m, a :: l => by
    simp only [take, min_succ_succ, take_take n m l]
#align list.take_take List.take_take

theorem take_replicate (a : α) : ∀ n m : ℕ, take n (replicate m a) = replicate (min n m) a
  | n, 0 => by simp
  | 0, m => by simp
  | succ n, succ m => by simp [min_succ_succ, take_replicate]
#align list.take_replicate List.take_replicate

theorem map_take {α β : Type _} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.take i).map f = (L.map f).take i
  | [], i => by simp
  | _, 0 => by simp
  | h :: t, n + 1 => by dsimp; rw [map_take f t n]
#align list.map_take List.map_take

/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
theorem take_append_eq_append_take {l₁ l₂ : List α} {n : ℕ} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := by
  induction l₁ generalizing n; {simp}
  cases n <;> simp [*]
#align list.take_append_eq_append_take List.take_append_eq_append_take

theorem take_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by simp [take_append_eq_append_take, tsub_eq_zero_iff_le.mpr h]
#align list.take_append_of_le_length List.take_append_of_le_length

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
theorem take_append {l₁ l₂ : List α} (i : ℕ) : take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ take i l₂ :=
  by simp [take_append_eq_append_take, take_all_of_le le_self_add]
#align list.take_append List.take_append

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem get_take (L : List α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
    get L ⟨i, hi⟩ = get (L.take j) ⟨i, length_take .. ▸ lt_min hj hi⟩ :=
  get_of_eq (take_append_drop j L).symm _ ▸ get_append ..

set_option linter.deprecated false in
/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
@[deprecated get_take]
theorem nthLe_take (L : List α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
    nthLe L i hi = nthLe (L.take j) i (length_take .. ▸ lt_min hj hi) :=
  get_take _ hi hj
#align list.nth_le_take List.nthLe_take

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
theorem get_take' (L : List α) {j i} :
    get (L.take j) i = get L ⟨i.1, lt_of_lt_of_le i.2 (by simp [le_refl])⟩ := by
  let ⟨i, hi⟩ := i; simp at hi; rw [get_take L _ hi.1]

set_option linter.deprecated false in
/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
@[deprecated get_take']
theorem nthLe_take' (L : List α) {i j : ℕ} (hi : i < (L.take j).length) :
    nthLe (L.take j) i hi = nthLe L i (lt_of_lt_of_le hi (by simp [le_refl])) := get_take' _
#align list.nth_le_take' List.nthLe_take'

theorem get?_take {l : List α} {n m : ℕ} (h : m < n) : (l.take n).get? m = l.get? m := by
  induction' n with n hn generalizing l m
  · simp only [Nat.zero_eq] at h
    exact absurd h (not_lt_of_le m.zero_le)
  · cases' l with hd tl
    · simp only [take_nil]
    · cases m
      · simp only [get?, take]
      · simpa only using hn (Nat.lt_of_succ_lt_succ h)
#align list.nth_take List.get?_take

@[simp]
theorem nth_take_of_succ {l : List α} {n : ℕ} : (l.take (n + 1)).get? n = l.get? n :=
  get?_take (Nat.lt_succ_self n)
#align list.nth_take_of_succ List.nth_take_of_succ

theorem take_succ {l : List α} {n : ℕ} : l.take (n + 1) = l.take n ++ (l.get? n).toList := by
  induction' l with hd tl hl generalizing n
  · simp only [Option.toList, get?, take_nil, append_nil]
  · cases n
    · simp only [Option.toList, get?, eq_self_iff_true, and_self_iff, take, nil_append]
    · simp only [hl, cons_append, get?, eq_self_iff_true, and_self_iff, take]
#align list.take_succ List.take_succ

@[simp]
theorem take_eq_nil_iff {l : List α} {k : ℕ} : l.take k = [] ↔ l = [] ∨ k = 0 := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]
#align list.take_eq_nil_iff List.take_eq_nil_iff

theorem take_eq_take :
    ∀ {l : List α} {m n : ℕ}, l.take m = l.take n ↔ min m l.length = min n l.length
  | [], m, n => by simp
  | _ :: xs, 0, 0 => by simp
  | x :: xs, m + 1, 0 => by simp
  | x :: xs, 0, n + 1 => by simp [@eq_comm ℕ 0]
  | x :: xs, m + 1, n + 1 => by simp [Nat.min_succ_succ, take_eq_take]
#align list.take_eq_take List.take_eq_take

theorem take_add (l : List α) (m n : ℕ) : l.take (m + n) = l.take m ++ (l.drop m).take n := by
  convert_to take (m + n) (take m l ++ drop m l) = take m l ++ take n (drop m l)
  · rw [take_append_drop]
  rw [take_append_eq_append_take, take_all_of_le, append_right_inj]
  · simp only [take_eq_take, length_take, length_drop]
    generalize l.length = k; by_cases h : m ≤ k
    · simp [min_eq_left_iff.mpr h]
    · push_neg  at h
      simp [Nat.sub_eq_zero_of_le (le_of_lt h)]
  · trans m
    · apply length_take_le
    · simp
#align list.take_add List.take_add

theorem dropLast_eq_take (l : List α) : l.dropLast = l.take l.length.pred := by
  cases' l with x l
  · simp [dropLast]
  · induction' l with hd tl hl generalizing x
    · simp [dropLast]
    · simp [dropLast, hl]
#align list.init_eq_take List.dropLast_eq_take

theorem dropLast_take {n : ℕ} {l : List α} (h : n < l.length) :
    (l.take n).dropLast = l.take n.pred := by
  simp [dropLast_eq_take, min_eq_left_of_lt h, take_take, pred_le]
#align list.init_take List.dropLast_take

theorem dropLast_cons_of_ne_nil {α : Type _} {x : α}
    {l : List α} (h : l ≠ []) : (x :: l).dropLast = x :: l.dropLast := by simp [h]
#align list.init_cons_of_ne_nil List.dropLast_cons_of_ne_nil

@[simp]
theorem dropLast_append_of_ne_nil {α : Type _} {l : List α} :
    ∀ (l' : List α) (_ : l ≠ []), (l' ++ l).dropLast = l' ++ l.dropLast
  | [], _ => by simp only [nil_append]
  | a :: l', h => by
    rw [cons_append, dropLast, dropLast_append_of_ne_nil l' h, cons_append]
    simp [h]
#align list.init_append_of_ne_nil List.dropLast_append_of_ne_nil

#align list.drop_eq_nil_of_le List.drop_eq_nil_of_le

theorem drop_eq_nil_iff_le {l : List α} {k : ℕ} : l.drop k = [] ↔ l.length ≤ k := by
  refine' ⟨fun h => _, drop_eq_nil_of_le⟩
  induction' k with k hk generalizing l
  · simp only [drop] at h
    simp [h]
  · cases l
    · simp
    · simp only [drop] at h
      simpa [Nat.succ_le_succ_iff] using hk h
#align list.drop_eq_nil_iff_le List.drop_eq_nil_iff_le

theorem tail_drop (l : List α) (n : ℕ) : (l.drop n).tail = l.drop (n + 1) := by
  induction' l with hd tl hl generalizing n
  · simp
  · cases n
    · simp
    · simp [hl]
#align list.tail_drop List.tail_drop

theorem cons_get_drop_succ {l : List α} {n} :
    l.get n :: l.drop (n.1 + 1) = l.drop n.1 := by
  induction' l with hd tl hl
  · exact absurd n.1.zero_le (not_le_of_lt (nomatch n))
  · match n with
    | ⟨0, _⟩ => simp [get]
    | ⟨n+1, hn⟩ =>
      simp only [Nat.succ_lt_succ_iff, List.length] at hn
      simpa [List.get, List.drop] using hl

@[deprecated cons_get_drop_succ]
theorem cons_nthLe_drop_succ {l : List α} {n : ℕ} (hn : n < l.length) :
    l.nthLe n hn :: l.drop (n + 1) = l.drop n := cons_get_drop_succ
#align list.cons_nth_le_drop_succ List.cons_nthLe_drop_succ

#align list.drop_nil List.drop_nil

@[simp]
theorem drop_one : ∀ l : List α, drop 1 l = tail l
  | [] | _ :: _ => rfl
#align list.drop_one List.drop_one

theorem drop_add : ∀ (m n) (l : List α), drop (m + n) l = drop m (drop n l)
  | _, 0, _ => rfl
  | _, _ + 1, [] => drop_nil.symm
  | m, n + 1, _ :: _ => drop_add m n _
#align list.drop_add List.drop_add

@[simp]
theorem drop_left : ∀ l₁ l₂ : List α, drop (length l₁) (l₁ ++ l₂) = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_left l₁ l₂
#align list.drop_left List.drop_left

theorem drop_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : drop n (l₁ ++ l₂) = l₂ := by
  rw [← h]; apply drop_left
#align list.drop_left' List.drop_left'

theorem drop_eq_get_cons : ∀ {n} {l : List α} (h), drop n l = get l ⟨n, h⟩ :: drop (n + 1) l
  | 0, _ :: _, _ => rfl
  | n + 1, _ :: _, _ => @drop_eq_get_cons n _ _
#align list.drop_eq_nth_le_cons List.drop_eq_get_consₓ -- nth_le vs get

#align list.drop_length List.drop_length

theorem drop_length_cons {l : List α} (h : l ≠ []) (a : α) :
    (a :: l).drop l.length = [l.getLast h] := by
  induction' l with y l ih generalizing a
  · cases h rfl
  · simp only [drop, length]
    by_cases h₁ : l = []
    · simp [h₁]
    rw [getLast_cons h₁]
    exact ih h₁ y
#align list.drop_length_cons List.drop_length_cons

/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
theorem drop_append_eq_append_drop {l₁ l₂ : List α} {n : ℕ} :
    drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ := by
  induction l₁ generalizing n; · simp
  cases n <;> simp [*]
#align list.drop_append_eq_append_drop List.drop_append_eq_append_drop

theorem drop_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, tsub_eq_zero_iff_le.mpr h]
#align list.drop_append_of_le_length List.drop_append_of_le_length

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
theorem drop_append {l₁ l₂ : List α} (i : ℕ) : drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ := by
  rw [drop_append_eq_append_drop, drop_eq_nil_of_le] <;> simp
#align list.drop_append List.drop_append

theorem drop_sizeOf_le [SizeOf α] (l : List α) : ∀ n : ℕ, sizeOf (l.drop n) ≤ sizeOf l := by
  induction' l with _ _ lih <;> intro n
  · rw [drop_nil]
  · induction' n with n
    · rfl
    · exact Trans.trans (lih _) le_add_self
#align list.drop_sizeof_le List.drop_sizeOf_le

set_option linter.deprecated false in -- FIXME
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem get_drop (L : List α) {i j : ℕ} (h : i + j < L.length) :
    get L ⟨i + j, h⟩ = get (L.drop i) ⟨j, by
      have A : i < L.length := lt_of_le_of_lt (Nat.le.intro rfl) h
      rw [(take_append_drop i L).symm] at h
      simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take,
        length_append] using h⟩ := by
  rw [← nthLe_eq, ← nthLe_eq]
  rw [nthLe_of_eq (take_append_drop i L).symm h, nthLe_append_right] <;>
  simp [min_eq_left (show i ≤ length L from le_trans (by simp) (le_of_lt h))]

set_option linter.deprecated false in
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
@[deprecated get_drop]
theorem nthLe_drop (L : List α) {i j : ℕ} (h : i + j < L.length) :
    nthLe L (i + j) h = nthLe (L.drop i) j (by
      have A : i < L.length := lt_of_le_of_lt (Nat.le.intro rfl) h
      rw [(take_append_drop i L).symm] at h
      simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take,
        length_append] using h) := get_drop ..
#align list.nth_le_drop List.nthLe_drop

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
theorem get_drop' (L : List α) {i j} :
    get (L.drop i) j = get L ⟨i + j, lt_tsub_iff_left.mp (length_drop i L ▸ j.2)⟩ := by
  rw [get_drop]

set_option linter.deprecated false in
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
@[deprecated get_drop']
theorem nthLe_drop' (L : List α) {i j : ℕ} (h : j < (L.drop i).length) :
    nthLe (L.drop i) j h = nthLe L (i + j) (lt_tsub_iff_left.mp (length_drop i L ▸ h)) :=
  get_drop' ..
#align list.nth_le_drop' List.nthLe_drop'

theorem get?_drop (L : List α) (i j : ℕ) : get? (L.drop i) j = get? L (i + j) := by
  ext
  simp only [get?_eq_some, get_drop', Option.mem_def]
  constructor <;> exact fun ⟨h, ha⟩ => ⟨by simpa [lt_tsub_iff_left] using h, ha⟩
#align list.nth_drop List.get?_drop

@[simp]
theorem drop_drop (n : ℕ) : ∀ (m) (l : List α), drop n (drop m l) = drop (n + m) l
  | m, [] => by simp
  | 0, l => by simp
  | m + 1, a :: l =>
    calc
      drop n (drop (m + 1) (a :: l)) = drop n (drop m l) := rfl
      _ = drop (n + m) l := drop_drop n m l
      _ = drop (n + (m + 1)) (a :: l) := rfl
#align list.drop_drop List.drop_drop

theorem drop_take : ∀ (m : ℕ) (n : ℕ) (l : List α), drop m (take (m + n) l) = take n (drop m l)
  | 0, n, _ => by simp
  | m + 1, n, nil => by simp
  | m + 1, n, _ :: l => by
    have h : m + 1 + n = m + n + 1 := by ac_rfl
    simpa [take_cons, h] using drop_take m n l
#align list.drop_take List.drop_take

theorem map_drop {α β : Type _} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.drop i).map f = (L.map f).drop i
  | [], i => by simp
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [map_drop f t]
#align list.map_drop List.map_drop

theorem modifyNthTail_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ n l, modifyNthTail f n l = take n l ++ f (drop n l)
  | 0, _ => rfl
  | _ + 1, [] => H.symm
  | n + 1, b :: l => congr_arg (cons b) (modifyNthTail_eq_take_drop f H n l)
#align list.modify_nth_tail_eq_take_drop List.modifyNthTail_eq_take_drop

theorem modifyNth_eq_take_drop (f : α → α) :
    ∀ n l, modifyNth f n l = take n l ++ modifyHead f (drop n l) :=
  modifyNthTail_eq_take_drop _ rfl
#align list.modify_nth_eq_take_drop List.modifyNth_eq_take_drop

theorem modifyNth_eq_take_cons_drop (f : α → α) {n l} (h) :
    modifyNth f n l = take n l ++ f (get l ⟨n, h⟩) :: drop (n + 1) l := by
  rw [modifyNth_eq_take_drop, drop_eq_get_cons h]; rfl
#align list.modify_nth_eq_take_cons_drop List.modifyNth_eq_take_cons_drop

theorem set_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
    set l n a = take n l ++ a :: drop (n + 1) l := by
  rw [set_eq_modifyNth, modifyNth_eq_take_cons_drop _ h]
#align list.update_nth_eq_take_cons_drop List.set_eq_take_cons_drop

theorem reverse_take {α} {xs : List α} (n : ℕ) (h : n ≤ xs.length) :
    xs.reverse.take n = (xs.drop (xs.length - n)).reverse := by
  induction' xs with xs_hd xs_tl xs_ih generalizing n <;>
    simp only [reverse_cons, drop, reverse_nil, zero_tsub, length, take_nil]
  cases' h.lt_or_eq_dec with h' h'
  · replace h' := le_of_succ_le_succ h'
    rw [take_append_of_le_length, xs_ih _ h']
    rw [show xs_tl.length + 1 - n = succ (xs_tl.length - n) from _, drop]
    · rwa [succ_eq_add_one, ← @tsub_add_eq_add_tsub]
    · rwa [length_reverse]
  · subst h'
    rw [length, tsub_self, drop]
    suffices xs_tl.length + 1 = (xs_tl.reverse ++ [xs_hd]).length by
      rw [this, take_length, reverse_cons]
    rw [length_append, length_reverse]
    rfl
#align list.reverse_take List.reverse_take

@[simp]
theorem set_eq_nil (l : List α) (n : ℕ) (a : α) : l.set n a = [] ↔ l = [] := by
  cases l <;> cases n <;> simp only [set]
#align list.update_nth_eq_nil List.set_eq_nil

section TakeI

variable [Inhabited α]

@[simp]
theorem takeI_length : ∀ n l, length (@takeI α _ n l) = n
  | 0, _ => rfl
  | _ + 1, _ => congr_arg succ (takeI_length _ _)
#align list.take'_length List.takeI_length

@[simp]
theorem takeI_nil : ∀ n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | _ + 1 => congr_arg (cons _) (takeI_nil _)
#align list.take'_nil List.takeI_nil

theorem takeI_eq_take : ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l
  | 0, _, _ => rfl
  | _ + 1, _ :: _, h => congr_arg (cons _) <| takeI_eq_take <| le_of_succ_le_succ h
#align list.take'_eq_take List.takeI_eq_take

@[simp]
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)
#align list.take'_left List.takeI_left

theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply takeI_left
#align list.take'_left' List.takeI_left'

end TakeI

/- Porting note: in mathlib3 we just had `take` and `take'`. Now we have `take`, `takeI`, and
  `takeD`. The following section replicates the theorems above but for `takeD`. -/
section TakeD

@[simp]
theorem takeD_length : ∀ n l a, length (@takeD α n l a) = n
  | 0, _, _ => rfl
  | _ + 1, _, _ => congr_arg succ (takeD_length _ _ _)

-- Porting note: `takeD_nil` is already in std

theorem takeD_eq_take : ∀ {n} {l : List α} a, n ≤ length l → takeD n l a = take n l
  | 0, _, _, _ => rfl
  | _ + 1, _ :: _, a, h => congr_arg (cons _) <| takeD_eq_take a <| le_of_succ_le_succ h

@[simp]
theorem takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁ :=
  (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)

theorem takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ l₂) a = l₁ :=
  by rw [← h]; apply takeD_left

end TakeD

/-! ### foldl, foldr -/

theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
    foldl f a l = foldl g a l := by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin, H a hd (mem_cons_self _ _)]
#align list.foldl_ext List.foldl_ext

theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction' l with hd tl ih; · rfl
  simp only [mem_cons, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]
#align list.foldr_ext List.foldr_ext

@[simp]
theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a :=
  rfl
#align list.foldl_nil List.foldl_nil

@[simp]
theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : List β) :
    foldl f a (b :: l) = foldl f (f a b) l :=
  rfl
#align list.foldl_cons List.foldl_cons

@[simp]
theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b :=
  rfl
#align list.foldr_nil List.foldr_nil

@[simp]
theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    foldr f b (a :: l) = f a (foldr f b l) :=
  rfl
#align list.foldr_cons List.foldr_cons

#align list.foldl_append List.foldl_append

#align list.foldr_append List.foldr_append

theorem foldl_fixed' {f : α → β → α} {a : α} (hf : ∀ b, f a b = a) : ∀ l : List β, foldl f a l = a
  | [] => rfl
  | b :: l => by rw [foldl_cons, hf b, foldl_fixed' hf l]
#align list.foldl_fixed' List.foldl_fixed'

theorem foldr_fixed' {f : α → β → β} {b : β} (hf : ∀ a, f a b = b) : ∀ l : List α, foldr f b l = b
  | [] => rfl
  | a :: l => by rw [foldr_cons, foldr_fixed' hf l, hf a]
#align list.foldr_fixed' List.foldr_fixed'

@[simp]
theorem foldl_fixed {a : α} : ∀ l : List β, foldl (fun a _ => a) a l = a :=
  foldl_fixed' fun _ => rfl
#align list.foldl_fixed List.foldl_fixed

@[simp]
theorem foldr_fixed {b : β} : ∀ l : List α, foldr (fun _ b => b) b l = b :=
  foldr_fixed' fun _ => rfl
#align list.foldr_fixed List.foldr_fixed

@[simp]
theorem foldl_join (f : α → β → α) :
    ∀ (a : α) (L : List (List β)), foldl f a (join L) = foldl (foldl f) a L
  | a, [] => rfl
  | a, l :: L => by simp only [join, foldl_append, foldl_cons, foldl_join f (foldl f a l) L]
#align list.foldl_join List.foldl_join

@[simp]
theorem foldr_join (f : α → β → β) :
    ∀ (b : β) (L : List (List α)), foldr f b (join L) = foldr (fun l b => foldr f b l) b L
  | a, [] => rfl
  | a, l :: L => by simp only [join, foldr_append, foldr_join f a L, foldr_cons]
#align list.foldr_join List.foldr_join

#align list.foldl_reverse List.foldl_reverse

#align list.foldr_reverse List.foldr_reverse

-- Porting note: simp can prove this
-- @[simp]
theorem foldr_eta : ∀ l : List α, foldr cons [] l = l :=
  by simp only [foldr_self_append, append_nil, forall_const]
#align list.foldr_eta List.foldr_eta

@[simp]
theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  rw [← foldr_reverse]; simp only [foldr_self_append, append_nil, reverse_reverse]
#align list.reverse_foldl List.reverse_foldl

#align list.foldl_map List.foldl_map

#align list.foldr_map List.foldr_map

theorem foldl_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldl f' (g a) (l.map g) = g (List.foldl f a l) := by
  induction l generalizing a
  · simp
  · simp [*, h]
#align list.foldl_map' List.foldl_map'

theorem foldr_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldr f' (g a) (l.map g) = g (List.foldr f a l) := by
  induction l generalizing a
  · simp
  · simp [*, h]
#align list.foldr_map' List.foldr_map'

#align list.foldl_hom List.foldl_hom

#align list.foldr_hom List.foldr_hom

theorem foldl_hom₂ (l : List ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β)
    (op₃ : γ → ι → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
    foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
  Eq.symm <| by
    revert a b
    induction l <;> intros <;> [rfl; simp only [*, foldl]]
#align list.foldl_hom₂ List.foldl_hom₂

theorem foldr_hom₂ (l : List ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β)
    (op₃ : ι → γ → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
    foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) := by
  revert a
  induction l <;> intros <;> [rfl; simp only [*, foldr]]
#align list.foldr_hom₂ List.foldr_hom₂

theorem injective_foldl_comp {α : Type _} {l : List (α → α)} {f : α → α}
    (hl : ∀ f ∈ l, Function.Injective f) (hf : Function.Injective f) :
    Function.Injective (@List.foldl (α → α) (α → α) Function.comp f l) := by
  induction' l with lh lt l_ih generalizing f
  · exact hf
  · apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ (List.mem_cons_self _ _)
#align list.injective_foldl_comp List.injective_foldl_comp

/- Porting note: couldn't do induction proof because "code generator does not support recursor
  'List.rec' yet". Earlier proof:

  induction l with
  | nil => exact hb
  | cons hd tl IH =>
    refine' hl _ _ hd (mem_cons_self hd tl)
    refine' IH _
    intro y hy x hx
    exact hl y hy x (mem_cons_of_mem hd hx)
-/
/-- Induction principle for values produced by a `foldr`: if a property holds
for the seed element `b : β` and for all incremental `op : α → β → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldrRecOn {C : β → Sort _} (l : List α) (op : α → β → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ l), C (op a b)) : C (foldr op b l) := by
  cases l with
  | nil => exact hb
  | cons hd tl =>
    have IH : ((b : β) → C b → (a : α) → a ∈ tl → C (op a b)) → C (foldr op b tl) :=
      foldrRecOn _ _ _ hb
    refine' hl _ _ hd (mem_cons_self hd tl)
    refine' IH _
    intro y hy x hx
    exact hl y hy x (mem_cons_of_mem hd hx)
#align list.foldr_rec_on List.foldrRecOn

/- Porting note: couldn't do induction proof because "code generator does not support recursor
  'List.rec' yet". Earlier proof:

  induction l generalizing b with
  | nil => exact hb
  | cons hd tl IH =>
    refine' IH _ _ _
    · exact hl b hb hd (mem_cons_self hd tl)
    · intro y hy x hx
      exact hl y hy x (mem_cons_of_mem hd hx)
-/
/-- Induction principle for values produced by a `foldl`: if a property holds
for the seed element `b : β` and for all incremental `op : β → α → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldlRecOn {C : β → Sort _} (l : List α) (op : β → α → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ l), C (op b a)) : C (foldl op b l) := by
  cases l with
  | nil => exact hb
  | cons hd tl =>
    have IH : (b : β) → C b → ((b : β) → C b → (a : α) → a ∈ tl → C (op b a)) → C (foldl op b tl) :=
      foldlRecOn _ _
    refine' IH _ _ _
    · exact hl b hb hd (mem_cons_self hd tl)
    · intro y hy x hx
      exact hl y hy x (mem_cons_of_mem hd hx)
#align list.foldl_rec_on List.foldlRecOn

@[simp]
theorem foldrRecOn_nil {C : β → Sort _} (op : α → β → β) (b) (hb : C b) (hl) :
    foldrRecOn [] op b hb hl = hb :=
  rfl
#align list.foldr_rec_on_nil List.foldrRecOn_nil

@[simp]
theorem foldrRecOn_cons {C : β → Sort _} (x : α) (l : List α) (op : α → β → β) (b) (hb : C b)
    (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ x :: l), C (op a b)) :
    foldrRecOn (x :: l) op b hb hl =
      hl _ (foldrRecOn l op b hb fun b hb a ha => hl b hb a (mem_cons_of_mem _ ha)) x
        (mem_cons_self _ _) :=
  rfl
#align list.foldr_rec_on_cons List.foldrRecOn_cons

@[simp]
theorem foldlRecOn_nil {C : β → Sort _} (op : β → α → β) (b) (hb : C b) (hl) :
    foldlRecOn [] op b hb hl = hb :=
  rfl
#align list.foldl_rec_on_nil List.foldlRecOn_nil

section Scanl

variable {f : β → α → β} {b : β} {a : α} {l : List α}

theorem length_scanl : ∀ a l, length (scanl f a l) = l.length + 1
  | a, [] => rfl
  | a, x :: l => by
    rw [scanl, length_cons, length_cons, ←succ_eq_add_one, congr_arg succ]
    exact length_scanl _ _
#align list.length_scanl List.length_scanl

@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl
#align list.scanl_nil List.scanl_nil

@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := by
  simp only [scanl, eq_self_iff_true, singleton_append, and_self_iff]
#align list.scanl_cons List.scanl_cons

@[simp]
theorem get?_zero_scanl : (scanl f b l).get? 0 = some b := by
  cases l
  · simp only [get?, scanl_nil]
  · simp only [get?, scanl_cons, singleton_append]
#align list.nth_zero_scanl List.get?_zero_scanl

@[simp]
theorem get_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).get ⟨0, h⟩ = b := by
  cases l
  · simp only [get, scanl_nil]
  · simp only [get, scanl_cons, singleton_append]

set_option linter.deprecated false in
@[simp, deprecated get_zero_scanl]
theorem nthLe_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).nthLe 0 h = b :=
  get_zero_scanl
#align list.nth_le_zero_scanl List.nthLe_zero_scanl

theorem get?_succ_scanl {i : ℕ} : (scanl f b l).get? (i + 1) =
    ((scanl f b l).get? i).bind fun x => (l.get? i).map fun y => f x y := by
  induction' l with hd tl hl generalizing b i
  · symm
    simp only [Option.bind_eq_none', get?, forall₂_true_iff, not_false_iff, Option.map_none',
      scanl_nil, Option.not_mem_none, forall_true_iff]
  · simp only [scanl_cons, singleton_append]
    cases i
    · simp only [Option.map_some', get?_zero_scanl, get?, Option.some_bind']
    · simp only [hl, get?]
#align list.nth_succ_scanl List.get?_succ_scanl

set_option linter.deprecated false in
theorem nthLe_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
    (scanl f b l).nthLe (i + 1) h =
      f ((scanl f b l).nthLe i (Nat.lt_of_succ_lt h))
        (l.nthLe i (Nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l))))) := by
  induction i generalizing b l with
  | zero =>
    cases l
    · simp only [length, zero_add, scanl_nil] at h
    · simp [scanl_cons, singleton_append, nthLe_zero_scanl, nthLe_cons]
  | succ i hi =>
    cases l
    · simp only [length, add_lt_iff_neg_right, scanl_nil] at h
      exact absurd h (not_lt_of_lt Nat.succ_pos')
    · simp_rw [scanl_cons]
      rw [nthLe_append_right]
      · simp only [length, zero_add 1, succ_add_sub_one, hi]; rfl
      · simp only [length, Nat.zero_le, le_add_iff_nonneg_left]
#align list.nth_le_succ_scanl List.nthLe_succ_scanl

theorem get_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
    (scanl f b l).get ⟨i + 1, h⟩ =
      f ((scanl f b l).get ⟨i, Nat.lt_of_succ_lt h⟩)
        (l.get ⟨i, Nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l)))⟩) :=
  nthLe_succ_scanl

-- FIXME: we should do the proof the other way around
attribute [deprecated get_succ_scanl] nthLe_succ_scanl

end Scanl

-- scanr
@[simp]
theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl
#align list.scanr_nil List.scanr_nil

#noalign list.scanr_aux_cons

@[simp]
theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, foldr, cons.injEq, and_true]
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih => simp only [foldr, ih]
#align list.scanr_cons List.scanr_cons

section FoldlEqFoldr

-- foldl and foldr coincide when f is commutative and associative
variable {f : α → α → α} (hcomm : Commutative f) (hassoc : Associative f)

theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l ++ [b]) = foldr f b (a :: l)
  | a, b, nil => rfl
  | a, b, c :: l => by
    simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l]; rw [hassoc]
#align list.foldl1_eq_foldr1 List.foldl1_eq_foldr1

theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b :: l) = f b (foldl f a l)
  | a, b, nil => hcomm a b
  | a, b, c :: l => by
    simp only [foldl_cons]
    rw [← foldl_eq_of_comm_of_assoc .., right_comm _ hcomm hassoc]; rfl
#align list.foldl_eq_of_comm_of_assoc List.foldl_eq_of_comm_of_assoc

theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a, nil => rfl
  | a, b :: l => by
    simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc]; rw [foldl_eq_foldr a l]
#align list.foldl_eq_foldr List.foldl_eq_foldr

end FoldlEqFoldr

section FoldlEqFoldlr'

variable {f : α → β → α}

variable (hf : ∀ a b c, f (f a b) c = f (f a c) b)

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b :: l) = f (foldl f a l) b
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldl, foldl, foldl, ← foldl_eq_of_comm' .., foldl, hf]
#align list.foldl_eq_of_comm' List.foldl_eq_of_comm'

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
  | a, [] => rfl
  | a, b :: l => by rw [foldl_eq_of_comm' hf, foldr, foldl_eq_foldr' ..]; rfl
#align list.foldl_eq_foldr' List.foldl_eq_foldr'

end FoldlEqFoldlr'

section FoldlEqFoldlr'

variable {f : α → β → β}

variable (hf : ∀ a b c, f a (f b c) = f b (f a c))

theorem foldr_eq_of_comm' : ∀ a b l, foldr f a (b :: l) = foldr f (f b a) l
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldr, foldr, foldr, hf, ← foldr_eq_of_comm' ..]; rfl
#align list.foldr_eq_of_comm' List.foldr_eq_of_comm'

end FoldlEqFoldlr'

section

variable {op : α → α → α} [ha : IsAssociative α op] [hc : IsCommutative α op]

/-- Notation for `op a b`. -/
local notation a " ⋆ " b => op a b

/-- Notation for `foldl op a l`. -/
local notation l " <*> " a => foldl op a l

theorem foldl_assoc : ∀ {l : List α} {a₁ a₂}, (l <*> a₁ ⋆ a₂) = a₁ ⋆ l <*> a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ =>
    calc
      ((a :: l) <*> a₁ ⋆ a₂) = l <*> a₁ ⋆ a₂ ⋆ a := by simp only [foldl_cons, ha.assoc]
      _ = a₁ ⋆ (a :: l) <*> a₂ := by rw [foldl_assoc, foldl_cons]
#align list.foldl_assoc List.foldl_assoc

theorem foldl_op_eq_op_foldr_assoc :
    ∀ {l : List α} {a₁ a₂}, ((l <*> a₁) ⋆ a₂) = a₁ ⋆ l.foldr (· ⋆ ·) a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ => by
    simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc]; rw [foldl_op_eq_op_foldr_assoc]
#align list.foldl_op_eq_op_foldr_assoc List.foldl_op_eq_op_foldr_assoc

theorem foldl_assoc_comm_cons {l : List α} {a₁ a₂} : ((a₁ :: l) <*> a₂) = a₁ ⋆ l <*> a₂ := by
  rw [foldl_cons, hc.comm, foldl_assoc]
#align list.foldl_assoc_comm_cons List.foldl_assoc_comm_cons

end

/-! ### foldlM, foldrM, mapM -/

section FoldlMFoldrM

variable {m : Type v → Type w} [Monad m]

@[simp]
theorem foldlM_nil (f : β → α → m β) {b} : List.foldlM f b [] = pure b :=
  rfl
#align list.mfoldl_nil List.foldlM_nil

-- Porting note: now in std
#align list.mfoldr_nil List.foldrM_nil

@[simp]
theorem foldlM_cons {f : β → α → m β} {b a l} :
    List.foldlM f b (a :: l) = f b a >>= fun b' => List.foldlM f b' l :=
  rfl
#align list.mfoldl_cons List.foldlM_cons

/- Porting note: now in std; now assumes an instance of `LawfulMonad m`, so we make everything
  `foldrM_eq_foldr` depend on one as well. (An instance of `LawfulMonad m` was already present for
  everything following; this just moves it a few lines up.) -/
#align list.mfoldr_cons List.foldrM_cons

variable [LawfulMonad m]

theorem foldrM_eq_foldr (f : α → β → m β) (b l) :
    foldrM f b l = foldr (fun a mb => mb >>= f a) (pure b) l := by induction l <;> simp [*]
#align list.mfoldr_eq_foldr List.foldrM_eq_foldr

attribute [simp] mapM mapM'

theorem foldlM_eq_foldl (f : β → α → m β) (b l) :
    List.foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l := by
  suffices h :
    ∀ mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
  · simp [← h (pure b)]
  induction l with
  | nil => intro; simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ←l_ih, functor_norm]
#align list.mfoldl_eq_foldl List.foldlM_eq_foldl

-- Porting note: now in std
#align list.mfoldl_append List.foldlM_append

--Porting note: now in std
#align list.mfoldr_append List.foldrM_append

end FoldlMFoldrM

/-! ### intersperse -/

@[simp]
theorem intersperse_nil {α : Type u} (a : α) : intersperse a [] = [] :=
  rfl
#align list.intersperse_nil List.intersperse_nil

@[simp]
theorem intersperse_singleton {α : Type u} (a b : α) : intersperse a [b] = [b] :=
  rfl
#align list.intersperse_singleton List.intersperse_singleton

@[simp]
theorem intersperse_cons_cons {α : Type u} (a b c : α) (tl : List α) :
    intersperse a (b :: c :: tl) = b :: a :: intersperse a (c :: tl) :=
  rfl
#align list.intersperse_cons_cons List.intersperse_cons_cons

/-! ### splitAt and splitOn -/

section SplitAtOn

/- Porting note: the new version of `splitOnP` uses a `Bool`-valued predicate instead of a
  `Prop`-valued one. All downstream definitions have been updated to match. -/

variable (p : α → Bool) (xs ys : List α) (ls : List (List α)) (f : List α → List α)

/- Porting note: this had to be rewritten because of the new implementation of `splitAt`. It's
  long in large part because `splitAt.go` (`splitAt`'s auxiliary function) works differently
  in the case where n ≥ length l, requiring two separate cases (and two separate inductions). Still,
  this can hopefully be golfed. -/

@[simp]
theorem splitAt_eq_take_drop (n : ℕ) (l : List α) : splitAt n l = (take n l, drop n l) := by
  by_cases h : n < l.length <;> rw [splitAt, go_eq_take_drop]
  · rw [if_pos h]; rfl
  · rw [if_neg h, take_all_of_le <| le_of_not_lt h, drop_eq_nil_of_le <| le_of_not_lt h]
where
  go_eq_take_drop (n : ℕ) (l xs : List α) (acc : Array α) : splitAt.go l xs n acc =
      if n < xs.length then (acc.toList ++ take n xs, drop n xs) else (l, []) := by
    split_ifs with h
    · induction n generalizing xs acc with
      | zero =>
        rw [splitAt.go, take, drop, append_nil]
        · intros h₁; rw [h₁] at h; contradiction
        · intros; contradiction
      | succ _ ih =>
        cases xs with
        | nil => contradiction
        | cons hd tl =>
          rw [length, succ_eq_add_one] at h
          rw [splitAt.go, take, drop, append_cons, Array.toList_eq, ←Array.push_data,
            ←Array.toList_eq]
          exact ih _ _ <| lt_of_add_lt_add_right h
    · induction n generalizing xs acc with
      | zero =>
        rw [zero_eq, not_lt, nonpos_iff_eq_zero] at h
        rw [eq_nil_of_length_eq_zero h, splitAt.go]
      | succ _ ih =>
        cases xs with
        | nil => rw [splitAt.go]
        | cons hd tl =>
          rw [length, succ_eq_add_one] at h
          rw [splitAt.go]
          exact ih _ _ <| not_imp_not.mpr (Nat.add_lt_add_right · 1) h
#align list.split_at_eq_take_drop List.splitAt_eq_take_drop

@[simp]
theorem splitOn_nil {α : Type u} [DecidableEq α] (a : α) : [].splitOn a = [[]] :=
  rfl
#align list.split_on_nil List.splitOn_nil

@[simp]
theorem splitOnP_nil : [].splitOnP p = [[]] :=
  rfl
#align list.split_on_p_nil List.splitOnP_nilₓ

/- Porting note: `split_on_p_aux` and `split_on_p_aux'` were used to prove facts about
  `split_on_p`. `splitOnP` has a different structure, and we need different facts about
  `splitOnP.go`. Theorems involving `split_on_p_aux` have been omitted where possible. -/

#noalign list.split_on_p_aux_ne_nil
#noalign list.split_on_p_aux_spec
#noalign list.split_on_p_aux'
#noalign list.split_on_p_aux_eq
#noalign list.split_on_p_aux_nil

theorem splitOnP.go_ne_nil (xs acc : List α) : splitOnP.go p xs acc ≠ [] := by
  induction xs generalizing acc <;> simp [go]; split <;> simp [*]

theorem splitOnP.go_acc (xs acc : List α) :
    splitOnP.go p xs acc = modifyHead (acc.reverse ++ ·) (splitOnP p xs) := by
  induction xs generalizing acc with
  | nil => simp only [go, modifyHead, splitOnP_nil, append_nil]
  | cons hd tl ih =>
    simp only [splitOnP, go]; split
    · simp only [modifyHead, reverse_nil, append_nil]
    · rw [ih [hd], modifyHead_modifyHead, ih]
      congr; funext x; simp only [reverse_cons, append_assoc]; rfl

theorem splitOnP_ne_nil (xs : List α) : xs.splitOnP p ≠ [] := splitOnP.go_ne_nil _ _ _
#align list.split_on_p_ne_nil List.splitOnP_ne_nilₓ

@[simp]
theorem splitOnP_cons (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) := by
  rw [splitOnP, splitOnP.go]; split <;> [rfl; simp [splitOnP.go_acc]]
#align list.split_on_p_cons List.splitOnP_consₓ

/-- The original list `L` can be recovered by joining the lists produced by `splitOnP p L`,
interspersed with the elements `L.filter p`. -/
theorem splitOnP_spec (as : List α) :
    join (zipWith (· ++ ·) (splitOnP p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    rw [splitOnP_cons, filter]
    by_cases h : p a
    · rw [if_pos h, h, map, cons_append, zipWith, nil_append, join, cons_append, cons_inj]
      exact ih
    · rw [if_neg h, eq_false_of_ne_true h, join_zipWith (splitOnP_ne_nil _ _)
        (append_ne_nil_of_ne_nil_right _ [[]] (cons_ne_nil [] [])), cons_inj]
      exact ih
where
  join_zipWith {xs ys : List (List α)} {a : α} (hxs : xs ≠ []) (hys : ys ≠ []) :
      join (zipWith (fun x x_1 ↦ x ++ x_1) (modifyHead (cons a) xs) ys) =
        a :: join (zipWith (fun x x_1 ↦ x ++ x_1) xs ys) := by
    cases xs with | nil => contradiction | cons =>
      cases ys with | nil => contradiction | cons => rfl
#align list.split_on_p_spec List.splitOnP_specₓ

/-- If no element satisfies `p` in the list `xs`, then `xs.splitOnP p = [xs]` -/
theorem splitOnP_eq_single (h : ∀ x ∈ xs, ¬p x) : xs.splitOnP p = [xs] := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [splitOnP_cons, h hd (mem_cons_self hd tl), if_neg]
    rw [ih <| forall_mem_of_forall_mem_cons h]
    rfl
#align list.split_on_p_eq_single List.splitOnP_eq_singleₓ

/-- When a list of the form `[...xs, sep, ...as]` is split on `p`, the first element is `xs`,
  assuming no element in `xs` satisfies `p` but `sep` does satisfy `p` -/
theorem splitOnP_first (h : ∀ x ∈ xs, ¬p x) (sep : α) (hsep : p sep) (as : List α) :
    (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p := by
  induction xs with
  | nil => simp [hsep]
  | cons hd tl ih => simp [h hd _, ih <| forall_mem_of_forall_mem_cons h]
#align list.split_on_p_first List.splitOnP_firstₓ

/-- `intercalate [x]` is the left inverse of `splitOn x`  -/
theorem intercalate_splitOn (x : α) [DecidableEq α] : [x].intercalate (xs.splitOn x) = xs := by
  simp only [intercalate, splitOn]
  induction' xs with hd tl ih; · simp [join]
  cases' h' : splitOnP (· == x) tl with hd' tl'; · exact (splitOnP_ne_nil _ tl h').elim
  rw [h'] at ih
  rw [splitOnP_cons]
  split_ifs with h;
  · rw [beq_iff_eq] at h
    subst h
    simp [ih, join, h']
  cases tl' <;> simpa [join, h'] using ih
#align list.intercalate_split_on List.intercalate_splitOn

/-- `splitOn x` is the left inverse of `intercalate [x]`, on the domain
  consisting of each nonempty list of lists `ls` whose elements do not contain `x`  -/
theorem splitOn_intercalate [DecidableEq α] (x : α) (hx : ∀ l ∈ ls, x ∉ l) (hls : ls ≠ []) :
    ([x].intercalate ls).splitOn x = ls := by
  simp only [intercalate]
  induction' ls with hd tl ih; · contradiction
  cases tl
  · suffices hd.splitOn x = [hd] by simpa [join]
    refine' splitOnP_eq_single _ _ _
    intro y hy H
    rw [eq_of_beq H] at hy
    refine' hx hd _ hy
    simp
  · simp only [intersperse_cons_cons, singleton_append, join]
    specialize ih _ _
    · intro l hl
      apply hx l
      simp at hl⊢
      exact Or.inr hl
    · exact List.noConfusion
    have := splitOnP_first (· == x) hd ?h x (beq_self_eq_true _)
    case h =>
      intro y hy H
      rw [eq_of_beq H] at hy
      exact hx hd (.head _) hy
    simp only [splitOn] at ih⊢
    rw [this, ih]
#align list.split_on_intercalate List.splitOn_intercalate

end SplitAtOn

/- Porting note: new; here tentatively -/
/-! ### modifyLast -/

section ModifyLast

theorem modifyLast.go_append_one (f : α → α) (a : α) (tl : List α) (r : Array α):
    modifyLast.go f (tl ++ [a]) r = (r.toListAppend <| modifyLast.go f (tl ++ [a]) #[]) := by
  cases tl with
  | nil =>
    simp only [nil_append, modifyLast.go]; rfl
  | cons hd tl =>
    simp only [cons_append]
    rw [modifyLast.go, modifyLast.go]
    case x_3 | x_3 => exact append_ne_nil_of_ne_nil_right tl [a] (cons_ne_nil a [])
    rw [modifyLast.go_append_one _ _ tl _, modifyLast.go_append_one _ _ tl (Array.push #[] hd)]
    simp only [Array.toListAppend_eq, Array.push_data, Array.data_toArray, nil_append, append_assoc]

theorem modifyLast_append_one (f : α → α) (a : α) (l : List α) :
    modifyLast f (l ++ [a]) = l ++ [f a] := by
  cases l with
  | nil =>
    simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq, Array.data_toArray]
  | cons _ tl =>
    simp only [cons_append, modifyLast]
    rw [modifyLast.go]
    case x_3 => exact append_ne_nil_of_ne_nil_right tl [a] (cons_ne_nil a [])
    rw [modifyLast.go_append_one, Array.toListAppend_eq, Array.push_data, Array.data_toArray,
      nil_append, cons_append, nil_append, cons_inj]
    exact modifyLast_append_one _ _ tl

theorem modifyLast_append (f : α → α) (l₁ l₂ : List α) (_ : l₂ ≠ []) :
    modifyLast f (l₁ ++ l₂) = l₁ ++ modifyLast f l₂ := by
  cases l₂ with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil => exact modifyLast_append_one _ hd _
    | cons hd' tl' =>
      rw [append_cons, ←nil_append (hd :: hd' :: tl'), append_cons [], nil_append,
        modifyLast_append _ (l₁ ++ [hd]) (hd' :: tl') _, modifyLast_append _ [hd] (hd' :: tl') _,
        append_assoc]
      all_goals { exact cons_ne_nil _ _ }

end ModifyLast

/-! ### map for partial functions -/

#align list.pmap List.pmap
#align list.attach List.attach

theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) :
    SizeOf.sizeOf x < SizeOf.sizeOf l := by
  induction' l with h t ih <;> cases hx <;> rw [cons.sizeOf_spec]
  · exact lt_add_of_lt_of_nonneg (lt_one_add _) (Nat.zero_le _)
  · refine lt_add_of_pos_of_le ?_ (le_of_lt (ih ‹_›))
    rw [add_comm]; exact succ_pos _
#align list.sizeof_lt_sizeof_of_mem List.sizeOf_lt_sizeOf_of_mem

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l <;> [rfl; simp only [*, pmap, map]]
#align list.pmap_eq_map List.pmap_eq_map

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  induction' l with _ _ ih
  · rfl
  · rw [pmap, pmap, h _ (mem_cons_self _ _), ih fun a ha => h a (mem_cons_of_mem _ ha)]
#align list.pmap_congr List.pmap_congr

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l <;> [rfl; simp only [*, pmap, map]]
#align list.map_pmap List.map_pmap

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun a h => H _ (mem_map_of_mem _ h) := by
  induction l <;> [rfl; simp only [*, pmap, map]]
#align list.pmap_map List.pmap_map

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, map_pmap]; exact pmap_congr l fun _ _ _ _ => rfl
#align list.pmap_eq_map_attach List.pmap_eq_map_attach

-- @[simp] -- Porting note: lean 4 simp can't rewrite with this
theorem attach_map_coe' (l : List α) (f : α → β) :
    (l.attach.map fun (i : {i // i ∈ l}) => f i) = l.map f := by
  rw [attach, map_pmap]; exact pmap_eq_map _ _ _ _
#align list.attach_map_coe' List.attach_map_coe'

theorem attach_map_val' (l : List α) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe' _ _
#align list.attach_map_val' List.attach_map_val'

@[simp]
theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l :=
  (attach_map_coe' _ _).trans l.map_id
-- porting note: coe is expanded eagerly, so "attach_map_coe" would have the same syntactic form.
#align list.attach_map_coe List.attach_map_val
#align list.attach_map_val List.attach_map_val

@[simp]
theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_val] <;> exact h);
      · rcases this with ⟨⟨_, _⟩, m, rfl⟩
        exact m
#align list.mem_attach List.mem_attach

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _)(h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and_iff, Subtype.exists, eq_comm]
#align list.mem_pmap List.mem_pmap

@[simp]
theorem length_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l <;> [rfl; simp only [*, pmap, length]]
#align list.length_pmap List.length_pmap

@[simp]
theorem length_attach (L : List α) : L.attach.length = L.length :=
  length_pmap
#align list.length_attach List.length_attach

@[simp]
theorem pmap_eq_nil {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] := by
  rw [← length_eq_zero, length_pmap, length_eq_zero]
#align list.pmap_eq_nil List.pmap_eq_nil

@[simp]
theorem attach_eq_nil (l : List α) : l.attach = [] ↔ l = [] :=
  pmap_eq_nil
#align list.attach_eq_nil List.attach_eq_nil

theorem getLast_pmap {α β : Type _} (p : α → Prop) (f : ∀ a, p a → β) (l : List α)
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
    (l.pmap f hl₁).getLast (mt List.pmap_eq_nil.1 hl₂) =
      f (l.getLast hl₂) (hl₁ _ (List.getLast_mem hl₂)) := by
  induction' l with l_hd l_tl l_ih
  · apply (hl₂ rfl).elim
  · by_cases hl_tl : l_tl = []
    · simp [hl_tl]
    · simp only [pmap]
      rw [getLast_cons, l_ih _ hl_tl]
      simp only [getLast_cons hl_tl]
#align list.last_pmap List.getLast_pmap

theorem get?_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) (n : ℕ) :
    get? (pmap f l h) n = Option.pmap f (get? l n) fun x H => h x (get?_mem H) := by
  induction' l with hd tl hl generalizing n
  · simp
  · cases' n with n
    . simp
    . simp [hl]
#align list.nth_pmap List.get?_pmap

theorem get_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : ℕ}
    (hn : n < (pmap f l h).length) :
    get (pmap f l h) ⟨n, hn⟩ =
      f (get l ⟨n, @length_pmap _ _ p f l h ▸ hn⟩)
        (h _ (get_mem l n (@length_pmap _ _ p f l h ▸ hn))) := by
  induction' l with hd tl hl generalizing n
  · simp only [length, pmap] at hn
    exact absurd hn (not_lt_of_le n.zero_le)
  · cases n
    · simp
    · simp [hl]

set_option linter.deprecated false in
@[deprecated get_pmap]
theorem nthLe_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : ℕ}
    (hn : n < (pmap f l h).length) :
    nthLe (pmap f l h) n hn =
      f (nthLe l n (@length_pmap _ _ p f l h ▸ hn))
        (h _ (get_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
  get_pmap ..

#align list.nth_le_pmap List.nthLe_pmap

theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ l₂ : List ι)
    (h : ∀ a ∈ l₁ ++ l₂, p a) :
    (l₁ ++ l₂).pmap f h =
      (l₁.pmap f fun a ha => h a (mem_append_left l₂ ha)) ++
        l₂.pmap f fun a ha => h a (mem_append_right l₁ ha) := by
  induction' l₁ with _ _ ih
  · rfl
  · dsimp only [pmap, cons_append]
    rw [ih]
#align list.pmap_append List.pmap_append

theorem pmap_append' {α β : Type _} {p : α → Prop} (f : ∀ a : α, p a → β) (l₁ l₂ : List α)
    (h₁ : ∀ a ∈ l₁, p a) (h₂ : ∀ a ∈ l₂, p a) :
    ((l₁ ++ l₂).pmap f fun a ha => (List.mem_append.1 ha).elim (h₁ a) (h₂ a)) =
      l₁.pmap f h₁ ++ l₂.pmap f h₂ :=
  pmap_append f l₁ l₂ _
#align list.pmap_append' List.pmap_append'

/-! ### find -/

section find?

variable {p : α → Bool} {l : List α} {a : α}

@[simp]
theorem find?_nil (p : α → Bool) : find? p [] = none :=
  rfl
#align list.find_nil List.find?_nil

-- Porting note: List.find? is given @[simp] in Std.Data.List.Init.Lemmas
-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] find?_cons_of_pos
#align list.find_cons_of_pos List.find?_cons_of_pos

-- Porting note: List.find? is given @[simp] in Std.Data.List.Init.Lemmas
-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] find?_cons_of_neg
#align list.find_cons_of_neg List.find?_cons_of_neg

attribute [simp] find?_eq_none
#align list.find_eq_none List.find?_eq_none

#align list.find_some List.find?_some

@[simp]
theorem find?_mem (H : find? p l = some a) : a ∈ l := by
  induction' l with b l IH; · contradiction
  by_cases h : p b
  · rw [find?_cons_of_pos _ h] at H
    cases H
    apply mem_cons_self
  · rw [find?_cons_of_neg _ h] at H
    exact mem_cons_of_mem _ (IH H)
#align list.find_mem List.find?_mem

end find?

/-! ### lookmap -/

section Lookmap

variable (f : α → Option α)

/- Porting note: need a helper theorem for lookmap.go. -/
theorem lookmap.go_append (l : List α) (acc : Array α) :
    lookmap.go f l acc = acc.toListAppend (lookmap f l) := by
  cases l with
  | nil => rfl
  | cons hd tl =>
    rw [lookmap, go, go]
    cases f hd with
    | none => simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.push_data]; rfl
    | some a => rfl

@[simp]
theorem lookmap_nil : [].lookmap f = [] :=
  rfl
#align list.lookmap_nil List.lookmap_nil

@[simp]
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) :
    (a :: l).lookmap f = a :: l.lookmap f := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, Array.data_toArray, nil_append]
  rw [lookmap.go_append, h]; rfl
#align list.lookmap_cons_none List.lookmap_cons_none

@[simp]
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) :
    (a :: l).lookmap f = b :: l := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, Array.data_toArray, nil_append]
  rw [h]
#align list.lookmap_cons_some List.lookmap_cons_some

theorem lookmap_some : ∀ l : List α, l.lookmap some = l
  | [] => rfl
  | _ :: _ => rfl
#align list.lookmap_some List.lookmap_some

theorem lookmap_none : ∀ l : List α, (l.lookmap fun _ => none) = l
  | [] => rfl
  | a :: l => (lookmap_cons_none _ l rfl).trans (congr_arg (cons a) (lookmap_none l))
#align list.lookmap_none List.lookmap_none

theorem lookmap_congr {f g : α → Option α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
  | [], _ => rfl
  | a :: l, H => by
    cases' forall_mem_cons.1 H with H₁ H₂
    cases' h : g a with b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]
#align list.lookmap_congr List.lookmap_congr

theorem lookmap_of_forall_not {l : List α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)
#align list.lookmap_of_forall_not List.lookmap_of_forall_not

theorem lookmap_map_eq (g : α → β) (h : ∀ (a), ∀ b ∈ f a, g a = g b) :
    ∀ l : List α, map g (l.lookmap f) = map g l
  | [] => rfl
  | a :: l => by
    cases' h' : f a with b
    · simp [h']; exact lookmap_map_eq _ h l
    · simp [lookmap_cons_some _ _ h', h _ _ h']
#align list.lookmap_map_eq List.lookmap_map_eq

theorem lookmap_id' (h : ∀ (a), ∀ b ∈ f a, a = b) (l : List α) : l.lookmap f = l := by
  rw [← map_id (l.lookmap f), lookmap_map_eq, map_id]; exact h
#align list.lookmap_id' List.lookmap_id'

theorem length_lookmap (l : List α) : length (l.lookmap f) = length l := by
  rw [← length_map, lookmap_map_eq _ fun _ => (), length_map]; simp
#align list.length_lookmap List.length_lookmap

end Lookmap

/-! ### filter -/
-- Porting note: These lemmas are from Lean3 core

#align list.filter_nil List.filter_nil

#align list.filter_cons_of_pos List.filter_cons_of_pos

#align list.filter_cons_of_neg List.filter_cons_of_neg

#align list.filter_append List.filter_append

#align list.filter_sublist List.filter_sublist

/-! ### filterMap -/

#align list.filter_map_nil List.filterMap_nil

-- Porting note: List.filterMap is given @[simp] in Std.Data.List.Init.Lemmas
-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] filterMap_cons_none
#align list.filter_map_cons_none List.filterMap_cons_none

-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] filterMap_cons_some
#align list.filter_map_cons_some List.filterMap_cons_some

#align list.filter_map_cons List.filterMap_cons

#align list.filter_map_append List.filterMap_append

#align list.filter_map_eq_map List.filterMap_eq_map

#align list.filter_map_eq_filter List.filterMap_eq_filter

#align list.filter_map_filter_map List.filterMap_filterMap

#align list.map_filter_map List.map_filterMap

#align list.filter_map_map List.filterMap_map

#align list.filter_filter_map List.filter_filterMap

#align list.filter_map_filter List.filterMap_filter

#align list.filter_map_some List.filterMap_some

#align list.map_filter_map_some_eq_filter_map_is_some List.map_filterMap_some_eq_filter_map_is_some

#align list.mem_filter_map List.mem_filterMap

#align list.filter_map_join List.filterMap_join

#align list.map_filter_map_of_inv List.map_filterMap_of_inv

#align list.length_filter_le List.length_filter_leₓ

#align list.length_filter_map_le List.length_filterMap_le

#align list.sublist.filter_map List.Sublist.filterMap

theorem Sublist.map (f : α → β) {l₁ l₂ : List α} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
  filterMap_eq_map f ▸ s.filterMap _
#align list.sublist.map List.Sublist.map

/-! ### reduceOption -/

@[simp]
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id.def, eq_self_iff_true, and_self_iff]
#align list.reduce_option_cons_of_some List.reduceOption_cons_of_some

@[simp]
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id.def]
#align list.reduce_option_cons_of_none List.reduceOption_cons_of_none

@[simp]
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl
#align list.reduce_option_nil List.reduceOption_nil

@[simp]
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction' l with hd tl hl
  · simp only [reduceOption_nil, map_nil]
  ·cases hd <;>
      simpa [true_and_iff, Option.map_some', map, eq_self_iff_true,
        reduceOption_cons_of_some] using hl
#align list.reduce_option_map List.reduceOption_map

theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append l l' id
#align list.reduce_option_append List.reduceOption_append

theorem reduceOption_length_le (l : List (Option α)) : l.reduceOption.length ≤ l.length := by
  induction' l with hd tl hl
  · simp only [reduceOption_nil, length]
  · cases hd
    · exact Nat.le_succ_of_le hl
    · simpa only [length, add_le_add_iff_right, reduceOption_cons_of_some] using hl
#align list.reduce_option_length_le List.reduceOption_length_le

theorem reduceOption_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x := by
  induction' l with hd tl hl
  · simp only [forall_const, reduceOption_nil, not_mem_nil, forall_prop_of_false, eq_self_iff_true,
      length, not_false_iff]
  · cases hd
    · simp only [mem_cons, forall_eq_or_imp, Bool.coe_sort_false, false_and_iff,
        reduceOption_cons_of_none, length, Option.isSome_none, iff_false_iff]
      intro H
      have := reduceOption_length_le tl
      rw [H] at this
      exact absurd (Nat.lt_succ_self _) (not_lt_of_le this)
    · simp only [length, add_left_inj, find?, mem_cons, forall_eq_or_imp, Option.isSome_some,
        ← hl, reduceOption, true_and]
#align list.reduce_option_length_eq_iff List.reduceOption_length_eq_iff

theorem reduceOption_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none ∈ l := by
  rw [(reduceOption_length_le l).lt_iff_ne, Ne, reduceOption_length_eq_iff]
  induction l <;> simp [*]
  rw [@eq_comm _ none, ← Option.not_isSome_iff_eq_none, Decidable.imp_iff_not_or]
  simp [Option.isNone_iff_eq_none]
#align list.reduce_option_length_lt_iff List.reduceOption_length_lt_iff

theorem reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl
#align list.reduce_option_singleton List.reduceOption_singleton

theorem reduceOption_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList := by
  induction' l with hd tl hl generalizing x
  · cases x <;> simp [Option.toList]
  · simp only [concat_eq_append, reduceOption_append] at hl
    cases hd <;> simp [hl, reduceOption_append]
#align list.reduce_option_concat List.reduceOption_concat

theorem reduceOption_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]
#align list.reduce_option_concat_of_some List.reduceOption_concat_of_some

theorem reduceOption_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduceOption ↔ some x ∈ l := by
  simp only [reduceOption, id.def, mem_filterMap, exists_eq_right]
#align list.reduce_option_mem_iff List.reduceOption_mem_iff

theorem reduceOption_get?_iff {l : List (Option α)} {x : α} :
    (∃ i, l.get? i = some (some x)) ↔ ∃ i, l.reduceOption.get? i = some x := by
  rw [← mem_iff_get?, ← mem_iff_get?, reduceOption_mem_iff]
#align list.reduce_option_nth_iff List.reduceOption_get?_iff

/-! ### filter -/

section Filter

-- Porting note: Lemmas for `filter` are stated in terms of `p : α → Bool`
-- rather than `p : α → Prop` with `DecidablePred p`, since `filter` itself is.
-- Likewise, `if` sometimes becomes `bif`.
variable {p : α → Bool}

theorem filter_singleton {a : α} : [a].filter p = bif p a then [a] else [] :=
  rfl
#align list.filter_singleton List.filter_singleton

theorem filter_eq_foldr (p : α → Bool) (l : List α) :
    filter p l = foldr (fun a out => bif p a then a :: out else out) [] l := by
  induction l <;> simp [*, filter]; rfl
#align list.filter_eq_foldr List.filter_eq_foldr

#align list.filter_congr' List.filter_congr'

@[simp]
theorem filter_subset (l : List α) : filter p l ⊆ l :=
  (filter_sublist l).subset
#align list.filter_subset List.filter_subset

theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
  | b :: l, ain =>
    if pb : p b then
      have : a ∈ b :: filter p l := by simpa only [filter_cons_of_pos _ pb] using ain
      Or.elim (eq_or_mem_of_mem_cons this) (fun h : a = b => by rw [← h] at pb; exact pb)
        fun h : a ∈ filter p l => of_mem_filter h
    else by simp only [filter_cons_of_neg _ pb] at ain; exact of_mem_filter ain
#align list.of_mem_filter List.of_mem_filter

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset l h
#align list.mem_of_mem_filter List.mem_of_mem_filter

theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
  | x :: l, h, h1 => by
    rcases mem_cons.1 h with rfl | h
    . simp [filter, h1]
    . rw [filter]
      cases p x <;> simp [mem_filter_of_mem h h1]
#align list.mem_filter_of_mem List.mem_filter_of_mem

#align list.mem_filter List.mem_filter

theorem monotone_filter_left (p : α → Bool) ⦃l l' : List α⦄ (h : l ⊆ l') :
    filter p l ⊆ filter p l' := by
  intro x hx
  rw [mem_filter] at hx⊢
  exact ⟨h hx.left, hx.right⟩
#align list.monotone_filter_left List.monotone_filter_left

#align list.filter_eq_self List.filter_eq_self

#align list.filter_length_eq_length List.filter_length_eq_length

#align list.filter_eq_nil List.filter_eq_nil

variable (p)

#align list.sublist.filter List.Sublist.filter

theorem monotone_filter_right (l : List α) ⦃p q : α → Bool⦄
    (h : ∀ a, p a → q a) : l.filter p <+ l.filter q := by
  induction' l with hd tl IH
  · rfl
  · by_cases hp : p hd
    · rw [filter_cons_of_pos _ hp, filter_cons_of_pos _ (h _ hp)]
      exact IH.cons_cons hd
    · rw [filter_cons_of_neg _ hp]
      by_cases hq : q hd
      · rw [filter_cons_of_pos _ hq]
        exact sublist_cons_of_sublist hd IH
      · rw [filter_cons_of_neg _ hq]
        exact IH
#align list.monotone_filter_right List.monotone_filter_right

#align list.map_filter List.map_filter

#align list.filter_filter List.filter_filter

@[simp]
theorem filter_true  (l : List α) :
    filter (fun _ => true) l = l := by induction l <;> simp [*, filter]
#align list.filter_true List.filter_true

@[simp]
theorem filter_false (l : List α) :
    filter (fun _ => false) l = [] := by induction l <;> simp [*, filter]
#align list.filter_false List.filter_false

/- Porting note: need a helper theorem for span.loop. -/
theorem span.loop_eq_take_drop :
  ∀ l₁ l₂ : List α, span.loop p l₁ l₂ = (l₂.reverse ++ takeWhile p l₁, dropWhile p l₁)
  | [], l₂ => by simp [span.loop, takeWhile, dropWhile]
  | (a :: l), l₂ => by
    cases hp : p a <;> simp [hp, span.loop, span.loop_eq_take_drop, takeWhile, dropWhile]

@[simp]
theorem span_eq_take_drop (l : List α) : span p l = (takeWhile p l, dropWhile p l) := by
  simpa using span.loop_eq_take_drop p l []
#align list.span_eq_take_drop List.span_eq_take_drop

#align list.take_while_append_drop List.takeWhile_append_dropWhile

theorem dropWhile_nthLe_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).nthLe 0 hl) := by
  induction' l with hd tl IH
  · cases hl
  · simp only [dropWhile]
    by_cases hp : p hd
    · simp [hp, IH]
    · simp [hp, nthLe_cons]
-- porting note: How did the Lean 3 proof work,
-- without mentioning nthLe_cons?
-- Same question for takeWhile_eq_nil_iff below
#align list.drop_while_nth_le_zero_not List.dropWhile_nthLe_zero_not

variable {p} {l : List α}

@[simp]
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp [dropWhile]
  · by_cases hp : p x <;> simp [hp, dropWhile, IH]
#align list.drop_while_eq_nil_iff List.dropWhile_eq_nil_iff

@[simp]
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp [takeWhile]
  · by_cases hp : p x <;> simp [hp, takeWhile, IH]
#align list.take_while_eq_self_iff List.takeWhile_eq_self_iff

@[simp]
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.nthLe 0 hl) := by
  induction' l with x xs IH
  · simp [takeWhile, true_iff]
    intro h
    simp at h
  · by_cases hp : p x <;> simp [hp, takeWhile, IH, nthLe_cons]
#align list.take_while_eq_nil_iff List.takeWhile_eq_nil_iff

theorem mem_takeWhile_imp {x : α} (hx : x ∈ takeWhile p l) : p x := by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx
#align list.mem_take_while_imp List.mem_takeWhile_imp

theorem takeWhile_takeWhile (p q : α → Bool) (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction' l with hd tl IH
  · simp [takeWhile]
  · by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]
#align list.take_while_take_while List.takeWhile_takeWhile

theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]
#align list.take_while_idem List.takeWhile_idem

end Filter

/-! ### erasep -/

section eraseP

variable {p : α → Bool}

#align list.erasep_nil List.eraseP_nilₓ -- prop -> bool
#align list.erasep_cons List.eraseP_consₓ -- prop -> bool

#align list.erasep_cons_of_pos List.eraseP_cons_of_posₓ -- prop -> bool
#align list.erasep_cons_of_neg List.eraseP_cons_of_negₓ -- prop -> bool
#align list.erasep_of_forall_not List.eraseP_of_forall_notₓ -- prop -> bool
#align list.exists_of_erasep List.exists_of_erasePₓ -- prop -> bool
#align list.exists_or_eq_self_of_erasep List.exists_or_eq_self_of_erasePₓ -- prop -> bool
#align list.length_erasep_of_mem List.length_eraseP_of_memₓ -- prop -> bool

@[simp]
theorem length_eraseP_add_one {l : List α} {a} (al : a ∈ l) (pa : p a) :
    (l.eraseP p).length + 1 = l.length := by
  let ⟨_, l₁, l₂, _, _, h₁, h₂⟩ := exists_of_eraseP al pa
  rw [h₂, h₁, length_append, length_append]
  rfl
#align list.length_erasep_add_one List.length_eraseP_add_oneₓ -- prop -> bool

#align list.erasep_append_left List.eraseP_append_leftₓ -- prop -> bool
#align list.erasep_append_right List.eraseP_append_rightₓ -- prop -> bool
#align list.erasep_sublist List.eraseP_sublistₓ -- prop -> bool
#align list.erasep_subset List.eraseP_subsetₓ -- prop -> bool
#align list.sublist.erasep List.Sublist.erasePₓ -- prop -> bool
#align list.mem_of_mem_erasep List.mem_of_mem_erasePₓ -- prop -> bool
#align list.mem_erasep_of_neg List.mem_eraseP_of_negₓ -- prop -> bool
#align list.erasep_map List.eraseP_mapₓ -- prop -> bool
#align list.extractp_eq_find_erasep List.extractP_eq_find?_erasePₓ -- prop -> bool

end eraseP

/-! ### erase -/

section Erase

variable [DecidableEq α]

#align list.erase_nil List.erase_nil

#align list.erase_cons List.erase_consₓ -- DecidableEq -> BEq
#align list.erase_cons_head List.erase_cons_headₓ -- DecidableEq -> BEq
#align list.erase_cons_tail List.erase_cons_tailₓ -- DecidableEq -> BEq
#align list.erase_eq_erasep List.erase_eq_erasePₓ -- DecidableEq -> BEq
#align list.erase_of_not_mem List.erase_of_not_memₓ -- DecidableEq -> BEq
#align list.exists_erase_eq List.exists_erase_eqₓ -- DecidableEq -> BEq
#align list.length_erase_of_mem List.length_erase_of_memₓ -- DecidableEq -> BEq

@[simp] theorem length_erase_add_one {a : α} {l : List α} (h : a ∈ l) :
    (l.erase a).length + 1 = l.length := by
  rw [erase_eq_eraseP, length_eraseP_add_one h (decide_eq_true rfl)]
#align list.length_erase_add_one List.length_erase_add_oneₓ -- DecidableEq -> BEq

#align list.erase_append_left List.erase_append_leftₓ -- DecidableEq -> BEq
#align list.erase_append_right List.erase_append_rightₓ -- DecidableEq -> BEq
#align list.erase_sublist List.erase_sublistₓ -- DecidableEq -> BEq
#align list.erase_subset List.erase_subsetₓ -- DecidableEq -> BEq

#align list.sublist.erase List.Sublist.eraseₓ -- DecidableEq -> BEq

#align list.mem_of_mem_erase List.mem_of_mem_eraseₓ -- DecidableEq -> BEq
#align list.mem_erase_of_ne List.mem_erase_of_neₓ -- DecidableEq -> BEq
#align list.erase_comm List.erase_commₓ -- DecidableEq -> BEq

theorem map_erase [DecidableEq β] {f : α → β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) := by
  have this : Eq a = Eq (f a) ∘ f := by ext b; simp [finj.eq_iff]
  simp [erase_eq_eraseP, erase_eq_eraseP, eraseP_map, this]; rfl
#align list.map_erase List.map_erase

theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]
#align list.map_foldl_erase List.map_foldl_erase

end Erase

/-! ### diff -/

section Diff

variable [DecidableEq α]

#align list.diff_nil List.diff_nil

#align list.diff_cons List.diff_cons

#align list.diff_cons_right List.diff_cons_right

#align list.diff_erase List.diff_erase

#align list.nil_diff List.nil_diff

#align list.cons_diff List.cons_diff

#align list.cons_diff_of_mem List.cons_diff_of_mem

#align list.cons_diff_of_not_mem List.cons_diff_of_not_mem

#align list.diff_eq_foldl List.diff_eq_foldl

#align list.diff_append List.diff_append

@[simp]
theorem map_diff [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]
#align list.map_diff List.map_diff

#align list.diff_sublist List.diff_sublist

#align list.diff_subset List.diff_subset

#align list.mem_diff_of_mem List.mem_diff_of_mem

#align list.sublist.diff_right List.Sublist.diff_right

theorem erase_diff_erase_sublist_of_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], l₂, _ => erase_sublist _ _
  | b :: l₁, l₂, h =>
    if heq : b = a then by simp only [heq, erase_cons_head, diff_cons]; rfl
    else by
      simp only [erase_cons_head b l₁, erase_cons_tail l₁ heq,
        diff_cons ((List.erase l₂ a)) (List.erase l₁ a) b, diff_cons l₂ l₁ b, erase_comm a b l₂]
      have h' := h.erase b
      rw [erase_cons_head] at h'
      exact @erase_diff_erase_sublist_of_sublist _ l₁ (l₂.erase b) h'
#align list.erase_diff_erase_sublist_of_sublist List.erase_diff_erase_sublist_of_sublist

end Diff

/-! ### enum -/

theorem length_enumFrom : ∀ (n) (l : List α), length (enumFrom n l) = length l
  | _, [] => rfl
  | _, _ :: _ => congr_arg Nat.succ (length_enumFrom _ _)
#align list.length_enum_from List.length_enumFrom

theorem length_enum : ∀ l : List α, length (enum l) = length l :=
  length_enumFrom _
#align list.length_enum List.length_enum

@[simp]
theorem enumFrom_get? :
    ∀ (n) (l : List α) (m), get? (enumFrom n l) m = (fun a => (n + m, a)) <$> get? l m
  | n, [], m => rfl
  | n, a :: l, 0 => rfl
  | n, a :: l, m + 1 => (enumFrom_get? (n + 1) l m).trans <| by rw [add_right_comm]; rfl
#align list.enum_from_nth List.enumFrom_get?

@[simp]
theorem enum_get? : ∀ (l : List α) (n), get? (enum l) n = (fun a => (n, a)) <$> get? l n := by
  simp only [enum, enumFrom_get?, zero_add]; intros; trivial
#align list.enum_nth List.enum_get?

@[simp]
theorem enumFrom_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | _, [] => rfl
  | _, _ :: _ => congr_arg (cons _) (enumFrom_map_snd _ _)
#align list.enum_from_map_snd List.enumFrom_map_snd

@[simp]
theorem enum_map_snd : ∀ l : List α, map Prod.snd (enum l) = l :=
  enumFrom_map_snd _
#align list.enum_map_snd List.enum_map_snd

theorem mem_enumFrom {x : α} {i : ℕ} :
    ∀ {j : ℕ} (xs : List α), (i, x) ∈ xs.enumFrom j → j ≤ i ∧ i < j + xs.length ∧ x ∈ xs
  | j, [] => by simp [enumFrom]
  | j, y :: ys => by
    suffices
      i = j ∧ x = y ∨ (i, x) ∈ enumFrom (j + 1) ys →
        j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys)
      by simpa [enumFrom, mem_enumFrom ys]
    rintro (h | h)
    · refine' ⟨le_of_eq h.1.symm, h.1 ▸ _, Or.inl h.2⟩
      apply Nat.lt_add_of_pos_right; simp
    · have ⟨hji, hijlen, hmem⟩ := mem_enumFrom _ h
      refine' ⟨_, _, _⟩
      · exact le_trans (Nat.le_succ _) hji
      · convert hijlen using 1
        ac_rfl
      · simp [hmem]
#align list.mem_enum_from List.mem_enumFrom

@[simp]
theorem enum_nil : enum ([] : List α) = [] :=
  rfl
#align list.enum_nil List.enum_nil

@[simp]
theorem enumFrom_nil (n : ℕ) : enumFrom n ([] : List α) = [] :=
  rfl
#align list.enum_from_nil List.enumFrom_nil

@[simp]
theorem enumFrom_cons (x : α) (xs : List α) (n : ℕ) :
    enumFrom n (x :: xs) = (n, x) :: enumFrom (n + 1) xs :=
  rfl
#align list.enum_from_cons List.enumFrom_cons

@[simp]
theorem enum_cons (x : α) (xs : List α) : enum (x :: xs) = (0, x) :: enumFrom 1 xs :=
  rfl
#align list.enum_cons List.enum_cons

@[simp]
theorem enumFrom_singleton (x : α) (n : ℕ) : enumFrom n [x] = [(n, x)] :=
  rfl
#align list.enum_from_singleton List.enumFrom_singleton

@[simp]
theorem enum_singleton (x : α) : enum [x] = [(0, x)] :=
  rfl
#align list.enum_singleton List.enum_singleton

theorem enumFrom_append (xs ys : List α) (n : ℕ) :
    enumFrom n (xs ++ ys) = enumFrom n xs ++ enumFrom (n + xs.length) ys := by
  induction' xs with x xs IH generalizing ys n
  · simp
  · rw [cons_append, enumFrom_cons, IH, ← cons_append, ← enumFrom_cons, length, add_right_comm,
      add_assoc]
#align list.enum_from_append List.enumFrom_append

theorem enum_append (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]
#align list.enum_append List.enum_append

theorem map_fst_add_enumFrom_eq_enumFrom (l : List α) (n k : ℕ) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l := by
  induction' l with hd tl IH generalizing n k
  · simp [enumFrom]
  · simp only [enumFrom, map, zero_add, Prod.map_mk, id.def, eq_self_iff_true, true_and_iff]
    simp [IH, add_comm n k, add_assoc, add_left_comm]
#align list.map_fst_add_enum_from_eq_enum_from List.map_fst_add_enumFrom_eq_enumFrom

theorem map_fst_add_enum_eq_enumFrom (l : List α) (n : ℕ) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enumFrom_eq_enumFrom l _ _
#align list.map_fst_add_enum_eq_enum_from List.map_fst_add_enum_eq_enumFrom

theorem enumFrom_cons' (n : ℕ) (x : α) (xs : List α) :
    enumFrom n (x :: xs) = (n, x) :: (enumFrom n xs).map (Prod.map Nat.succ id) := by
  rw [enumFrom_cons, add_comm, ← map_fst_add_enumFrom_eq_enumFrom]
#align list.enum_from_cons' List.enumFrom_cons'

theorem enum_cons' (x : α) (xs : List α) :
    enum (x :: xs) = (0, x) :: (enum xs).map (Prod.map Nat.succ id) :=
  enumFrom_cons' _ _ _
#align list.enum_cons' List.enum_cons'

theorem enumFrom_map (n : ℕ) (l : List α) (f : α → β) :
    enumFrom n (l.map f) = (enumFrom n l).map (Prod.map id f) := by
  induction' l with hd tl IH
  · rfl
  · rw [map_cons, enumFrom_cons', enumFrom_cons', map_cons, map_map, IH, map_map]
    rfl
#align list.enum_from_map List.enumFrom_map

theorem enum_map (l : List α) (f : α → β) : (l.map f).enum = l.enum.map (Prod.map id f) :=
  enumFrom_map _ _ _
#align list.enum_map List.enum_map

theorem get_enumFrom (l : List α) (n) (i : Fin (l.enumFrom n).length)
    (hi : i.1 < l.length := (by simpa [length_enumFrom] using i.2)) :
    (l.enumFrom n).get i = (n + i, l.get ⟨i, hi⟩) := by
  rw [← Option.some_inj, ← get?_eq_get]
  simp [enumFrom_get?, get?_eq_get hi]

set_option linter.deprecated false in
@[deprecated get_enumFrom]
theorem nthLe_enumFrom (l : List α) (n i : ℕ) (hi' : i < (l.enumFrom n).length)
    (hi : i < l.length := (by simpa [length_enumFrom] using hi')) :
    (l.enumFrom n).nthLe i hi' = (n + i, l.nthLe i hi) :=
  get_enumFrom ..
#align list.nth_le_enum_from List.nthLe_enumFrom

theorem get_enum (l : List α) (i : Fin l.enum.length)
    (hi : i < l.length := (by simpa [length_enum] using i.2)) :
    l.enum.get i = (i.1, l.get ⟨i, hi⟩) := by
  convert get_enumFrom _ _ i
  exact (zero_add _).symm

set_option linter.deprecated false in
@[deprecated get_enum]
theorem nthLe_enum (l : List α) (i : ℕ) (hi' : i < l.enum.length)
    (hi : i < l.length := (by simpa [length_enum] using hi')) :
    l.enum.nthLe i hi' = (i, l.nthLe i hi) := get_enum ..
#align list.nth_le_enum List.nthLe_enum

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

theorem choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
#align list.choose_spec List.choose_spec

theorem choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
#align list.choose_mem List.choose_mem

theorem choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2
#align list.choose_property List.choose_property

end Choose

/-! ### map₂Left' -/

section Map₂Left'

-- The definitional equalities for `map₂Left'` can already be used by the
-- simplifier because `map₂Left'` is marked `@[simp]`.
@[simp]
theorem map₂Left'_nil_right (f : α → Option β → γ) (as) :
    map₂Left' f as [] = (as.map fun a => f a none, []) := by cases as <;> rfl
#align list.map₂_left'_nil_right List.map₂Left'_nil_right

end Map₂Left'

/-! ### map₂Right' -/

section Map₂Right'

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂Right'_nil_left : map₂Right' f [] bs = (bs.map (f none), []) := by cases bs <;> rfl
#align list.map₂_right'_nil_left List.map₂Right'_nil_left

@[simp]
theorem map₂Right'_nil_right : map₂Right' f as [] = ([], as) :=
  rfl
#align list.map₂_right'_nil_right List.map₂Right'_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem map₂Right'_nil_cons : map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl
#align list.map₂_right'_nil_cons List.map₂Right'_nil_cons

@[simp]
theorem map₂Right'_cons_cons :
    map₂Right' f (a :: as) (b :: bs) =
      let r := map₂Right' f as bs
      (f (some a) b :: r.fst, r.snd) :=
  rfl
#align list.map₂_right'_cons_cons List.map₂Right'_cons_cons

end Map₂Right'

/-! ### zipLeft' -/

section ZipLeft'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map fun a => (a, none), []) := by
  cases as <;> rfl
#align list.zip_left'_nil_right List.zipLeft'_nil_right

@[simp]
theorem zipLeft'_nil_left : zipLeft' ([] : List α) bs = ([], bs) :=
  rfl
#align list.zip_left'_nil_left List.zipLeft'_nil_left

-- Porting note: simp can prove this
-- @[simp]
theorem zipLeft'_cons_nil :
    zipLeft' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl
#align list.zip_left'_cons_nil List.zipLeft'_cons_nil

@[simp]
theorem zipLeft'_cons_cons :
    zipLeft' (a :: as) (b :: bs) =
      let r := zipLeft' as bs
      ((a, some b) :: r.fst, r.snd) :=
  rfl
#align list.zip_left'_cons_cons List.zipLeft'_cons_cons

end ZipLeft'

/-! ### zipRight' -/

section ZipRight'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.map fun b => (none, b), []) := by
  cases bs <;> rfl
#align list.zip_right'_nil_left List.zipRight'_nil_left

@[simp]
theorem zipRight'_nil_right : zipRight' as ([] : List β) = ([], as) :=
  rfl
#align list.zip_right'_nil_right List.zipRight'_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem zipRight'_nil_cons :
    zipRight' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl
#align list.zip_right'_nil_cons List.zipRight'_nil_cons

@[simp]
theorem zipRight'_cons_cons :
    zipRight' (a :: as) (b :: bs) =
      let r := zipRight' as bs
      ((some a, b) :: r.fst, r.snd) :=
  rfl
#align list.zip_right'_cons_cons List.zipRight'_cons_cons

end ZipRight'

/-! ### map₂Left -/

section Map₂Left

variable (f : α → Option β → γ) (as : List α)

-- The definitional equalities for `map₂Left` can already be used by the
-- simplifier because `map₂Left` is marked `@[simp]`.
@[simp]
theorem map₂Left_nil_right : map₂Left f as [] = as.map fun a => f a none := by cases as <;> rfl
#align list.map₂_left_nil_right List.map₂Left_nil_right

theorem map₂Left_eq_map₂Left' : ∀ as bs, map₂Left f as bs = (map₂Left' f as bs).fst
  | [], _ => by simp
  | a :: as, [] => by simp
  | a :: as, b :: bs => by simp [map₂Left_eq_map₂Left']
#align list.map₂_left_eq_map₂_left' List.map₂Left_eq_map₂Left'

theorem map₂Left_eq_zipWith :
    ∀ as bs, length as ≤ length bs → map₂Left f as bs = zipWith (fun a b => f a (some b)) as bs
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp
  | a :: as, [], h => by
    simp at h
  | a :: as, b :: bs, h => by
    simp [Nat.succ_le_succ_iff] at h
    simp [h, map₂Left_eq_zipWith]
#align list.map₂_left_eq_map₂ List.map₂Left_eq_zipWith

end Map₂Left

/-! ### map₂Right -/

section Map₂Right

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂Right_nil_left : map₂Right f [] bs = bs.map (f none) := by cases bs <;> rfl
#align list.map₂_right_nil_left List.map₂Right_nil_left

@[simp]
theorem map₂Right_nil_right : map₂Right f as [] = [] :=
  rfl
#align list.map₂_right_nil_right List.map₂Right_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem map₂Right_nil_cons : map₂Right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl
#align list.map₂_right_nil_cons List.map₂Right_nil_cons

@[simp]
theorem map₂Right_cons_cons :
    map₂Right f (a :: as) (b :: bs) = f (some a) b :: map₂Right f as bs :=
  rfl
#align list.map₂_right_cons_cons List.map₂Right_cons_cons

theorem map₂Right_eq_map₂Right' : map₂Right f as bs = (map₂Right' f as bs).fst := by
  simp only [map₂Right, map₂Right', map₂Left_eq_map₂Left']
#align list.map₂_right_eq_map₂_right' List.map₂Right_eq_map₂Right'

theorem map₂Right_eq_zipWith (h : length bs ≤ length as) :
    map₂Right f as bs = zipWith (fun a b => f (some a) b) as bs := by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂Right, map₂Left_eq_zipWith, zipWith_flip, *]
#align list.map₂_right_eq_map₂ List.map₂Right_eq_zipWith

end Map₂Right

/-! ### zipLeft -/

section ZipLeft

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipLeft_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none) := by
  cases as <;> rfl
#align list.zip_left_nil_right List.zipLeft_nil_right

@[simp]
theorem zipLeft_nil_left : zipLeft ([] : List α) bs = [] :=
  rfl
#align list.zip_left_nil_left List.zipLeft_nil_left

-- Porting note: simp can prove this
-- @[simp]
theorem zipLeft_cons_nil :
    zipLeft (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl
#align list.zip_left_cons_nil List.zipLeft_cons_nil

@[simp]
theorem zipLeft_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs :=
  rfl
#align list.zip_left_cons_cons List.zipLeft_cons_cons

-- Porting note: arguments explicit for recursion
theorem zipLeft_eq_zipLeft' (as : List α) (bs : List β) : zipLeft as bs = (zipLeft' as bs).fst := by
  rw [zipLeft, zipLeft']
  cases as with
  | nil => rfl
  | cons _ atl =>
    cases bs with
    | nil => rfl
    | cons _ btl => rw [zipWithLeft, zipWithLeft', cons_inj]; exact @zipLeft_eq_zipLeft' atl btl
#align list.zip_left_eq_zip_left' List.zipLeft_eq_zipLeft'

end ZipLeft

/-! ### zipRight -/

section ZipRight

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipRight_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b) := by
  cases bs <;> rfl
#align list.zip_right_nil_left List.zipRight_nil_left

@[simp]
theorem zipRight_nil_right : zipRight as ([] : List β) = [] :=
  rfl
#align list.zip_right_nil_right List.zipRight_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem zipRight_nil_cons :
    zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl
#align list.zip_right_nil_cons List.zipRight_nil_cons

@[simp]
theorem zipRight_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs :=
  rfl
#align list.zip_right_cons_cons List.zipRight_cons_cons

theorem zipRight_eq_zipRight' : zipRight as bs = (zipRight' as bs).fst := by
  induction as generalizing bs <;> cases bs <;> simp [*]
#align list.zip_right_eq_zip_right' List.zipRight_eq_zipRight'

end ZipRight

/-! ### toChunks -/

-- Porting note:
-- The definition of `toChunks` has changed substantially from Lean 3.
-- The theorems about `toChunks` are not used anywhere in mathlib, anyways.
-- TODO: Prove these theorems for the new definitions.

#noalign list.to_chunks_nil
#noalign list.to_chunks_aux_eq
#noalign list.to_chunks_eq_cons'
#noalign list.to_chunks_eq_cons
#noalign list.to_chunks_aux_join
#noalign list.to_chunks_join
#noalign list.to_chunks_length_le

/-! ### all₂ -/

section All₂

variable {p q : α → Prop} {l : List α}

@[simp]
theorem all₂_cons (p : α → Prop) (x : α) : ∀ l : List α, All₂ p (x :: l) ↔ p x ∧ All₂ p l
  | [] => (and_true_iff _).symm
  | _ :: _ => Iff.rfl
#align list.all₂_cons List.all₂_cons

theorem all₂_iff_forall : ∀ {l : List α}, All₂ p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [forall_mem_cons, all₂_cons, all₂_iff_forall]
#align list.all₂_iff_forall List.all₂_iff_forall

theorem All₂.imp (h : ∀ x, p x → q x) : ∀ {l : List α}, All₂ p l → All₂ q l
  | [] => id
  | x :: l => by simp; rw [←and_imp]; exact And.imp (h x) (All₂.imp h)
#align list.all₂.imp List.All₂.imp

@[simp]
theorem all₂_map_iff {p : β → Prop} (f : α → β) : All₂ p (l.map f) ↔ All₂ (p ∘ f) l := by
  induction l <;> simp [*]
#align list.all₂_map_iff List.all₂_map_iff

instance (p : α → Prop) [DecidablePred p] : DecidablePred (All₂ p) := fun _ =>
  decidable_of_iff' _ all₂_iff_forall

end All₂

/-! ### Retroattributes

The list definitions happen earlier than `to_additive`, so here we tag the few multiplicative
definitions that couldn't be tagged earlier.
-/

attribute [to_additive existing] List.prod -- `List.sum`
attribute [to_additive existing] alternatingProd -- `List.alternatingSum`

/-! ### Miscellaneous lemmas -/

theorem getLast_reverse {l : List α} (hl : l.reverse ≠ [])
    (hl' : 0 < l.length := (by
      contrapose! hl
      simpa [length_eq_zero] using hl)) :
    l.reverse.getLast hl = l.get ⟨0, hl'⟩ := by
  rw [getLast_eq_get, get_reverse']
  · simp
  · simpa using hl'
#align list.last_reverse List.getLast_reverse

theorem ilast'_mem : ∀ a l, @ilast' α a l ∈ a :: l
  | a, [] => by simp [ilast']
  | a, b :: l => by rw [mem_cons]; exact Or.inr (ilast'_mem b l)
#align list.ilast'_mem List.ilast'_mem

@[simp]
theorem get_attach (L : List α) (i) :
    (L.attach.get i).1 = L.get ⟨i, length_attach L ▸ i.2⟩ :=
  calc
    (L.attach.get i).1 = (L.attach.map Subtype.val).get ⟨i, by simpa using i.2⟩ :=
      by rw [get_map]
    _ = L.get { val := i, isLt := _ } := by congr 2 <;> simp

@[simp, deprecated get_attach]
theorem nthLe_attach (L : List α) (i) (H : i < L.attach.length) :
    (L.attach.nthLe i H).1 = L.nthLe i (length_attach L ▸ H) := get_attach ..
#align list.nth_le_attach List.nthLe_attach

@[simp 1100]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs := by
  induction' xs with x xs xs_ih
  · simp only [not_mem_nil, map_nil]
  · cases' x with a b
    simp only [mem_cons, Prod.mk.inj_iff, map, Prod.swap_prod_mk, Prod.exists, xs_ih, and_comm]
#align list.mem_map_swap List.mem_map_swap

theorem dropSlice_eq (xs : List α) (n m : ℕ) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs
  · cases xs <;> simp [dropSlice]
  · cases xs <;> simp [dropSlice, *, Nat.succ_add]
#align list.slice_eq List.dropSlice_eq

theorem sizeOf_dropSlice_lt [SizeOf α] (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    SizeOf.sizeOf (List.dropSlice i j xs) < SizeOf.sizeOf xs := by
  induction xs generalizing i j hj with
  | nil => cases hi
  | cons x xs xs_ih =>
    cases i <;> simp only [List.dropSlice]
    · cases j with
      | zero => contradiction
      | succ n =>
        dsimp only [drop]; apply @lt_of_le_of_lt _ _ _ (sizeOf xs)
        induction xs generalizing n with
        | nil => rw [drop_nil]
        | cons _ xs_tl =>
          cases n
          · simp
          · simp [drop]
            rw [←Nat.zero_add (sizeOf (drop _ xs_tl))]
            exact Nat.add_le_add (Nat.zero_le _) (drop_sizeOf_le xs_tl _)
        · simp
    · simp
      apply xs_ih _ j hj
      apply lt_of_succ_lt_succ hi
#align list.sizeof_slice_lt List.sizeOf_dropSlice_lt

/-! ### getD and getI -/

section getD

variable (l : List α) (x : α) (xs : List α) (d : α) (n : ℕ)

@[simp]
theorem getD_nil : getD [] n d = d :=
  rfl
#align list.nthd_nil List.getD_nilₓ -- argument order

@[simp]
theorem getD_cons_zero : getD (x :: xs) 0 d = x :=
  rfl
#align list.nthd_cons_zero List.getD_cons_zeroₓ -- argument order

@[simp]
theorem getD_cons_succ : getD (x :: xs) (n + 1) d = getD xs n d :=
  rfl
#align list.nthd_cons_succ List.getD_cons_succₓ -- argument order

theorem getD_eq_get {n : ℕ} (hn : n < l.length) : l.getD n d = l.get ⟨n, hn⟩ := by
  induction' l with hd tl IH generalizing n
  · exact absurd hn (not_lt_of_ge (Nat.zero_le _))
  · cases n
    · exact getD_cons_zero _ _ _
    · exact IH _

set_option linter.deprecated false in
@[deprecated getD_eq_get]
theorem getD_eq_nthLe {n : ℕ} (hn : n < l.length) : l.getD n d = l.nthLe n hn :=
  getD_eq_get ..
#align list.nthd_eq_nth_le List.getD_eq_nthLeₓ -- argument order

theorem getD_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getD n d = d := by
  induction' l with hd tl IH generalizing n
  · exact getD_nil _ _
  · cases n
    · refine' absurd (Nat.zero_lt_succ _) (not_lt_of_ge hn)
    · exact IH (Nat.le_of_succ_le_succ hn)
#align list.nthd_eq_default List.getD_eq_defaultₓ -- argument order

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`. -/
def decidableGetDNilNe {α} (a : α) : DecidablePred fun i : ℕ => getD ([] : List α) i a ≠ a :=
  fun _ => isFalse fun H => H (getD_nil _ _)
#align list.decidable_nthd_nil_ne List.decidableGetDNilNeₓ -- argument order

@[simp]
theorem getD_singleton_default_eq (n : ℕ) : [d].getD n d = d := by cases n <;> simp
#align list.nthd_singleton_default_eq List.getD_singleton_default_eqₓ -- argument order

@[simp]
theorem getD_replicate_default_eq (r n : ℕ) : (replicate r d).getD n d = d := by
  induction' r with r IH generalizing n
  · simp
  · cases n <;> simp [IH]
#align list.nthd_replicate_default_eq List.getD_replicate_default_eqₓ -- argument order

theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').getD n d = l.getD n d := by
  rw [getD_eq_get _ _ h', get_append _ h, getD_eq_get]
#align list.nthd_append List.getD_appendₓ -- argument order

theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  cases' lt_or_le n (l ++l').length with h' h'
  · rw [getD_eq_get (l ++ l') d h', get_append_right, getD_eq_get]
    · rw [length_append] at h'
      exact Nat.sub_lt_left_of_lt_add h h'
    · exact not_lt_of_le h
  · rw [getD_eq_default _ _ h', getD_eq_default]
    rwa [le_tsub_iff_left h, ← length_append]
#align list.nthd_append_right List.getD_append_rightₓ -- argument order

theorem getD_eq_getD_get? (n : ℕ) : l.getD n d = (l.get? n).getD d := by
  cases' lt_or_le n l.length with h h
  · rw [getD_eq_get _ _ h, get?_eq_get h, Option.getD_some]
  · rw [getD_eq_default _ _ h, get?_eq_none.mpr h, Option.getD_none]
#align list.nthd_eq_get_or_else_nth List.getD_eq_getD_get?ₓ -- argument order

end getD

section getI

variable [Inhabited α] (l : List α) (x : α) (xs : List α) (n : ℕ)

@[simp]
theorem getI_nil : getI ([] : List α) n = default :=
  rfl
#align list.inth_nil List.getI_nil

@[simp]
theorem getI_cons_zero : getI (x :: xs) 0 = x :=
  rfl
#align list.inth_cons_zero List.getI_cons_zero

@[simp]
theorem getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n :=
  rfl
#align list.inth_cons_succ List.getI_cons_succ

theorem getI_eq_get {n : ℕ} (hn : n < l.length) : l.getI n = l.get ⟨n, hn⟩ :=
  getD_eq_get ..

@[deprecated getI_eq_get]
theorem getI_eq_nthLe {n : ℕ} (hn : n < l.length) : l.getI n = l.nthLe n hn :=
  getI_eq_get ..
#align list.inth_eq_nth_le List.getI_eq_nthLe

theorem getI_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getI n = default :=
  getD_eq_default _ _ hn
#align list.inth_eq_default List.getI_eq_default

theorem getD_default_eq_getI {n : ℕ} : l.getD n default = l.getI n :=
  rfl
#align list.nthd_default_eq_inth List.getD_default_eq_getIₓ -- new argument `n`

theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').getI n = l.getI n :=
  getD_append _ _ _ _ h h'
#align list.inth_append List.getI_append

theorem getI_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getI n = l'.getI (n - l.length) :=
  getD_append_right _ _ _ _ h
#align list.inth_append_right List.getI_append_right

theorem getI_eq_iget_get? (n : ℕ) : l.getI n = (l.get? n).iget := by
  rw [← getD_default_eq_getI, getD_eq_getD_get?, Option.getD_default_eq_iget]
#align list.inth_eq_iget_nth List.getI_eq_iget_get?

theorem getI_zero_eq_headI : l.getI 0 = l.headI := by cases l <;> rfl
#align list.inth_zero_eq_head List.getI_zero_eq_headI

end getI

end List
