/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.set.n_ary
! leanprover-community/mathlib commit 5e526d18cea33550268dcbbddcb822d5cde40654
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Prod

/-!
# N-ary images of sets

This file defines `Set.image2`, the binary image of finsets. This is the finset version of
`Set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to the n-ary section of `Data.Set.Basic`, to `Order.Filter.NAry` and to
`Data.Option.NAry`. Please keep them in sync.

We do not define `Set.image3` as its only purpose would be to prove properties of `Set.image2`
and `Set.image2` already fulfills this task.
-/


open Function

namespace Set
variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type _} {f f' : α → β → γ} {g g' : α → β → γ → δ}
variable {s s' : Set α} {t t' : Set β} {u u' : Set γ} {v : Set δ} {a a' : α} {b b' : β} {c c' : γ}
  {d d' : δ}

/-- The image of a binary function `f : α → β → γ` as a function `Set α → Set β → Set γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`.-/
def image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ :=
  { c | ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c }
#align set.image2 Set.image2

@[simp]
theorem mem_image2 : c ∈ image2 f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c :=
  Iff.rfl
#align set.mem_image2 Set.mem_image2

theorem mem_image2_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image2 f s t :=
  ⟨a, b, ha, hb, rfl⟩
#align set.mem_image2_of_mem Set.mem_image2_of_mem

theorem mem_image2_iff (hf : Injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  ⟨by
    rintro ⟨a', b', ha', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩
#align set.mem_image2_iff Set.mem_image2_iff

/-- image2 is monotone with respect to `⊆`. -/
theorem image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : image2 f s t ⊆ image2 f s' t' := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)
#align set.image2_subset Set.image2_subset

theorem image2_subset_left (ht : t ⊆ t') : image2 f s t ⊆ image2 f s t' :=
  image2_subset Subset.rfl ht
#align set.image2_subset_left Set.image2_subset_left

theorem image2_subset_right (hs : s ⊆ s') : image2 f s t ⊆ image2 f s' t :=
  image2_subset hs Subset.rfl
#align set.image2_subset_right Set.image2_subset_right

theorem image_subset_image2_left (hb : b ∈ t) : (fun a => f a b) '' s ⊆ image2 f s t :=
  ball_image_of_ball fun _ ha => mem_image2_of_mem ha hb
#align set.image_subset_image2_left Set.image_subset_image2_left

theorem image_subset_image2_right (ha : a ∈ s) : f a '' t ⊆ image2 f s t :=
  ball_image_of_ball fun _ => mem_image2_of_mem ha
#align set.image_subset_image2_right Set.image_subset_image2_right

theorem forall_image2_iff {p : γ → Prop} :
    (∀ z ∈ image2 f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) :=
  ⟨fun h x hx y hy => h _ ⟨x, y, hx, hy, rfl⟩, fun h _ ⟨x, y, hx, hy, hz⟩ => hz ▸ h x hx y hy⟩
#align set.forall_image2_iff Set.forall_image2_iff

@[simp]
theorem image2_subset_iff {u : Set γ} : image2 f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_image2_iff
#align set.image2_subset_iff Set.image2_subset_iff

theorem image2_subset_iff_left : image2 f s t ⊆ u ↔ ∀ a ∈ s, (fun b => f a b) '' t ⊆ u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]
#align set.image2_subset_iff_left Set.image2_subset_iff_left

theorem image2_subset_iff_right : image2 f s t ⊆ u ↔ ∀ b ∈ t, (fun a => f a b) '' s ⊆ u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage, @forall₂_swap α]
#align set.image2_subset_iff_right Set.image2_subset_iff_right

variable (f)

-- Porting note: Removing `simp` - LHS does not simplify
lemma image_prod : (fun x : α × β ↦ f x.1 x.2) '' s ×ˢ t = image2 f s t :=
ext $ fun a ↦
⟨ by rintro ⟨_, _, rfl⟩; exact ⟨_, _, (mem_prod.1 ‹_›).1, (mem_prod.1 ‹_›).2, rfl⟩,
  by rintro ⟨_, _, _, _, rfl⟩; exact ⟨(_, _), ⟨‹_›, ‹_›⟩, rfl⟩⟩
#align set.image_prod Set.image_prod

@[simp] lemma image_uncurry_prod (s : Set α) (t : Set β) : uncurry f '' s ×ˢ t = image2 f s t :=
image_prod _
#align set.image_uncurry_prod Set.image_uncurry_prod

@[simp] lemma image2_mk_eq_prod : image2 Prod.mk s t = s ×ˢ t := ext $ by simp
#align set.image2_mk_eq_prod Set.image2_mk_eq_prod

-- Porting note: Removing `simp` - LHS does not simplify
lemma image2_curry (f : α × β → γ) (s : Set α) (t : Set β) :
  image2 (fun a b ↦ f (a, b)) s t = f '' s ×ˢ t :=
by simp [←image_uncurry_prod, uncurry]
#align set.image2_curry Set.image2_curry

theorem image2_swap (s : Set α) (t : Set β) : image2 f s t = image2 (fun a b => f b a) t s := by
  ext
  constructor <;> rintro ⟨a, b, ha, hb, rfl⟩ <;> exact ⟨b, a, hb, ha, rfl⟩
#align set.image2_swap Set.image2_swap

variable {f}

theorem image2_union_left : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t := by
  ext c
  constructor
  · rintro ⟨a, b, ha | ha, hb, rfl⟩ <;> [left; right] <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
  · rintro (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> refine' ⟨_, _, _, ‹_›, rfl⟩ <;>
      simp [mem_union, *]
#align set.image2_union_left Set.image2_union_left

theorem image2_union_right : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' := by
  rw [← image2_swap, image2_union_left, image2_swap f, image2_swap f]
#align set.image2_union_right Set.image2_union_right

lemma image2_inter_left (hf : Injective2 f) : image2 f (s ∩ s') t = image2 f s t ∩ image2 f s' t :=
by simp_rw [←image_uncurry_prod, inter_prod, image_inter hf.uncurry]
#align set.image2_inter_left Set.image2_inter_left

lemma image2_inter_right (hf : Injective2 f) : image2 f s (t ∩ t') = image2 f s t ∩ image2 f s t' :=
by simp_rw [←image_uncurry_prod, prod_inter, image_inter hf.uncurry]
#align set.image2_inter_right Set.image2_inter_right

@[simp]
theorem image2_empty_left : image2 f ∅ t = ∅ :=
  ext <| by simp
#align set.image2_empty_left Set.image2_empty_left

@[simp]
theorem image2_empty_right : image2 f s ∅ = ∅ :=
  ext <| by simp
#align set.image2_empty_right Set.image2_empty_right

theorem Nonempty.image2 : s.Nonempty → t.Nonempty → (image2 f s t).Nonempty :=
  fun ⟨_, ha⟩ ⟨_, hb⟩ => ⟨_, mem_image2_of_mem ha hb⟩
#align set.nonempty.image2 Set.Nonempty.image2

@[simp]
theorem image2_nonempty_iff : (image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun ⟨_, a, b, ha, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.image2 h.2⟩
#align set.image2_nonempty_iff Set.image2_nonempty_iff

theorem Nonempty.of_image2_left (h : (Set.image2 f s t).Nonempty) : s.Nonempty :=
  (image2_nonempty_iff.1 h).1
#align set.nonempty.of_image2_left Set.Nonempty.of_image2_left

theorem Nonempty.of_image2_right (h : (Set.image2 f s t).Nonempty) : t.Nonempty :=
  (image2_nonempty_iff.1 h).2
#align set.nonempty.of_image2_right Set.Nonempty.of_image2_right

@[simp]
theorem image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  rw [← not_nonempty_iff_eq_empty, image2_nonempty_iff, not_and_or]
  simp [not_nonempty_iff_eq_empty]
#align set.image2_eq_empty_iff Set.image2_eq_empty_iff

theorem image2_inter_subset_left : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t := by
  rintro _ ⟨a, b, ⟨h1a, h2a⟩, hb, rfl⟩
  constructor <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
#align set.image2_inter_subset_left Set.image2_inter_subset_left

theorem image2_inter_subset_right : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' := by
  rintro _ ⟨a, b, ha, ⟨h1b, h2b⟩, rfl⟩
  constructor <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
#align set.image2_inter_subset_right Set.image2_inter_subset_right

@[simp]
theorem image2_singleton_left : image2 f {a} t = f a '' t :=
  ext fun x => by simp
#align set.image2_singleton_left Set.image2_singleton_left

@[simp]
theorem image2_singleton_right : image2 f s {b} = (fun a => f a b) '' s :=
  ext fun x => by simp
#align set.image2_singleton_right Set.image2_singleton_right

theorem image2_singleton : image2 f {a} {b} = {f a b} := by simp
#align set.image2_singleton Set.image2_singleton

@[simp]
theorem image2_insert_left : image2 f (insert a s) t = (fun b => f a b) '' t ∪ image2 f s t := by
  rw [insert_eq, image2_union_left, image2_singleton_left]
#align set.image2_insert_left Set.image2_insert_left

@[simp]
theorem image2_insert_right : image2 f s (insert b t) = (fun a => f a b) '' s ∪ image2 f s t := by
  rw [insert_eq, image2_union_right, image2_singleton_right]
#align set.image2_insert_right Set.image2_insert_right

@[congr]
theorem image2_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : image2 f s t = image2 f' s t := by
  ext
  constructor <;> rintro ⟨a, b, ha, hb, rfl⟩ <;> refine' ⟨a, b, ha, hb, by rw [h a ha b hb]⟩
#align set.image2_congr Set.image2_congr

/-- A common special case of `image2_congr` -/
theorem image2_congr' (h : ∀ a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
  image2_congr fun a _ b _ => h a b
#align set.image2_congr' Set.image2_congr'

/-- The image of a ternary function `f : α → β → γ → δ` as a function
  `Set α → Set β → Set γ → Set δ`. Mathematically this should be thought of as the image of the
  corresponding function `α × β × γ → δ`.
-/
def image3 (g : α → β → γ → δ) (s : Set α) (t : Set β) (u : Set γ) : Set δ :=
  { d | ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d }
#align set.image3 Set.image3

@[simp]
theorem mem_image3 : d ∈ image3 g s t u ↔ ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d :=
  Iff.rfl
#align set.mem_image3 Set.mem_image3

theorem image3_mono (hs : s ⊆ s') (ht : t ⊆ t') (hu : u ⊆ u') :
    image3 g s t u ⊆ image3 g s' t' u' := fun _ =>
  Exists₃.imp fun _ _ _ ⟨ha, hb, hc, hx⟩ => ⟨hs ha, ht hb, hu hc, hx⟩
#align set.image3_mono Set.image3_mono

@[congr]
theorem image3_congr (h : ∀ a ∈ s, ∀ b ∈ t, ∀ c ∈ u, g a b c = g' a b c) :
    image3 g s t u = image3 g' s t u := by
  ext x
  constructor <;> rintro ⟨a, b, c, ha, hb, hc, rfl⟩ <;>
    exact ⟨a, b, c, ha, hb, hc, by rw [h a ha b hb c hc]⟩
#align set.image3_congr Set.image3_congr

/-- A common special case of `image3_congr` -/
theorem image3_congr' (h : ∀ a b c, g a b c = g' a b c) : image3 g s t u = image3 g' s t u :=
  image3_congr fun a _ b _ c _ => h a b c
#align set.image3_congr' Set.image3_congr'

theorem image2_image2_left (f : δ → γ → ε) (g : α → β → δ) :
    image2 f (image2 g s t) u = image3 (fun a b c => f (g a b) c) s t u := by
  ext; constructor
  · rintro ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
    refine' ⟨a, b, c, ha, hb, hc, rfl⟩
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    refine' ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
#align set.image2_image2_left Set.image2_image2_left

theorem image2_image2_right (f : α → δ → ε) (g : β → γ → δ) :
    image2 f s (image2 g t u) = image3 (fun a b c => f a (g b c)) s t u := by
  ext; constructor
  · rintro ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
    refine' ⟨a, b, c, ha, hb, hc, rfl⟩
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    refine' ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
#align set.image2_image2_right Set.image2_image2_right

theorem image_image2 (f : α → β → γ) (g : γ → δ) :
    g '' image2 f s t = image2 (fun a b => g (f a b)) s t := by
  ext; constructor
  · rintro ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
#align set.image_image2 Set.image_image2

theorem image2_image_left (f : γ → β → δ) (g : α → γ) :
    image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t := by
  ext; constructor
  · rintro ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩
#align set.image2_image_left Set.image2_image_left

theorem image2_image_right (f : α → γ → δ) (g : β → γ) :
    image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t := by
  ext; constructor
  · rintro ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩
#align set.image2_image_right Set.image2_image_right

@[simp]
theorem image2_left (h : t.Nonempty) : image2 (fun x _ => x) s t = s := by
  simp [nonempty_def.mp h, ext_iff]
#align set.image2_left Set.image2_left

@[simp]
theorem image2_right (h : s.Nonempty) : image2 (fun _ y => y) s t = t := by
  simp [nonempty_def.mp h, ext_iff]
#align set.image2_right Set.image2_right

theorem image2_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image2 f (image2 g s t) u = image2 f' s (image2 g' t u) := by
  simp only [image2_image2_left, image2_image2_right, h_assoc]
#align set.image2_assoc Set.image2_assoc

theorem image2_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image2 f s t = image2 g t s :=
  (image2_swap _ _ _).trans <| by simp_rw [h_comm]
#align set.image2_comm Set.image2_comm

theorem image2_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    image2 f s (image2 g t u) = image2 g' t (image2 f' s u) := by
  rw [image2_swap f', image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _
#align set.image2_left_comm Set.image2_left_comm

theorem image2_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image2 f (image2 g s t) u = image2 g' (image2 f' s u) t := by
  rw [image2_swap g, image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _
#align set.image2_right_comm Set.image2_right_comm

theorem image2_image2_image2_comm {f : ε → ζ → ν} {g : α → β → ε} {h : γ → δ → ζ} {f' : ε' → ζ' → ν}
    {g' : α → γ → ε'} {h' : β → δ → ζ'}
    (h_comm : ∀ a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) :
    image2 f (image2 g s t) (image2 h u v) = image2 f' (image2 g' s u) (image2 h' t v) := by
  ext; constructor
  · rintro ⟨_, _, ⟨a, b, ha, hb, rfl⟩, ⟨c, d, hc, hd, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨a, c, ha, hc, rfl⟩, ⟨b, d, hb, hd, rfl⟩, (h_comm _ _ _ _).symm⟩
  · rintro ⟨_, _, ⟨a, c, ha, hc, rfl⟩, ⟨b, d, hb, hd, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨a, b, ha, hb, rfl⟩, ⟨c, d, hc, hd, rfl⟩, h_comm _ _ _ _⟩
#align set.image2_image2_image2_comm Set.image2_image2_image2_comm

theorem image_image2_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image2 f s t).image g = image2 f' (s.image g₁) (t.image g₂) := by
  simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]
#align set.image_image2_distrib Set.image_image2_distrib

/-- Symmetric statement to `Set.image2_image_left_comm`. -/
theorem image_image2_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (image2 f s t).image g = image2 f' (s.image g') t :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']
#align set.image_image2_distrib_left Set.image_image2_distrib_left

/-- Symmetric statement to `Set.image_image2_right_comm`. -/
theorem image_image2_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
    (image2 f s t).image g = image2 f' s (t.image g') :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']
#align set.image_image2_distrib_right Set.image_image2_distrib_right

/-- Symmetric statement to `Set.image_image2_distrib_left`. -/
theorem image2_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
    image2 f (s.image g) t = (image2 f' s t).image g' :=
  (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm
#align set.image2_image_left_comm Set.image2_image_left_comm

/-- Symmetric statement to `Set.image_image2_distrib_right`. -/
theorem image_image2_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    image2 f s (t.image g) = (image2 f' s t).image g' :=
  (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm
#align set.image_image2_right_comm Set.image_image2_right_comm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image2_distrib_subset_left {f : α → δ → ε} {g : β → γ → δ} {f₁ : α → β → β'}
    {f₂ : α → γ → γ'} {g' : β' → γ' → ε} (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image2 f s (image2 g t u) ⊆ image2 g' (image2 f₁ s t) (image2 f₂ s u) := by
  rintro _ ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hb) (mem_image2_of_mem ha hc)
#align set.image2_distrib_subset_left Set.image2_distrib_subset_left

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image2_distrib_subset_right {f : δ → γ → ε} {g : α → β → δ} {f₁ : α → γ → α'}
    {f₂ : β → γ → β'} {g' : α' → β' → ε} (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image2 f (image2 g s t) u ⊆ image2 g' (image2 f₁ s u) (image2 f₂ t u) := by
  rintro _ ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hc) (mem_image2_of_mem hb hc)
#align set.image2_distrib_subset_right Set.image2_distrib_subset_right

theorem image_image2_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image2 f s t).image g = image2 f' (t.image g₁) (s.image g₂) := by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _
#align set.image_image2_antidistrib Set.image_image2_antidistrib

/-- Symmetric statement to `Set.image2_image_left_anticomm`. -/
theorem image_image2_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (image2 f s t).image g = image2 f' (t.image g') s :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']
#align set.image_image2_antidistrib_left Set.image_image2_antidistrib_left

/-- Symmetric statement to `Set.image_image2_right_anticomm`. -/
theorem image_image2_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (image2 f s t).image g = image2 f' t (s.image g') :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']
#align set.image_image2_antidistrib_right Set.image_image2_antidistrib_right

/-- Symmetric statement to `Set.image_image2_antidistrib_left`. -/
theorem image2_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    image2 f (s.image g) t = (image2 f' t s).image g' :=
  (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm
#align set.image2_image_left_anticomm Set.image2_image_left_anticomm

/-- Symmetric statement to `Set.image_image2_antidistrib_right`. -/
theorem image_image2_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    image2 f s (t.image g) = (image2 f' t s).image g' :=
  (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm
#align set.image_image2_right_anticomm Set.image_image2_right_anticomm

/-- If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`Set.image2 f`. -/
lemma image2_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (t : Set β) :
    image2 f {a} t = t := by
  rw [image2_singleton_left, show f a = id from funext h, image_id]
#align set.image2_left_identity Set.image2_left_identity

/-- If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity for
`Set.image2 f`. -/
lemma image2_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (s : Set α) :
    image2 f s {b} = s := by
  rw [image2_singleton_right, funext h, image_id']
#align set.image2_right_identity Set.image2_right_identity

theorem image2_inter_union_subset_union :
    image2 f (s ∩ s') (t ∪ t') ⊆ image2 f s t ∪ image2 f s' t' := by
  rw [image2_union_right]
  exact
    union_subset_union (image2_subset_right <| inter_subset_left _ _)
      (image2_subset_right <| inter_subset_right _ _)
#align set.image2_inter_union_subset_union Set.image2_inter_union_subset_union

theorem image2_union_inter_subset_union :
    image2 f (s ∪ s') (t ∩ t') ⊆ image2 f s t ∪ image2 f s' t' := by
  rw [image2_union_left]
  exact
    union_subset_union (image2_subset_left <| inter_subset_left _ _)
      (image2_subset_left <| inter_subset_right _ _)
#align set.image2_union_inter_subset_union Set.image2_union_inter_subset_union

theorem image2_inter_union_subset {f : α → α → β} {s t : Set α} (hf : ∀ a b, f a b = f b a) :
    image2 f (s ∩ t) (s ∪ t) ⊆ image2 f s t := by
  rw [inter_comm]
  exact image2_inter_union_subset_union.trans (union_subset (image2_comm hf).subset Subset.rfl)
#align set.image2_inter_union_subset Set.image2_inter_union_subset

theorem image2_union_inter_subset {f : α → α → β} {s t : Set α} (hf : ∀ a b, f a b = f b a) :
    image2 f (s ∪ t) (s ∩ t) ⊆ image2 f s t := by
  rw [image2_comm hf]
  exact image2_inter_union_subset hf
#align set.image2_union_inter_subset Set.image2_union_inter_subset

end Set
