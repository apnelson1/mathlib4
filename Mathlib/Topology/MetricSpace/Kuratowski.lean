/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.kuratowski
! leanprover-community/mathlib commit 95d4f6586d313c8c28e00f36621d2a6a66893aa6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Topology.Sets.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℝ)`.
-/


noncomputable section

set_option linter.uppercaseLean3 false

open Set Metric TopologicalSpace

open scoped ENNReal

local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace KuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/


variable {f g : ℓ_infty_ℝ} {n : ℕ} {C : ℝ} [MetricSpace α] (x : ℕ → α) (a b : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `kuratowskiEmbedding`,
without density assumptions. -/
def embeddingOfSubset : ℓ_infty_ℝ :=
  ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply memℓp_infty
    use dist a (x 0)
    rintro - ⟨n, rfl⟩
    exact abs_dist_sub_le _ _ _⟩
#align Kuratowski_embedding.embedding_of_subset KuratowskiEmbedding.embeddingOfSubset

theorem embeddingOfSubset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl
#align Kuratowski_embedding.embedding_of_subset_coe KuratowskiEmbedding.embeddingOfSubset_coe

/-- The embedding map is always a semi-contraction. -/
theorem embeddingOfSubset_dist_le (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b := by
  refine' lp.norm_le_of_forall_le dist_nonneg fun n => _
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe, Real.dist_eq]
  convert abs_dist_sub_le a b (x n) using 2
  ring
#align Kuratowski_embedding.embedding_of_subset_dist_le KuratowskiEmbedding.embeddingOfSubset_dist_le

/-- When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embeddingOfSubset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) := by
  refine' Isometry.of_dist_eq fun a b => _
  refine' (embeddingOfSubset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => _)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm control at index n to conclude
  have C : dist b (x n) - dist a (x n) = embeddingOfSubset x b n - embeddingOfSubset x a n := by
    simp only [embeddingOfSubset_coe, sub_sub_sub_cancel_right]
  have :=
    calc
      dist a b ≤ dist a (x n) + dist (x n) b := dist_triangle _ _ _
      _ = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) := by simp [dist_comm]; ring
      _ ≤ 2 * dist a (x n) + |dist b (x n) - dist a (x n)| := by
        apply_rules [add_le_add_left, le_abs_self]
      _ ≤ 2 * (e / 2) + |embeddingOfSubset x b n - embeddingOfSubset x a n| := by
        rw [C]
        apply_rules [add_le_add, mul_le_mul_of_nonneg_left, hn.le, le_refl]
        norm_num
      _ ≤ 2 * (e / 2) + dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
        have : |embeddingOfSubset x b n - embeddingOfSubset x a n| ≤
            dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
          simp only [dist_eq_norm]
          exact lp.norm_apply_le_norm ENNReal.top_ne_zero
            (embeddingOfSubset x b - embeddingOfSubset x a) n
        nlinarith
      _ = dist (embeddingOfSubset x b) (embeddingOfSubset x a) + e := by ring
  simpa [dist_comm] using this
#align Kuratowski_embedding.embedding_of_subset_isometry KuratowskiEmbedding.embeddingOfSubset_isometry

/-- Every separable metric space embeds isometrically in `ℓ_infty_ℝ`. -/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α] :
    ∃ f : α → ℓ_infty_ℝ, Isometry f := by
  cases' (univ : Set α).eq_empty_or_nonempty with h h
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    haveI : Inhabited α := ⟨basepoint⟩
    have : ∃ s : Set α, s.Countable ∧ Dense s := exists_countable_dense α
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    rcases Set.countable_iff_exists_subset_range.1 S_countable with ⟨x, x_range⟩
    -- Use embeddingOfSubset to construct the desired isometry
    exact ⟨embeddingOfSubset x, embeddingOfSubset_isometry x (S_dense.mono x_range)⟩
#align Kuratowski_embedding.exists_isometric_embedding KuratowskiEmbedding.exists_isometric_embedding

end KuratowskiEmbedding

open TopologicalSpace KuratowskiEmbedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℝ)`. -/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α → ℓ_infty_ℝ :=
  Classical.choose (KuratowskiEmbedding.exists_isometric_embedding α)
#align Kuratowski_embedding kuratowskiEmbedding

/-- The Kuratowski embedding is an isometry. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.choose_spec (exists_isometric_embedding α)
#align Kuratowski_embedding.isometry kuratowskiEmbedding.isometry

/-- Version of the Kuratowski embedding for nonempty compacts -/
nonrec def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α]
    [Nonempty α] : NonemptyCompacts ℓ_infty_ℝ where
  carrier := range (kuratowskiEmbedding α)
  isCompact' := isCompact_range (kuratowskiEmbedding.isometry α).continuous
  nonempty' := range_nonempty _
#align nonempty_compacts.Kuratowski_embedding NonemptyCompacts.kuratowskiEmbedding
