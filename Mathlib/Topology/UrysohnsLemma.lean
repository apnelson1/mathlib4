/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.urysohns_lemma
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Topology.ContinuousFunction.Basic

/-!
# Urysohn's lemma

In this file we prove Urysohn's lemma `exists_continuous_zero_one_of_closed`: for any two disjoint
closed sets `s` and `t` in a normal topological space `X` there exists a continuous function
`f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.

## Implementation notes

Most paper sources prove Urysohn's lemma using a family of open sets indexed by dyadic rational
numbers on `[0, 1]`. There are many technical difficulties with formalizing this proof (e.g., one
needs to formalize the "dyadic induction", then prove that the resulting family of open sets is
monotone). So, we formalize a slightly different proof.

Let `Urysohns.CU` be the type of pairs `(C, U)` of a closed set `C` and an open set `U` such that
`C ⊆ U`. Since `X` is a normal topological space, for each `c : CU X` there exists an open set `u`
such that `c.C ⊆ u ∧ closure u ⊆ c.U`. We define `c.left` and `c.right` to be `(c.C, u)` and
`(closure u, c.U)`, respectively. Then we define a family of functions
`Urysohns.CU.approx (c : Urysohns.CU X) (n : ℕ) : X → ℝ` by recursion on `n`:

* `c.approx 0` is the indicator of `c.Uᶜ`;
* `c.approx (n + 1) x = (c.left.approx n x + c.right.approx n x) / 2`.

For each `x` this is a monotone family of functions that are equal to zero on `c.C` and are equal to
one outside of `c.U`. We also have `c.approx n x ∈ [0, 1]` for all `c`, `n`, and `x`.

Let `Urysohns.CU.lim c` be the supremum (or equivalently, the limit) of `c.approx n`. Then
properties of `Urysohns.CU.approx` immediately imply that

* `c.lim x ∈ [0, 1]` for all `x`;
* `c.lim` equals zero on `c.C` and equals one outside of `c.U`;
* `c.lim x = (c.left.lim x + c.right.lim x) / 2`.

In order to prove that `c.lim` is continuous at `x`, we prove by induction on `n : ℕ` that for `y`
in a small neighborhood of `x` we have `|c.lim y - c.lim x| ≤ (3 / 4) ^ n`. Induction base follows
from `c.lim x ∈ [0, 1]`, `c.lim y ∈ [0, 1]`. For the induction step, consider two cases:

* `x ∈ c.left.U`; then for `y` in a small neighborhood of `x` we have `y ∈ c.left.U ⊆ c.right.C`
  (hence `c.right.lim x = c.right.lim y = 0`) and `|c.left.lim y - c.left.lim x| ≤ (3 / 4) ^ n`.
  Then
  `|c.lim y - c.lim x| = |c.left.lim y - c.left.lim x| / 2 ≤ (3 / 4) ^ n / 2 < (3 / 4) ^ (n + 1)`.
* otherwise, `x ∉ c.left.right.C`; then for `y` in a small neighborhood of `x` we have
  `y ∉ c.left.right.C ⊇ c.left.left.U` (hence `c.left.left.lim x = c.left.left.lim y = 1`),
  `|c.left.right.lim y - c.left.right.lim x| ≤ (3 / 4) ^ n`, and
  `|c.right.lim y - c.right.lim x| ≤ (3 / 4) ^ n`. Combining these inequalities, the triangle
  inequality, and the recurrence formula for `c.lim`, we get
  `|c.lim x - c.lim y| ≤ (3 / 4) ^ (n + 1)`.

The actual formalization uses `midpoint ℝ x y` instead of `(x + y) / 2` because we have more API
lemmas about `midpoint`.

## Tags

Urysohn's lemma, normal topological space
-/


variable {X : Type _} [TopologicalSpace X]

open Set Filter TopologicalSpace Topology Filter

namespace Urysohns

set_option linter.uppercaseLean3 false

/-- An auxiliary type for the proof of Urysohn's lemma: a pair of a closed set `C` and its
open neighborhood `U`. -/
structure CU (X : Type _) [TopologicalSpace X] where
  protected (C U : Set X)
  protected closed_C : IsClosed C
  protected open_U : IsOpen U
  protected subset : C ⊆ U
#align urysohns.CU Urysohns.CU

instance : Inhabited (CU X) :=
  ⟨⟨∅, univ, isClosed_empty, isOpen_univ, empty_subset _⟩⟩

variable [NormalSpace X]

namespace CU

/-- Due to `normal_exists_closure_subset`, for each `c : CU X` there exists an open set `u`
such chat `c.C ⊆ u` and `closure u ⊆ c.U`. `c.left` is the pair `(c.C, u)`. -/
@[simps C]
def left (c : CU X) : CU X where
  C := c.C
  U := (normal_exists_closure_subset c.closed_C c.open_U c.subset).choose
  closed_C := c.closed_C
  open_U := (normal_exists_closure_subset c.closed_C c.open_U c.subset).choose_spec.1
  subset := (normal_exists_closure_subset c.closed_C c.open_U c.subset).choose_spec.2.1
#align urysohns.CU.left Urysohns.CU.left

/-- Due to `normal_exists_closure_subset`, for each `c : CU X` there exists an open set `u`
such chat `c.C ⊆ u` and `closure u ⊆ c.U`. `c.right` is the pair `(closure u, c.U)`. -/
@[simps U]
def right (c : CU X) : CU X where
  C := closure (normal_exists_closure_subset c.closed_C c.open_U c.subset).choose
  U := c.U
  closed_C := isClosed_closure
  open_U := c.open_U
  subset := (normal_exists_closure_subset c.closed_C c.open_U c.subset).choose_spec.2.2
#align urysohns.CU.right Urysohns.CU.right

theorem left_U_subset_right_C (c : CU X) : c.left.U ⊆ c.right.C :=
  subset_closure
#align urysohns.CU.left_U_subset_right_C Urysohns.CU.left_U_subset_right_C

theorem left_U_subset (c : CU X) : c.left.U ⊆ c.U :=
  Subset.trans c.left_U_subset_right_C c.right.subset
#align urysohns.CU.left_U_subset Urysohns.CU.left_U_subset

theorem subset_right_C (c : CU X) : c.C ⊆ c.right.C :=
  Subset.trans c.left.subset c.left_U_subset_right_C
#align urysohns.CU.subset_right_C Urysohns.CU.subset_right_C

/-- `n`-th approximation to a continuous function `f : X → ℝ` such that `f = 0` on `c.C` and `f = 1`
outside of `c.U`. -/
noncomputable def approx : ℕ → CU X → X → ℝ
  | 0, c, x => indicator (c.Uᶜ) 1 x
  | n + 1, c, x => midpoint ℝ (approx n c.left x) (approx n c.right x)
#align urysohns.CU.approx Urysohns.CU.approx

theorem approx_of_mem_C (c : CU X) (n : ℕ) {x : X} (hx : x ∈ c.C) : c.approx n x = 0 := by
  induction' n with n ihn generalizing c
  · exact indicator_of_not_mem (fun (hU : x ∈ c.Uᶜ) => hU <| c.subset hx) _
  · simp only [approx]
    rw [ihn, ihn, midpoint_self]
    exacts [c.subset_right_C hx, hx]
#align urysohns.CU.approx_of_mem_C Urysohns.CU.approx_of_mem_C

theorem approx_of_nmem_U (c : CU X) (n : ℕ) {x : X} (hx : x ∉ c.U) : c.approx n x = 1 := by
  induction' n with n ihn generalizing c
  · rw [← mem_compl_iff] at hx
    exact indicator_of_mem hx _
  · simp only [approx]
    rw [ihn, ihn, midpoint_self]
    exacts [hx, fun hU => hx <| c.left_U_subset hU]
#align urysohns.CU.approx_of_nmem_U Urysohns.CU.approx_of_nmem_U

theorem approx_nonneg (c : CU X) (n : ℕ) (x : X) : 0 ≤ c.approx n x := by
  induction' n with n ihn generalizing c
  · exact indicator_nonneg (fun _ _ => zero_le_one) _
  · simp only [approx, midpoint_eq_smul_add, invOf_eq_inv]
    refine' mul_nonneg (inv_nonneg.2 zero_le_two) (add_nonneg _ _) <;> apply ihn
#align urysohns.CU.approx_nonneg Urysohns.CU.approx_nonneg

theorem approx_le_one (c : CU X) (n : ℕ) (x : X) : c.approx n x ≤ 1 := by
  induction' n with n ihn generalizing c
  · exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  · simp only [approx, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, ← div_eq_inv_mul]
    have := add_le_add (ihn (left c)) (ihn (right c))
    norm_num at this
    exact Iff.mpr (div_le_one zero_lt_two) this
#align urysohns.CU.approx_le_one Urysohns.CU.approx_le_one

theorem bddAbove_range_approx (c : CU X) (x : X) : BddAbove (range fun n => c.approx n x) :=
  ⟨1, fun _ ⟨n, hn⟩ => hn ▸ c.approx_le_one n x⟩
#align urysohns.CU.bdd_above_range_approx Urysohns.CU.bddAbove_range_approx

theorem approx_le_approx_of_U_sub_C {c₁ c₂ : CU X} (h : c₁.U ⊆ c₂.C) (n₁ n₂ : ℕ) (x : X) :
    c₂.approx n₂ x ≤ c₁.approx n₁ x := by
  by_cases hx : x ∈ c₁.U
  · calc
      approx n₂ c₂ x = 0 := approx_of_mem_C _ _ (h hx)
      _ ≤ approx n₁ c₁ x := approx_nonneg _ _ _
  · calc
      approx n₂ c₂ x ≤ 1 := approx_le_one _ _ _
      _ = approx n₁ c₁ x := (approx_of_nmem_U _ _ hx).symm
#align urysohns.CU.approx_le_approx_of_U_sub_C Urysohns.CU.approx_le_approx_of_U_sub_C

theorem approx_mem_Icc_right_left (c : CU X) (n : ℕ) (x : X) :
    c.approx n x ∈ Icc (c.right.approx n x) (c.left.approx n x) := by
  induction' n with n ihn generalizing c
  · exact ⟨le_rfl, indicator_le_indicator_of_subset (compl_subset_compl.2 c.left_U_subset)
      (fun _ => zero_le_one) _⟩
  · simp only [approx, mem_Icc]
    refine' ⟨midpoint_le_midpoint _ (ihn _).1, midpoint_le_midpoint (ihn _).2 _⟩ <;>
      apply approx_le_approx_of_U_sub_C
    exacts [subset_closure, subset_closure]
#align urysohns.CU.approx_mem_Icc_right_left Urysohns.CU.approx_mem_Icc_right_left

theorem approx_le_succ (c : CU X) (n : ℕ) (x : X) : c.approx n x ≤ c.approx (n + 1) x := by
  induction' n with n ihn generalizing c
  · simp only [approx, right_U, right_le_midpoint]
    exact (approx_mem_Icc_right_left c 0 x).2
  · rw [approx, approx]
    exact midpoint_le_midpoint (ihn _) (ihn _)
#align urysohns.CU.approx_le_succ Urysohns.CU.approx_le_succ

theorem approx_mono (c : CU X) (x : X) : Monotone fun n => c.approx n x :=
  monotone_nat_of_le_succ fun n => c.approx_le_succ n x
#align urysohns.CU.approx_mono Urysohns.CU.approx_mono

/-- A continuous function `f : X → ℝ` such that

* `0 ≤ f x ≤ 1` for all `x`;
* `f` equals zero on `c.C` and equals one outside of `c.U`;
-/
protected noncomputable def lim (c : CU X) (x : X) : ℝ :=
  ⨆ n, c.approx n x
#align urysohns.CU.lim Urysohns.CU.lim

theorem tendsto_approx_atTop (c : CU X) (x : X) :
    Tendsto (fun n => c.approx n x) atTop (𝓝 <| c.lim x) :=
  tendsto_atTop_ciSup (c.approx_mono x) ⟨1, fun _ ⟨_, hn⟩ => hn ▸ c.approx_le_one _ _⟩
#align urysohns.CU.tendsto_approx_at_top Urysohns.CU.tendsto_approx_atTop

theorem lim_of_mem_C (c : CU X) (x : X) (h : x ∈ c.C) : c.lim x = 0 := by
  simp only [CU.lim, approx_of_mem_C, h, ciSup_const]
#align urysohns.CU.lim_of_mem_C Urysohns.CU.lim_of_mem_C

theorem lim_of_nmem_U (c : CU X) (x : X) (h : x ∉ c.U) : c.lim x = 1 := by
  simp only [CU.lim, approx_of_nmem_U c _ h, ciSup_const]
#align urysohns.CU.lim_of_nmem_U Urysohns.CU.lim_of_nmem_U

theorem lim_eq_midpoint (c : CU X) (x : X) :
    c.lim x = midpoint ℝ (c.left.lim x) (c.right.lim x) := by
  refine' tendsto_nhds_unique (c.tendsto_approx_atTop x) ((tendsto_add_atTop_iff_nat 1).1 _)
  simp only [approx]
  exact (c.left.tendsto_approx_atTop x).midpoint (c.right.tendsto_approx_atTop x)
#align urysohns.CU.lim_eq_midpoint Urysohns.CU.lim_eq_midpoint

theorem approx_le_lim (c : CU X) (x : X) (n : ℕ) : c.approx n x ≤ c.lim x :=
  le_ciSup (c.bddAbove_range_approx x) _
#align urysohns.CU.approx_le_lim Urysohns.CU.approx_le_lim

theorem lim_nonneg (c : CU X) (x : X) : 0 ≤ c.lim x :=
  (c.approx_nonneg 0 x).trans (c.approx_le_lim x 0)
#align urysohns.CU.lim_nonneg Urysohns.CU.lim_nonneg

theorem lim_le_one (c : CU X) (x : X) : c.lim x ≤ 1 :=
  ciSup_le fun _ => c.approx_le_one _ _
#align urysohns.CU.lim_le_one Urysohns.CU.lim_le_one

theorem lim_mem_Icc (c : CU X) (x : X) : c.lim x ∈ Icc (0 : ℝ) 1 :=
  ⟨c.lim_nonneg x, c.lim_le_one x⟩
#align urysohns.CU.lim_mem_Icc Urysohns.CU.lim_mem_Icc

/-- Continuity of `Urysohns.CU.lim`. See module docstring for a sketch of the proofs. -/
theorem continuous_lim (c : CU X) : Continuous c.lim := by
  obtain ⟨h0, h1234, h1⟩ : 0 < (2⁻¹ : ℝ) ∧ (2⁻¹ : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 := by norm_num
  refine'
    continuous_iff_continuousAt.2 fun x =>
      (Metric.nhds_basis_closedBall_pow (h0.trans h1234) h1).tendsto_right_iff.2 fun n _ => _
  simp only [Metric.mem_closedBall]
  induction' n with n ihn generalizing c
  · refine' eventually_of_forall fun y => _
    rw [pow_zero]
    exact Real.dist_le_of_mem_Icc_01 (c.lim_mem_Icc _) (c.lim_mem_Icc _)
  · by_cases hxl : x ∈ c.left.U
    · filter_upwards [IsOpen.mem_nhds c.left.open_U hxl, ihn c.left]with _ hyl hyd
      rw [pow_succ, c.lim_eq_midpoint, c.lim_eq_midpoint,
        c.right.lim_of_mem_C _ (c.left_U_subset_right_C hyl),
        c.right.lim_of_mem_C _ (c.left_U_subset_right_C hxl)]
      refine' (dist_midpoint_midpoint_le _ _ _ _).trans _
      rw [dist_self, add_zero, div_eq_inv_mul]
      exact mul_le_mul h1234.le hyd dist_nonneg (h0.trans h1234).le
    · replace hxl : x ∈ c.left.right.Cᶜ
      exact compl_subset_compl.2 c.left.right.subset hxl
      filter_upwards [IsOpen.mem_nhds (isOpen_compl_iff.2 c.left.right.closed_C) hxl,
        ihn c.left.right, ihn c.right]with y hyl hydl hydr
      replace hxl : x ∉ c.left.left.U
      exact compl_subset_compl.2 c.left.left_U_subset_right_C hxl
      replace hyl : y ∉ c.left.left.U
      exact compl_subset_compl.2 c.left.left_U_subset_right_C hyl
      simp only [pow_succ, c.lim_eq_midpoint, c.left.lim_eq_midpoint,
        c.left.left.lim_of_nmem_U _ hxl, c.left.left.lim_of_nmem_U _ hyl]
      refine' (dist_midpoint_midpoint_le _ _ _ _).trans _
      refine' (div_le_div_of_le_of_nonneg (add_le_add_right (dist_midpoint_midpoint_le _ _ _ _) _)
        zero_le_two).trans _
      rw [dist_self, zero_add]
      refine' (div_le_div_of_le_of_nonneg (add_le_add (div_le_div_of_le_of_nonneg hydl zero_le_two)
        hydr) zero_le_two).trans_eq _
      generalize (3 / 4 : ℝ) ^ n = r
      field_simp [two_ne_zero' ℝ]
      ring
#align urysohns.CU.continuous_lim Urysohns.CU.continuous_lim

end CU

end Urysohns

variable [NormalSpace X]

/-- Urysohn's lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
then there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_zero_one_of_closed {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  -- The actual proof is in the code above. Here we just repack it into the expected format.
  set c : Urysohns.CU X := ⟨s, tᶜ, hs, ht.isOpen_compl, disjoint_left.1 hd⟩
  exact ⟨⟨c.lim, c.continuous_lim⟩, c.lim_of_mem_C, fun x hx => c.lim_of_nmem_U _ fun h => h hx,
    c.lim_mem_Icc⟩
#align exists_continuous_zero_one_of_closed exists_continuous_zero_one_of_closed
