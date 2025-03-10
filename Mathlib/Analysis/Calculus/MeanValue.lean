/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.mean_value
! leanprover-community/mathlib commit 3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Normed
import Mathlib.Data.IsROrC.Basic
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `Convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map. This lemma and its versions are formulated using `IsROrC`,
  so they work both for real and complex derivatives.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `‖f x‖ ≤ B x` from upper estimates on `f'` or `‖f'‖`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `‖f x‖ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `‖f x - f a‖ ≤ C * ‖x - a‖`; several versions deal with
  right derivative and derivative within `[a, b]` (`HasDerivWithinAt` or `derivWithin`).

* `Convex.is_const_of_fderivWithin_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `exists_ratio_hasDerivAt_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_hasDerivAt_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `Convex.image_sub_lt_mul_sub_of_deriv_lt`, `Convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `Convex.image_sub_le_mul_sub_of_deriv_le`, `Convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `Convex.monotoneOn_of_deriv_nonneg`, `Convex.antitoneOn_of_deriv_nonpos`,
  `Convex.strictMono_of_deriv_pos`, `Convex.strictAnti_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/antitone/strictly monotone/strictly monotonically
  decreasing.

* `convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

* `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` : a C^1 function over the reals is
  strictly differentiable. (This is a corollary of the mean value inequality.)
-/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open Metric Set Asymptotics ContinuousLinearMap Filter

open scoped Classical Topology NNReal

/-! ### One-dimensional fencing inequalities -/


/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  change Icc a b ⊆ { x | f x ≤ B x }
  set s := { x | f x ≤ B x } ∩ Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prod hB
  have : IsClosed s := by
    simp only [inter_comm]
    exact A.preimage_closed_of_closed isClosed_Icc OrderClosedTopology.isClosed_le'
  apply this.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxB : f x ≤ B x, xab⟩ y hy
  cases' hxB.lt_or_eq with hxB hxB
  · -- If `f x < B x`, then all we need is continuity of both sides
    refine' nonempty_of_mem (inter_mem _ (Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, hy⟩))
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x :=
      A x (Ico_subset_Icc_self xab) (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hxB)
    have : ∀ᶠ x in 𝓝[>] x, f x < B x := nhdsWithin_le_of_mem (Icc_mem_nhdsWithin_Ioi xab) this
    exact this.mono fun y => le_of_lt
  · rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩
    specialize hf' x xab r hfr
    have HB : ∀ᶠ z in 𝓝[>] x, r < slope B x z :=
      (hasDerivWithinAt_iff_tendsto_slope' <| lt_irrefl x).1 (hB' x xab).Ioi_of_Ici
        (Ioi_mem_nhds hrB)
    obtain ⟨z, hfz, hzB, hz⟩ : ∃ z, slope f x z < r ∧ r < slope B x z ∧ z ∈ Ioc x y
    exact (hf'.and_eventually (HB.and (Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, hy⟩))).exists
    refine' ⟨z, _, hz⟩
    have := (hfz.trans hzB).le
    rwa [slope_def_field, slope_def_field, div_le_div_right (sub_pos.2 hz.1), hxB,
      sub_le_sub_iff_right] at this
#align image_le_of_liminf_slope_right_lt_deriv_boundary' image_le_of_liminf_slope_right_lt_deriv_boundary'

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
#align image_le_of_liminf_slope_right_lt_deriv_boundary image_le_of_liminf_slope_right_lt_deriv_boundary

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    -- `bound` actually says `liminf (f z - f x) / (z - x) ≤ B' x`
    (bound : ∀ x ∈ Ico a b, ∀ r, B' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  have Hr : ∀ x ∈ Icc a b, ∀ r > 0, f x ≤ B x + r * (x - a) := fun x hx r hr => by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zero]
    · exact hB.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro x hx
      exact (hB' x hx).add (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul r)
    · intro x _ _
      rw [mul_one]
      exact (lt_add_iff_pos_right _).2 hr
    exact hx
  intro x hx
  have : ContinuousWithinAt (fun r => B x + r * (x - a)) (Ioi 0) 0 :=
    continuousWithinAt_const.add (continuousWithinAt_id.mul continuousWithinAt_const)
  convert continuousWithinAt_const.closure_le _ this (Hr x hx) using 1 <;> simp
#align image_le_of_liminf_slope_right_le_deriv_boundary image_le_of_liminf_slope_right_le_deriv_boundary

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound
#align image_le_of_deriv_right_lt_deriv_boundary' image_le_of_deriv_right_lt_deriv_boundary'

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
#align image_le_of_deriv_right_lt_deriv_boundary image_le_of_deriv_right_lt_deriv_boundary

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f' x ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' fun x hx _ hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)
#align image_le_of_deriv_right_le_deriv_boundary image_le_of_deriv_right_le_deriv_boundary

/-! ### Vector-valued functions `f : ℝ → E` -/


section

variable {f : ℝ → E} {a b : ℝ}

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(‖f z‖ - ‖f x‖) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. -/
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type _}
    [NormedAddCommGroup E] {f : ℝ → E} {f' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (‖f z‖ - ‖f x‖) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope (norm ∘ f) x z < r)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuousOn hf) hf' ha hB
    hB' bound
#align image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound
#align image_norm_le_of_norm_deriv_right_lt_deriv_boundary' image_norm_le_of_norm_deriv_right_lt_deriv_boundary'

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
#align image_norm_le_of_norm_deriv_right_lt_deriv_boundary image_norm_le_of_norm_deriv_right_lt_deriv_boundary

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuousOn hf) ha hB hB'
    fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le ((bound x hx).trans_lt hr)
#align image_norm_le_of_norm_deriv_right_le_deriv_boundary' image_norm_le_of_norm_deriv_right_le_deriv_boundary'

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
#align image_norm_le_of_norm_deriv_right_le_deriv_boundary image_norm_le_of_norm_deriv_right_le_deriv_boundary

/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `‖f x - f a‖ ≤ C * (x - a)`. -/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : ℝ → E} {C : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  let g x := f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub continuousOn_const
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simpa using (hf' x hx).sub (hasDerivWithinAt_const _ _ _)
  let B x := C * (x - a)
  have hB : ∀ x, HasDerivAt B C x := by
    intro x
    simpa using (hasDerivAt_const x C).mul ((hasDerivAt_id x).sub (hasDerivAt_const x a))
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound
  simp only; rw [sub_self, norm_zero, sub_self, mul_zero]
#align norm_image_sub_le_of_norm_deriv_right_le_segment norm_image_sub_le_of_norm_deriv_right_le_segment

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `HasDerivWithinAt`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine'
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).continuousWithinAt)
      (fun x hx => _) bound
  exact (hf x <| Ico_subset_Icc_self hx).nhdsWithin (Icc_mem_nhdsWithin_Ici hx)
#align norm_image_sub_le_of_norm_deriv_le_segment' norm_image_sub_le_of_norm_deriv_le_segment'

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `derivWithin`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : DifferentiableOn ℝ f (Icc a b))
    (bound : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ C) :
    ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine' norm_image_sub_le_of_norm_deriv_le_segment' _ bound
  exact fun x hx => (hf x hx).hasDerivWithinAt
#align norm_image_sub_le_of_norm_deriv_le_segment norm_image_sub_le_of_norm_deriv_le_segment

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `HasDerivWithinAt`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) 1) x)
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖f' x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)
#align norm_image_sub_le_of_norm_deriv_le_segment_01' norm_image_sub_le_of_norm_deriv_le_segment_01'

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `derivWithin` version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ}
    (hf : DifferentiableOn ℝ f (Icc (0 : ℝ) 1))
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖derivWithin f (Icc (0 : ℝ) 1) x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)
#align norm_image_sub_le_of_norm_deriv_le_segment_01 norm_image_sub_le_of_norm_deriv_le_segment_01

theorem constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt f 0 (Ici x) x) : ∀ x ∈ Icc a b, f x = f a := by
  have : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ 0 * (x - a) := fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv (fun _ _ => norm_zero.le) x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using this
#align constant_of_has_deriv_right_zero constant_of_has_deriv_right_zero

theorem constant_of_derivWithin_zero (hdiff : DifferentiableOn ℝ f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, derivWithin f (Icc a b) x = 0) : ∀ x ∈ Icc a b, f x = f a := by
  have H : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ 0 := by
    simpa only [norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx
#align constant_of_deriv_within_zero constant_of_derivWithin_zero

variable {f' g : ℝ → E}

/-- If two continuous functions on `[a, b]` have the same right derivative and are equal at `a`,
  then they are equal everywhere on `[a, b]`. -/
theorem eq_of_has_deriv_right_eq (derivf : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (derivg : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x) (fcont : ContinuousOn f (Icc a b))
    (gcont : ContinuousOn g (Icc a b)) (hi : f a = g a) : ∀ y ∈ Icc a b, f y = g y := by
  simp only [← @sub_eq_zero _ _ (f _)] at hi⊢
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
    simpa only [sub_self] using (derivf y hy).sub (derivg y hy)
#align eq_of_has_deriv_right_eq eq_of_has_deriv_right_eq

/-- If two differentiable functions on `[a, b]` have the same derivative within `[a, b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`. -/
theorem eq_of_derivWithin_eq (fdiff : DifferentiableOn ℝ f (Icc a b))
    (gdiff : DifferentiableOn ℝ g (Icc a b))
    (hderiv : EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a b)) (hi : f a = g a) :
    ∀ y ∈ Icc a b, f y = g y := by
  have A : ∀ y ∈ Ico a b, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.nhdsWithin (Icc_mem_nhdsWithin_Ici hy)
  have B : ∀ y ∈ Ico a b, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y := fun y hy =>
    (gdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.nhdsWithin (Icc_mem_nhdsWithin_Ici hy)
  exact
    eq_of_has_deriv_right_eq A (fun y hy => (hderiv hy).symm ▸ B y hy) fdiff.continuousOn
      gdiff.continuousOn hi
#align eq_of_deriv_within_eq eq_of_derivWithin_eq

end

/-!
### Vector-valued functions `f : E → G`

Theorems in this section work both for real and complex differentiable functions. We use assumptions
`[IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]` to achieve this result. For the domain `E` we
also assume `[NormedSpace ℝ E]` to have a notion of a `Convex` set. -/

section

variable {𝕜 G : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace Convex

variable {f g : E → G} {C : ℝ} {s : Set E} {x y : E} {f' g' : E → E →L[𝕜] G} {φ : E →L[𝕜] G}

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `HasFDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  letI : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  /- By composition with `AffineMap.lineMap x y`, we reduce to a statement for functions defined
    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
    We just have to check the differentiability of the composition and bounds on its derivative,
    which is straightforward but tedious for lack of automation. -/
  set g := (AffineMap.lineMap x y : ℝ → E)
  have segm : MapsTo g (Icc 0 1 : Set ℝ) s := hs.mapsTo_lineMap xs ys
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t := fun t ht => by
    simpa using ((hf (g t) (segm ht)).restrictScalars ℝ).comp_hasDerivWithinAt _
      AffineMap.hasDerivWithinAt_lineMap segm
  have bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (g t) (y - x)‖ ≤ C * ‖y - x‖ := fun t ht =>
    le_of_op_norm_le _ (bound _ <| segm <| Ico_subset_Icc_self ht) _
  simpa using norm_image_sub_le_of_norm_deriv_le_segment_01' hD bound
#align convex.norm_image_sub_le_of_norm_has_fderiv_within_le Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `HasFDerivWithinAt` and
`LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_hasFDerivWithin_le {C : ℝ≥0}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C)
    (hs : Convex ℝ s) : LipschitzOnWith C f s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in
#align convex.lipschitz_on_with_of_nnnorm_has_fderiv_within_le Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊`, `f` is
`K`-Lipschitz on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt` for a version that claims
existence of `K` instead of an explicit estimate. -/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : Convex ℝ s)
    {f : E → G} (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hcont : ContinuousWithinAt f' s x) (K : ℝ≥0) (hK : ‖f' x‖₊ < K) :
    ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨ε, ε0, hε⟩ : ∃ ε > 0, ball x ε ∩ s ⊆ { y | HasFDerivWithinAt f (f' y) s y ∧ ‖f' y‖₊ < K }
  exact mem_nhdsWithin_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine' ⟨s ∩ ball x ε, inter_mem_nhdsWithin _ (ball_mem_nhds _ ε0), _⟩
  exact
    (hs.inter (convex_ball _ _)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun y hy => (hε hy).1.mono (inter_subset_left _ _)) fun y hy => (hε hy).2.le
#align convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊`, `f` is Lipschitz
on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt` for a version
with an explicit estimate on the Lipschitz constant. -/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex ℝ s) {f : E → G}
    (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <|
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt hder hcont
#align convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderivWithin`. -/
theorem norm_image_sub_le_of_norm_fderivWithin_le (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys
#align convex.norm_image_sub_le_of_norm_fderiv_within_le Convex.norm_image_sub_le_of_norm_fderivWithin_le

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderivWithin` and
`LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_fderivWithin_le {C : ℝ≥0} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
#align convex.lipschitz_on_with_of_nnnorm_fderiv_within_le Convex.lipschitzOnWith_of_nnnorm_fderivWithin_le

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys
#align convex.norm_image_sub_le_of_norm_fderiv_le Convex.norm_image_sub_le_of_norm_fderiv_le

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_fderiv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound
#align convex.lipschitz_on_with_of_nnnorm_fderiv_le Convex.lipschitzOnWith_of_nnnorm_fderiv_le

/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`HasFDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x - φ‖ ≤ C)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ := by
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
    applies, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. Then, we just need to glue
    together the pieces, expressing back `f` in terms of `g`. -/
  let g y := f y - φ y
  have hg : ∀ x ∈ s, HasFDerivWithinAt g (f' x - φ) s x := fun x xs =>
    (hf x xs).sub φ.hasFDerivWithinAt
  calc
    ‖f y - f x - φ (y - x)‖ = ‖f y - f x - (φ y - φ x)‖ := by simp
    _ = ‖f y - φ y - (f x - φ x)‖ := by congr 1; abel
    _ = ‖g y - g x‖ := by simp
    _ ≤ C * ‖y - x‖ := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg bound hs xs ys
#align convex.norm_image_sub_le_of_norm_has_fderiv_within_le' Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'

/-- Variant of the mean value inequality on a convex set. Version with `fderivWithin`. -/
theorem norm_image_sub_le_of_norm_fderivWithin_le' (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys
#align convex.norm_image_sub_le_of_norm_fderiv_within_le' Convex.norm_image_sub_le_of_norm_fderivWithin_le'

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le' (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys
#align convex.norm_image_sub_le_of_norm_fderiv_le' Convex.norm_image_sub_le_of_norm_fderiv_le'

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem is_const_of_fderivWithin_eq_zero (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : ∀ x ∈ s, fderivWithin 𝕜 f s x = 0) (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  have bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ 0 := fun x hx => by
    simp only [hf' x hx, norm_zero, le_rfl]
  simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
    hs.norm_image_sub_le_of_norm_fderivWithin_le hf bound hx hy
#align convex.is_const_of_fderiv_within_eq_zero Convex.is_const_of_fderivWithin_eq_zero

theorem _root_.is_const_of_fderiv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, fderiv 𝕜 f x = 0)
    (x y : E) : f x = f y :=
  convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
    (fun x _ => by rw [fderivWithin_univ]; exact hf' x) trivial trivial
#align is_const_of_fderiv_eq_zero is_const_of_fderiv_eq_zero

/-- If two functions have equal Fréchet derivatives at every point of a convex set, and are equal at
one point in that set, then they are equal on that set. -/
theorem eqOn_of_fderivWithin_eq (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDiffOn 𝕜 s)
    (hf' : ∀ x ∈ s, fderivWithin 𝕜 f s x = fderivWithin 𝕜 g s x) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g := fun y hy => by
  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
  refine' hs.is_const_of_fderivWithin_eq_zero (hf.sub hg) (fun z hz => _) hx hy
  rw [fderivWithin_sub (hs' _ hz) (hf _ hz) (hg _ hz), sub_eq_zero, hf' _ hz]
#align convex.eq_on_of_fderiv_within_eq Convex.eqOn_of_fderivWithin_eq

theorem _root_.eq_of_fderiv_eq (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g)
    (hf' : ∀ x, fderiv 𝕜 f x = fderiv 𝕜 g x) (x : E) (hfgx : f x = g x) : f = g :=
  suffices Set.univ.EqOn f g from funext fun x => this <| mem_univ x
  convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn uniqueDiffOn_univ
    (fun x _ => by simpa using hf' _) (mem_univ _) hfgx
#align eq_of_fderiv_eq eq_of_fderiv_eq

end Convex

namespace Convex

variable {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `HasDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys
#align convex.norm_image_sub_le_of_norm_has_deriv_within_le Convex.norm_image_sub_le_of_norm_hasDerivWithin_le

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `HasDerivWithinAt` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_hasDerivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs
#align convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `derivWithin` -/
theorem norm_image_sub_le_of_norm_derivWithin_le {C : ℝ} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖derivWithin f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
    ys
#align convex.norm_image_sub_le_of_norm_deriv_within_le Convex.norm_image_sub_le_of_norm_derivWithin_le

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `derivWithin` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_derivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : DifferentiableOn 𝕜 f s) (bound : ∀ x ∈ s, ‖derivWithin f s x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound
#align convex.lipschitz_on_with_of_nnnorm_deriv_within_le Convex.lipschitzOnWith_of_nnnorm_derivWithin_le

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
theorem norm_image_sub_le_of_norm_deriv_le {C : ℝ} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound xs ys
#align convex.norm_image_sub_le_of_norm_deriv_le Convex.norm_image_sub_le_of_norm_deriv_le

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound
#align convex.lipschitz_on_with_of_nnnorm_deriv_le Convex.lipschitzOnWith_of_nnnorm_deriv_le

/-- The mean value theorem set in dimension 1: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `deriv` and `LipschitzWith`. -/
theorem _root_.lipschitzWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : Differentiable 𝕜 f)
    (bound : ∀ x, ‖deriv f x‖₊ ≤ C) : LipschitzWith C f :=
  lipschitz_on_univ.1 <|
    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x
#align lipschitz_with_of_nnnorm_deriv_le lipschitzWith_of_nnnorm_deriv_le

/-- If `f : 𝕜 → G`, `𝕜 = R` or `𝕜 = ℂ`, is differentiable everywhere and its derivative equal zero,
then it is a constant function. -/
theorem _root_.is_const_of_deriv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, deriv f x = 0)
    (x y : 𝕜) : f x = f y :=
  is_const_of_fderiv_eq_zero hf (fun z => by ext; simp [← deriv_fderiv, hf']) _ _
#align is_const_of_deriv_eq_zero is_const_of_deriv_eq_zero

end Convex

end

/-! ### Functions `[a, b] → ℝ`. -/

section Interval

-- Declare all variables here to make sure they come in a correct order
variable (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hfd : DifferentiableOn ℝ f (Ioo a b))
  (g g' : ℝ → ℝ) (hgc : ContinuousOn g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
  (hgd : DifferentiableOn ℝ g (Ioo a b))

/-- Cauchy's **Mean Value Theorem**, `HasDerivAt` version. -/
theorem exists_ratio_hasDerivAt_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) :=
    (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  rcases exists_hasDerivAt_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
#align exists_ratio_has_deriv_at_eq_ratio_slope exists_ratio_hasDerivAt_eq_ratio_slope

/-- Cauchy's **Mean Value Theorem**, extended `HasDerivAt` version. -/
theorem exists_ratio_hasDerivAt_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * f' c = (lfb - lfa) * g' c := by
  let h x := (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : Tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert this using 2
    ring
  have hhb : Tendsto h (𝓝[<] b) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[<] b) (𝓝 <| (lgb - lga) * lfb - (lfb - lfa) * lgb) :=
      (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb)
    convert this using 2
    ring
  let h' x := (lgb - lga) * f' x - (lfb - lfa) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := by
    intro x hx
    exact ((hff' x hx).const_mul _).sub ((hgg' x hx).const_mul _)
  rcases exists_hasDerivAt_eq_zero' hab hha hhb hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
#align exists_ratio_has_deriv_at_eq_ratio_slope' exists_ratio_hasDerivAt_eq_ratio_slope'

/-- Lagrange's Mean Value Theorem, `HasDerivAt` version -/
theorem exists_hasDerivAt_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ => hasDerivAt_id x
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc
#align exists_has_deriv_at_eq_slope exists_hasDerivAt_eq_slope

/-- Cauchy's Mean Value Theorem, `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope f (deriv f) hab hfc
    (fun x hx => ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt) g
    (deriv g) hgc fun x hx =>
    ((hgd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt
#align exists_ratio_deriv_eq_ratio_slope exists_ratio_deriv_eq_ratio_slope

/-- Cauchy's Mean Value Theorem, extended `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hdf : DifferentiableOn ℝ f <| Ioo a b) (hdg : DifferentiableOn ℝ g <| Ioo a b)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * deriv f c = (lfb - lfa) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt)
    (fun x hx => ((hdg x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt) hfa hga hfb hgb
#align exists_ratio_deriv_eq_ratio_slope' exists_ratio_deriv_eq_ratio_slope'

/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
theorem exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt
#align exists_deriv_eq_slope exists_deriv_eq_slope

end Interval

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem Convex.mul_sub_lt_image_sub_of_lt_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_gt : ∀ x ∈ interior D, C < deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x < y → C * (y - x) < f y - f x := by
  intro x hx y hy hxy
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
  have : C < (f y - f x) / (y - x) := ha ▸ hf'_gt _ (hxyD' a_mem)
  exact (lt_div_iff (sub_pos.2 hxy)).1 this
#align convex.mul_sub_lt_image_sub_of_lt_deriv Convex.mul_sub_lt_image_sub_of_lt_deriv

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄ (hxy : x < y) : C * (y - x) < f y - f x :=
  convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_gt x) x trivial y trivial hxy
#align mul_sub_lt_image_sub_of_lt_deriv mul_sub_lt_image_sub_of_lt_deriv

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem Convex.mul_sub_le_image_sub_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x ≤ y → C * (y - x) ≤ f y - f x := by
  intro x hx y hy hxy
  cases' eq_or_lt_of_le hxy with hxy' hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
  exact exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD')
  have : C ≤ (f y - f x) / (y - x) := ha ▸ hf'_ge _ (hxyD' a_mem)
  exact (le_div_iff (sub_pos.2 hxy')).1 this
#align convex.mul_sub_le_image_sub_of_le_deriv Convex.mul_sub_le_image_sub_of_le_deriv

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄ (hxy : x ≤ y) : C * (y - x) ≤ f y - f x :=
  convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_ge x) x trivial y trivial hxy
#align mul_sub_le_image_sub_of_le_deriv mul_sub_le_image_sub_of_le_deriv

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem Convex.image_sub_lt_mul_sub_of_deriv_lt {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (lt_hf' : ∀ x ∈ interior D, deriv f x < C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x < y) : f y - f x < C * (y - x) :=
  have hf'_gt : ∀ x ∈ interior D, -C < deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.neg, neg_lt_neg_iff]
    exact lt_hf' x hx
  by linarith [hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x hx y hy hxy]
#align convex.image_sub_lt_mul_sub_of_deriv_lt Convex.image_sub_lt_mul_sub_of_deriv_lt

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄ (hxy : x < y) : f y - f x < C * (y - x) :=
  convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => lt_hf' x) x trivial y trivial hxy
#align image_sub_lt_mul_sub_of_deriv_lt image_sub_lt_mul_sub_of_deriv_lt

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem Convex.image_sub_le_mul_sub_of_deriv_le {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (le_hf' : ∀ x ∈ interior D, deriv f x ≤ C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  have hf'_ge : ∀ x ∈ interior D, -C ≤ deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.neg, neg_le_neg_iff]
    exact le_hf' x hx
  by linarith [hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x hx y hy hxy]
#align convex.image_sub_le_mul_sub_of_deriv_le Convex.image_sub_le_mul_sub_of_deriv_le

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄ (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => le_hf' x) x trivial y trivial hxy
#align image_sub_le_mul_sub_of_deriv_le image_sub_le_mul_sub_of_deriv_le

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotone function on `D`.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem Convex.strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) : StrictMonoOn f D := by
  intro x hx y hy
  have : DifferentiableOn ℝ f (interior D) := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hf' z hz).ne').differentiableWithinAt
  simpa only [zero_mul, sub_pos] using
    hD.mul_sub_lt_image_sub_of_lt_deriv hf this hf' x hx y hy
#align convex.strict_mono_on_of_deriv_pos Convex.strictMonoOn_of_deriv_pos

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem strictMono_of_deriv_pos {f : ℝ → ℝ} (hf' : ∀ x, 0 < deriv f x) : StrictMono f :=
  strictMonoOn_univ.1 <| convex_univ.strictMonoOn_of_deriv_pos (fun z _ =>
    (differentiableAt_of_deriv_ne_zero (hf' z).ne').differentiableWithinAt.continuousWithinAt)
    fun x _ => hf' x
#align strict_mono_of_deriv_pos strictMono_of_deriv_pos

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotone function on `D`. -/
theorem Convex.monotoneOn_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) : MonotoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonneg] using
    hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy
#align convex.monotone_on_of_deriv_nonneg Convex.monotoneOn_of_deriv_nonneg

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function. -/
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) :
    Monotone f :=
  monotoneOn_univ.1 <|
    convex_univ.monotoneOn_of_deriv_nonneg hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x
#align monotone_of_deriv_nonneg monotone_of_deriv_nonneg

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly antitone function on `D`. -/
theorem Convex.strictAntiOn_of_deriv_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, deriv f x < 0) : StrictAntiOn f D :=
  fun x hx y => by
  simpa only [zero_mul, sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz => (differentiableAt_of_deriv_ne_zero (hf' z hz).ne).differentiableWithinAt) hf' x
      hx y
#align convex.strict_anti_on_of_deriv_neg Convex.strictAntiOn_of_deriv_neg

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly antitone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly negative. -/
theorem strictAnti_of_deriv_neg {f : ℝ → ℝ} (hf' : ∀ x, deriv f x < 0) : StrictAnti f :=
  strictAntiOn_univ.1 <|
    convex_univ.strictAntiOn_of_deriv_neg
      (fun z _ =>
        (differentiableAt_of_deriv_ne_zero (hf' z).ne).differentiableWithinAt.continuousWithinAt)
      fun x _ => hf' x
#align strict_anti_of_deriv_neg strictAnti_of_deriv_neg

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is an antitone function on `D`. -/
theorem Convex.antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonpos] using
    hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy
#align convex.antitone_on_of_deriv_nonpos Convex.antitoneOn_of_deriv_nonpos

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is an antitone function. -/
theorem antitone_of_deriv_nonpos {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) :
    Antitone f :=
  antitoneOn_univ.1 <|
    convex_univ.antitoneOn_of_deriv_nonpos hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x
#align antitone_of_deriv_nonpos antitone_of_deriv_nonpos

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem MonotoneOn.convexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_mono : MonotoneOn (deriv f) (interior D)) : ConvexOn ℝ D f :=
  convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
      have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
      have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
      have hyzD' : Ioo y z ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
      -- Then we apply MVT to both `[x, y]` and `[y, z]`
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
      exact exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y)
      exact exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')
      rw [← ha, ← hb]
      exact hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le)
#align monotone_on.convex_on_of_deriv MonotoneOn.convexOn_of_deriv

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antitone on the interior, then `f` is concave on `D`. -/
theorem AntitoneOn.concaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn ℝ D f :=
  haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)
#align antitone_on.concave_on_of_deriv AntitoneOn.concaveOn_of_deriv

theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
  exact exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine' ⟨b, ⟨hxa.trans hab, hby⟩, _⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab
#align strict_mono_on.exists_slope_lt_deriv_aux StrictMonoOn.exists_slope_lt_deriv_aux

theorem StrictMonoOn.exists_slope_lt_deriv {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · push_neg  at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, (f y - f w) / (y - w) < deriv f b := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hwy _ _
      · refine' hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine' ⟨b, ⟨hxw.trans hwb, hby⟩, _⟩
    simp only [div_lt_iff, hxy, hxw, hwy, sub_pos] at ha hb⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith
#align strict_mono_on.exists_slope_lt_deriv StrictMonoOn.exists_slope_lt_deriv

theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
  exact exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine' ⟨b, ⟨hxb, hba.trans hay⟩, _⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba
#align strict_mono_on.exists_deriv_lt_slope_aux StrictMonoOn.exists_deriv_lt_slope_aux

theorem StrictMonoOn.exists_deriv_lt_slope {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · push_neg  at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, deriv f b < (f y - f w) / (y - w) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hwy _ _
      · refine' hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine' ⟨a, ⟨hxa, haw.trans hwy⟩, _⟩
    simp only [lt_div_iff, hxy, hxw, hwy, sub_pos] at ha hb⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith
#align strict_mono_on.exists_deriv_lt_slope StrictMonoOn.exists_deriv_lt_slope

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, and `f'` is strictly monotone on the
interior, then `f` is strictly convex on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMonoOn.strictConvexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : StrictMonoOn (deriv f) (interior D)) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_slope_strict_mono_adjacent hD <| fun {x y z} hx hz hxy hyz => by
    -- First we prove some trivial inclusions
    have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
    have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
    have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
    have hyzD' : Ioo y z ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
    -- Then we get points `a` and `b` in each interval `[x, y]` and `[y, z]` where the derivatives
    -- can be compared to the slopes between `x, y` and `y, z` respectively.
    obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a
    · exact StrictMonoOn.exists_slope_lt_deriv (hf.mono hxyD) hxy (hf'.mono hxyD')
    obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b < (f z - f y) / (z - y)
    · exact StrictMonoOn.exists_deriv_lt_slope (hf.mono hyzD) hyz (hf'.mono hyzD')
    apply ha.trans (lt_trans _ hb)
    exact hf' (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb)
#align strict_mono_on.strict_convex_on_of_deriv StrictMonoOn.strictConvexOn_of_deriv

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f'` is strictly antitone on the
interior, then `f` is strictly concave on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAntiOn.strictConcaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (interior D)) :
    StrictConcaveOn ℝ D f :=
  have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg
#align strict_anti_on.strict_concave_on_of_deriv StrictAntiOn.strictConcaveOn_of_deriv

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem Monotone.convexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_mono : Monotone (deriv f)) : ConvexOn ℝ univ f :=
  (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn
#align monotone.convex_on_univ_of_deriv Monotone.convexOn_univ_of_deriv

/-- If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is concave. -/
theorem Antitone.concaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_anti : Antitone (deriv f)) : ConcaveOn ℝ univ f :=
  (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn
#align antitone.concave_on_univ_of_deriv Antitone.concaveOn_univ_of_deriv

/-- If a function `f` is continuous and `f'` is strictly monotone on `ℝ` then `f` is strictly
convex. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMono.strictConvexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_mono : StrictMono (deriv f)) : StrictConvexOn ℝ univ f :=
  (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn
#align strict_mono.strict_convex_on_univ_of_deriv StrictMono.strictConvexOn_univ_of_deriv

/-- If a function `f` is continuous and `f'` is strictly antitone on `ℝ` then `f` is strictly
concave. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAnti.strictConcaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn ℝ univ f :=
  (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn
#align strict_anti.strict_concave_on_univ_of_deriv StrictAnti.strictConcaveOn_univ_of_deriv

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ (deriv^[2]) f x) : ConvexOn ℝ D f :=
  (hD.interior.monotoneOn_of_deriv_nonneg hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'
#align convex_on_of_deriv2_nonneg convexOn_of_deriv2_nonneg

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonpos : ∀ x ∈ interior D, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ D f :=
  (hD.interior.antitoneOn_of_deriv_nonpos hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'
#align concave_on_of_deriv2_nonpos concaveOn_of_deriv2_nonpos

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on the
interior, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, 0 < ((deriv^[2]) f) x) :
    StrictConvexOn ℝ D f :=
  ((hD.interior.strictMonoOn_of_deriv_pos fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf
#align strict_convex_on_of_deriv2_pos strictConvexOn_of_deriv2_pos

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on the
interior, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, (deriv^[2]) f x < 0) :
    StrictConcaveOn ℝ D f :=
  ((hD.interior.strictAntiOn_of_deriv_neg fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf
#align strict_concave_on_of_deriv2_neg strictConcaveOn_of_deriv2_neg

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ ((deriv^[2]) f) x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)
#align convex_on_of_deriv2_nonneg' convexOn_of_deriv2_nonneg'

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonpos : ∀ x ∈ D, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ D f :=
  concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)
#align concave_on_of_deriv2_nonpos' concaveOn_of_deriv2_nonpos'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on `D`,
then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_of_deriv2_pos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, 0 < ((deriv^[2]) f) x) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)
#align strict_convex_on_of_deriv2_pos' strictConvexOn_of_deriv2_pos'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on `D`,
then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_of_deriv2_neg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, (deriv^[2]) f x < 0) : StrictConcaveOn ℝ D f :=
  strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)
#align strict_concave_on_of_deriv2_neg' strictConcaveOn_of_deriv2_neg'

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convexOn_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ ((deriv^[2]) f) x) :
    ConvexOn ℝ univ f :=
  convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x
#align convex_on_univ_of_deriv2_nonneg convexOn_univ_of_deriv2_nonneg

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concaveOn_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonpos : ∀ x, (deriv^[2]) f x ≤ 0) :
    ConcaveOn ℝ univ f :=
  concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x
#align concave_on_univ_of_deriv2_nonpos concaveOn_univ_of_deriv2_nonpos

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_univ_of_deriv2_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, 0 < ((deriv^[2]) f) x) : StrictConvexOn ℝ univ f :=
  strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x
#align strict_convex_on_univ_of_deriv2_pos strictConvexOn_univ_of_deriv2_pos

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_univ_of_deriv2_neg {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, (deriv^[2]) f x < 0) : StrictConcaveOn ℝ univ f :=
  strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x
#align strict_concave_on_univ_of_deriv2_neg strictConcaveOn_univ_of_deriv2_neg

/-! ### Functions `f : E → ℝ` -/


/-- Lagrange's **Mean Value Theorem**, applied to convex domains. -/
theorem domain_mvt {f : E → ℝ} {s : Set E} {x y : E} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∃ z ∈ segment ℝ x y, f y - f x = f' z (y - x) := by
  -- Use `g = AffineMap.lineMap x y` to parametrize the segment
  set g : ℝ → E := fun t => AffineMap.lineMap x y t
  set I := Icc (0 : ℝ) 1
  have hsub : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self
  have hmaps : MapsTo g I s := hs.mapsTo_lineMap xs ys
  -- The one-variable function `f ∘ g` has derivative `f' (g t) (y - x)` at each `t ∈ I`
  have hfg : ∀ t ∈ I, HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) I t := fun t ht =>
    (hf _ (hmaps ht)).comp_hasDerivWithinAt t AffineMap.hasDerivWithinAt_lineMap hmaps
  -- apply 1-variable mean value theorem to pullback
  have hMVT : ∃ t ∈ Ioo (0 : ℝ) 1, f' (g t) (y - x) = (f (g 1) - f (g 0)) / (1 - 0) := by
    refine' exists_hasDerivAt_eq_slope (f ∘ g) _ (by norm_num) _ _
    · exact fun t Ht => (hfg t Ht).continuousWithinAt
    · exact fun t Ht => (hfg t <| hsub Ht).hasDerivAt (Icc_mem_nhds Ht.1 Ht.2)
  -- reinterpret on domain
  rcases hMVT with ⟨t, Ht, hMVT'⟩
  rw [segment_eq_image_lineMap, bex_image_iff]
  refine ⟨t, hsub Ht, ?_⟩
  simpa using hMVT'.symm
#align domain_mvt domain_mvt

section IsROrC

/-!
### Vector-valued functions `f : E → F`. Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/

variable {𝕜 : Type _} [IsROrC 𝕜] {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {H : Type _}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] {f : G → H} {f' : G → G →L[𝕜] H} {x : G}

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (hder : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictFDerivAt f (f' x) x := by
  -- turn little-o definition of strict_fderiv into an epsilon-delta statement
  refine' isLittleO_iff.mpr fun c hc => Metric.eventually_nhds_iff_ball.mpr _
  -- the correct ε is the modulus of continuity of f'
  rcases Metric.mem_nhds_iff.mp (inter_mem hder (hcont <| ball_mem_nhds _ hc)) with ⟨ε, ε0, hε⟩
  refine' ⟨ε, ε0, _⟩
  -- simplify formulas involving the product E × E
  rintro ⟨a, b⟩ h
  rw [← ball_prod_same, prod_mk_mem_set_prod_eq] at h
  -- exploit the choice of ε as the modulus of continuity of f'
  have hf' : ∀ x' ∈ ball x ε, ‖f' x' - f' x‖ ≤ c := fun x' H' => by
    rw [← dist_eq_norm]
    exact le_of_lt (hε H').2
  -- apply mean value theorem
  letI : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  refine' (convex_ball _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le' _ hf' h.2 h.1
  exact fun y hy => (hε hy).1.hasFDerivWithinAt
#align has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem hasStrictDerivAt_of_hasDerivAt_of_continuousAt {f f' : 𝕜 → G} {x : 𝕜}
    (hder : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictDerivAt f (f' x) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder.mono fun _ hy => hy.hasFDerivAt) <|
    (smulRightL 𝕜 𝕜 G 1).continuous.continuousAt.comp hcont
#align has_strict_deriv_at_of_has_deriv_at_of_continuous_at hasStrictDerivAt_of_hasDerivAt_of_continuousAt

end IsROrC
