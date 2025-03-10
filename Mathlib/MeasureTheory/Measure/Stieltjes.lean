/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.measure.stieltjes
! leanprover-community/mathlib commit 20d5763051978e9bc6428578ed070445df6a18b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Order.LeftRightLim

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`.

## Main definitions

* `StieltjesFunction` is a structure containing a function from `ℝ → ℝ`, together with the
assertions that it is monotone and right-continuous. To `f : StieltjesFunction`, one associates
a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/


section MoveThis

-- Porting note: this section contains lemmas that should be moved to appropriate places after the
-- port to lean 4

open Filter Set Topology

theorem iInf_Ioi_eq_iInf_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : BddBelow (f '' Ioi x))
    (hf_mono : Monotone f) : (⨅ r : Ioi x, f r) = ⨅ q : { q' : ℚ // x < q' }, f q := by
  refine' le_antisymm _ _
  · have : Nonempty { r' : ℚ // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine' le_ciInf fun r => _
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine' ciInf_set_le hf (hxy.trans _)
    exact_mod_cast hyr
  · refine' le_ciInf fun q => _
    have hq := q.prop
    rw [mem_Ioi] at hq
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq
    refine' (ciInf_le _ _).trans _
    · refine' ⟨hf.some, fun z => _⟩
      rintro ⟨u, rfl⟩
      suffices hfu : f u ∈ f '' Ioi x
      exact hf.choose_spec hfu
      exact ⟨u, u.prop, rfl⟩
    · exact ⟨y, hxy⟩
    · refine' hf_mono (le_trans _ hyq.le)
      norm_cast
#align infi_Ioi_eq_infi_rat_gt iInf_Ioi_eq_iInf_rat_gt

-- todo after the port: move to topology/algebra/order/left_right_lim
theorem rightLim_eq_of_tendsto {α β : Type _} [LinearOrder α] [TopologicalSpace β]
    [TopologicalSpace α] [OrderTopology α] [T2Space β] {f : α → β} {a : α} {y : β}
    (h : 𝓝[>] a ≠ ⊥) (h' : Tendsto f (𝓝[>] a) (𝓝 y)) : Function.rightLim f a = y :=
  @leftLim_eq_of_tendsto αᵒᵈ _ _ _ _ _ _ f a y h h'
#align right_lim_eq_of_tendsto rightLim_eq_of_tendsto

-- todo after the port: move to topology/algebra/order/left_right_lim
theorem rightLim_eq_sInf {α β : Type _} [LinearOrder α] [TopologicalSpace β]
    [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} (hf : Monotone f) {x : α}
    [TopologicalSpace α] [OrderTopology α] (h : 𝓝[>] x ≠ ⊥) :
    Function.rightLim f x = sInf (f '' Ioi x) :=
  rightLim_eq_of_tendsto h (hf.tendsto_nhdsWithin_Ioi x)
#align right_lim_eq_Inf rightLim_eq_sInf

-- todo after the port: move to order/filter/at_top_bot
theorem exists_seq_monotone_tendsto_atTop_atTop (α : Type _) [SemilatticeSup α] [Nonempty α]
    [(atTop : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Monotone xs ∧ Tendsto xs atTop atTop := by
  haveI h_ne_bot : (atTop : Filter α).NeBot := atTop_neBot
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  let xs : ℕ → α := fun n => Finset.sup' (Finset.range (n + 1)) Finset.nonempty_range_succ ys
  have h_mono : Monotone xs := by
    intro i j hij
    rw [Finset.sup'_le_iff]
    intro k hk
    refine' Finset.le_sup'_of_le _ _ le_rfl
    rw [Finset.mem_range] at hk⊢
    exact hk.trans_le (add_le_add_right hij _)
  refine' ⟨xs, h_mono, _⟩
  · refine' tendsto_atTop_atTop_of_monotone h_mono _
    have : ∀ a : α, ∃ n : ℕ, a ≤ ys n := by
      rw [tendsto_atTop_atTop] at h
      intro a
      obtain ⟨i, hi⟩ := h a
      exact ⟨i, hi i le_rfl⟩
    intro a
    obtain ⟨i, hi⟩ := this a
    refine' ⟨i, hi.trans _⟩
    refine' Finset.le_sup'_of_le _ _ le_rfl
    rw [Finset.mem_range_succ_iff]
#align exists_seq_monotone_tendsto_at_top_at_top exists_seq_monotone_tendsto_atTop_atTop

theorem exists_seq_antitone_tendsto_atTop_atBot (α : Type _) [SemilatticeInf α] [Nonempty α]
    [h2 : (atBot : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Antitone xs ∧ Tendsto xs atTop atBot :=
  @exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ _ _ h2
#align exists_seq_antitone_tendsto_at_top_at_bot exists_seq_antitone_tendsto_atTop_atBot

-- todo after the port: move to topology/algebra/order/monotone_convergence
theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type _} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : (⨆ i, f i) = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)
#align supr_eq_supr_subseq_of_antitone iSup_eq_iSup_subseq_of_antitone

namespace MeasureTheory

-- todo after the port: move these lemmas to measure_theory/measure/measure_space?
variable {α : Type _} {mα : MeasurableSpace α}

theorem tendsto_measure_Ico_atTop [SemilatticeSup α] [NoMaxOrder α]
    [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ico a x)) atTop (𝓝 (μ (Ici a))) := by
  haveI : Nonempty α := ⟨a⟩
  have h_mono : Monotone fun x => μ (Ico a x) := fun i j hij =>
    measure_mono (Ico_subset_Ico_right hij)
  convert tendsto_atTop_iSup h_mono
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_monotone_tendsto_atTop_atTop α
  have h_Ici : Ici a = ⋃ n, Ico a (xs n) := by
    ext1 x
    simp only [mem_Ici, mem_iUnion, mem_Ico, exists_and_left, iff_self_and]
    intro
    obtain ⟨y, hxy⟩ := NoMaxOrder.exists_gt x
    obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hxs_tendsto y
    exact ⟨n, hxy.trans_le (hn n le_rfl)⟩
  rw [h_Ici, measure_iUnion_eq_iSup, iSup_eq_iSup_subseq_of_monotone h_mono hxs_tendsto]
  exact Monotone.directed_le fun i j hij => Ico_subset_Ico_right (hxs_mono hij)
#align measure_theory.tendsto_measure_Ico_at_top MeasureTheory.tendsto_measure_Ico_atTop

theorem tendsto_measure_Ioc_atBot [SemilatticeInf α] [NoMinOrder α]
    [(atBot : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioc x a)) atBot (𝓝 (μ (Iic a))) := by
  haveI : Nonempty α := ⟨a⟩
  have h_mono : Antitone fun x => μ (Ioc x a) := fun i j hij =>
    measure_mono (Ioc_subset_Ioc_left hij)
  convert tendsto_atBot_iSup h_mono
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_antitone_tendsto_atTop_atBot α
  have h_Iic : Iic a = ⋃ n, Ioc (xs n) a := by
    ext1 x
    simp only [mem_Iic, mem_iUnion, mem_Ioc, exists_and_right, iff_and_self]
    intro
    obtain ⟨y, hxy⟩ := NoMinOrder.exists_lt x
    obtain ⟨n, hn⟩ := tendsto_atTop_atBot.mp hxs_tendsto y
    exact ⟨n, (hn n le_rfl).trans_lt hxy⟩
  rw [h_Iic, measure_iUnion_eq_iSup, iSup_eq_iSup_subseq_of_antitone h_mono hxs_tendsto]
  exact Monotone.directed_le fun i j hij => Ioc_subset_Ioc_left (hxs_mono hij)
#align measure_theory.tendsto_measure_Ioc_at_bot MeasureTheory.tendsto_measure_Ioc_atBot

theorem tendsto_measure_Iic_atTop [SemilatticeSup α] [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Iic x)) atTop (𝓝 (μ univ)) := by
  cases isEmpty_or_nonempty α
  · have h1 : ∀ x : α, Iic x = ∅ := fun x => Subsingleton.elim _ _
    have h2 : (univ : Set α) = ∅ := Subsingleton.elim _ _
    simp_rw [h1, h2]
    exact tendsto_const_nhds
  have h_mono : Monotone fun x => μ (Iic x) := fun i j hij => measure_mono (Iic_subset_Iic.mpr hij)
  convert tendsto_atTop_iSup h_mono
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_monotone_tendsto_atTop_atTop α
  have h_univ : (univ : Set α) = ⋃ n, Iic (xs n) := by
    ext1 x
    simp only [mem_univ, mem_iUnion, mem_Iic, true_iff_iff]
    obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hxs_tendsto x
    exact ⟨n, hn n le_rfl⟩
  rw [h_univ, measure_iUnion_eq_iSup, iSup_eq_iSup_subseq_of_monotone h_mono hxs_tendsto]
  exact Monotone.directed_le fun i j hij => Iic_subset_Iic.mpr (hxs_mono hij)
#align measure_theory.tendsto_measure_Iic_at_top MeasureTheory.tendsto_measure_Iic_atTop

theorem tendsto_measure_Ici_atBot [SemilatticeInf α] [h : (atBot : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Ici x)) atBot (𝓝 (μ univ)) :=
  @tendsto_measure_Iic_atTop αᵒᵈ _ _ h μ
#align measure_theory.tendsto_measure_Ici_at_bot MeasureTheory.tendsto_measure_Ici_atBot

end MeasureTheory

end MoveThis

noncomputable section

open Classical Set Filter Function BigOperators ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)


/-! ### Basic properties of Stieltjes functions -/


/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure StieltjesFunction where
  toFun : ℝ → ℝ
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x
#align stieltjes_function StieltjesFunction
#align stieltjes_function.to_fun StieltjesFunction.toFun
#align stieltjes_function.mono' StieltjesFunction.mono'
#align stieltjes_function.right_continuous' StieltjesFunction.right_continuous'

namespace StieltjesFunction

attribute [coe] toFun

instance instCoeFun : CoeFun StieltjesFunction fun _ => ℝ → ℝ :=
  ⟨toFun⟩
#align stieltjes_function.has_coe_to_fun StieltjesFunction.instCoeFun

initialize_simps_projections StieltjesFunction (toFun → apply)

variable (f : StieltjesFunction)

theorem mono : Monotone f :=
  f.mono'
#align stieltjes_function.mono StieltjesFunction.mono

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x
#align stieltjes_function.right_continuous StieltjesFunction.right_continuous

theorem rightLim_eq (f : StieltjesFunction) (x : ℝ) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x
#align stieltjes_function.right_lim_eq StieltjesFunction.rightLim_eq

theorem iInf_Ioi_eq (f : StieltjesFunction) (x : ℝ) : (⨅ r : Ioi x, f r) = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [rightLim_eq_sInf f.mono, sInf_image']
  rw [← neBot_iff]
  infer_instance
#align stieltjes_function.infi_Ioi_eq StieltjesFunction.iInf_Ioi_eq

theorem iInf_rat_gt_eq (f : StieltjesFunction) (x : ℝ) :
    (⨅ r : { r' : ℚ // x < r' }, f r) = f x := by
  rw [← iInf_Ioi_eq f x]
  refine' (iInf_Ioi_eq_iInf_rat_gt _ _ f.mono).symm
  refine' ⟨f x, fun y => _⟩
  rintro ⟨y, hy_mem, rfl⟩
  exact f.mono (le_of_lt hy_mem)
#align stieltjes_function.infi_rat_gt_eq StieltjesFunction.iInf_rat_gt_eq

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps]
protected def id : StieltjesFunction where
  toFun := id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id
#align stieltjes_function.id StieltjesFunction.id
#align stieltjes_function.id_apply StieltjesFunction.id_apply

@[simp]
theorem id_leftLim (x : ℝ) : leftLim StieltjesFunction.id x = x :=
  tendsto_nhds_unique (StieltjesFunction.id.mono.tendsto_leftLim x) <|
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
#align stieltjes_function.id_left_lim StieltjesFunction.id_leftLim

instance instInhabited : Inhabited StieltjesFunction :=
  ⟨StieltjesFunction.id⟩
#align stieltjes_function.inhabited StieltjesFunction.instInhabited

/-- If a function `f : ℝ → ℝ` is monotone, then the function mapping `x` to the right limit of `f`
at `x` is a Stieltjes function, i.e., it is monotone and right-continuous. -/
noncomputable def _root_.Monotone.stieltjesFunction {f : ℝ → ℝ} (hf : Monotone f) :
    StieltjesFunction where
  toFun := rightLim f
  mono' x y hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    obtain ⟨l, u, hlu, lus⟩ : ∃ l u : ℝ, rightLim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    obtain ⟨y, xy, h'y⟩ : ∃ (y : ℝ), x < y ∧ Ioc x y ⊆ f ⁻¹' Ioo l u :=
      mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.1 (hf.tendsto_rightLim x (Ioo_mem_nhds hlu.1 hlu.2))
    change ∀ᶠ y in 𝓝[≥] x, rightLim f y ∈ s
    filter_upwards [Ico_mem_nhdsWithin_Ici ⟨le_refl x, xy⟩]with z hz
    apply lus
    refine' ⟨hlu.1.trans_le (hf.rightLim hz.1), _⟩
    obtain ⟨a, za, ay⟩ : ∃ a : ℝ, z < a ∧ a < y := exists_between hz.2
    calc
      rightLim f z ≤ f a := hf.rightLim_le za
      _ < u := (h'y ⟨hz.1.trans_lt za, ay.le⟩).2
#align monotone.stieltjes_function Monotone.stieltjesFunction

theorem _root_.Monotone.stieltjesFunction_eq {f : ℝ → ℝ} (hf : Monotone f) (x : ℝ) :
    hf.stieltjesFunction x = rightLim f x :=
  rfl
#align monotone.stieltjes_function_eq Monotone.stieltjesFunction_eq

theorem countable_leftLim_ne (f : StieltjesFunction) : Set.Countable { x | leftLim f x ≠ f x } := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact tendsto_nhds_unique (f.mono.tendsto_leftLim x) (h'x.tendsto.mono_left nhdsWithin_le_nhds)
#align stieltjes_function.countable_left_lim_ne StieltjesFunction.countable_leftLim_ne

/-! ### The outer measure associated to a Stieltjes function -/


/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : Set ℝ) : ℝ≥0∞ :=
  ⨅ (a) (b) (_h : s ⊆ Ioc a b), ofReal (f b - f a)
#align stieltjes_function.length StieltjesFunction.length

@[simp]
theorem length_empty : f.length ∅ = 0 :=
  nonpos_iff_eq_zero.1 <| iInf_le_of_le 0 <| iInf_le_of_le 0 <| by simp
#align stieltjes_function.length_empty StieltjesFunction.length_empty

@[simp]
theorem length_Ioc (a b : ℝ) : f.length (Ioc a b) = ofReal (f b - f a) := by
  refine'
    le_antisymm (iInf_le_of_le a <| iInf₂_le b Subset.rfl)
      (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ENNReal.coe_le_coe.2 _)
  cases' le_or_lt b a with ab ab
  · rw [Real.toNNReal_of_nonpos (sub_nonpos.2 (f.mono ab))]
    apply zero_le
  cases' (Ioc_subset_Ioc_iff ab).1 h with h₁ h₂
  exact Real.toNNReal_le_toNNReal (sub_le_sub (f.mono h₁) (f.mono h₂))
#align stieltjes_function.length_Ioc StieltjesFunction.length_Ioc

theorem length_mono {s₁ s₂ : Set ℝ} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ :=
  iInf_mono fun _ => biInf_mono fun _ => h.trans
#align stieltjes_function.length_mono StieltjesFunction.length_mono

open MeasureTheory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : OuterMeasure ℝ :=
  OuterMeasure.ofFunction f.length f.length_empty
#align stieltjes_function.outer StieltjesFunction.outer

theorem outer_le_length (s : Set ℝ) : f.outer s ≤ f.length s :=
  OuterMeasure.ofFunction_le _
#align stieltjes_function.outer_le_length StieltjesFunction.outer_le_length

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
theorem length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ} (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
    ofReal (f b - f a) ≤ ∑' i, ofReal (f (d i) - f (c i)) := by
  suffices
    ∀ (s : Finset ℕ) (b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Ioo (c i) (d i)) →
      (ofReal (f b - f a) : ℝ≥0∞) ≤ ∑ i in s, ofReal (f (d i) - f (c i)) by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : ℕ) (_ : i ∈ univ) => @isOpen_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with
      ⟨s, _, hf, hs⟩
    have e : (⋃ i ∈ (hf.toFinset : Set ℕ), Ioo (c i) (d i)) = ⋃ i ∈ s, Ioo (c i) (d i) := by
      simp only [ext_iff, exists_prop, Finset.set_biUnion_coe, mem_iUnion, forall_const,
        iff_self_iff, Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine' le_trans _ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e] )
  clear ss b
  refine' fun s => Finset.strongInductionOn s fun s IH b cv => _
  cases' le_total b a with ab ab
  · rw [ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 (f.mono ab))]
    exact zero_le _
  have := cv ⟨ab, le_rfl⟩
  simp only [Finset.mem_coe, gt_iff_lt, not_lt, ge_iff_le, mem_iUnion, mem_Ioo, exists_and_left,
    exists_prop] at this
  rcases this with ⟨i, cb, is, bd⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
  refine' le_trans _ (add_le_add_left (IH _ (Finset.erase_ssubset is) (c i) _) _)
  · refine' le_trans (ENNReal.ofReal_le_ofReal _) ENNReal.ofReal_add_le
    rw [sub_add_sub_cancel]
    exact sub_le_sub_right (f.mono bd.le) _
  · rintro x ⟨h₁, h₂⟩
    refine' (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt And.left (not_lt_of_le h₂))
#align stieltjes_function.length_subadditive_Icc_Ioo StieltjesFunction.length_subadditive_Icc_Ioo

@[simp]
theorem outer_Ioc (a b : ℝ) : f.outer (Ioc a b) = ofReal (f b - f a) := by
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use
    the right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is
    still covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a`
    (up to `ε/2`).
    Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
    very close to  that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
    slightly to the right, then the `f`-length will change very little by right continuity, and we
    will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
    of the `f`-length of `s i`. -/
  refine'
    le_antisymm
      (by
        rw [← f.length_Ioc]
        apply outer_le_length)
      (le_iInf₂ fun s hs => ENNReal.le_of_forall_pos_le_add fun ε εpos h => _)
  let δ := ε / 2
  have δpos : 0 < (δ : ℝ≥0∞) := by simpa using εpos.ne'
  rcases ENNReal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a' := by
    have A : ContinuousWithinAt (fun r => f r - f a) (Ioi a) a := by
      refine' ContinuousWithinAt.sub _ continuousWithinAt_const
      exact (f.right_continuous a).mono Ioi_subset_Ici_self
    have B : f a - f a < δ := by rwa [sub_self, NNReal.coe_pos, ← ENNReal.coe_pos]
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists
  have : ∀ i, ∃ p : ℝ × ℝ, s i ⊆ Ioo p.1 p.2 ∧
      (ofReal (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i) + ε' i := by
    intro i
    have hl :=
      ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
    conv at hl =>
      lhs
      rw [length]
    simp only [iInf_lt_iff, exists_prop] at hl
    rcases hl with ⟨p, q', spq, hq'⟩
    have : ContinuousWithinAt (fun r => ofReal (f r - f p)) (Ioi q') q' := by
      apply ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      refine' ContinuousWithinAt.sub _ continuousWithinAt_const
      exact (f.right_continuous q').mono Ioi_subset_Ici_self
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
    exact ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩
  choose g hg using this
  have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 :=
    calc
      Icc a' b ⊆ Ioc a b := fun x hx => ⟨aa'.trans_le hx.1, hx.2⟩
      _ ⊆ ⋃ i, s i := hs
      _ ⊆ ⋃ i, Ioo (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
  calc
    ofReal (f b - f a) = ofReal (f b - f a' + (f a' - f a)) := by rw [sub_add_sub_cancel]
    _ ≤ ofReal (f b - f a') + ofReal (f a' - f a) := ENNReal.ofReal_add_le
    _ ≤ (∑' i, ofReal (f (g i).2 - f (g i).1)) + ofReal δ :=
      (add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ENNReal.ofReal_le_ofReal ha'.le))
    _ ≤ (∑' i, f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = (∑' i, f.length (s i)) + (∑' i, (ε' i : ℝ≥0∞)) + δ := by rw [ENNReal.tsum_add]
    _ ≤ (∑' i, f.length (s i)) + δ + δ := (add_le_add (add_le_add le_rfl hε.le) le_rfl)
    _ = (∑' i : ℕ, f.length (s i)) + ε := by simp [add_assoc, ENNReal.add_halves]
#align stieltjes_function.outer_Ioc StieltjesFunction.outer_Ioc

theorem measurableSet_Ioi {c : ℝ} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  refine' le_iInf fun a => le_iInf fun b => le_iInf fun h => _
  refine'
    le_trans
      (add_le_add (f.length_mono <| inter_subset_inter_left _ h)
        (f.length_mono <| diff_subset_diff_left h)) _
  cases' le_total a c with hac hac <;> cases' le_total b c with hbc hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, _root_.sup_eq_max, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      _root_.sup_eq_max, ← ENNReal.ofReal_add, f.mono hac, f.mono hbc, sub_nonneg,
      sub_add_sub_cancel, le_refl,
      max_eq_right]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi, f.length_empty,
      zero_add, or_true_iff, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right, _root_.sup_eq_max,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]
#align stieltjes_function.measurable_set_Ioi StieltjesFunction.measurableSet_Ioi

theorem outer_trim : f.outer.trim = f.outer := by
  refine' le_antisymm (fun s => _) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine' le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => _
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  refine' le_trans _ (add_le_add_left (le_of_lt hε) _)
  rw [← ENNReal.tsum_add]
  choose g hg using
    show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s ∧ f.outer s ≤ f.length (t i) + ofReal (ε' i) by
      intro i
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      conv at hl =>
        lhs
        rw [length]
      simp only [iInf_lt_iff] at hl
      rcases hl with ⟨a, b, h₁, h₂⟩
      rw [← f.outer_Ioc] at h₂
      exact ⟨_, h₁, measurableSet_Ioc, le_of_lt <| by simpa using h₂⟩
  simp only [ofReal_coe_nnreal] at hg
  apply iInf_le_of_le (iUnion g) _
  apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
  exact le_trans (f.outer.iUnion _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)
#align stieltjes_function.outer_trim StieltjesFunction.outer_trim

theorem borel_le_measurable : borel ℝ ≤ f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine' MeasurableSpace.generateFrom_le _
  simp (config := { contextual := true }) [f.measurableSet_Ioi]
#align stieltjes_function.borel_le_measurable StieltjesFunction.borel_le_measurable

/-! ### The measure associated to a Stieltjes function -/


/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
protected irreducible_def measure : Measure ℝ :=
  { toOuterMeasure := f.outer
    m_iUnion := fun _s hs =>
      f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ (hs i)
    trimmed := f.outer_trim }
#align stieltjes_function.measure StieltjesFunction.measure

@[simp]
theorem measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = ofReal (f b - f a) := by
  rw [StieltjesFunction.measure]
  exact f.outer_Ioc a b
#align stieltjes_function.measure_Ioc StieltjesFunction.measure_Ioc

@[simp]
theorem measure_singleton (a : ℝ) : f.measure {a} = ofReal (f a - leftLim f a) := by
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n : ℕ, u n < a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto a
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine' Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => _
    simp at hx
    have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
    rw [A]
    refine' tendsto_measure_iInter (fun n => measurableSet_Ioc) (fun m n hmn => _) _
    · exact Ioc_subset_Ioc (u_mono.monotone hmn) le_rfl
    · exact ⟨0, by simpa only [measure_Ioc] using ENNReal.ofReal_ne_top⟩
  have L2 :
      Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (ofReal (f a - leftLim f a))) := by
    simp only [measure_Ioc]
    have : Tendsto (fun n => f (u n)) atTop (𝓝 (leftLim f a)) := by
      apply (f.mono.tendsto_leftLim a).comp
      exact
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ u_lim
          (eventually_of_forall fun n => u_lt_a n)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub this)
  exact tendsto_nhds_unique L1 L2
#align stieltjes_function.measure_singleton StieltjesFunction.measure_singleton

@[simp]
theorem measure_Icc (a b : ℝ) : f.measure (Icc a b) = ofReal (f b - leftLim f a) := by
  rcases le_or_lt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
      f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.le_leftLim hab]
#align stieltjes_function.measure_Icc StieltjesFunction.measure_Icc

@[simp]
theorem measure_Ioo {a b : ℝ} : f.measure (Ioo a b) = ofReal (leftLim f b - f a) := by
  rcases le_or_lt b a with (hab | hab)
  · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
  · have A : Disjoint (Ioo a b) {b} := by simp
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
    have := f.measure_Ioc a b
    simp only [← Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A (measurableSet_singleton b), Icc_self] at this
    rw [D, ENNReal.ofReal_add, add_comm] at this
    · simpa only [ENNReal.add_right_inj ENNReal.ofReal_ne_top]
    · simp only [f.mono.leftLim_le le_rfl, sub_nonneg]
    · simp only [f.mono.le_leftLim hab, sub_nonneg]
#align stieltjes_function.measure_Ioo StieltjesFunction.measure_Ioo

@[simp]
theorem measure_Ico (a b : ℝ) : f.measure (Ico a b) = ofReal (leftLim f b - leftLim f a) := by
  rcases le_or_lt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, hab.ne, f.mono.leftLim_le,
      measure_union A measurableSet_Ioo, f.mono.le_leftLim hab, ← ENNReal.ofReal_add]
#align stieltjes_function.measure_Ico StieltjesFunction.measure_Ico

theorem measure_Iic {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
    f.measure (Iic x) = ofReal (f x - l) := by
  refine' tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) _
  simp_rw [measure_Ioc]
  exact ENNReal.tendsto_ofReal (Tendsto.const_sub _ hf)
#align stieltjes_function.measure_Iic StieltjesFunction.measure_Iic

theorem measure_Ici {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
    f.measure (Ici x) = ofReal (l - leftLim f x) := by
  refine' tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) _
  simp_rw [measure_Ico]
  refine' ENNReal.tendsto_ofReal (Tendsto.sub_const _ _)
  have h_le1 : ∀ x, f (x - 1) ≤ leftLim f x := fun x => Monotone.le_leftLim f.mono (sub_one_lt x)
  have h_le2 : ∀ x, leftLim f x ≤ f x := fun x => Monotone.leftLim_le f.mono le_rfl
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le (hf.comp _) hf h_le1 h_le2
  rw [tendsto_atTop_atTop]
  exact fun y => ⟨y + 1, fun z hyz => by rwa [le_sub_iff_add_le]⟩
#align stieltjes_function.measure_Ici StieltjesFunction.measure_Ici

theorem measure_univ {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    f.measure univ = ofReal (u - l) := by
  refine' tendsto_nhds_unique (tendsto_measure_Iic_atTop _) _
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)
#align stieltjes_function.measure_univ StieltjesFunction.measure_univ

instance instLocallyFiniteMeasure : LocallyFiniteMeasure f.measure :=
  ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), by simp⟩⟩
#align stieltjes_function.measure.measure_theory.is_locally_finite_measure StieltjesFunction.instLocallyFiniteMeasure

end StieltjesFunction
