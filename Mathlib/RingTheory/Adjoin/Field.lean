/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module ring_theory.adjoin.field
! leanprover-community/mathlib commit c4658a649d216f57e99621708b09dcb3dcccbd23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Polynomial.Splits
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# Adjoining elements to a field

Some lemmas on the ring generated by adjoining an element to a field.

## Main statements

* `lift_of_splits`: If `K` and `L` are field extensions of `F` and we have `s : Finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `Algebra.adjoin F s` embeds in `L`.

-/


noncomputable section

open BigOperators Polynomial

section Embeddings

variable (F : Type _) [Field F]
-- Porting note: timed out in term mode.
-- Using `apply` appears to be faster than using `refine/exact`.
/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly {R : Type _} [CommRing R] [Algebra F R] (x : R) :
    Algebra.adjoin F ({x} : Set R) ≃ₐ[F] AdjoinRoot (minpoly F x) := by
  refine AlgEquiv.symm ?_
  refine AlgEquiv.ofBijective
      (AlgHom.codRestrict (AdjoinRoot.liftHom _ x <| minpoly.aeval F x) _ fun p => ?_) ⟨?_, ?_⟩
  · induction p using AdjoinRoot.induction_on with
    | ih p => exact (Algebra.adjoin_singleton_eq_range_aeval F x).symm ▸
        (Polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩
  · apply (AlgHom.injective_codRestrict _ _ _).2
    apply (injective_iff_map_eq_zero _).2
    intro p
    induction p using AdjoinRoot.induction_on with
    | ih p =>
      intro hp
      apply Ideal.Quotient.eq_zero_iff_mem.2
      apply Ideal.mem_span_singleton.2
      apply minpoly.dvd F x hp
  · intro y
    let ⟨p, hp⟩ := (SetLike.ext_iff.1 (Algebra.adjoin_singleton_eq_range_aeval F x) (y : R)).1 y.2
    exact ⟨AdjoinRoot.mk _ p, Subtype.eq hp⟩
#align alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly

open Finset

set_option maxHeartbeats 950000 in
set_option synthInstance.maxHeartbeats 140000 in
/-- If `K` and `L` are field extensions of `F` and we have `s : Finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `Algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits {F K L : Type _} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    (s : Finset K) : (∀ x ∈ s, IsIntegral F x ∧ Polynomial.Splits (algebraMap F L) (minpoly F x)) →
      Nonempty (Algebra.adjoin F (↑s : Set K) →ₐ[F] L) := by
  classical
    refine' Finset.induction_on s (fun _ => _) fun a s _ ih H => _
    · rw [coe_empty, Algebra.adjoin_empty]
      exact ⟨(Algebra.ofId F L).comp (Algebra.botEquiv F K)⟩
    rw [forall_mem_insert] at H
    rcases H with ⟨⟨H1, H2⟩, H3⟩
    cases' ih H3 with f
    choose H3 _ using H3
    rw [coe_insert, Set.insert_eq, Set.union_comm, Algebra.adjoin_union_eq_adjoin_adjoin]
    letI := (f : Algebra.adjoin F (↑s : Set K) →+* L).toAlgebra
    haveI : FiniteDimensional F (Algebra.adjoin F (↑s : Set K)) :=
      ((Submodule.fg_iff_finiteDimensional _).1
        (FG_adjoin_of_finite s.finite_toSet H3)).of_subalgebra_toSubmodule
    letI := fieldOfFiniteDimensional F (Algebra.adjoin F (↑s : Set K))
    have H5 : IsIntegral (Algebra.adjoin F (s : Set K)) a := isIntegral_of_isScalarTower H1
    have H6 : (minpoly (Algebra.adjoin F (s : Set K)) a).Splits
        (algebraMap (Algebra.adjoin F (s : Set K)) L) := by
      have : Polynomial.map (algebraMap F (Algebra.adjoin F (s : Set K))) (minpoly F a) ≠ 0 :=
        Polynomial.map_ne_zero <| minpoly.ne_zero H1
      refine' Polynomial.splits_of_splits_of_dvd _ this
        ((Polynomial.splits_map_iff _ _).2 _) (minpoly.dvd _ _ _)
      · rw [← IsScalarTower.algebraMap_eq]
        exact H2
      · rw [Polynomial.aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨y, hy⟩ := Polynomial.exists_root_of_splits _ H6 (ne_of_lt (minpoly.degree_pos H5)).symm
    refine' ⟨Subalgebra.ofRestrictScalars F _ _⟩
    refine' (AdjoinRoot.liftHom (minpoly (Algebra.adjoin F (↑s : Set K)) a) y hy).comp _
    exact (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly
      (Algebra.adjoin F (↑s : Set K)) a).toAlgHom
#align lift_of_splits lift_of_splits

end Embeddings
