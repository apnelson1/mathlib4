/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.module
! leanprover-community/mathlib commit 2e59a6de168f95d16b16d217b808a36290398c0a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.Basis
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

 * `LinearIndependent.localization`: `b` is linear independent over a localization of `R`
   if it is linear independent over `R` itself
 * `Basis.localizationLocalization`: promote an `R`-basis `b` of `A` to an `Rₛ`-basis of `Aₛ`,
   where `Rₛ` and `Aₛ` are localizations of `R` and `A` at `s` respectively
 * `LinearIndependent.iff_fractionRing`: `b` is linear independent over `R` iff it is
   linear independent over `Frac(R)`
-/


open BigOperators

open nonZeroDivisors

section Localization

variable {R : Type _} (Rₛ : Type _) [CommRing R] [CommRing Rₛ] [Algebra R Rₛ]

variable (S : Submonoid R) [hT : IsLocalization S Rₛ]

-- include hT

section AddCommMonoid

variable {M : Type _} [AddCommMonoid M] [Module R M] [Module Rₛ M] [IsScalarTower R Rₛ M]

theorem LinearIndependent.localization {ι : Type _} {b : ι → M} (hli : LinearIndependent R b) :
    LinearIndependent Rₛ b := by
  rw [linearIndependent_iff'] at hli⊢
  intro s g hg i hi
  choose! a g' hg' using IsLocalization.exist_integer_multiples S s g
  specialize hli s g' _ i hi
  · rw [← @smul_zero _ M _ _ (a : R), ← hg, Finset.smul_sum]
    refine' Finset.sum_congr rfl fun i hi => _
    rw [← IsScalarTower.algebraMap_smul Rₛ, hg' i hi, smul_assoc]
  refine' (IsLocalization.map_units Rₛ a).mul_right_eq_zero.mp _
  rw [← Algebra.smul_def, ← map_zero (algebraMap R Rₛ), ← hli, hg' i hi]
#align linear_independent.localization LinearIndependent.localization

end AddCommMonoid

section LocalizationLocalization

variable {A : Type _} [CommRing A] [Algebra R A]

variable (Aₛ : Type _) [CommRing Aₛ] [Algebra A Aₛ]

variable [Algebra Rₛ Aₛ] [Algebra R Aₛ] [IsScalarTower R Rₛ Aₛ] [IsScalarTower R A Aₛ]

variable [hA : IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]

--include hA

open Submodule

theorem LinearIndependent.localization_localization {ι : Type _} {v : ι → A}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (algebraMap A Aₛ ∘ v) := by
  rw [linearIndependent_iff'] at hv⊢
  intro s g hg i hi
  choose! a g' hg' using IsLocalization.exist_integer_multiples S s g
  have h0 : algebraMap A Aₛ (∑ i in s, g' i • v i) = 0 := by
    apply_fun (· • ·) (a : R)  at hg
    rw [smul_zero, Finset.smul_sum] at hg
    rw [map_sum, ← hg]
    refine' Finset.sum_congr rfl fun i hi => _
    rw [← smul_assoc, ← hg' i hi, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ←
      Algebra.smul_def, algebraMap_smul, Function.comp_apply]
  obtain ⟨⟨_, r, hrS, rfl⟩, hr : algebraMap R A r * _ = 0⟩ :=
    (IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid A S) _ _).1 h0
  simp_rw [Finset.mul_sum, ← Algebra.smul_def, smul_smul] at hr
  specialize hv s _ hr i hi
  rw [← (IsLocalization.map_units Rₛ a).mul_right_eq_zero, ← Algebra.smul_def, ← hg' i hi]
  exact (IsLocalization.map_eq_zero_iff S _ _).2 ⟨⟨r, hrS⟩, hv⟩
#align linear_independent.localization_localization LinearIndependent.localization_localization

theorem SpanEqTop.localization_localization {v : Set A} (hv : span R v = ⊤) :
    span Rₛ (algebraMap A Aₛ '' v) = ⊤ := by
  rw [eq_top_iff]
  rintro a' -
  obtain ⟨a, ⟨_, s, hs, rfl⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid A S) a'
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm, ← map_one (algebraMap R A)]
  erw [← IsLocalization.algebraMap_mk' A Rₛ Aₛ (1 : R) ⟨s, hs⟩]
  -- `erw` needed to unify `⟨s, hs⟩`
  rw [← Algebra.smul_def]
  refine' smul_mem _ _ (span_subset_span R Rₛ _ _)
  rw [← Algebra.coe_linearMap, ← LinearMap.coe_restrictScalars R, ← LinearMap.map_span]
  exact mem_map_of_mem (hv.symm ▸ mem_top)
#align span_eq_top.localization_localization SpanEqTop.localization_localization

/-- If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localized at `S`.

A suitable instance for `[Algebra A Aₛ]` is `localizationAlgebra`.
-/
noncomputable def Basis.localizationLocalization {ι : Type _} (b : Basis ι R A) : Basis ι Rₛ Aₛ :=
  Basis.mk (b.linearIndependent.localization_localization _ S _)
    (by rw [Set.range_comp, SpanEqTop.localization_localization Rₛ S Aₛ b.span_eq])
#align basis.localization_localization Basis.localizationLocalization

@[simp]
theorem Basis.localizationLocalization_apply {ι : Type _} (b : Basis ι R A) (i) :
    b.localizationLocalization Rₛ S Aₛ i = algebraMap A Aₛ (b i) :=
  Basis.mk_apply _ _ _
#align basis.localization_localization_apply Basis.localizationLocalization_apply

@[simp]
theorem Basis.localizationLocalization_repr_algebraMap {ι : Type _} (b : Basis ι R A) (x i) :
    (b.localizationLocalization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i =
      algebraMap R Rₛ (b.repr x i) :=
  calc
    (b.localizationLocalization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i =
        (b.localizationLocalization Rₛ S Aₛ).repr
          ((b.repr x).sum fun j c => algebraMap R Rₛ c • algebraMap A Aₛ (b j)) i := by
      simp_rw [IsScalarTower.algebraMap_smul, Algebra.smul_def,
        IsScalarTower.algebraMap_apply R A Aₛ, ← _root_.map_mul, ← map_finsupp_sum, ←
        Algebra.smul_def, ← Finsupp.total_apply, Basis.total_repr]
    _ = (b.repr x).sum fun j c => algebraMap R Rₛ c • Finsupp.single j (1 : Rₛ) i := by
      simp_rw [← b.localizationLocalization_apply Rₛ S Aₛ, map_finsupp_sum, LinearEquiv.map_smul,
        Basis.repr_self, Finsupp.sum_apply, Finsupp.smul_apply]
    _ = _ :=
      (Finset.sum_eq_single i (fun j _ hj => by simp [hj]) fun hi => by
        simp [Finsupp.not_mem_support_iff.mp hi])
    _ = algebraMap R Rₛ (b.repr x i) := by simp [Algebra.smul_def]
#align basis.localization_localization_repr_algebra_map Basis.localizationLocalization_repr_algebraMap

end LocalizationLocalization

end Localization

section FractionRing

variable (R K : Type _) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable {V : Type _} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem LinearIndependent.iff_fractionRing {ι : Type _} {b : ι → V} :
    LinearIndependent R b ↔ LinearIndependent K b :=
  ⟨LinearIndependent.localization K R⁰,
    LinearIndependent.restrict_scalars (smul_left_injective R one_ne_zero)⟩
#align linear_independent.iff_fraction_ring LinearIndependent.iff_fractionRing

end FractionRing
