/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.to_linear_equiv
! leanprover-community/mathlib commit e42cfdb03b7902f8787a1eb552cb8f77766b45b9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Matrices and linear equivalences

This file gives the map `Matrix.toLinearEquiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

 * `Matrix.toLinearEquiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

 * `Matrix.exists_mulVec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear_equiv, determinant, inverse

-/


namespace Matrix

open LinearMap

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

variable {n : Type _} [Fintype n]

section ToLinearEquiv'

variable [DecidableEq n]

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `Matrix.toLinearEquiv` for the same map on arbitrary modules.
-/
def toLinearEquiv' (P : Matrix n n R) (_ : Invertible P) : (n → R) ≃ₗ[R] n → R :=
  GeneralLinearGroup.generalLinearEquiv _ _ <|
    Matrix.GeneralLinearGroup.toLinear <| unitOfInvertible P
#align matrix.to_linear_equiv' Matrix.toLinearEquiv'

@[simp]
theorem toLinearEquiv'_apply (P : Matrix n n R) (h : Invertible P) :
    (P.toLinearEquiv' h : Module.End R (n → R)) = Matrix.toLin' P :=
  rfl
#align matrix.to_linear_equiv'_apply Matrix.toLinearEquiv'_apply

@[simp]
theorem toLinearEquiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h).symm : Module.End R (n → R)) = Matrix.toLin' (⅟ P) :=
  rfl
#align matrix.to_linear_equiv'_symm_apply Matrix.toLinearEquiv'_symm_apply

end ToLinearEquiv'

section ToLinearEquiv

variable (b : Basis n R M)

/-- Given `hA : IsUnit A.det` and `b : Basis R b`, `A.toLinearEquiv b hA` is
the `LinearEquiv` arising from `toLin b b A`.

See `Matrix.toLinearEquiv'` for this result on `n → R`.
-/
@[simps apply]
noncomputable def toLinearEquiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    M ≃ₗ[R] M := by
  refine'
  { toLin b b A with
    toFun := toLin b b A
    invFun := toLin b b A⁻¹
    left_inv := fun x => _
    right_inv := fun x => _ } <;>
    simp only <;>
    rw [← LinearMap.comp_apply] <;>
    simp only [← Matrix.toLin_mul b b b, Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hA,
      toLin_one, LinearMap.id_apply]
#align matrix.to_linear_equiv Matrix.toLinearEquiv

theorem ker_toLin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.ker (toLin b b A) = ⊥ :=
  ker_eq_bot.mpr (toLinearEquiv b A hA).injective
#align matrix.ker_to_lin_eq_bot Matrix.ker_toLin_eq_bot

theorem range_toLin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.range (toLin b b A) = ⊤ :=
  range_eq_top.mpr (toLinearEquiv b A hA).surjective
#align matrix.range_to_lin_eq_top Matrix.range_toLin_eq_top

end ToLinearEquiv

section Nondegenerate

open Matrix

/-- This holds for all integral domains (see `Matrix.exists_mulVec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
theorem exists_mulVec_eq_zero_iff_aux {K : Type _} [DecidableEq n] [Field K] {M : Matrix n n K} :
    (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 := by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mulVec_eq_zero hv mul_eq
  · contrapose!
    intro h
    have : Function.Injective (Matrix.toLin' M) := by
      simpa only [← LinearMap.ker_eq_bot, ker_toLin'_eq_bot_iff, not_imp_not] using h
    have :
      M ⬝
          LinearMap.toMatrix'
            ((LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) this).symm : (n → K) →ₗ[K] n → K) =
        1 := by
      refine' Matrix.toLin'.injective (LinearMap.ext fun v => _)
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix', LinearMap.comp_apply]
      exact (LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) this).apply_symm_apply v
    exact Matrix.det_ne_zero_of_right_inverse this
#align matrix.exists_mul_vec_eq_zero_iff_aux Matrix.exists_mulVec_eq_zero_iff_aux

theorem exists_mulVec_eq_zero_iff' {A : Type _} (K : Type _) [DecidableEq n] [CommRing A]
    [Nontrivial A] [Field K] [Algebra A K] [IsFractionRing A K] {M : Matrix n n A} :
    (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 := by
  have : (∃ (v : _)(_ : v ≠ 0), mulVec ((algebraMap A K).mapMatrix M) v = 0) ↔ _ :=
    exists_mulVec_eq_zero_iff_aux
  rw [← RingHom.map_det, IsFractionRing.to_map_eq_zero_iff] at this
  refine' Iff.trans _ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine' ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => _) hv, _⟩
    · exact IsFractionRing.to_map_eq_zero_iff.mp (congr_fun h i)
    · ext i
      refine' (RingHom.map_mulVec _ _ _ i).symm.trans _
      rw [mul_eq, Pi.zero_apply, RingHom.map_zero, Pi.zero_apply]
  · letI := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (Finset.univ.image v)
    choose f hf using ba_eq
    refine'
      ⟨fun i => f _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => _) hv, _⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf, Subtype.coe_mk, Pi.zero_apply, RingHom.map_zero, Algebra.smul_def, mul_eq_zero,
        IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine' IsFractionRing.injective A K _
      calc
        algebraMap A K (M.mulVec (fun i : n => f (v i) _) i) =
            ((algebraMap A K).mapMatrix M).mulVec (algebraMap _ K b • v) i := ?_
        _ = 0 := ?_
        _ = algebraMap A K 0 := (RingHom.map_zero _).symm
      · simp_rw [RingHom.map_mulVec, mulVec, dotProduct, Function.comp_apply, hf, Subtype.coe_mk,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mulVec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]
#align matrix.exists_mul_vec_eq_zero_iff' Matrix.exists_mulVec_eq_zero_iff'

theorem exists_mulVec_eq_zero_iff {A : Type _} [DecidableEq n] [CommRing A] [IsDomain A]
    {M : Matrix n n A} : (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 :=
  exists_mulVec_eq_zero_iff' (FractionRing A)
#align matrix.exists_mul_vec_eq_zero_iff Matrix.exists_mulVec_eq_zero_iff

theorem exists_vecMul_eq_zero_iff {A : Type _} [DecidableEq n] [CommRing A] [IsDomain A]
    {M : Matrix n n A} : (∃ (v : _)(_ : v ≠ 0), M.vecMul v = 0) ↔ M.det = 0 := by
  simpa only [← M.det_transpose, ← mulVec_transpose] using exists_mulVec_eq_zero_iff
#align matrix.exists_vec_mul_eq_zero_iff Matrix.exists_vecMul_eq_zero_iff

theorem nondegenerate_iff_det_ne_zero {A : Type _} [DecidableEq n] [CommRing A] [IsDomain A]
    {M : Matrix n n A} : Nondegenerate M ↔ M.det ≠ 0 := by
  refine' Iff.trans _ (not_iff_not.mpr exists_vecMul_eq_zero_iff)
  simp only [not_exists]
  constructor
  · intro hM v hv hMv
    obtain ⟨w, hwMv⟩ := hM.exists_not_ortho_of_ne_zero hv
    simp [dotProduct_mulVec, hMv, zero_dotProduct, ne_eq, not_true] at hwMv
  · intro h v hv
    refine' not_imp_not.mp (h v) (funext fun i => _)
    simpa only [dotProduct_mulVec, dotProduct_single, mul_one] using hv (Pi.single i 1)
#align matrix.nondegenerate_iff_det_ne_zero Matrix.nondegenerate_iff_det_ne_zero

alias nondegenerate_iff_det_ne_zero ↔ Nondegenerate.det_ne_zero Nondegenerate.of_det_ne_zero
#align matrix.nondegenerate.det_ne_zero Matrix.Nondegenerate.det_ne_zero
#align matrix.nondegenerate.of_det_ne_zero Matrix.Nondegenerate.of_det_ne_zero

end Nondegenerate

end Matrix
