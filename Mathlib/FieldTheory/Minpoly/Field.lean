/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin

! This file was ported from Lean 3 source module field_theory.minpoly.field
! leanprover-community/mathlib commit cbdf7b565832144d024caa5a550117c6df0204a5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Polynomial.FieldDivision
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic

/-!
# Minimal polynomials on an algebra over a field

This file specializes the theory of minpoly to the setting of field extensions
and derives some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/


open Classical Polynomial

open Polynomial Set Function minpoly

namespace minpoly

variable {A B : Type _}

variable (A) [Field A]

section Ring

variable [Ring B] [Algebra A B] (x : B)

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `gcd_domain_degree_le_of_ne_zero` which relaxes
the assumptions on `A` in exchange for stronger assumptions on `B`. -/
theorem degree_le_of_ne_zero {p : A[X]} (pnz : p ≠ 0) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) ≤ degree p :=
  calc
    degree (minpoly A x) ≤ degree (p * C (leadingCoeff p)⁻¹) :=
      min A x (monic_mul_leadingCoeff_inv pnz) (by simp [hp])
    _ = degree p := degree_mul_leadingCoeff_inv p pnz
#align minpoly.degree_le_of_ne_zero minpoly.degree_le_of_ne_zero

theorem ne_zero_of_finite_field_extension (e : B) [FiniteDimensional A B] : minpoly A e ≠ 0 :=
  minpoly.ne_zero <| isIntegral_of_noetherian (IsNoetherian.iff_fg.2 inferInstance) _
#align minpoly.ne_zero_of_finite_field_extension minpoly.ne_zero_of_finite_field_extension

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.gcd_unique` which relaxes the
assumptions on `A` in exchange for stronger assumptions on `B`. -/
theorem unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
    (pmin : ∀ q : A[X], q.Monic → Polynomial.aeval x q = 0 → degree p ≤ degree q) :
    p = minpoly A x := by
  have hx : IsIntegral A x := ⟨p, pmonic, hp⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  have hd := degree_le_of_ne_zero A x hnz (by simp [hp])
  contrapose! hd
  apply degree_sub_lt _ (minpoly.ne_zero hx)
  · rw [(monic hx).leadingCoeff, pmonic.leadingCoeff]
  · exact le_antisymm (min A x pmonic hp) (pmin (minpoly A x) (monic hx) (aeval A x))
#align minpoly.unique minpoly.unique

/-- If an element `x` is a root of a polynomial `p`, then the minimal polynomial of `x` divides `p`.
See also `minpoly.gcd_domain_dvd` which relaxes the assumptions on `A` in exchange for stronger
assumptions on `B`. -/
theorem dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A x ∣ p := by
  by_cases hp0 : p = 0
  · simp only [hp0, dvd_zero]
  have hx : IsIntegral A x := by
    rw [← isAlgebraic_iff_isIntegral]
    exact ⟨p, hp0, hp⟩
  rw [← dvd_iff_modByMonic_eq_zero (monic hx)]
  by_contra hnz
  have hd := degree_le_of_ne_zero A x hnz
    ((aeval_modByMonic_eq_self_of_root (monic hx) (aeval _ _)).trans hp)
  contrapose! hd
  exact degree_modByMonic_lt _ (monic hx)
#align minpoly.dvd minpoly.dvd

theorem dvd_map_of_isScalarTower (A K : Type _) {R : Type _} [CommRing A] [Field K] [CommRing R]
    [Algebra A K] [Algebra A R] [Algebra K R] [IsScalarTower A K R] (x : R) :
    minpoly K x ∣ (minpoly A x).map (algebraMap A K) := by
  refine' minpoly.dvd K x _
  rw [aeval_map_algebraMap, minpoly.aeval]
#align minpoly.dvd_map_of_is_scalar_tower minpoly.dvd_map_of_isScalarTower

theorem dvd_map_of_is_scalar_tower' (R : Type _) {S : Type _} (K L : Type _) [CommRing R]
    [CommRing S] [Field K] [CommRing L] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] (s : S) :
    minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (minpoly R s) := by
  apply minpoly.dvd K (algebraMap S L s)
  rw [← map_aeval_eq_aeval_map, minpoly.aeval, map_zero]
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
#align minpoly.dvd_map_of_is_scalar_tower' minpoly.dvd_map_of_is_scalar_tower'

/-- If `y` is a conjugate of `x` over a field `K`, then it is a conjugate over a subring `R`. -/
theorem aeval_of_isScalarTower (R : Type _) {K T U : Type _} [CommRing R] [Field K] [CommRing T]
    [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T] [CommSemiring U] [Algebra K U]
    [Algebra R U] [IsScalarTower R K U] (x : T) (y : U)
    (hy : Polynomial.aeval y (minpoly K x) = 0) : Polynomial.aeval y (minpoly R x) = 0 :=
  aeval_map_algebraMap K y (minpoly R x) ▸
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y
      (minpoly.dvd_map_of_isScalarTower R K x) hy
#align minpoly.aeval_of_is_scalar_tower minpoly.aeval_of_isScalarTower

variable {A x}

theorem eq_of_irreducible_of_monic [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) (hp3 : p.Monic) : p = minpoly A x :=
  let ⟨_, hq⟩ := dvd A x hp2
  eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩) <|
    mul_one (minpoly A x) ▸ hq.symm ▸ Associated.mul_left _
      (associated_one_iff_isUnit.2 <| (hp1.isUnit_or_isUnit hq).resolve_left <| not_isUnit A x)
#align minpoly.eq_of_irreducible_of_monic minpoly.eq_of_irreducible_of_monic

theorem eq_of_irreducible [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ = minpoly A x := by
  have : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp1.ne_zero
  apply eq_of_irreducible_of_monic
  · exact Associated.irreducible ⟨⟨C p.leadingCoeff⁻¹, C p.leadingCoeff,
      by rwa [← C_mul, inv_mul_cancel, C_1], by rwa [← C_mul, mul_inv_cancel, C_1]⟩, rfl⟩ hp1
  · rw [aeval_mul, hp2, MulZeroClass.zero_mul]
  · rwa [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel]
#align minpoly.eq_of_irreducible minpoly.eq_of_irreducible

/-- If `y` is the image of `x` in an extension, their minimal polynomials coincide.

We take `h : y = algebraMap L T x` as an argument because `rw h` typically fails
since `IsIntegral R y` depends on y.
-/
theorem eq_of_algebraMap_eq {K S T : Type _} [Field K] [CommRing S] [CommRing T] [Algebra K S]
    [Algebra K T] [Algebra S T] [IsScalarTower K S T] (hST : Function.Injective (algebraMap S T))
    {x : S} {y : T} (hx : IsIntegral K x) (h : y = algebraMap S T x) : minpoly K x = minpoly K y :=
  minpoly.unique _ _ (minpoly.monic hx)
    (by rw [h, aeval_algebraMap_apply, minpoly.aeval, RingHom.map_zero]) fun q q_monic root_q =>
    minpoly.min _ _ q_monic
      ((aeval_algebraMap_eq_zero_iff_of_injective hST).mp
        (h ▸ root_q : Polynomial.aeval (algebraMap S T x) q = 0))
#align minpoly.eq_of_algebra_map_eq minpoly.eq_of_algebraMap_eq

theorem add_algebraMap {B : Type _} [CommRing B] [Algebra A B] {x : B} (hx : IsIntegral A x)
    (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X - C a) := by
  refine' (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) _ fun q qmo hq => _).symm
  · simp [aeval_comp]
  · have : (Polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq
    have H := minpoly.min A x (qmo.comp_X_add_C _) this
    rw [degree_eq_natDegree qmo.ne_zero,
      degree_eq_natDegree ((minpoly.monic hx).comp_X_sub_C _).ne_zero, natDegree_comp,
      natDegree_X_sub_C, mul_one]
    rwa [degree_eq_natDegree (minpoly.ne_zero hx),
      degree_eq_natDegree (qmo.comp_X_add_C _).ne_zero, natDegree_comp,
      natDegree_X_add_C, mul_one] at H
#align minpoly.add_algebra_map minpoly.add_algebraMap

theorem sub_algebraMap {B : Type _} [CommRing B] [Algebra A B] {x : B} (hx : IsIntegral A x)
    (a : A) : minpoly A (x - algebraMap A B a) = (minpoly A x).comp (X + C a) := by
  simpa [sub_eq_add_neg] using add_algebraMap hx (-a)
#align minpoly.sub_algebra_map minpoly.sub_algebraMap

section AlgHomFintype

/-- A technical finiteness result. -/
noncomputable def Fintype.subtypeProd {E : Type _} {X : Set E} (hX : X.Finite) {L : Type _}
    (F : E → Multiset L) : Fintype (∀ x : X, { l : L // l ∈ F x }) :=
  @Pi.fintype _ _ _ (Finite.fintype hX) _
#align minpoly.fintype.subtype_prod minpoly.Fintype.subtypeProd

variable (F E K : Type _) [Field F] [Ring E] [CommRing K] [IsDomain K] [Algebra F E] [Algebra F K]
  [FiniteDimensional F E]

-- Marked as `noncomputable!` since this definition takes multiple seconds to compile,
-- and isn't very computable in practice (since neither `finrank` nor `finBasis` are).
/-- Function from Hom_K(E,L) to pi type Π (x : basis), roots of min poly of x -/
noncomputable def rootsOfMinPolyPiType (φ : E →ₐ[F] K)
    (x : range (FiniteDimensional.finBasis F E : _ → E)) :
    { l : K // l ∈ (((minpoly F x.1).map (algebraMap F K)).roots : Multiset K) } :=
  ⟨φ x, by
    rw [mem_roots_map (minpoly.ne_zero_of_finite_field_extension F x.val),
      ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]⟩
#align minpoly.roots_of_min_poly_pi_type minpoly.rootsOfMinPolyPiType

theorem aux_inj_roots_of_min_poly : Injective (rootsOfMinPolyPiType F E K) := by
  intro f g h
  suffices (f : E →ₗ[F] K) = g by rwa [FunLike.ext'_iff] at this⊢
  rw [funext_iff] at h
  exact LinearMap.ext_on (FiniteDimensional.finBasis F E).span_eq fun e he =>
    Subtype.ext_iff.mp (h ⟨e, he⟩)
#align minpoly.aux_inj_roots_of_min_poly minpoly.aux_inj_roots_of_min_poly

/-- Given field extensions `E/F` and `K/F`, with `E/F` finite, there are finitely many `F`-algebra
  homomorphisms `E →ₐ[K] K`. -/
noncomputable instance AlgHom.fintype : Fintype (E →ₐ[F] K) :=
  @Fintype.ofInjective _ _
    (Fintype.subtypeProd (finite_range (FiniteDimensional.finBasis F E)) fun e =>
      ((minpoly F e).map (algebraMap F K)).roots)
    _ (aux_inj_roots_of_min_poly F E K)
#align minpoly.alg_hom.fintype minpoly.AlgHom.fintype

end AlgHomFintype

variable (B) [Nontrivial B]

/-- If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebraMap K B x` is `X - C x`. -/
theorem eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = X - C a :=
  eq_X_sub_C_of_algebraMap_inj a (algebraMap A B).injective
set_option linter.uppercaseLean3 false in
#align minpoly.eq_X_sub_C minpoly.eq_X_sub_C

theorem eq_X_sub_C' (a : A) : minpoly A a = X - C a :=
  eq_X_sub_C A a
set_option linter.uppercaseLean3 false in
#align minpoly.eq_X_sub_C' minpoly.eq_X_sub_C'

variable (A)

/-- The minimal polynomial of `0` is `X`. -/
@[simp]
theorem zero : minpoly A (0 : B) = X := by
  simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, RingHom.map_zero] using eq_X_sub_C B (0 : A)
#align minpoly.zero minpoly.zero

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp]
theorem one : minpoly A (1 : B) = X - 1 := by
  simpa only [RingHom.map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1 : A)
#align minpoly.one minpoly.one

end Ring

section IsDomain

variable [Ring B] [IsDomain B] [Algebra A B]

variable {A} {x : B}

/-- A minimal polynomial is prime. -/
theorem prime (hx : IsIntegral A x) : Prime (minpoly A x) := by
  refine' ⟨minpoly.ne_zero hx, not_isUnit A x, _⟩
  rintro p q ⟨d, h⟩
  have : Polynomial.aeval x (p * q) = 0 := by simp [h, aeval A x]
  replace : Polynomial.aeval x p = 0 ∨ Polynomial.aeval x q = 0 := by simpa
  exact Or.imp (dvd A x) (dvd A x) this
#align minpoly.prime minpoly.prime

/-- If `L/K` is a field extension and an element `y` of `K` is a root of the minimal polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding. -/
theorem root {x : B} (hx : IsIntegral A x) {y : A} (h : IsRoot (minpoly A x) y) :
    algebraMap A B y = x := by
  have key : minpoly A x = X - C y := eq_of_monic_of_associated (monic hx) (monic_X_sub_C y)
    (associated_of_dvd_dvd ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_isRoot.2 h))
      (dvd_iff_isRoot.2 h))
  have := aeval A x
  rwa [key, AlgHom.map_sub, aeval_X, aeval_C, sub_eq_zero, eq_comm] at this
#align minpoly.root minpoly.root

/-- The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp]
theorem coeff_zero_eq_zero (hx : IsIntegral A x) : coeff (minpoly A x) 0 = 0 ↔ x = 0 := by
  constructor
  · intro h
    have zero_root := zero_isRoot_of_coeff_zero_eq_zero h
    rw [← root hx zero_root]
    exact RingHom.map_zero _
  · rintro rfl
    simp
#align minpoly.coeff_zero_eq_zero minpoly.coeff_zero_eq_zero

/-- The minimal polynomial of a nonzero element has nonzero constant coefficient. -/
theorem coeff_zero_ne_zero (hx : IsIntegral A x) (h : x ≠ 0) : coeff (minpoly A x) 0 ≠ 0 := by
  contrapose! h
  simpa only [hx, coeff_zero_eq_zero] using h
#align minpoly.coeff_zero_ne_zero minpoly.coeff_zero_ne_zero

end IsDomain

end minpoly
