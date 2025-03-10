/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller

! This file was ported from Lean 3 source module linear_algebra.dual
! leanprover-community/mathlib commit b1c017582e9f18d8494e5c18602a8cb4a6f843ac
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.RingTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.

## Main definitions

* Duals and transposes:
  * `Module.Dual R M` defines the dual space of the `R`-module `M`, as `M →ₗ[R] R`.
  * `Module.dualPairing R M` is the canonical pairing between `Dual R M` and `M`.
  * `Module.Dual.eval R M : M →ₗ[R] Dual R (Dual R)` is the canonical map to the double dual.
  * `Module.Dual.transpose` is the linear map from `M →ₗ[R] M'` to `Dual R M' →ₗ[R] Dual R M`.
  * `LinearMap.dualMap` is `Module.Dual.transpose` of a given linear map, for dot notation.
  * `LinearEquiv.dualMap` is for the dual of an equivalence.
* Bases:
  * `Basis.toDual` produces the map `M →ₗ[R] Dual R M` associated to a basis for an `R`-module `M`.
  * `Basis.toDual_equiv` is the equivalence `M ≃ₗ[R] Dual R M` associated to a finite basis.
  * `Basis.dualBasis` is a basis for `Dual R M` given a finite basis for `M`.
  * `Module.dual_bases e ε` is the proposition that the families `e` of vectors and `ε` of dual
    vectors have the characteristic properties of a basis and a dual.
* Submodules:
  * `Submodule.dualRestrict W` is the transpose `Dual R M →ₗ[R] Dual R W` of the inclusion map.
  * `Submodule.dualAnnihilator W` is the kernel of `W.dualRestrict`. That is, it is the submodule
    of `dual R M` whose elements all annihilate `W`.
  * `Submodule.dualRestrict_comap W'` is the dual annihilator of `W' : Submodule R (Dual R M)`,
    pulled back along `Module.Dual.eval R M`.
  * `Submodule.dualCopairing W` is the canonical pairing between `W.dualAnnihilator` and `M ⧸ W`.
    It is nondegenerate for vector spaces (`subspace.dualCopairing_nondegenerate`).
  * `Submodule.dualPairing W` is the canonical pairing between `Dual R M ⧸ W.dualAnnihilator`
    and `W`. It is nondegenerate for vector spaces (`Subspace.dualPairing_nondegenerate`).
* Vector spaces:
  * `Subspace.dualLift W` is an arbitrary section (using choice) of `Submodule.dualRestrict W`.

## Main results

* Bases:
  * `Module.dualBasis.basis` and `Module.dualBasis.coe_basis`: if `e` and `ε` form a dual pair,
    then `e` is a basis.
  * `Module.dualBasis.coe_dualBasis`: if `e` and `ε` form a dual pair,
    then `ε` is a basis.
* Annihilators:
  * `Module.dualAnnihilator_gc R M` is the antitone Galois correspondence between
    `Submodule.dualAnnihilator` and `Submodule.dualConnihilator`.
  * `LinearMap.ker_dual_map_eq_dualAnnihilator_range` says that
    `f.dual_map.ker = f.range.dualAnnihilator`
  * `LinearMap.range_dual_map_eq_dualAnnihilator_ker_of_subtype_range_surjective` says that
    `f.dual_map.range = f.ker.dualAnnihilator`; this is specialized to vector spaces in
    `LinearMap.range_dual_map_eq_dualAnnihilator_ker`.
  * `Submodule.dual_quot_equiv_dualAnnihilator` is the equivalence
    `Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator`
* Vector spaces:
  * `Subspace.dualAnnihilator_dualConnihilator_eq` says that the double dual annihilator,
    pulled back ground `Module.Dual.eval`, is the original submodule.
  * `Subspace.dualAnnihilator_gci` says that `module.dualAnnihilator_gc R M` is an
    antitone Galois coinsertion.
  * `Subspace.quotAnnihilatorEquiv` is the equivalence
    `Dual K V ⧸ W.dualAnnihilator ≃ₗ[K] Dual K W`.
  * `LinearMap.dualPairing_nondegenerate` says that `Module.dualPairing` is nondegenerate.
  * `Subspace.is_compl_dualAnnihilator` says that the dual annihilator carries complementary
    subspaces to complementary subspaces.
* Finite-dimensional vector spaces:
  * `Module.evalEquiv` is the equivalence `V ≃ₗ[K] Dual K (Dual K V)`
  * `Module.mapEvalEquiv` is the order isomorphism between subspaces of `V` and
    subspaces of `Dual K (Dual K V)`.
  * `Subspace.quotDualEquivAnnihilator W` is the equivalence
    `(Dual K V ⧸ W.dualLift.range) ≃ₗ[K] W.dualAnnihilator`, where `W.dualLift.range` is a copy
    of `Dual K W` inside `Dual K V`.
  * `Subspace.quotEquivAnnihilator W` is the equivalence `(V ⧸ W) ≃ₗ[K] W.dualAnnihilator`
  * `Subspace.dualQuotDistrib W` is an equivalence
    `Dual K (V₁ ⧸ W) ≃ₗ[K] Dual K V₁ ⧸ W.dualLift.range` from an arbitrary choice of
    splitting of `V₁`.

## TODO

Erdős-Kaplansky theorem about the dimension of a dual vector space in case of infinite dimension.
-/


noncomputable section

namespace Module

-- Porting note: max u v universe issues so name and specific below
universe u v v' v'' w u₁ u₂

variable (R : Type u) (M : Type v)

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
@[reducible]
def Dual :=
  M →ₗ[R] R
#align module.dual Module.Dual

/-- The canonical pairing of a vector space and its algebraic dual. -/
def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id
#align module.dual_pairing Module.dualPairing

@[simp]
theorem dualPairing_apply (v x) : dualPairing R M v x = v x :=
  rfl
#align module.dual_pairing_apply Module.dualPairing_apply

namespace Dual

instance : Inhabited (Dual R M) := ⟨0⟩

instance : FunLike (Dual R M) M fun _ => R :=
  inferInstanceAs (FunLike (M →ₗ[R] R) M fun _ => R)

/-- Maps a module M to the dual of the dual of M. See `Module.erange_coe` and
`Module.evalEquiv`. -/
def eval : M →ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id
#align module.dual.eval Module.Dual.eval

@[simp]
theorem eval_apply (v : M) (a : Dual R M) : eval R M v a = a v :=
  rfl
#align module.dual.eval_apply Module.Dual.eval_apply

variable {R M} {M' : Type v'}
variable [AddCommMonoid M'] [Module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`Dual R M' →ₗ[R] Dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip
#align module.dual.transpose Module.Dual.transpose

-- Porting note: with reducible def need to specify some parameters to transpose explicitly
theorem transpose_apply (u : M →ₗ[R] M') (l : Dual R M') : transpose (R := R) u l = l.comp u :=
  rfl
#align module.dual.transpose_apply Module.Dual.transpose_apply

variable {M'' : Type v''} [AddCommMonoid M''] [Module R M'']

-- Porting note: with reducible def need to specify some parameters to transpose explicitly
theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
    transpose (R := R) (u.comp v) = (transpose (R := R) v).comp (transpose (R := R) u) :=
  rfl
#align module.dual.transpose_comp Module.Dual.transpose_comp

end Dual

section Prod

variable (M' : Type v') [AddCommMonoid M'] [Module R M']

/-- Taking duals distributes over products. -/
@[simps!]
def dualProdDualEquivDual : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M') :=
  LinearMap.coprodEquiv R
#align module.dual_prod_dual_equiv_dual Module.dualProdDualEquivDual

@[simp]
theorem dualProdDualEquivDual_apply (φ : Module.Dual R M) (ψ : Module.Dual R M') :
    dualProdDualEquivDual R M M' (φ, ψ) = φ.coprod ψ :=
  rfl
#align module.dual_prod_dual_equiv_dual_apply Module.dualProdDualEquivDual_apply

end Prod

end Module

section DualMap

open Module

variable {R : Type u} [CommSemiring R] {M₁ : Type v} {M₂ : Type v'}

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dualMap` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : Dual R M₂ →ₗ[R] Dual R M₁ :=
-- Porting note: with reducible def need to specify some parameters to transpose explicitly
  Module.Dual.transpose (R := R) f
#align linear_map.dual_map LinearMap.dualMap

-- Porting note: with reducible def need to specify some parameters to transpose explicitly
theorem LinearMap.dualMap_def (f : M₁ →ₗ[R] M₂) : f.dualMap = Module.Dual.transpose (R := R) f :=
  rfl
#align linear_map.dual_map_def LinearMap.dualMap_def

theorem LinearMap.dualMap_apply' (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) : f.dualMap g = g.comp f :=
  rfl
#align linear_map.dual_map_apply' LinearMap.dualMap_apply'

@[simp]
theorem LinearMap.dualMap_apply (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl
#align linear_map.dual_map_apply LinearMap.dualMap_apply

@[simp]
theorem LinearMap.dualMap_id : (LinearMap.id : M₁ →ₗ[R] M₁).dualMap = LinearMap.id := by
  ext
  rfl
#align linear_map.dual_map_id LinearMap.dualMap_id

theorem LinearMap.dualMap_comp_dualMap {M₃ : Type _} [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f).dualMap :=
  rfl
#align linear_map.dual_map_comp_dual_map LinearMap.dualMap_comp_dualMap

/-- If a linear map is surjective, then its dual is injective. -/
theorem LinearMap.dualMap_injective_of_surjective {f : M₁ →ₗ[R] M₂} (hf : Function.Surjective f) :
    Function.Injective f.dualMap := by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congr_arg (fun g : Module.Dual R M₁ => g y) h
#align linear_map.dual_map_injective_of_surjective LinearMap.dualMap_injective_of_surjective

/-- The `Linear_equiv` version of `LinearMap.dualMap`. -/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ :=
  { f.toLinearMap.dualMap with
    invFun := f.symm.toLinearMap.dualMap
    left_inv := by
      intro φ; ext x
      simp only [LinearMap.dualMap_apply, LinearEquiv.coe_toLinearMap, LinearMap.toFun_eq_coe,
        LinearEquiv.apply_symm_apply]
    right_inv := by
      intro φ; ext x
      simp only [LinearMap.dualMap_apply, LinearEquiv.coe_toLinearMap, LinearMap.toFun_eq_coe,
        LinearEquiv.symm_apply_apply] }
#align linear_equiv.dual_map LinearEquiv.dualMap

@[simp]
theorem LinearEquiv.dualMap_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl
#align linear_equiv.dual_map_apply LinearEquiv.dualMap_apply

@[simp]
theorem LinearEquiv.dualMap_refl :
    (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (Dual R M₁) := by
  ext
  rfl
#align linear_equiv.dual_map_refl LinearEquiv.dualMap_refl

@[simp]
theorem LinearEquiv.dualMap_symm {f : M₁ ≃ₗ[R] M₂} :
    (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl
#align linear_equiv.dual_map_symm LinearEquiv.dualMap_symm

theorem LinearEquiv.dualMap_trans {M₃ : Type _} [AddCommGroup M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂)
    (g : M₂ ≃ₗ[R] M₃) : g.dualMap.trans f.dualMap = (f.trans g).dualMap :=
  rfl
#align linear_equiv.dual_map_trans LinearEquiv.dualMap_trans

end DualMap

namespace Basis

universe u v w

open Module Module.Dual Submodule LinearMap Cardinal Function

open BigOperators

variable {R : Type u} {M : Type v} {K : Type u₁} {V : Type u₂} {ι : Type w}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]

variable (b : Basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def toDual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ fun v => b.constr ℕ fun w => if w = v then (1 : R) else 0
#align basis.to_dual Basis.toDual

theorem toDual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 := by
  erw [constr_basis b, constr_basis b]
  simp only [eq_comm]
#align basis.to_dual_apply Basis.toDual_apply

@[simp]
theorem toDual_total_left (f : ι →₀ R) (i : ι) :
    b.toDual (Finsupp.total ι M R b f) (b i) = f i := by
  rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum, LinearMap.sum_apply]
  simp_rw [LinearMap.map_smul, LinearMap.smul_apply, toDual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.not_mem_support_iff.mp h]
#align basis.to_dual_total_left Basis.toDual_total_left

@[simp]
theorem toDual_total_right (f : ι →₀ R) (i : ι) :
    b.toDual (b i) (Finsupp.total ι M R b f) = f i := by
  rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum]
  simp_rw [LinearMap.map_smul, toDual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finsupp.not_mem_support_iff.mp h]
#align basis.to_dual_total_right Basis.toDual_total_right

theorem toDual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i := by
  rw [← b.toDual_total_left, b.total_repr]
#align basis.to_dual_apply_left Basis.toDual_apply_left

theorem toDual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i := by
  rw [← b.toDual_total_right, b.total_repr]
#align basis.to_dual_apply_right Basis.toDual_apply_right

theorem coe_toDual_self (i : ι) : b.toDual (b i) = b.coord i := by
  ext
  apply toDual_apply_right
#align basis.coe_to_dual_self Basis.coe_toDual_self

/-- `h.toDual_flip v` is the linear map sending `w` to `h.toDual w v`. -/
def toDualFlip (m : M) : M →ₗ[R] R :=
  b.toDual.flip m
#align basis.to_dual_flip Basis.toDualFlip

theorem toDualFlip_apply (m₁ m₂ : M) : b.toDualFlip m₁ m₂ = b.toDual m₂ m₁ :=
  rfl
#align basis.to_dual_flip_apply Basis.toDualFlip_apply

theorem toDual_eq_repr (m : M) (i : ι) : b.toDual m (b i) = b.repr m i :=
  b.toDual_apply_left m i
#align basis.to_dual_eq_repr Basis.toDual_eq_repr

theorem toDual_eq_equivFun [Fintype ι] (m : M) (i : ι) : b.toDual m (b i) = b.equivFun m i := by
  rw [b.equivFun_apply, toDual_eq_repr]
#align basis.to_dual_eq_equiv_fun Basis.toDual_eq_equivFun

theorem toDual_inj (m : M) (a : b.toDual m = 0) : m = 0 := by
  rw [← mem_bot R, ← b.repr.ker, mem_ker, LinearEquiv.coe_coe]
  apply Finsupp.ext
  intro b
  rw [← toDual_eq_repr, a]
  rfl
#align basis.to_dual_inj Basis.toDual_inj

-- Porting note: broken dot notation lean4#1910 LinearMap.ker
theorem toDual_ker : LinearMap.ker b.toDual = ⊥ :=
  ker_eq_bot'.mpr b.toDual_inj
#align basis.to_dual_ker Basis.toDual_ker

-- Porting note: broken dot notation lean4#1910 LinearMap.range
theorem toDual_range [Finite ι] : LinearMap.range b.toDual = ⊤ := by
  cases nonempty_fintype ι
  refine' eq_top_iff'.2 fun f => _
  rw [LinearMap.mem_range]
  let lin_comb : ι →₀ R := Finsupp.equivFunOnFinite.symm fun i => f.toFun (b i)
  refine' ⟨Finsupp.total ι M R b lin_comb, b.ext fun i => _⟩
  rw [b.toDual_eq_repr _ i, repr_total b]
  rfl
#align basis.to_dual_range Basis.toDual_range

end CommSemiring

section

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι]

variable (b : Basis ι R M)

@[simp]
theorem sum_dual_apply_smul_coord (f : Module.Dual R M) :
    (∑ x, f (b x) • b.coord x) = f := by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul, ←
    f.map_smul, ← f.map_sum, Basis.coord_apply, Basis.sum_repr]
#align basis.sum_dual_apply_smul_coord Basis.sum_dual_apply_smul_coord

end

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι]

variable (b : Basis ι R M)

section Finite

variable [Finite ι]

/-- A vector space is linearly equivalent to its dual space. -/
def toDualEquiv : M ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective b.toDual ⟨ker_eq_bot.mp b.toDual_ker, range_eq_top.mp b.toDual_range⟩
#align basis.to_dual_equiv Basis.toDualEquiv

-- `simps` times out when generating this
@[simp]
theorem toDualEquiv_apply (m : M) : b.toDualEquiv m = b.toDual m :=
  rfl
#align basis.to_dual_equiv_apply Basis.toDualEquiv_apply

/-- Maps a basis for `V` to a basis for the dual space. -/
def dualBasis : Basis ι R (Dual R M) :=
  b.map b.toDualEquiv
#align basis.dual_basis Basis.dualBasis

-- We use `j = i` to match `Basis.repr_self`
theorem dualBasis_apply_self (i j : ι) : b.dualBasis i (b j) =
    if j = i then 1 else 0 := by
  convert b.toDual_apply i j using 2
  rw [@eq_comm _ j i]
#align basis.dual_basis_apply_self Basis.dualBasis_apply_self

theorem total_dualBasis (f : ι →₀ R) (i : ι) :
    Finsupp.total ι (Dual R M) R b.dualBasis f (b i) = f i := by
  cases nonempty_fintype ι
  rw [Finsupp.total_apply, Finsupp.sum_fintype, LinearMap.sum_apply]
  · simp_rw [LinearMap.smul_apply, smul_eq_mul, dualBasis_apply_self, mul_boole,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  · intro
    rw [zero_smul]
#align basis.total_dual_basis Basis.total_dualBasis

theorem dualBasis_repr (l : Dual R M) (i : ι) : b.dualBasis.repr l i = l (b i) := by
  rw [← total_dualBasis b, Basis.total_repr b.dualBasis l]
#align basis.dual_basis_repr Basis.dualBasis_repr

theorem dualBasis_apply (i : ι) (m : M) : b.dualBasis i m = b.repr m i :=
  b.toDual_apply_right i m
#align basis.dual_basis_apply Basis.dualBasis_apply

@[simp]
theorem coe_dualBasis : ⇑b.dualBasis = b.coord := by
  ext (i x)
  apply dualBasis_apply
#align basis.coe_dual_basis Basis.coe_dualBasis

@[simp]
theorem toDual_toDual : b.dualBasis.toDual.comp b.toDual = Dual.eval R M := by
  refine' b.ext fun i => b.dualBasis.ext fun j => _
  rw [LinearMap.comp_apply, toDual_apply_left, coe_toDual_self, ← coe_dualBasis,
    Dual.eval_apply, Basis.repr_self, Finsupp.single_apply, dualBasis_apply_self]
#align basis.to_dual_to_dual Basis.toDual_toDual

end Finite

theorem dualBasis_equivFun [Fintype ι] (l : Dual R M) (i : ι) :
    b.dualBasis.equivFun l i = l (b i) := by rw [Basis.equivFun_apply, dualBasis_repr]
#align basis.dual_basis_equiv_fun Basis.dualBasis_equivFun

theorem eval_ker {ι : Type _} (b : Basis ι R M) :
    LinearMap.ker (Dual.eval R M) = ⊥ := by
  rw [ker_eq_bot']
  intro m hm
  simp_rw [LinearMap.ext_iff, Dual.eval_apply, zero_apply] at hm
  exact (Basis.forall_coord_eq_zero_iff _).mp fun i => hm (b.coord i)
#align basis.eval_ker Basis.eval_ker

-- Porting note: broken dot notation lean4#1910 LinearMap.range
theorem eval_range {ι : Type _} [Finite ι] (b : Basis ι R M) :
    LinearMap.range (Dual.eval R M) = ⊤ := by
  classical
    cases nonempty_fintype ι
    rw [← b.toDual_toDual, range_comp, b.toDual_range, Submodule.map_top, toDual_range _]
#align basis.eval_range Basis.eval_range

/-- A module with a basis is linearly equivalent to the dual of its dual space. -/
def evalEquiv {ι : Type _} [Finite ι] (b : Basis ι R M) : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective (eval R M) ⟨ker_eq_bot.mp b.eval_ker, range_eq_top.mp b.eval_range⟩
#align basis.eval_equiv Basis.evalEquiv

@[simp]
theorem evalEquiv_toLinearMap {ι : Type _} [Finite ι] (b : Basis ι R M) :
    b.evalEquiv.toLinearMap = Dual.eval R M :=
  rfl
#align basis.eval_equiv_to_linear_map Basis.evalEquiv_toLinearMap

section

open Classical

variable [Finite R M] [Free R M] [Nontrivial R]

instance dual_free : Free R (Dual R M) :=
  Free.of_basis (Free.chooseBasis R M).dualBasis
#align basis.dual_free Basis.dual_free

instance dual_finite : Finite R (Dual R M) :=
  Finite.of_basis (Free.chooseBasis R M).dualBasis
#align basis.dual_finite Basis.dual_finite

end

end CommRing

/-- `simp` normal form version of `total_dualBasis` -/
@[simp]
theorem total_coord [CommRing R] [AddCommGroup M] [Module R M] [Finite ι] (b : Basis ι R M)
    (f : ι →₀ R) (i : ι) : Finsupp.total ι (Dual R M) R b.coord f (b i) = f i := by
  haveI := Classical.decEq ι
  rw [← coe_dualBasis, total_dualBasis]
#align basis.total_coord Basis.total_coord

-- Porting note: universes very dodgy in Cardinals...
theorem dual_rank_eq [CommRing K] [AddCommGroup V] [Module K V] [Finite ι] (b : Basis ι K V) :
    Cardinal.lift.{u₁,u₂} (Module.rank K V) = Module.rank K (Dual K V) := by
  classical
    cases nonempty_fintype ι
    have := LinearEquiv.lift_rank_eq b.toDualEquiv
    rw [Cardinal.lift_umax.{u₂,u₁}] at this
    rw [this, ← Cardinal.lift_umax]
    apply Cardinal.lift_id
#align basis.dual_rank_eq Basis.dual_rank_eq

end Basis

namespace Module

variable {K : Type u₁} {V : Type u₂}

variable [Field K] [AddCommGroup V] [Module K V]

open Module Module.Dual Submodule LinearMap Cardinal Basis FiniteDimensional

section

variable (K) (V)

-- Porting note: broken dot notation lean4#1910 LinearMap.ker
theorem eval_ker : LinearMap.ker (eval K V) = ⊥ := by
  classical exact (Basis.ofVectorSpace K V).eval_ker
#align module.eval_ker Module.eval_ker

theorem map_eval_injective : (Submodule.map (eval K V)).Injective := by
  apply Submodule.map_injective_of_injective
  rw [← LinearMap.ker_eq_bot]
  apply eval_ker K V
#align module.map_eval_injective Module.map_eval_injective

-- elaborates faster than `exact`
theorem comap_eval_surjective : (Submodule.comap (eval K V)).Surjective := by
  apply Submodule.comap_surjective_of_injective
  rw [← LinearMap.ker_eq_bot]
  apply eval_ker K V
#align module.comap_eval_surjective Module.comap_eval_surjective

-- elaborates faster than `exact`
end

section

variable (K)

theorem eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0 := by
  simpa only using SetLike.ext_iff.mp (eval_ker K V) v
#align module.eval_apply_eq_zero_iff Module.eval_apply_eq_zero_iff

theorem eval_apply_injective : Function.Injective (eval K V) :=
  (injective_iff_map_eq_zero' (eval K V)).mpr (eval_apply_eq_zero_iff K)
#align module.eval_apply_injective Module.eval_apply_injective

theorem forall_dual_apply_eq_zero_iff (v : V) : (∀ φ : Module.Dual K V, φ v = 0) ↔ v = 0 := by
  rw [← eval_apply_eq_zero_iff K v, LinearMap.ext_iff]
  rfl
#align module.forall_dual_apply_eq_zero_iff Module.forall_dual_apply_eq_zero_iff

end

-- TODO(jmc): generalize to rings, once `Module.rank` is generalized
theorem dual_rank_eq [FiniteDimensional K V] :
    Cardinal.lift.{u₁,u₂} (Module.rank K V) = Module.rank K (Dual K V) :=
  (Basis.ofVectorSpace K V).dual_rank_eq
#align module.dual_rank_eq Module.dual_rank_eq

-- Porting note: broken dot notation lean4#1910 LinearMap.range
theorem erange_coe [FiniteDimensional K V] : LinearMap.range (eval K V) = ⊤ :=
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  (Basis.ofVectorSpace K V).eval_range
#align module.erange_coe Module.erange_coe

variable (K V)

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def evalEquiv [FiniteDimensional K V] : V ≃ₗ[K] Dual K (Dual K V) :=
  LinearEquiv.ofBijective
    (eval K V)-- 60x faster elaboration than using `ker_eq_bot.mp eval_ker` directly:
    ⟨by
      rw [← ker_eq_bot]
      apply eval_ker K V, range_eq_top.mp erange_coe⟩
#align module.eval_equiv Module.evalEquiv

/-- The isomorphism `Module.evalEquiv` induces an order isomorphism on subspaces. -/
def mapEvalEquiv [FiniteDimensional K V] : Subspace K V ≃o Subspace K (Dual K (Dual K V)) :=
  Submodule.orderIsoMapComap (evalEquiv K V)
#align module.map_eval_equiv Module.mapEvalEquiv

variable {K V}

@[simp]
theorem evalEquiv_toLinearMap [FiniteDimensional K V] :
    (evalEquiv K V).toLinearMap = Dual.eval K V :=
  rfl
#align module.eval_equiv_to_linear_map Module.evalEquiv_toLinearMap

@[simp]
theorem mapEvalEquiv_apply [FiniteDimensional K V] (W : Subspace K V) :
    mapEvalEquiv K V W = W.map (eval K V) :=
  rfl
#align module.map_eval_equiv_apply Module.mapEvalEquiv_apply

@[simp]
theorem mapEvalEquiv_symm_apply [FiniteDimensional K V] (W'' : Subspace K (Dual K (Dual K V))) :
    (mapEvalEquiv K V).symm W'' = W''.comap (eval K V) :=
  rfl
#align module.map_eval_equiv_symm_apply Module.mapEvalEquiv_symm_apply

end Module

section DualBases

open Module

variable {R M ι : Type _}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]

-- Porting note: replace use_finite_instance tactic
open Lean.Elab.Tactic in
/-- Try using `Set.to_finite` to dispatch a `Set.finite` goal. -/
def evalUseFiniteInstance : TacticM Unit := do
  evalTactic (← `(tactic|intros; apply Set.toFinite ))

elab "use_finite_instance" : tactic => evalUseFiniteInstance

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
-- @[nolint has_nonempty_instance] Porting note: removed
structure Module.DualBases (e : ι → M) (ε : ι → Dual R M) : Prop where
  eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0
  Total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0
  Finite : ∀ m : M, { i | ε i m ≠ 0 }.Finite := by
      use_finite_instance
#align module.dual_bases Module.DualBases

end DualBases

namespace Module.DualBases

open Module Module.Dual LinearMap Function

variable {R M ι : Type _}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {e : ι → M} {ε : ι → Dual R M}

/-- The coefficients of `v` on the basis `e` -/
def coeffs [DecidableEq ι] (h : DualBases e ε) (m : M) : ι →₀ R where
  toFun i := ε i m
  support := (h.Finite m).toFinset
  mem_support_toFun := by
    intro i
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
#align module.dual_bases.coeffs Module.DualBases.coeffs

@[simp]
theorem coeffs_apply [DecidableEq ι] (h : DualBases e ε) (m : M) (i : ι) : h.coeffs m i = ε i m :=
  rfl
#align module.dual_bases.coeffs_apply Module.DualBases.coeffs_apply

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `Finsupp.total _ M R e l` -/
def lc {ι} (e : ι → M) (l : ι →₀ R) : M :=
  l.sum fun (i : ι) (a : R) => a • e i
#align module.dual_bases.lc Module.DualBases.lc

theorem lc_def (e : ι → M) (l : ι →₀ R) : lc e l = Finsupp.total _ _ R e l :=
  rfl
#align module.dual_bases.lc_def Module.DualBases.lc_def

open Module

variable [DecidableEq ι] (h : DualBases e ε)

theorem dual_lc (l : ι →₀ R) (i : ι) : ε i (DualBases.lc e l) = l i := by
  erw [LinearMap.map_sum]
  simp_rw [map_smul]
  -- Porting note: cannot get at •
  -- simp only [h.eval, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [h.eval, smul_eq_mul]
  · intro q _ q_ne
    simp [q_ne.symm, h.eval, smul_eq_mul]
  · intro p_not_in
    simp [Finsupp.not_mem_support_iff.1 p_not_in]
#align module.dual_bases.dual_lc Module.DualBases.dual_lc

@[simp]
theorem coeffs_lc (l : ι →₀ R) : h.coeffs (DualBases.lc e l) = l := by
  ext i
  rw [h.coeffs_apply, h.dual_lc]
#align module.dual_bases.coeffs_lc Module.DualBases.coeffs_lc

/-- For any m : M n, \sum_{p ∈ Q n} (ε p m) • e p = m -/
@[simp]
theorem lc_coeffs (m : M) : DualBases.lc e (h.coeffs m) = m := by
  refine' eq_of_sub_eq_zero (h.Total _)
  intro i
  simp [LinearMap.map_sub, h.dual_lc, sub_eq_zero]
#align module.dual_bases.lc_coeffs Module.DualBases.lc_coeffs

/-- `(h : dual_bases e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps]
def basis : Basis ι R M :=
  Basis.ofRepr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }
#align module.dual_bases.basis Module.DualBases.basis

-- Porting note : from simpNF the LHS simplifies; it yields lc_def.symm
-- probably not a useful simp lemma; nolint simpNF since it cannot see this removal
attribute [-simp, nolint simpNF] basis_repr_symm_apply

@[simp]
theorem coe_basis : ⇑h.basis = e := by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rw [h.basis_repr_apply, coeffs_apply, h.eval, Finsupp.single_apply]
  convert if_congr (eq_comm (a := j) (b := i)) rfl rfl
#align module.dual_bases.coe_basis Module.DualBases.coe_basis

-- `convert` to get rid of a `DecidableEq` mismatch
theorem mem_of_mem_span {H : Set ι} {x : M} (hmem : x ∈ Submodule.span R (e '' H)) :
    ∀ i : ι, ε i x ≠ 0 → i ∈ H := by
  intro i hi
  rcases(Finsupp.mem_span_image_iff_total _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi
#align module.dual_bases.mem_of_mem_span Module.DualBases.mem_of_mem_span

theorem coe_dualBasis [Fintype ι] : ⇑h.basis.dualBasis = ε :=
  funext fun i =>
    h.basis.ext fun j => by
      rw [h.basis.dualBasis_apply_self, h.coe_basis, h.eval, if_congr eq_comm rfl rfl]
#align module.dual_bases.coe_dual_basis Module.DualBases.coe_dualBasis

end Module.DualBases

namespace Submodule

universe u v w

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {W : Submodule R M}

/-- The `dualRestrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dualRestrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W
#align submodule.dual_restrict Submodule.dualRestrict

theorem dualRestrict_def (W : Submodule R M) : W.dualRestrict = W.subtype.dualMap :=
  rfl
#align submodule.dual_restrict_def Submodule.dualRestrict_def

@[simp]
theorem dualRestrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) :
    W.dualRestrict φ x = φ (x : M) :=
  rfl
#align submodule.dual_restrict_apply Submodule.dualRestrict_apply

/-- The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dualAnnihilator {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (W : Submodule R M) : Submodule R <| Module.Dual R M :=
-- Porting note: broken dot notation lean4#1910 LinearMap.ker
  LinearMap.ker W.dualRestrict
#align submodule.dual_annihilator Submodule.dualAnnihilator

@[simp]
theorem mem_dualAnnihilator (φ : Module.Dual R M) : φ ∈ W.dualAnnihilator ↔ ∀ w ∈ W, φ w = 0 := by
  refine' LinearMap.mem_ker.trans _
  simp_rw [LinearMap.ext_iff, dualRestrict_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩
#align submodule.mem_dual_annihilator Submodule.mem_dualAnnihilator

/-- That $\operatorname{ker}(\iota^* : V^* \to W^*) = \operatorname{ann}(W)$.
This is the definition of the dual annihilator of the submodule $W$. -/
theorem dualRestrict_ker_eq_dualAnnihilator (W : Submodule R M) :
-- Porting note: broken dot notation lean4#1910 LinearMap.ker
    LinearMap.ker W.dualRestrict = W.dualAnnihilator :=
  rfl
#align submodule.dual_restrict_ker_eq_dual_annihilator Submodule.dualRestrict_ker_eq_dualAnnihilator

/-- The `dualAnnihilator` of a submodule of the dual space pulled back along the evaluation map
`Module.Dual.eval`. -/
def dualCoannihilator (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)
#align submodule.dual_coannihilator Submodule.dualCoannihilator

theorem mem_dualCoannihilator {Φ : Submodule R (Module.Dual R M)} (x : M) :
    x ∈ Φ.dualCoannihilator ↔ ∀ φ ∈ Φ, (φ x : R) = 0 := by
  simp_rw [dualCoannihilator, mem_comap, mem_dualAnnihilator, Module.Dual.eval_apply]
#align submodule.mem_dual_coannihilator Submodule.mem_dualCoannihilator

theorem dualAnnihilator_gc (R M : Type _) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    GaloisConnection
      (OrderDual.toDual ∘ (dualAnnihilator : Submodule R M → Submodule R (Module.Dual R M)))
      (dualCoannihilator ∘ OrderDual.ofDual) := by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual]
  constructor <;>
    · intro h x hx
      simp only [mem_dualAnnihilator, mem_dualCoannihilator]
      intro y hy
      have := h hy
      simp only [mem_dualAnnihilator, mem_dualCoannihilator] at this
      exact this x hx
#align submodule.dual_annihilator_gc Submodule.dualAnnihilator_gc

theorem le_dualAnnihilator_iff_le_dualCoannihilator {U : Submodule R (Module.Dual R M)}
    {V : Submodule R M} : U ≤ V.dualAnnihilator ↔ V ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_iff_le
#align submodule.le_dual_annihilator_iff_le_dual_coannihilator Submodule.le_dualAnnihilator_iff_le_dualCoannihilator

@[simp]
theorem dualAnnihilator_bot : (⊥ : Submodule R M).dualAnnihilator = ⊤ :=
  (dualAnnihilator_gc R M).l_bot
#align submodule.dual_annihilator_bot Submodule.dualAnnihilator_bot

@[simp]
theorem dualAnnihilator_top : (⊤ : Submodule R M).dualAnnihilator = ⊥ := by
  rw [eq_bot_iff]
  intro v
  simp_rw [mem_dualAnnihilator, mem_bot, mem_top, forall_true_left]
  exact fun h => LinearMap.ext h
#align submodule.dual_annihilator_top Submodule.dualAnnihilator_top

@[simp]
theorem dualCoannihilator_bot : (⊥ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊤ :=
  (dualAnnihilator_gc R M).u_top
#align submodule.dual_coannihilator_bot Submodule.dualCoannihilator_bot

@[mono]
theorem dualAnnihilator_anti {U V : Submodule R M} (hUV : U ≤ V) :
    V.dualAnnihilator ≤ U.dualAnnihilator :=
  (dualAnnihilator_gc R M).monotone_l hUV
#align submodule.dual_annihilator_anti Submodule.dualAnnihilator_anti

@[mono]
theorem dualCoannihilator_anti {U V : Submodule R (Module.Dual R M)} (hUV : U ≤ V) :
    V.dualCoannihilator ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).monotone_u hUV
#align submodule.dual_coannihilator_anti Submodule.dualCoannihilator_anti

theorem le_dualAnnihilator_dualCoannihilator (U : Submodule R M) :
    U ≤ U.dualAnnihilator.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_u_l U
#align submodule.le_dual_annihilator_dual_coannihilator Submodule.le_dualAnnihilator_dualCoannihilator

theorem le_dualCoannihilator_dualAnnihilator (U : Submodule R (Module.Dual R M)) :
    U ≤ U.dualCoannihilator.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_le U
#align submodule.le_dual_coannihilator_dual_annihilator Submodule.le_dualCoannihilator_dualAnnihilator

theorem dualAnnihilator_dualCoannihilator_dualAnnihilator (U : Submodule R M) :
    U.dualAnnihilator.dualCoannihilator.dualAnnihilator = U.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_l_eq_l U
#align submodule.dual_annihilator_dual_coannihilator_dual_annihilator Submodule.dualAnnihilator_dualCoannihilator_dualAnnihilator

theorem dualCoannihilator_dualAnnihilator_dualCoannihilator (U : Submodule R (Module.Dual R M)) :
    U.dualCoannihilator.dualAnnihilator.dualCoannihilator = U.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_l_u_eq_u U
#align submodule.dual_coannihilator_dual_annihilator_dual_coannihilator Submodule.dualCoannihilator_dualAnnihilator_dualCoannihilator

theorem dualAnnihilator_sup_eq (U V : Submodule R M) :
    (U ⊔ V).dualAnnihilator = U.dualAnnihilator ⊓ V.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_sup
#align submodule.dual_annihilator_sup_eq Submodule.dualAnnihilator_sup_eq

theorem dualCoannihilator_sup_eq (U V : Submodule R (Module.Dual R M)) :
    (U ⊔ V).dualCoannihilator = U.dualCoannihilator ⊓ V.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_inf
#align submodule.dual_coannihilator_sup_eq Submodule.dualCoannihilator_sup_eq

theorem dualAnnihilator_iSup_eq {ι : Type _} (U : ι → Submodule R M) :
    (⨆ i : ι, U i).dualAnnihilator = ⨅ i : ι, (U i).dualAnnihilator :=
  (dualAnnihilator_gc R M).l_iSup
#align submodule.dual_annihilator_supr_eq Submodule.dualAnnihilator_iSup_eq

theorem dualCoannihilator_iSup_eq {ι : Type _} (U : ι → Submodule R (Module.Dual R M)) :
    (⨆ i : ι, U i).dualCoannihilator = ⨅ i : ι, (U i).dualCoannihilator :=
  (dualAnnihilator_gc R M).u_iInf
#align submodule.dual_coannihilator_supr_eq Submodule.dualCoannihilator_iSup_eq

/-- See also `Subspace.dualAnnihilator_inf_eq` for vector subspaces. -/
theorem sup_dualAnnihilator_le_inf (U V : Submodule R M) :
    U.dualAnnihilator ⊔ V.dualAnnihilator ≤ (U ⊓ V).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_dualAnnihilator_dualCoannihilator _
#align submodule.sup_dual_annihilator_le_inf Submodule.sup_dualAnnihilator_le_inf

/-- See also `Subspace.dualAnnihilator_iInf_eq` for vector subspaces when `ι` is finite. -/
theorem iSup_dualAnnihilator_le_iInf {ι : Type _} (U : ι → Submodule R M) :
    (⨆ i : ι, (U i).dualAnnihilator) ≤ (⨅ i : ι, U i).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_iSup_eq]
  apply iInf_mono
  exact fun i : ι => le_dualAnnihilator_dualCoannihilator (U i)
#align submodule.supr_dual_annihilator_le_infi Submodule.iSup_dualAnnihilator_le_iInf

end Submodule

namespace Subspace

open Submodule LinearMap

universe u v w

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[simp]
theorem dualCoannihilator_top (W : Subspace K V) :
    (⊤ : Subspace K (Module.Dual K W)).dualCoannihilator = ⊥ := by
  rw [dualCoannihilator, dualAnnihilator_top, comap_bot, Module.eval_ker]
#align subspace.dual_coannihilator_top Subspace.dualCoannihilator_top

theorem dualAnnihilator_dualCoannihilator_eq {W : Subspace K V} :
    W.dualAnnihilator.dualCoannihilator = W := by
  refine' le_antisymm _ (le_dualAnnihilator_dualCoannihilator _)
  intro v
  simp only [mem_dualAnnihilator, mem_dualCoannihilator]
  contrapose!
  intro hv
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl W
  obtain ⟨⟨w, w'⟩, rfl, -⟩ := existsUnique_add_of_isCompl_prod hW v
  have hw'n : (w' : V) ∉ W := by
    contrapose! hv
    exact Submodule.add_mem W w.2 hv
  have hw'nz : w' ≠ 0 := by
    rintro rfl
    exact hw'n (Submodule.zero_mem W)
  rw [Ne.def, ← Module.forall_dual_apply_eq_zero_iff K w'] at hw'nz
  push_neg  at hw'nz
  obtain ⟨φ, hφ⟩ := hw'nz
  exists ((LinearMap.ofIsComplProd hW).comp (LinearMap.inr _ _ _)) φ
  simp only [coe_comp, coe_inr, Function.comp_apply, ofIsComplProd_apply, map_add,
    ofIsCompl_left_apply, zero_apply, ofIsCompl_right_apply, zero_add, Ne.def]
  refine' ⟨_, hφ⟩
  intro v hv
  apply LinearMap.ofIsCompl_left_apply hW ⟨v, hv⟩
#align subspace.dual_annihilator_dual_coannihilator_eq Subspace.dualAnnihilator_dualCoannihilator_eq

-- exact elaborates slowly
theorem forall_mem_dualAnnihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) :
    (∀ φ : Module.Dual K V, φ ∈ W.dualAnnihilator → φ v = 0) ↔ v ∈ W := by
  rw [← SetLike.ext_iff.mp dualAnnihilator_dualCoannihilator_eq v, mem_dualCoannihilator]
#align subspace.forall_mem_dual_annihilator_apply_eq_zero_iff Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff

/-- `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator` form a Galois coinsertion. -/
def dualAnnihilatorGci (K V : Type _) [Field K] [AddCommGroup V] [Module K V] :
    GaloisCoinsertion
      (OrderDual.toDual ∘ (dualAnnihilator : Subspace K V → Subspace K (Module.Dual K V)))
      (dualCoannihilator ∘ OrderDual.ofDual) where
  choice W _ := dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl
#align subspace.dual_annihilator_gci Subspace.dualAnnihilatorGci

theorem dualAnnihilator_le_dualAnnihilator_iff {W W' : Subspace K V} :
    W.dualAnnihilator ≤ W'.dualAnnihilator ↔ W' ≤ W :=
  (dualAnnihilatorGci K V).l_le_l_iff
#align subspace.dual_annihilator_le_dual_annihilator_iff Subspace.dualAnnihilator_le_dualAnnihilator_iff

theorem dualAnnihilator_inj {W W' : Subspace K V} :
    W.dualAnnihilator = W'.dualAnnihilator ↔ W = W' := by
  constructor
  · apply (dualAnnihilatorGci K V).l_injective
  · rintro rfl
    rfl
#align subspace.dual_annihilator_inj Subspace.dualAnnihilator_inj

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dualLift W φ` is
an arbitrary extension of `φ` to an element of the dual of `V`.
That is, `dualLift W φ` sends `w ∈ W` to `φ x` and `x` in a chosen complement of `W` to `0`. -/
noncomputable def dualLift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  let h := Classical.indefiniteDescription _ W.exists_isCompl
  (LinearMap.ofIsComplProd h.2).comp (LinearMap.inl _ _ _)
#align subspace.dual_lift Subspace.dualLift

variable {W : Subspace K V}

@[simp]
theorem dualLift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) = φ w := by
  erw [ofIsCompl_left_apply _ w]
  rfl
#align subspace.dual_lift_of_subtype Subspace.dualLift_of_subtype

theorem dualLift_of_mem {φ : Module.Dual K W} {w : V} (hw : w ∈ W) : W.dualLift φ w = φ ⟨w, hw⟩ :=
  by convert dualLift_of_subtype ⟨w, hw⟩
#align subspace.dual_lift_of_mem Subspace.dualLift_of_mem

@[simp]
theorem dualRestrict_comp_dualLift (W : Subspace K V) : W.dualRestrict.comp W.dualLift = 1 := by
  ext (φ x)
  simp
#align subspace.dual_restrict_comp_dual_lift Subspace.dualRestrict_comp_dualLift

theorem dualRestrict_leftInverse (W : Subspace K V) :
    Function.LeftInverse W.dualRestrict W.dualLift := fun x =>
  show W.dualRestrict.comp W.dualLift x = x by
    rw [dualRestrict_comp_dualLift]
    rfl
#align subspace.dual_restrict_left_inverse Subspace.dualRestrict_leftInverse

theorem dualLift_rightInverse (W : Subspace K V) :
    Function.RightInverse W.dualLift W.dualRestrict :=
  W.dualRestrict_leftInverse
#align subspace.dual_lift_right_inverse Subspace.dualLift_rightInverse

theorem dualRestrict_surjective : Function.Surjective W.dualRestrict :=
  W.dualLift_rightInverse.surjective
#align subspace.dual_restrict_surjective Subspace.dualRestrict_surjective

theorem dualLift_injective : Function.Injective W.dualLift :=
  W.dualRestrict_leftInverse.injective
#align subspace.dual_lift_injective Subspace.dualLift_injective

/-- The quotient by the `dualAnnihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
  (quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans <|
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective
#align subspace.quot_annihilator_equiv Subspace.quotAnnihilatorEquiv

@[simp]
theorem quotAnnihilatorEquiv_apply (W : Subspace K V) (φ : Module.Dual K V) :
    W.quotAnnihilatorEquiv (Submodule.Quotient.mk φ) = W.dualRestrict φ := by
  ext
  rfl
#align subspace.quot_annihilator_equiv_apply Subspace.quotAnnihilatorEquiv_apply

/-- The natural isomorphism from the dual of a subspace `W` to `W.dualLift.range`. -/
-- Porting note: broken dot notation lean4#1910 LinearMap.range
noncomputable def dualEquivDual (W : Subspace K V) :
    Module.Dual K W ≃ₗ[K] LinearMap.range W.dualLift :=
  LinearEquiv.ofInjective _ dualLift_injective
#align subspace.dual_equiv_dual Subspace.dualEquivDual

theorem dualEquivDual_def (W : Subspace K V) :
    W.dualEquivDual.toLinearMap = W.dualLift.rangeRestrict :=
  rfl
#align subspace.dual_equiv_dual_def Subspace.dualEquivDual_def

@[simp]
theorem dualEquivDual_apply (φ : Module.Dual K W) :
    W.dualEquivDual φ = ⟨W.dualLift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl
#align subspace.dual_equiv_dual_apply Subspace.dualEquivDual_apply

section

open Classical

open FiniteDimensional

variable {V₁ : Type _} [AddCommGroup V₁] [Module K V₁]

instance [H : FiniteDimensional K V] : FiniteDimensional K (Module.Dual K V) := by infer_instance

variable [FiniteDimensional K V] [FiniteDimensional K V₁]

theorem dualAnnihilator_dualAnnihilator_eq (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator = Module.mapEvalEquiv K V W := by
  have : _ = W := Subspace.dualAnnihilator_dualCoannihilator_eq
  rw [dualCoannihilator, ← Module.mapEvalEquiv_symm_apply] at this
  rwa [← OrderIso.symm_apply_eq]
#align subspace.dual_annihilator_dual_annihilator_eq Subspace.dualAnnihilator_dualAnnihilator_eq

-- TODO(kmill): https://github.com/leanprover-community/mathlib/pull/17521#discussion_r1083241963
@[simp]
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V :=
  LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
#align subspace.dual_finrank_eq Subspace.dual_finrank_eq

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
-- Porting note: broken dot notation lean4#1910 LinearMap.range
noncomputable def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ LinearMap.range W.dualLift) ≃ₗ[K] W.dualAnnihilator :=
  LinearEquiv.quotEquivOfQuotEquiv <| LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual
#align subspace.quot_dual_equiv_annihilator Subspace.quotDualEquivAnnihilator

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator :=
  let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator
  -- Porting note: this prevents the timeout; ML3 proof preserved below
  -- refine' _ ≪≫ₗ W.quotDualEquivAnnihilator
  -- refine' LinearEquiv.quot_equiv_of_equiv _ (Basis.ofVectorSpace K V).toDualEquiv
  -- exact (Basis.ofVectorSpace K W).toDualEquiv.trans W.dual_equiv_dual
#align subspace.quot_equiv_annihilator Subspace.quotEquivAnnihilator

open FiniteDimensional

@[simp]
theorem finrank_dualCoannihilator_eq {Φ : Subspace K (Module.Dual K V)} :
    finrank K Φ.dualCoannihilator = finrank K Φ.dualAnnihilator := by
  rw [Submodule.dualCoannihilator, ← Module.evalEquiv_toLinearMap]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)
#align subspace.finrank_dual_coannihilator_eq Subspace.finrank_dualCoannihilator_eq

theorem finrank_add_finrank_dualCoannihilator_eq (W : Subspace K (Module.Dual K V)) :
    finrank K W + finrank K W.dualCoannihilator = finrank K V := by
  rw [finrank_dualCoannihilator_eq]
  -- Porting note: LineqrEquiv.finrank_eq needs help
  let equiv := W.quotEquivAnnihilator
  have eq := LinearEquiv.finrank_eq (R := K) (M := (Module.Dual K V) ⧸ W)
    (M₂ := { x // x ∈ dualAnnihilator W }) equiv
  rw [eq.symm, add_comm, Submodule.finrank_quotient_add_finrank, Subspace.dual_finrank_eq]
#align subspace.finrank_add_finrank_dual_coannihilator_eq Subspace.finrank_add_finrank_dualCoannihilator_eq

end

end Subspace

open Module

namespace LinearMap

variable {R : Type u} [CommSemiring R] {M₁ : Type v} {M₂ : Type v'}

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

variable (f : M₁ →ₗ[R] M₂)

-- Porting note: broken dot notation lean4#1910 LinearMap.ker
theorem ker_dualMap_eq_dualAnnihilator_range :
    LinearMap.ker f.dualMap = f.range.dualAnnihilator := by
  ext φ; constructor <;> intro hφ
  · rw [mem_ker] at hφ
    rw [Submodule.mem_dualAnnihilator]
    rintro y ⟨x, rfl⟩
    rw [← dualMap_apply, hφ, zero_apply]
  · ext x
    rw [dualMap_apply]
    rw [Submodule.mem_dualAnnihilator] at hφ
    exact hφ (f x) ⟨x, rfl⟩
#align linear_map.ker_dual_map_eq_dual_annihilator_range LinearMap.ker_dualMap_eq_dualAnnihilator_range

-- Porting note: broken dot notation lean4#1910 LinearMap.range
theorem range_dualMap_le_dualAnnihilator_ker :
    LinearMap.range f.dualMap ≤ f.ker.dualAnnihilator := by
  rintro _ ⟨ψ, rfl⟩
  simp_rw [Submodule.mem_dualAnnihilator, mem_ker]
  rintro x hx
  rw [dualMap_apply, hx, map_zero]
#align linear_map.range_dual_map_le_dual_annihilator_ker LinearMap.range_dualMap_le_dualAnnihilator_ker

end LinearMap

section CommRing

variable {R M M' : Type _}

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

namespace Submodule

/-- Given a submodule, corestrict to the pairing on `M ⧸ W` by
simultaneously restricting to `W.dualAnnihilator`.

See `Subspace.dualCopairing_nondegenerate`. -/
def dualCopairing (W : Submodule R M) : W.dualAnnihilator →ₗ[R] M ⧸ W →ₗ[R] R :=
  LinearMap.flip <|
    W.liftQ ((Module.dualPairing R M).domRestrict W.dualAnnihilator).flip
      (by
        intro w hw
        ext ⟨φ, hφ⟩
        exact (mem_dualAnnihilator φ).mp hφ w hw)
#align submodule.dual_copairing Submodule.dualCopairing

-- Porting note: helper instance
instance (W : Submodule R M) : FunLike (W.dualAnnihilator) M fun _ => R :=
  { coe := fun φ => φ.val,
    coe_injective' := fun φ ψ h => by
      ext
      simp only [Function.funext_iff] at h
      exact h _ }

@[simp]
theorem dualCopairing_apply {W : Submodule R M} (φ : W.dualAnnihilator) (x : M) :
    W.dualCopairing φ (Quotient.mk x) = φ x :=
  rfl
#align submodule.dual_copairing_apply Submodule.dualCopairing_apply

/-- Given a submodule, restrict to the pairing on `W` by
simultaneously corestricting to `Module.Dual R M ⧸ W.dualAnnihilator`.
This is `Submodule.dualRestrict` factored through the quotient by its kernel (which
is `W.dualAnnihilator` by definition).

See `Subspace.dualPairing_nondegenerate`. -/
def dualPairing (W : Submodule R M) : Module.Dual R M ⧸ W.dualAnnihilator →ₗ[R] W →ₗ[R] R :=
  W.dualAnnihilator.liftQ W.dualRestrict le_rfl
#align submodule.dual_pairing Submodule.dualPairing

@[simp]
theorem dualPairing_apply {W : Submodule R M} (φ : Module.Dual R M) (x : W) :
    W.dualPairing (Quotient.mk φ) x = φ x :=
  rfl
#align submodule.dual_pairing_apply Submodule.dualPairing_apply

-- Porting note: broken dot notation lean4#1910 LinearMap.range
/-- That $\operatorname{im}(q^* : (V/W)^* \to V^*) = \operatorname{ann}(W)$. -/
theorem range_dualMap_mkQ_eq (W : Submodule R M) :
    LinearMap.range W.mkQ.dualMap = W.dualAnnihilator := by
  ext φ
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩
    have := LinearMap.mem_range_self W.mkQ.dualMap ψ
    simpa only [ker_mkQ] using LinearMap.range_dualMap_le_dualAnnihilator_ker W.mkQ this
  · intro hφ
    exists W.dualCopairing ⟨φ, hφ⟩
#align submodule.range_dual_map_mkq_eq Submodule.range_dualMap_mkQ_eq

/-- Equivalence $(M/W)^* \approx \operatorname{ann}(W)$. That is, there is a one-to-one
correspondence between the dual of `M ⧸ W` and those elements of the dual of `M` that
vanish on `W`.

The inverse of this is `Submodule.dualCopairing`. -/
def dualQuotEquivDualAnnihilator (W : Submodule R M) :
    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=
  LinearEquiv.ofLinear
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
-- Porting note: broken dot notation lean4#1910 LinearMap.mem_range_self
      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)
    W.dualCopairing
    (by
      ext
      rfl)
    (by
      ext
      rfl)
#align submodule.dual_quot_equiv_dual_annihilator Submodule.dualQuotEquivDualAnnihilator

@[simp]
theorem dualQuotEquivDualAnnihilator_apply (W : Submodule R M) (φ : Module.Dual R (M ⧸ W)) (x : M) :
    dualQuotEquivDualAnnihilator W φ x = φ (Quotient.mk x) :=
  rfl
#align submodule.dual_quot_equiv_dual_annihilator_apply Submodule.dualQuotEquivDualAnnihilator_apply

theorem dualCopairing_eq (W : Submodule R M) :
    W.dualCopairing = (dualQuotEquivDualAnnihilator W).symm.toLinearMap :=
  rfl
#align submodule.dual_copairing_eq Submodule.dualCopairing_eq

@[simp]
theorem dualQuotEquivDualAnnihilator_symm_apply_mk (W : Submodule R M) (φ : W.dualAnnihilator)
    (x : M) : (dualQuotEquivDualAnnihilator W).symm φ (Quotient.mk x) = φ x :=
  rfl
#align submodule.dual_quot_equiv_dual_annihilator_symm_apply_mk Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk

end Submodule

namespace LinearMap

open Submodule

-- Porting note: broken dot notation lean4#1910 LinearMap.range
theorem range_dualMap_eq_dualAnnihilator_ker_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : LinearMap.range f.dualMap = f.ker.dualAnnihilator := by
  rw [← f.ker.range_dualMap_mkQ_eq]
  let f' := LinearMap.quotKerEquivOfSurjective f hf
  trans LinearMap.range (f.dualMap.comp f'.symm.dualMap.toLinearMap)
  · rw [LinearMap.range_comp_of_range_eq_top]
    apply LinearEquiv.range
  · apply congr_arg
    ext (φ x)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, LinearMap.dualMap_apply,
      LinearEquiv.dualMap_apply, mkQ_apply, LinearMap.quotKerEquivOfSurjective,
      LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.ofTop_symm_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, mkQ_apply, Function.comp]
#align linear_map.range_dual_map_eq_dual_annihilator_ker_of_surjective LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective

-- Note, this can be specialized to the case where `R` is an injective `R`-module, or when
-- `f.coker` is a projective `R`-module.
theorem range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f.range.subtype.dualMap) :
    LinearMap.range f.dualMap = f.ker.dualAnnihilator := by
  have rr_surj : Function.Surjective f.rangeRestrict := by
    rw [← LinearMap.range_eq_top, LinearMap.range_rangeRestrict]
  have := range_dualMap_eq_dualAnnihilator_ker_of_surjective f.rangeRestrict rr_surj
  convert this using 1
  -- Porting note: broken dot notation lean4#1910
  · change LinearMap.range
      ((Submodule.subtype <| LinearMap.range f).comp f.rangeRestrict).dualMap = _
    rw [← LinearMap.dualMap_comp_dualMap, LinearMap.range_comp_of_range_eq_top]
    rwa [LinearMap.range_eq_top]
  · apply congr_arg
    exact (LinearMap.ker_rangeRestrict f).symm
#align linear_map.range_dual_map_eq_dual_annihilator_ker_of_subtype_range_surjective LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective

end LinearMap

end CommRing

section VectorSpace

-- Porting note: adding `u` to avoid timeouts in `dualPairing_eq`
variable {K : Type u} [Field K] {V₁ : Type v'} {V₂ : Type v''}

variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace LinearMap

theorem dualPairing_nondegenerate : (dualPairing K V₁).Nondegenerate :=
  ⟨separatingLeft_iff_ker_eq_bot.mpr ker_id, fun x => (forall_dual_apply_eq_zero_iff K x).mp⟩
#align linear_map.dual_pairing_nondegenerate LinearMap.dualPairing_nondegenerate

theorem dualMap_surjective_of_injective {f : V₁ →ₗ[K] V₂} (hf : Function.Injective f) :
    Function.Surjective f.dualMap := by
  intro φ
  let f' := LinearEquiv.ofInjective f hf
  use Subspace.dualLift (range f) (f'.symm.dualMap φ)
  ext x
  rw [LinearMap.dualMap_apply, Subspace.dualLift_of_mem (mem_range_self f x),
    LinearEquiv.dualMap_apply]
  congr 1
  exact LinearEquiv.symm_apply_apply f' x
#align linear_map.dual_map_surjective_of_injective LinearMap.dualMap_surjective_of_injective

  -- Porting note: broken dot notation lean4#1910 LinearMap.range
theorem range_dualMap_eq_dualAnnihilator_ker (f : V₁ →ₗ[K] V₂) :
    LinearMap.range f.dualMap = f.ker.dualAnnihilator :=
  range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f <|
    dualMap_surjective_of_injective (range f).injective_subtype
#align linear_map.range_dual_map_eq_dual_annihilator_ker LinearMap.range_dualMap_eq_dualAnnihilator_ker

/-- For vector spaces, `f.dualMap` is surjective if and only if `f` is injective -/
@[simp]
theorem dualMap_surjective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Surjective f.dualMap ↔ Function.Injective f := by
  rw [← LinearMap.range_eq_top, range_dualMap_eq_dualAnnihilator_ker, ←
    Submodule.dualAnnihilator_bot, Subspace.dualAnnihilator_inj, LinearMap.ker_eq_bot]
#align linear_map.dual_map_surjective_iff LinearMap.dualMap_surjective_iff

end LinearMap

namespace Subspace

open Submodule

-- Porting note: remove this at some point; this spends a lot of time
-- checking that AddCommGroup structures on V₁ ⧸ W.dualAnnihilator are defEq
-- was much worse with implicit universe variables
set_option maxHeartbeats 400000 in
theorem dualPairing_eq (W : Subspace K V₁) :
    W.dualPairing = W.quotAnnihilatorEquiv.toLinearMap := by
  ext
  rfl
#align subspace.dual_pairing_eq Subspace.dualPairing_eq

-- Porting note: remove this
set_option maxHeartbeats 400000 in
theorem dualPairing_nondegenerate (W : Subspace K V₁) : W.dualPairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualPairing_eq]
    apply LinearEquiv.ker
  · intro x h
    rw [← forall_dual_apply_eq_zero_iff K x]
    intro φ
    simpa only [Submodule.dualPairing_apply, dualLift_of_subtype] using
      h (Submodule.Quotient.mk (W.dualLift φ))
#align subspace.dual_pairing_nondegenerate Subspace.dualPairing_nondegenerate

theorem dualCopairing_nondegenerate (W : Subspace K V₁) : W.dualCopairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualCopairing_eq]
    apply LinearEquiv.ker
  · rintro ⟨x⟩
    simp only [Quotient.quot_mk_eq_mk, dualCopairing_apply, Quotient.mk_eq_zero]
    rw [← forall_mem_dualAnnihilator_apply_eq_zero_iff, SetLike.forall]
    exact id
#align subspace.dual_copairing_nondegenerate Subspace.dualCopairing_nondegenerate

-- Argument from https://math.stackexchange.com/a/2423263/172988
theorem dualAnnihilator_inf_eq (W W' : Subspace K V₁) :
    (W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator := by
  refine' le_antisymm _ (sup_dualAnnihilator_le_inf W W')
  let F : V₁ →ₗ[K] (V₁ ⧸ W) × V₁ ⧸ W' := (Submodule.mkQ W).prod (Submodule.mkQ W')
  -- Porting note: broken dot notation lean4#1910 LinearMap.ker
  have : LinearMap.ker F = W ⊓ W' := by simp only [LinearMap.ker_prod, ker_mkQ]
  rw [← this, ← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  intro φ
  rw [LinearMap.mem_range]
  rintro ⟨x, rfl⟩
  rw [Submodule.mem_sup]
  obtain ⟨⟨a, b⟩, rfl⟩ := (dualProdDualEquivDual K (V₁ ⧸ W) (V₁ ⧸ W')).surjective x
  obtain ⟨a', rfl⟩ := (dualQuotEquivDualAnnihilator W).symm.surjective a
  obtain ⟨b', rfl⟩ := (dualQuotEquivDualAnnihilator W').symm.surjective b
  use a', a'.property, b', b'.property
  rfl
#align subspace.dual_annihilator_inf_eq Subspace.dualAnnihilator_inf_eq

-- This is also true if `V₁` is finite dimensional since one can restrict `ι` to some subtype
-- for which the infi and supr are the same.
-- The obstruction to the `dualAnnihilator_inf_eq` argument carrying through is that we need
-- for `Module.Dual R (Π (i : ι), V ⧸ W i) ≃ₗ[K] Π (i : ι), Module.Dual R (V ⧸ W i)`, which is not
-- true for infinite `ι`. One would need to add additional hypothesis on `W` (for example, it might
-- be true when the family is inf-closed).
theorem dualAnnihilator_iInf_eq {ι : Type _} [Finite ι] (W : ι → Subspace K V₁) :
    (⨅ i : ι, W i).dualAnnihilator = ⨆ i : ι, (W i).dualAnnihilator := by
  revert ι
  refine' @Finite.induction_empty_option _ _ _ _
  · intro α β h hyp W
    rw [← h.iInf_comp, hyp _, ← h.iSup_comp]
  · intro W
    rw [iSup_of_empty', iInf_of_empty', sInf_empty, sSup_empty, dualAnnihilator_top]
  · intro α _ h W
    rw [iInf_option, iSup_option, dualAnnihilator_inf_eq, h]
#align subspace.dual_annihilator_infi_eq Subspace.dualAnnihilator_iInf_eq

/-- For vector spaces, dual annihilators carry direct sum decompositions
to direct sum decompositions. -/
theorem isCompl_dualAnnihilator {W W' : Subspace K V₁} (h : IsCompl W W') :
    IsCompl W.dualAnnihilator W'.dualAnnihilator := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h⊢
  rw [← dualAnnihilator_inf_eq, ← dualAnnihilator_sup_eq, h.1, h.2, dualAnnihilator_top,
    dualAnnihilator_bot]
  exact ⟨rfl, rfl⟩
#align subspace.is_compl_dual_annihilator Subspace.isCompl_dualAnnihilator

/-- For finite-dimensional vector spaces, one can distribute duals over quotients by identifying
`W.dualLift.range` with `W`. Note that this depends on a choice of splitting of `V₁`. -/
def dualQuotDistrib [FiniteDimensional K V₁] (W : Subspace K V₁) :
    Module.Dual K (V₁ ⧸ W) ≃ₗ[K] Module.Dual K V₁ ⧸ LinearMap.range W.dualLift :=
  W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm
#align subspace.dual_quot_distrib Subspace.dualQuotDistrib

end Subspace

section FiniteDimensional

open FiniteDimensional LinearMap

variable [FiniteDimensional K V₂]

namespace LinearMap

-- TODO(kmill) remove finite_dimensional if possible
-- see https://github.com/leanprover-community/mathlib/pull/17521#discussion_r1083242551
@[simp]
theorem finrank_range_dualMap_eq_finrank_range (f : V₁ →ₗ[K] V₂) :
  -- Porting note: broken dot notation lean4#1910
    finrank K (LinearMap.range f.dualMap) = finrank K (LinearMap.range f) := by
  have that := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  -- Porting note: Again LinearEquiv.finrank_eq needs help
  let equiv := (Subspace.quotEquivAnnihilator <| LinearMap.range f)
  have eq := LinearEquiv.finrank_eq (R := K) (M := (V₂ ⧸ range f))
    (M₂ := { x // x ∈ Submodule.dualAnnihilator (range f) }) equiv
  rw [eq, ←ker_dualMap_eq_dualAnnihilator_range] at that
  -- Porting note: cannot convert at `this`?
  conv_rhs at that => rw [← Subspace.dual_finrank_eq]
  refine' add_left_injective (finrank K <| LinearMap.ker f.dualMap) _
  change _ + _ = _ + _
  rw [finrank_range_add_finrank_ker f.dualMap, add_comm, that]
#align linear_map.finrank_range_dual_map_eq_finrank_range LinearMap.finrank_range_dualMap_eq_finrank_range

/-- `f.dualMap` is injective if and only if `f` is surjective -/
@[simp]
theorem dualMap_injective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Injective f.dualMap ↔ Function.Surjective f := by
  refine' ⟨_, fun h => dualMap_injective_of_surjective h⟩
  rw [← range_eq_top, ← ker_eq_bot]
  intro h
  apply FiniteDimensional.eq_top_of_finrank_eq
  rw [← finrank_eq_zero] at h
  rw [← add_zero (FiniteDimensional.finrank K <| LinearMap.range f), ← h, ←
    LinearMap.finrank_range_dualMap_eq_finrank_range, LinearMap.finrank_range_add_finrank_ker,
    Subspace.dual_finrank_eq]
#align linear_map.dual_map_injective_iff LinearMap.dualMap_injective_iff

/-- `f.dualMap` is bijective if and only if `f` is -/
@[simp]
theorem dualMap_bijective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Bijective f.dualMap ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, dualMap_surjective_iff, dualMap_injective_iff, and_comm]
#align linear_map.dual_map_bijective_iff LinearMap.dualMap_bijective_iff

end LinearMap

end FiniteDimensional

end VectorSpace

namespace TensorProduct

variable (R : Type _) (M : Type _) (N : Type _)

variable {ι κ : Type _}

variable [DecidableEq ι] [DecidableEq κ]

variable [Fintype ι] [Fintype κ]

open BigOperators

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N]

/-- The canonical linear map from `Dual M ⊗ Dual N` to `Dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `TensorProduct.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dualDistrib : Dual R M ⊗[R] Dual R N →ₗ[R] Dual R (M ⊗[R] N) :=
  compRight ↑(TensorProduct.lid R R) ∘ₗ homTensorHomMap R M N R R
#align tensor_product.dual_distrib TensorProduct.dualDistrib

variable {R M N}

@[simp]
theorem dualDistrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * g n :=
  rfl
#align tensor_product.dual_distrib_apply TensorProduct.dualDistrib_apply

end

variable {R M N}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N]

/-- An inverse to `dual_tensor_dual_map` given bases.
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  -- Porting note: ∑ (i) (j) does not seem to work; applyₗneeds a little help to unify
  ∑ i, ∑ j,
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ
      (applyₗ (R := R) (c j)) ∘ₗ (applyₗ (R := R) (b i)) ∘ₗ lcurry R M N R
#align tensor_product.dual_distrib_inv_of_basis TensorProduct.dualDistribInvOfBasis

@[simp]
theorem dualDistribInvOfBasis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M ⊗[R] N)) :
    dualDistribInvOfBasis b c f = ∑ i, ∑ j, f (b i ⊗ₜ c j) • b.dualBasis i ⊗ₜ c.dualBasis j := by
  simp [dualDistribInvOfBasis]
#align tensor_product.dual_distrib_inv_of_basis_apply TensorProduct.dualDistribInvOfBasis_apply

-- Porting note: introduced to help with timeout in dualDistribEquivOfBasis
theorem dualDistrib_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistrib R M N) (dualDistribInvOfBasis b c) = LinearMap.id := by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, ne_eq, LinearMap.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, coeFn_sum, Finset.sum_apply, smul_apply, LinearEquiv.coe_coe,
    map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]; simp
  all_goals { intros; simp [*] at * }

-- Porting note: introduced to help with timeout in dualDistribEquivOfBasis
theorem dualDistrib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistribInvOfBasis b c) (dualDistrib R M N) = LinearMap.id := by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    ne_eq, id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]; simp
  all_goals { intros; simp [*] at * }

/-- A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps!]
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) := by
  refine' LinearEquiv.ofLinear (dualDistrib R M N) (dualDistribInvOfBasis b c) _ _
  . exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  . exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _
#align tensor_product.dual_distrib_equiv_of_basis TensorProduct.dualDistribEquivOfBasis

variable (R M N)

variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

variable [Nontrivial R]

open Classical

/--
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
noncomputable def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)
#align tensor_product.dual_distrib_equiv TensorProduct.dualDistribEquiv

end TensorProduct

