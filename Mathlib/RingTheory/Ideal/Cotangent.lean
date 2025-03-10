/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.ideal.cotangent
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Torsion
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.RingTheory.Ideal.LocalRing

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `Ideal.cotangentEquivIdeal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/


namespace Ideal

-- Porting note: universes need to be explicit to avoid bad universe levels in `quotCotangent`
universe u v w

variable {R : Type u} {S : Type v} {S' : Type w} [CommRing R] [CommSemiring S] [Algebra S R]

variable [CommSemiring S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] (I : Ideal R)

-- Porting note: instances that were derived automatically need to be proved by hand (see below)
/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
def Cotangent : Type _ := I ⧸ (I • ⊤ : Submodule R I)
#align ideal.cotangent Ideal.Cotangent

instance : AddCommGroup I.Cotangent := by delta Cotangent; infer_instance

instance CotangentModule : Module (R ⧸ I) I.Cotangent := by delta Cotangent; infer_instance

instance : Inhabited I.Cotangent := ⟨0⟩

instance Cotangent.moduleOfTower : Module S I.Cotangent :=
  Submodule.Quotient.module' _
#align ideal.cotangent.module_of_tower Ideal.Cotangent.moduleOfTower

instance : IsScalarTower S S' I.Cotangent := by
  delta Cotangent
  constructor
  intro s s' x
  rw [← @IsScalarTower.algebraMap_smul S' R, ← @IsScalarTower.algebraMap_smul S' R, ← smul_assoc, ←
    IsScalarTower.toAlgHom_apply S S' R, map_smul]
  rfl

instance [IsNoetherian R I] : IsNoetherian R I.Cotangent := by delta Cotangent; infer_instance

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps!] --  (config := lemmasOnly) apply -- Porting note: this option does not exist anymore
def toCotangent : I →ₗ[R] I.Cotangent := Submodule.mkQ _
#align ideal.to_cotangent Ideal.toCotangent

theorem map_toCotangent_ker : I.toCotangent.ker.map I.subtype = I ^ 2 := by
  rw [Ideal.toCotangent, Submodule.ker_mkQ, pow_two, Submodule.map_smul'' I ⊤ (Submodule.subtype I),
    Algebra.id.smul_eq_mul, Submodule.map_subtype_top]

#align ideal.map_to_cotangent_ker Ideal.map_toCotangent_ker

theorem mem_toCotangent_ker {x : I} : x ∈ LinearMap.ker I.toCotangent ↔ (x : R) ∈ I ^ 2 := by
  rw [← I.map_toCotangent_ker]
  simp
#align ideal.mem_to_cotangent_ker Ideal.mem_toCotangent_ker

theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 := by
  rw [← sub_eq_zero]
  exact I.mem_toCotangent_ker
#align ideal.to_cotangent_eq Ideal.toCotangent_eq

theorem toCotangent_eq_zero (x : I) : I.toCotangent x = 0 ↔ (x : R) ∈ I ^ 2 := I.mem_toCotangent_ker
#align ideal.to_cotangent_eq_zero Ideal.toCotangent_eq_zero

theorem toCotangent_surjective : Function.Surjective I.toCotangent := Submodule.mkQ_surjective _
#align ideal.to_cotangent_surjective Ideal.toCotangent_surjective

theorem toCotangent_range : LinearMap.range I.toCotangent = ⊤ := Submodule.range_mkQ _
#align ideal.to_cotangent_range Ideal.toCotangent_range

theorem cotangent_subsingleton_iff : Subsingleton I.Cotangent ↔ IsIdempotentElem I := by
  constructor
  · intro H
    refine' (pow_two I).symm.trans (le_antisymm (Ideal.pow_le_self two_ne_zero) _)
    exact fun x hx => (I.toCotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  · exact fun e =>
      ⟨fun x y =>
        Quotient.inductionOn₂' x y fun x y =>
          I.toCotangent_eq.mpr <| ((pow_two I).trans e).symm ▸ I.sub_mem x.prop y.prop⟩
#align ideal.cotangent_subsingleton_iff Ideal.cotangent_subsingleton_iff

/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
def cotangentToQuotientSquare : I.Cotangent →ₗ[R] R ⧸ I ^ 2 :=
  Submodule.mapQ (I • ⊤) (I ^ 2) I.subtype
    (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
        Submodule.range_subtype, smul_eq_mul, pow_two] )
#align ideal.cotangent_to_quotient_square Ideal.cotangentToQuotientSquare

theorem to_quotient_square_comp_toCotangent :
    I.cotangentToQuotientSquare.comp I.toCotangent = (I ^ 2).mkQ.comp (Submodule.subtype I) :=
  LinearMap.ext fun _ => rfl
#align ideal.to_quotient_square_comp_to_cotangent Ideal.to_quotient_square_comp_toCotangent

-- @[simp] -- Porting note: not in simpNF
theorem toCotangent_to_quotient_square (x : I) :
    I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkQ x := rfl
#align ideal.to_cotangent_to_quotient_square Ideal.toCotangent_to_quotient_square

/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
def cotangentIdeal (I : Ideal R) : Ideal (R ⧸ I ^ 2) := by
  haveI : @RingHomSurjective R (R ⧸ I ^ 2) _ _ _ := ⟨Ideal.Quotient.mk_surjective⟩
  let rq := Quotient.mk (I ^ 2)
  exact Submodule.map rq.toSemilinearMap I
#align ideal.cotangent_ideal Ideal.cotangentIdeal

theorem cotangentIdeal_square (I : Ideal R) : I.cotangentIdeal ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two I.cotangentIdeal, ← smul_eq_mul]
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero, pow_two]; exact Ideal.mul_mem_mul hx hy
  · intro x y hx hy; exact add_mem hx hy
#align ideal.cotangent_ideal_square Ideal.cotangentIdeal_square

theorem to_quotient_square_range :
    LinearMap.range I.cotangentToQuotientSquare = I.cotangentIdeal.restrictScalars R := by
  trans LinearMap.range (I.cotangentToQuotientSquare.comp I.toCotangent)
  · rw [LinearMap.range_comp, I.toCotangent_range, Submodule.map_top]
  · rw [to_quotient_square_comp_toCotangent, LinearMap.range_comp, I.range_subtype]; ext; rfl
#align ideal.to_quotient_square_range Ideal.to_quotient_square_range

/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
noncomputable def cotangentEquivIdeal : I.Cotangent ≃ₗ[R] I.cotangentIdeal := by
  refine
  { LinearMap.codRestrict (I.cotangentIdeal.restrictScalars R) I.cotangentToQuotientSquare
      fun x => by { rw [← to_quotient_square_range]; exact LinearMap.mem_range_self _ _ },
    Equiv.ofBijective _ ⟨?_, ?_⟩ with
  }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective y
    rw [I.toCotangent_eq]
    dsimp only [toCotangent_to_quotient_square, Submodule.mkQ_apply] at e
    rwa [Submodule.Quotient.eq] at e
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨I.toCotangent ⟨x, hx⟩, Subtype.ext rfl⟩
#align ideal.cotangent_equiv_ideal Ideal.cotangentEquivIdeal

@[simp]
theorem cotangentEquivIdeal_apply (x : I.Cotangent) :
    ↑(I.cotangentEquivIdeal x) = I.cotangentToQuotientSquare x := rfl
#align ideal.cotangent_equiv_ideal_apply Ideal.cotangentEquivIdeal_apply

theorem cotangentEquivIdeal_symm_apply (x : R) (hx : x ∈ I) :
    I.cotangentEquivIdeal.symm ⟨(I ^ 2).mkQ x, Submodule.mem_map_of_mem hx⟩ =
      I.toCotangent ⟨x, hx⟩ := by
  apply I.cotangentEquivIdeal.injective
  rw [I.cotangentEquivIdeal.apply_symm_apply]
  ext
  rfl
#align ideal.cotangent_equiv_ideal_symm_apply Ideal.cotangentEquivIdeal_symm_apply

variable {A B : Type _} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The lift of `f : A →ₐ[R] B` to `A ⧸ J ^ 2 →ₐ[R] B` with `J` being the kernel of `f`. -/
def _root_.AlgHom.kerSquareLift (f : A →ₐ[R] B) : A ⧸ RingHom.ker f.toRingHom ^ 2 →ₐ[R] B := by
  refine { Ideal.Quotient.lift (RingHom.ker f.toRingHom ^ 2) f.toRingHom ?_ with commutes' := ?_ }
  · intro a ha; exact Ideal.pow_le_self two_ne_zero ha
  · intro r;
    rw [IsScalarTower.algebraMap_apply R A, RingHom.toFun_eq_coe, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.lift_mk]
    exact f.map_algebraMap r
#align alg_hom.ker_square_lift AlgHom.kerSquareLift

theorem _root_.AlgHom.ker_ker_sqare_lift (f : A →ₐ[R] B) :
    RingHom.ker f.kerSquareLift.toRingHom = f.toRingHom.ker.cotangentIdeal := by
  apply le_antisymm
  · intro x hx; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hx
#align alg_hom.ker_ker_sqare_lift AlgHom.ker_ker_sqare_lift

/-- The quotient ring of `I ⧸ I ^ 2` is `R ⧸ I`. -/
def quotCotangent : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I := by
  refine (Ideal.quotEquivOfEq (Ideal.map_eq_submodule_map _ _).symm).trans ?_
  refine (DoubleQuot.quotQuotEquivQuotSup _ _).trans ?_
  exact Ideal.quotEquivOfEq (sup_eq_right.mpr <| Ideal.pow_le_self two_ne_zero)
#align ideal.quot_cotangent Ideal.quotCotangent

end Ideal

namespace LocalRing

variable (R : Type _) [CommRing R] [LocalRing R]

/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
@[reducible]
def CotangentSpace : Type _ := (maximalIdeal R).Cotangent
#align local_ring.cotangent_space LocalRing.CotangentSpace

instance : Module (ResidueField R) (CotangentSpace R) := Ideal.CotangentModule _

instance : IsScalarTower R (ResidueField R) (CotangentSpace R) :=
  Module.IsTorsionBySet.isScalarTower _

instance [IsNoetherianRing R] : FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  Module.Finite.of_restrictScalars_finite R _ _

end LocalRing
