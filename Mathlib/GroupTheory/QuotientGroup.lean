/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.

! This file was ported from Lean 3 source module group_theory.quotient_group
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.GroupTheory.Congruence
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Pointwise

/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main definitions

* `mk'`: the canonical group homomorphism `G →* G/N` given a normal subgroup `N` of `G`.
* `lift φ`: the group homomorphism `G/N →* H` given a group homomorphism `φ : G →* H` such that
  `N ⊆ ker φ`.
* `map f`: the group homomorphism `G/N →* H/M` given a group homomorphism `f : G →* H` such that
  `N ⊆ f⁻¹(M)`.

## Main statements

* `QuotientGroup.quotientKerEquivRange`: Noether's first isomorphism theorem, an explicit
  isomorphism `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `QuotientGroup.quotientInfEquivProdNormalQuotient`: Noether's second isomorphism theorem, an
  explicit isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H` and a normal subgroup
  `N` of a group `G`.
* `QuotientGroup.quotientQuotientEquivQuotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / N) / (M / N)` and `G / M`, where `N ≤ M`.

## Tags

isomorphism theorems, quotient groups
-/


open Function

universe u v

namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]

/-- The congruence relation generated by a normal subgroup. -/
@[to_additive "The additive congruence relation generated by a normal additive subgroup."]
protected def con : Con G where
  toSetoid := leftRel N
  mul' := @fun a b c d hab hcd => by
    rw [leftRel_eq] at hab hcd ⊢
    dsimp only
    calc
      (a * c)⁻¹ * (b * d) = c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ * (c⁻¹ * d) :=
        by simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      _ ∈ N := N.mul_mem (nN.conj_mem _ hab _) hcd
#align quotient_group.con QuotientGroup.con
#align quotient_add_group.con QuotientAddGroup.con

@[to_additive]
instance Quotient.group : Group (G ⧸ N) :=
  (QuotientGroup.con N).group
#align quotient_group.quotient.group QuotientGroup.Quotient.group
#align quotient_add_group.quotient.add_group QuotientAddGroup.Quotient.addGroup

/-- The group homomorphism from `G` to `G/N`. -/
@[to_additive "The additive group homomorphism from `G` to `G/N`."]
def mk' : G →* G ⧸ N :=
  MonoidHom.mk' QuotientGroup.mk fun _ _ => rfl
#align quotient_group.mk' QuotientGroup.mk'
#align quotient_add_group.mk' QuotientAddGroup.mk'

@[to_additive (attr := simp)]
theorem coe_mk' : (mk' N : G → G ⧸ N) = mk :=
  rfl
#align quotient_group.coe_mk' QuotientGroup.coe_mk'
#align quotient_add_group.coe_mk' QuotientAddGroup.coe_mk'

@[to_additive (attr := simp)]
theorem mk'_apply (x : G) : mk' N x = x :=
  rfl
#align quotient_group.mk'_apply QuotientGroup.mk'_apply
#align quotient_add_group.mk'_apply QuotientAddGroup.mk'_apply

@[to_additive]
theorem mk'_surjective : Surjective <| mk' N :=
  @mk_surjective _ _ N
#align quotient_group.mk'_surjective QuotientGroup.mk'_surjective
#align quotient_add_group.mk'_surjective QuotientAddGroup.mk'_surjective

@[to_additive]
theorem mk'_eq_mk' {x y : G} : mk' N x = mk' N y ↔ ∃ z ∈ N, x * z = y :=
  QuotientGroup.eq'.trans <| by
    simp only [← _root_.eq_inv_mul_iff_mul_eq, exists_prop, exists_eq_right]
#align quotient_group.mk'_eq_mk' QuotientGroup.mk'_eq_mk'
#align quotient_add_group.mk'_eq_mk' QuotientAddGroup.mk'_eq_mk'

/-- Two `MonoidHom`s from a quotient group are equal if their compositions with
`QuotientGroup.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext 1100) "Two `AddMonoidHoms`s from an additive quotient group are equal if
 their compositions with `AddQuotientGroup.mk'` are equal.

 See note [partially-applied ext lemmas]. "]
theorem monoidHom_ext ⦃f g : G ⧸ N →* H⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| (FunLike.congr_fun h : _)
#align quotient_group.monoid_hom_ext QuotientGroup.monoidHom_ext
#align quotient_add_group.add_monoid_hom_ext QuotientAddGroup.addMonoidHom_ext

@[to_additive (attr := simp)]
theorem eq_one_iff {N : Subgroup G} [nN : N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x ∈ N := by
  refine' QuotientGroup.eq.trans _
  rw [mul_one, Subgroup.inv_mem_iff]
#align quotient_group.eq_one_iff QuotientGroup.eq_one_iff
#align quotient_add_group.eq_zero_iff QuotientAddGroup.eq_zero_iff

@[to_additive (attr := simp)]
theorem ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G →* G ⧸ N) = N :=
  Subgroup.ext eq_one_iff
#align quotient_group.ker_mk QuotientGroup.ker_mk'
#align quotient_add_group.ker_mk QuotientAddGroup.ker_mk'
-- porting note: I think this is misnamed without the prime

@[to_additive]
theorem eq_iff_div_mem {N : Subgroup G} [nN : N.Normal] {x y : G} :
    (x : G ⧸ N) = y ↔ x / y ∈ N := by
  refine' eq_comm.trans (QuotientGroup.eq.trans _)
  rw [nN.mem_comm_iff, div_eq_mul_inv]
#align quotient_group.eq_iff_div_mem QuotientGroup.eq_iff_div_mem
#align quotient_add_group.eq_iff_sub_mem QuotientAddGroup.eq_iff_sub_mem

-- for commutative groups we don't need normality assumption

@[to_additive]
instance Quotient.commGroup {G : Type _} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) :=
  { @QuotientGroup.Quotient.group _ _ N N.normal_of_comm with
    mul_comm := fun a b => Quotient.inductionOn₂' a b fun a b => congr_arg mk (mul_comm a b) }
#align quotient_group.quotient.comm_group QuotientGroup.Quotient.commGroup
#align quotient_add_group.quotient.add_comm_group QuotientAddGroup.Quotient.addCommGroup

local notation " Q " => G ⧸ N

@[to_additive (attr := simp)]
theorem mk_one : ((1 : G) : Q ) = 1 :=
  rfl
#align quotient_group.coe_one QuotientGroup.mk_one
#align quotient_add_group.coe_zero QuotientAddGroup.mk_zero

@[to_additive (attr := simp)]
theorem mk_mul (a b : G) : ((a * b : G) : Q ) = a * b :=
  rfl
#align quotient_group.coe_mul QuotientGroup.mk_mul
#align quotient_add_group.coe_add QuotientAddGroup.mk_add

@[to_additive (attr := simp)]
theorem mk_inv (a : G) : ((a⁻¹ : G) : Q ) = (a : Q)⁻¹ :=
  rfl
#align quotient_group.coe_inv QuotientGroup.mk_inv
#align quotient_add_group.coe_neg QuotientAddGroup.mk_neg

@[to_additive (attr := simp)]
theorem mk_div (a b : G) : ((a / b : G) : Q ) = a / b :=
  rfl
#align quotient_group.coe_div QuotientGroup.mk_div
#align quotient_add_group.coe_sub QuotientAddGroup.mk_sub

@[to_additive (attr := simp)]
theorem mk_pow (a : G) (n : ℕ) : ((a ^ n : G) : Q ) = (a : Q) ^ n :=
  rfl
#align quotient_group.coe_pow QuotientGroup.mk_pow
#align quotient_add_group.coe_nsmul QuotientAddGroup.mk_nsmul

@[to_additive (attr := simp)]
theorem mk_zpow (a : G) (n : ℤ) : ((a ^ n : G) : Q ) = (a : Q) ^ n :=
  rfl
#align quotient_group.coe_zpow QuotientGroup.mk_zpow
#align quotient_add_group.coe_zsmul QuotientAddGroup.mk_zsmul

/-- A group homomorphism `φ : G →* H` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* H`. -/
@[to_additive "An `AddGroup` homomorphism `φ : G →+ H` with `N ⊆ ker(φ)` descends (i.e. `lift`s)
 to a group homomorphism `G/N →* H`."]
def lift (φ : G →* H) (HN : ∀ x ∈ N, φ x = 1) : Q →* H :=
  (QuotientGroup.con N).lift φ fun x y h => by
    simp only [QuotientGroup.con, leftRel_apply, Con.rel_mk] at h
    rw [Con.ker_rel]
    calc
      φ x = φ (y * (x⁻¹ * y)⁻¹) := by rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
      _ = φ y := by rw [φ.map_mul, HN _ (N.inv_mem h), mul_one]
#align quotient_group.lift QuotientGroup.lift
#align quotient_add_group.lift QuotientAddGroup.lift

@[to_additive (attr := simp)]
theorem lift_mk {φ : G →* H} (HN : ∀ x ∈ N, φ x = 1) (g : G) : lift N φ HN (g : Q ) = φ g :=
  rfl
#align quotient_group.lift_mk QuotientGroup.lift_mk
#align quotient_add_group.lift_mk QuotientAddGroup.lift_mk

@[to_additive (attr := simp)]
theorem lift_mk' {φ : G →* H} (HN : ∀ x ∈ N, φ x = 1) (g : G) : lift N φ HN (mk g : Q ) = φ g :=
  rfl
-- TODO: replace `mk` with  `mk'`)
#align quotient_group.lift_mk' QuotientGroup.lift_mk'
#align quotient_add_group.lift_mk' QuotientAddGroup.lift_mk'

@[to_additive (attr := simp)]
theorem lift_quot_mk {φ : G →* H} (HN : ∀ x ∈ N, φ x = 1) (g : G) :
    lift N φ HN (Quot.mk _ g : Q ) = φ g :=
  rfl
#align quotient_group.lift_quot_mk QuotientGroup.lift_quot_mk
#align quotient_add_group.lift_quot_mk QuotientAddGroup.lift_quot_mk

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
@[to_additive
      "An `AddGroup` homomorphism `f : G →+ H` induces a map `G/N →+ H/M` if `N ⊆ f⁻¹(M)`."]
def map (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) : G ⧸ N →* H ⧸ M := by
  refine' QuotientGroup.lift N ((mk' M).comp f) _
  intro x hx
  refine' QuotientGroup.eq.2 _
  rw [mul_one, Subgroup.inv_mem_iff]
  exact h hx
#align quotient_group.map QuotientGroup.map
#align quotient_add_group.map QuotientAddGroup.map

@[to_additive (attr := simp)]
theorem map_mk (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
    map N M f h ↑x = ↑(f x) :=
  rfl
#align quotient_group.map_coe QuotientGroup.map_mk
#align quotient_add_group.map_coe QuotientAddGroup.map_mk

@[to_additive]
theorem map_mk' (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
    map N M f h (mk' _ x) = ↑(f x) :=
  rfl
#align quotient_group.map_mk' QuotientGroup.map_mk'
#align quotient_add_group.map_mk' QuotientAddGroup.map_mk'

@[to_additive]
theorem map_id_apply (h : N ≤ Subgroup.comap (MonoidHom.id _) N := (Subgroup.comap_id N).le) (x) :
    map N N (MonoidHom.id _) h x = x :=
  induction_on' x fun _x => rfl
#align quotient_group.map_id_apply QuotientGroup.map_id_apply
#align quotient_add_group.map_id_apply QuotientAddGroup.map_id_apply

@[to_additive (attr := simp)]
theorem map_id (h : N ≤ Subgroup.comap (MonoidHom.id _) N := (Subgroup.comap_id N).le) :
    map N N (MonoidHom.id _) h = MonoidHom.id _ :=
  MonoidHom.ext (map_id_apply N h)
#align quotient_group.map_id QuotientGroup.map_id
#align quotient_add_group.map_id QuotientAddGroup.map_id

@[to_additive (attr := simp)]
theorem map_map {I : Type _} [Group I] (M : Subgroup H) (O : Subgroup I) [M.Normal] [O.Normal]
    (f : G →* H) (g : H →* I) (hf : N ≤ Subgroup.comap f M) (hg : M ≤ Subgroup.comap g O)
    (hgf : N ≤ Subgroup.comap (g.comp f) O :=
      hf.trans ((Subgroup.comap_mono hg).trans_eq (Subgroup.comap_comap _ _ _)))
    (x : G ⧸ N) : map M O g hg (map N M f hf x) = map N O (g.comp f) hgf x := by
  refine' induction_on' x fun x => _
  simp only [map_mk, MonoidHom.comp_apply]
#align quotient_group.map_map QuotientGroup.map_map
#align quotient_add_group.map_map QuotientAddGroup.map_map

@[to_additive (attr := simp)]
theorem map_comp_map {I : Type _} [Group I] (M : Subgroup H) (O : Subgroup I) [M.Normal] [O.Normal]
    (f : G →* H) (g : H →* I) (hf : N ≤ Subgroup.comap f M) (hg : M ≤ Subgroup.comap g O)
    (hgf : N ≤ Subgroup.comap (g.comp f) O :=
      hf.trans ((Subgroup.comap_mono hg).trans_eq (Subgroup.comap_comap _ _ _))) :
    (map M O g hg).comp (map N M f hf) = map N O (g.comp f) hgf :=
  MonoidHom.ext (map_map N M O f g hf hg hgf)
#align quotient_group.map_comp_map QuotientGroup.map_comp_map
#align quotient_add_group.map_comp_map QuotientAddGroup.map_comp_map

section congr

variable (G' : Subgroup G) (H' : Subgroup H) [Subgroup.Normal G'] [Subgroup.Normal H']

/-- `QuotientGroup.congr` lifts the isomorphism `e : G ≃ H` to `G ⧸ G' ≃ H ⧸ H'`,
given that `e` maps `G` to `H`. -/
@[to_additive "`QuotientAddGroup.congr` lifts the isomorphism `e : G ≃ H` to `G ⧸ G' ≃ H ⧸ H'`,
 given that `e` maps `G` to `H`."]
def congr (e : G ≃* H) (he : G'.map e = H') : G ⧸ G' ≃* H ⧸ H' :=
  { map G' H' e (he ▸ G'.le_comap_map (e : G →* H)) with
    toFun := map G' H' e (he ▸ G'.le_comap_map (e : G →* H))
    invFun := map H' G' e.symm (he ▸ (G'.map_equiv_eq_comap_symm e).le)
    left_inv := fun x => by
      rw [map_map G' H' G' e e.symm (he ▸ G'.le_comap_map (e : G →* H))
        (he ▸ (G'.map_equiv_eq_comap_symm e).le)]
      simp only [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
        MulEquiv.coe_monoidHom_refl, map_id_apply]
    right_inv := fun x => by
      rw [map_map H' G' H' e.symm e (he ▸ (G'.map_equiv_eq_comap_symm e).le)
        (he ▸ G'.le_comap_map (e : G →* H)) ]
      simp only [← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
        MulEquiv.coe_monoidHom_refl, map_id_apply] }
#align quotient_group.congr QuotientGroup.congr
#align quotient_add_group.congr QuotientAddGroup.congr

@[simp]
theorem congr_mk (e : G ≃* H) (he : G'.map ↑e = H') (x) : congr G' H' e he (mk x) = e x :=
  rfl
#align quotient_group.congr_mk QuotientGroup.congr_mk

theorem congr_mk' (e : G ≃* H) (he : G'.map ↑e = H') (x) :
    congr G' H' e he (mk' G' x) = mk' H' (e x) :=
  rfl
#align quotient_group.congr_mk' QuotientGroup.congr_mk'

@[simp]
theorem congr_apply (e : G ≃* H) (he : G'.map ↑e = H') (x : G) :
    congr G' H' e he x = mk' H' (e x) :=
  rfl
#align quotient_group.congr_apply QuotientGroup.congr_apply

@[simp]
theorem congr_refl (he : G'.map (MulEquiv.refl G : G →* G) = G' := Subgroup.map_id G') :
    congr G' G' (MulEquiv.refl G) he = MulEquiv.refl (G ⧸ G') := by
  ext ⟨x⟩
  rfl
#align quotient_group.congr_refl QuotientGroup.congr_refl

@[simp]
theorem congr_symm (e : G ≃* H) (he : G'.map ↑e = H') :
    (congr G' H' e he).symm = congr H' G' e.symm ((Subgroup.map_symm_eq_iff_map_eq _).mpr he) :=
  rfl
#align quotient_group.congr_symm QuotientGroup.congr_symm

end congr

variable (φ : G →* H)

open MonoidHom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive "The induced map from the quotient by the kernel to the codomain."]
def kerLift : G ⧸ ker φ →* H :=
  lift _ φ fun _g => φ.mem_ker.mp
#align quotient_group.ker_lift QuotientGroup.kerLift
#align quotient_add_group.ker_lift QuotientAddGroup.kerLift

@[to_additive (attr := simp)]
theorem kerLift_mk (g : G) : (kerLift φ) g = φ g :=
  lift_mk _ _ _
#align quotient_group.ker_lift_mk QuotientGroup.kerLift_mk
#align quotient_add_group.ker_lift_mk QuotientAddGroup.kerLift_mk

@[to_additive (attr := simp)]
theorem kerLift_mk' (g : G) : (kerLift φ) (mk g) = φ g :=
  lift_mk' _ _ _
#align quotient_group.ker_lift_mk' QuotientGroup.kerLift_mk'
#align quotient_add_group.ker_lift_mk' QuotientAddGroup.kerLift_mk'

@[to_additive]
theorem kerLift_injective : Injective (kerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
    Quotient.sound' <| by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_self]
#align quotient_group.ker_lift_injective QuotientGroup.kerLift_injective
#align quotient_add_group.ker_lift_injective QuotientAddGroup.kerLift_injective

-- Note that `ker φ` isn't definitionally `ker (φ.rangeRestrict)`
-- so there is a bit of annoying code duplication here
/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive "The induced map from the quotient by the kernel to the range."]
def rangeKerLift : G ⧸ ker φ →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => (mem_ker _).mp <| by rwa [ker_rangeRestrict]
#align quotient_group.range_ker_lift QuotientGroup.rangeKerLift
#align quotient_add_group.range_ker_lift QuotientAddGroup.rangeKerLift

@[to_additive]
theorem rangeKerLift_injective : Injective (rangeKerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
    Quotient.sound' <| by
      rw [leftRel_apply, ← ker_rangeRestrict, mem_ker, φ.rangeRestrict.map_mul, ← h,
        φ.rangeRestrict.map_inv, inv_mul_self]
#align quotient_group.range_ker_lift_injective QuotientGroup.rangeKerLift_injective
#align quotient_add_group.range_ker_lift_injective QuotientAddGroup.rangeKerLift_injective

@[to_additive]
theorem rangeKerLift_surjective : Surjective (rangeKerLift φ) := by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl
#align quotient_group.range_ker_lift_surjective QuotientGroup.rangeKerLift_surjective
#align quotient_add_group.range_ker_lift_surjective QuotientAddGroup.rangeKerLift_surjective

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive "The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`."]
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩
#align quotient_group.quotient_ker_equiv_range QuotientGroup.quotientKerEquivRange
#align quotient_add_group.quotient_ker_equiv_range QuotientAddGroup.quotientKerEquivRange

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive (attr := simps) "The canonical isomorphism `G/(ker φ) ≃+ H` induced by a homomorphism
`φ : G →+ H` with a right inverse `ψ : H → G`."]
def quotientKerEquivOfRightInverse (ψ : H → G) (hφ : RightInverse ψ φ) : G ⧸ ker φ ≃* H :=
  { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk', hφ])
    right_inv := hφ }
#align quotient_group.quotient_ker_equiv_of_right_inverse QuotientGroup.quotientKerEquivOfRightInverse
#align quotient_add_group.quotient_ker_equiv_of_right_inverse QuotientAddGroup.quotientKerEquivOfRightInverse

/-- The canonical isomorphism `G/⊥ ≃* G`. -/
@[to_additive (attr := simps!) "The canonical isomorphism `G/⊥ ≃+ G`."]
def quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G :=
  quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl
#align quotient_group.quotient_bot QuotientGroup.quotientBot
#align quotient_add_group.quotient_bot QuotientAddGroup.quotientBot

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `QuotientGroup.quotientKerEquivOfRightInverse`.
-/
@[to_additive "The canonical isomorphism `G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.
For a `computable` version, see `QuotientAddGroup.quotientKerEquivOfRightInverse`."]
noncomputable def quotientKerEquivOfSurjective (hφ : Surjective φ) : G ⧸ ker φ ≃* H :=
  quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec
#align quotient_group.quotient_ker_equiv_of_surjective QuotientGroup.quotientKerEquivOfSurjective
#align quotient_add_group.quotient_ker_equiv_of_surjective QuotientAddGroup.quotientKerEquivOfSurjective

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive "If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic."]
def quotientMulEquivOfEq {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N :=
  { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }
#align quotient_group.quotient_mul_equiv_of_eq QuotientGroup.quotientMulEquivOfEq
#align quotient_add_group.quotient_add_equiv_of_eq QuotientAddGroup.quotientAddEquivOfEq

@[to_additive (attr := simp)]
theorem quotientMulEquivOfEq_mk {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G) :
    QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl
#align quotient_group.quotient_mul_equiv_of_eq_mk QuotientGroup.quotientMulEquivOfEq_mk
#align quotient_add_group.quotient_add_equiv_of_eq_mk QuotientAddGroup.quotientAddEquivOfEq_mk

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[to_additive "Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`, then there is a map
`A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions."]
def quotientMapSubgroupOfOfLe {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) :
    A ⧸ A'.subgroupOf A →* B ⧸ B'.subgroupOf B :=
  map _ _ (Subgroup.inclusion h) <| Subgroup.comap_mono h'
#align quotient_group.quotient_map_subgroup_of_of_le QuotientGroup.quotientMapSubgroupOfOfLe
#align quotient_add_group.quotient_map_add_subgroup_of_of_le QuotientAddGroup.quotientMapAddSubgroupOfOfLe

@[to_additive (attr := simp)]
theorem quotientMapSubgroupOfOfLe_mk {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) (x : A) :
    quotientMapSubgroupOfOfLe h' h x = ↑(Subgroup.inclusion h x : B) :=
  rfl
#align quotient_group.quotient_map_subgroup_of_of_le_coe QuotientGroup.quotientMapSubgroupOfOfLe_mk
#align quotient_add_group.quotient_map_add_subgroup_of_of_le_coe QuotientAddGroup.quotientMapAddSubgroupOfOfLe_mk

/-- Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.subgroupOf A : Subgroup A)` depends on on `A`.
-/
@[to_additive "Let `A', A, B', B` be subgroups of `G`. If `A' = B'` and `A = B`, then the quotients
`A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic. Applying this equiv is nicer than rewriting along
the equalities, since the type of `(A'.addSubgroupOf A : AddSubgroup A)` depends on on `A`. "]
def equivQuotientSubgroupOfOfEq {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
    [hBN : (B'.subgroupOf B).Normal] (h' : A' = B') (h : A = B) :
    A ⧸ A'.subgroupOf A ≃* B ⧸ B'.subgroupOf B :=
  MonoidHom.toMulEquiv (quotientMapSubgroupOfOfLe h'.le h.le) (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)
#align quotient_group.equiv_quotient_subgroup_of_of_eq QuotientGroup.equivQuotientSubgroupOfOfEq
#align quotient_add_group.equiv_quotient_add_subgroup_of_of_eq QuotientAddGroup.equivQuotientAddSubgroupOfOfEq

section ZPow

variable {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]

variable (f : A →* B) (g : B →* A) (e : A ≃* B) (d : B ≃* C) (n : ℤ)

/-- The map of quotients by powers of an integer induced by a group homomorphism. -/
@[to_additive "The map of quotients by multiples of an integer induced by an additive group
homomorphism."]
def homQuotientZPowOfHom :
    A ⧸ (zpowGroupHom n : A →* A).range →* B ⧸ (zpowGroupHom n : B →* B).range :=
  lift _ ((mk' _).comp f) fun g ⟨h, (hg : h ^ n = g)⟩ =>
    (eq_one_iff _).mpr ⟨f h, by
      simp only [← hg, map_zpow, zpowGroupHom_apply]⟩
#align quotient_group.hom_quotient_zpow_of_hom QuotientGroup.homQuotientZPowOfHom
#align quotient_add_group.hom_quotient_zsmul_of_hom QuotientAddGroup.homQuotientZSMulOfHom

@[to_additive (attr := simp)]
theorem homQuotientZPowOfHom_id : homQuotientZPowOfHom (MonoidHom.id A) n = MonoidHom.id _ :=
  monoidHom_ext _ rfl
#align quotient_group.hom_quotient_zpow_of_hom_id QuotientGroup.homQuotientZPowOfHom_id
#align quotient_add_group.hom_quotient_zsmul_of_hom_id QuotientAddGroup.homQuotientZSMulOfHom_id

@[to_additive (attr := simp)]
theorem homQuotientZPowOfHom_comp :
    homQuotientZPowOfHom (f.comp g) n =
      (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) :=
  monoidHom_ext _ rfl
#align quotient_group.hom_quotient_zpow_of_hom_comp QuotientGroup.homQuotientZPowOfHom_comp
#align quotient_add_group.hom_quotient_zsmul_of_hom_comp QuotientAddGroup.homQuotientZSMulOfHom_comp

@[to_additive (attr := simp)]
theorem homQuotientZPowOfHom_comp_of_rightInverse (i : Function.RightInverse g f) :
    (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) = MonoidHom.id _ :=
  monoidHom_ext _ <| MonoidHom.ext fun x => congrArg _ <| i x
#align quotient_group.hom_quotient_zpow_of_hom_comp_of_right_inverse QuotientGroup.homQuotientZPowOfHom_comp_of_rightInverse
#align quotient_add_group.hom_quotient_zsmul_of_hom_comp_of_right_inverse QuotientAddGroup.homQuotientZSMulOfHom_comp_of_rightInverse

/-- The equivalence of quotients by powers of an integer induced by a group isomorphism. -/
@[to_additive "The equivalence of quotients by multiples of an integer induced by an additive group
isomorphism."]
def equivQuotientZPowOfEquiv :
    A ⧸ (zpowGroupHom n : A →* A).range ≃* B ⧸ (zpowGroupHom n : B →* B).range :=
  MonoidHom.toMulEquiv _ _
    (homQuotientZPowOfHom_comp_of_rightInverse (e.symm : B →* A) (e : A →* B) n e.left_inv)
    (homQuotientZPowOfHom_comp_of_rightInverse (e : A →* B) (e.symm : B →* A) n e.right_inv)
    -- porting note: had to explicitly coerce the `MulEquiv`s to `MonoidHom`s
#align quotient_group.equiv_quotient_zpow_of_equiv QuotientGroup.equivQuotientZPowOfEquiv
#align quotient_add_group.equiv_quotient_zsmul_of_equiv QuotientAddGroup.equivQuotientZSMulOfEquiv

@[to_additive (attr := simp)]
theorem equivQuotientZPowOfEquiv_refl :
    MulEquiv.refl (A ⧸ (zpowGroupHom n : A →* A).range) =
      equivQuotientZPowOfEquiv (MulEquiv.refl A) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl
#align quotient_group.equiv_quotient_zpow_of_equiv_refl QuotientGroup.equivQuotientZPowOfEquiv_refl
#align quotient_add_group.equiv_quotient_zsmul_of_equiv_refl QuotientAddGroup.equivQuotientZSMulOfEquiv_refl

@[to_additive (attr := simp)]
theorem equivQuotientZPowOfEquiv_symm :
    (equivQuotientZPowOfEquiv e n).symm = equivQuotientZPowOfEquiv e.symm n :=
  rfl
#align quotient_group.equiv_quotient_zpow_of_equiv_symm QuotientGroup.equivQuotientZPowOfEquiv_symm
#align quotient_add_group.equiv_quotient_zsmul_of_equiv_symm QuotientAddGroup.equivQuotientZSMulOfEquiv_symm

@[to_additive (attr := simp)]
theorem equivQuotientZPowOfEquiv_trans :
    (equivQuotientZPowOfEquiv e n).trans (equivQuotientZPowOfEquiv d n) =
      equivQuotientZPowOfEquiv (e.trans d) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl
#align quotient_group.equiv_quotient_zpow_of_equiv_trans QuotientGroup.equivQuotientZPowOfEquiv_trans
#align quotient_add_group.equiv_quotient_zsmul_of_equiv_trans QuotientAddGroup.equivQuotientZSMulOfEquiv_trans

end ZPow

section SndIsomorphismThm

open Subgroup

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`, where
`N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive "The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`, where
`N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`"]
noncomputable def quotientInfEquivProdNormalQuotient (H N : Subgroup G) [N.Normal] :
    H ⧸ N.subgroupOf H ≃* _ ⧸ N.subgroupOf (H ⊔ N) :=
  let
    φ :-- φ is the natural homomorphism H →* (HN)/N.
      H →*
      _ ⧸ N.subgroupOf (H ⊔ N) :=
    (mk' <| N.subgroupOf (H ⊔ N)).comp (inclusion le_sup_left)
  have φ_surjective : Surjective φ := fun x =>
    x.inductionOn' <| by
      rintro ⟨y, hy : y ∈ (H ⊔ N)⟩;
      rw [←SetLike.mem_coe] at hy
      rw [mul_normal H N] at hy
      rcases hy with ⟨h, n, hh, hn, rfl⟩
      use ⟨h, hh⟩
      let _ : Setoid ↑(H ⊔ N) :=
        (@leftRel ↑(H ⊔ N) (H ⊔ N : Subgroup G).toGroup (N.subgroupOf (H ⊔ N)))
      -- porting note: Lean couldn't find this automatically
      refine Quotient.eq.mpr ?_
      change Setoid.r _ _
      rw [leftRel_apply]
      change h⁻¹ * (h * n) ∈ N
      rwa [← mul_assoc, inv_mul_self, one_mul]
  (quotientMulEquivOfEq (by simp [← comap_ker])).trans (quotientKerEquivOfSurjective φ φ_surjective)
#align quotient_group.quotient_inf_equiv_prod_normal_quotient QuotientGroup.quotientInfEquivProdNormalQuotient
#align quotient_add_group.quotient_inf_equiv_sum_normal_quotient QuotientAddGroup.quotientInfEquivSumNormalQuotient

end SndIsomorphismThm

section ThirdIsoThm

variable (M : Subgroup G) [nM : M.Normal]

@[to_additive]
instance map_normal : (M.map (QuotientGroup.mk' N)).Normal :=
  nM.map _ mk_surjective
#align quotient_group.map_normal QuotientGroup.map_normal
#align quotient_add_group.map_normal QuotientAddGroup.map_normal

variable (h : N ≤ M)

/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive "The map from the third isomorphism theorem for additive groups:
`(A / N) / (M / N) → A / M`."]
def quotientQuotientEquivQuotientAux : (G ⧸ N) ⧸ M.map (mk' N) →* G ⧸ M :=
  lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)
#align quotient_group.quotient_quotient_equiv_quotient_aux QuotientGroup.quotientQuotientEquivQuotientAux
#align quotient_add_group.quotient_quotient_equiv_quotient_aux QuotientAddGroup.quotientQuotientEquivQuotientAux

@[to_additive (attr := simp)]
theorem quotientQuotientEquivQuotientAux_mk (x : G ⧸ N) :
    quotientQuotientEquivQuotientAux N M h x = QuotientGroup.map N M (MonoidHom.id G) h x :=
  QuotientGroup.lift_mk' _ _ x
#align quotient_group.quotient_quotient_equiv_quotient_aux_coe QuotientGroup.quotientQuotientEquivQuotientAux_mk
#align quotient_add_group.quotient_quotient_equiv_quotient_aux_coe QuotientAddGroup.quotientQuotientEquivQuotientAux_mk

@[to_additive]
theorem quotientQuotientEquivQuotientAux_mk_mk (x : G) :
    quotientQuotientEquivQuotientAux N M h (x : G ⧸ N) = x :=
  QuotientGroup.lift_mk' (M.map (mk' N)) _ x
#align quotient_group.quotient_quotient_equiv_quotient_aux_coe_coe QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
#align quotient_add_group.quotient_quotient_equiv_quotient_aux_coe_coe QuotientAddGroup.quotientQuotientEquivQuotientAux_mk_mk

/-- **Noether's third isomorphism theorem** for groups: `(G / N) / (M / N) ≃* G / M`. -/
@[to_additive
      "**Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃+ A / M`."]
def quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M :=
  MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)
#align quotient_group.quotient_quotient_equiv_quotient QuotientGroup.quotientQuotientEquivQuotient
#align quotient_add_group.quotient_quotient_equiv_quotient QuotientAddGroup.quotientQuotientEquivQuotient

end ThirdIsoThm

section trivial

@[to_additive]
theorem subsingleton_quotient_top : Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  dsimp [HasQuotient.Quotient, QuotientGroup.instHasQuotientSubgroup, Quotient]
  rw [leftRel_eq]
  exact Trunc.instSubsingletonTrunc
#align quotient_group.subsingleton_quotient_top QuotientGroup.subsingleton_quotient_top
#align quotient_add_group.subsingleton_quotient_top QuotientAddGroup.subsingleton_quotient_top

/-- If the quotient by a subgroup gives a singleton then the subgroup is the whole group. -/
@[to_additive "If the quotient by an additive subgroup gives a singleton then the additive subgroup
is the whole additive group."]
theorem subgroup_eq_top_of_subsingleton (H : Subgroup G) (h : Subsingleton (G ⧸ H)) : H = ⊤ :=
  top_unique fun x _ => by
    have this : 1⁻¹ * x ∈ H := QuotientGroup.eq.1 (Subsingleton.elim _ _)
    rwa [inv_one, one_mul] at this
#align quotient_group.subgroup_eq_top_of_subsingleton QuotientGroup.subgroup_eq_top_of_subsingleton
#align quotient_add_group.add_subgroup_eq_top_of_subsingleton QuotientAddGroup.addSubgroup_eq_top_of_subsingleton

end trivial

@[to_additive]
theorem comap_comap_center {H₁ : Subgroup G} [H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} [H₂.Normal] :
    ((Subgroup.center ((G ⧸ H₁) ⧸ H₂)).comap (mk' H₂)).comap (mk' H₁) =
      (Subgroup.center (G ⧸ H₂.comap (mk' H₁))).comap (mk' (H₂.comap (mk' H₁))) := by
  ext x
  simp only [mk'_apply, Subgroup.mem_comap, Subgroup.mem_center_iff, forall_mk, ← mk_mul,
    eq_iff_div_mem, mk_div]
#align quotient_group.comap_comap_center QuotientGroup.comap_comap_center
#align quotient_add_group.comap_comap_center QuotientAddGroup.comap_comap_center

end QuotientGroup

namespace Group

open Classical

open QuotientGroup Subgroup

variable {F G H : Type u} [Group F] [Group G] [Group H] [Fintype F] [Fintype H]

variable (f : F →* G) (g : G →* H)

/-- If `F` and `H` are finite such that `ker(G →* H) ≤ im(F →* G)`, then `G` is finite. -/
@[to_additive "If `F` and `H` are finite such that `ker(G →+ H) ≤ im(F →+ G)`, then `G` is finite."]
noncomputable def fintypeOfKerLeRange (h : g.ker ≤ f.range) : Fintype G :=
  @Fintype.ofEquiv _ _
    (@instFintypeProd _ _ (Fintype.ofInjective _ <| kerLift_injective g) <|
      Fintype.ofInjective _ <| inclusion_injective h)
    groupEquivQuotientProdSubgroup.symm
#align group.fintype_of_ker_le_range Group.fintypeOfKerLeRange
#align add_group.fintype_of_ker_le_range AddGroup.fintypeOfKerLeRange

/-- If `F` and `H` are finite such that `ker(G →* H) = im(F →* G)`, then `G` is finite. -/
@[to_additive "If `F` and `H` are finite such that `ker(G →+ H) = im(F →+ G)`, then `G` is finite."]
noncomputable def fintypeOfKerEqRange (h : g.ker = f.range) : Fintype G :=
  fintypeOfKerLeRange _ _ h.le
#align group.fintype_of_ker_eq_range Group.fintypeOfKerEqRange
#align add_group.fintype_of_ker_eq_range AddGroup.fintypeOfKerEqRange

/-- If `ker(G →* H)` and `H` are finite, then `G` is finite. -/
@[to_additive "If `ker(G →+ H)` and `H` are finite, then `G` is finite."]
noncomputable def fintypeOfKerOfCodom [Fintype g.ker] : Fintype G :=
  fintypeOfKerLeRange ((topEquiv : _ ≃* G).toMonoidHom.comp <| inclusion le_top) g fun x hx =>
    ⟨⟨x, hx⟩, rfl⟩
#align group.fintype_of_ker_of_codom Group.fintypeOfKerOfCodom
#align add_group.fintype_of_ker_of_codom AddGroup.fintypeOfKerOfCodom

/-- If `F` and `coker(F →* G)` are finite, then `G` is finite. -/
@[to_additive "If `F` and `coker(F →+ G)` are finite, then `G` is finite."]
noncomputable def fintypeOfDomOfCoker [Normal f.range] [Fintype <| G ⧸ f.range] : Fintype G :=
  fintypeOfKerLeRange _ (mk' f.range) fun x => (eq_one_iff x).mp
#align group.fintype_of_dom_of_coker Group.fintypeOfDomOfCoker
#align add_group.fintype_of_dom_of_coker AddGroup.fintypeOfDomOfCoker

end Group
