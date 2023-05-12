/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.sites.dense_subsite
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
set_option autoImplicit false -- TODO remove
-- TODO update module doc
/-!
# Dense subsites

We define `cover_dense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

We will primarily consider cover-dense functors that are also full, since this notion is in general
not well-behaved otherwise. Note that https://ncatlab.org/nlab/show/dense+sub-site indeed has a
weaker notion of cover-dense that loosens this requirement, but it would not have all the properties
we would need, and some sheafification would be needed for here and there.

## Main results

- `category_theory.cover_dense.presheaf_hom`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any presheaf `ℱ` and sheaf `ℱ'` on `D`, and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`,
  we may glue them together to obtain a morphism of presheaves `ℱ ⟶ ℱ'`.
- `category_theory.cover_dense.sheaf_iso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `category_theory.cover_dense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`, then `α` is an iso if
  `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting`:
  If `G : (C, J) ⥤ (D, K)` is fully-faithful, cover-lifting, cover-preserving, and cover-dense,
  then it will induce an equivalence of categories of sheaves valued in a complete category.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/


universe w v u

namespace CategoryTheory

variable {C : Type _} [Category C] {D : Type _} [Category D] {E : Type _} [Category E]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology E}

/-- An auxiliary structure that witnesses the fact that `f` factors through an image object of `G`.
-/
-- porting note: removed `@[nolint has_nonempty_instance]`
structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by aesop_cat
#align category_theory.presieve.cover_by_image_structure CategoryTheory.Presieve.CoverByImageStructure

restate_axiom Presieve.CoverByImageStructure.fac

-- TODO ask about `reassoc.1`
attribute [simp, reassoc] Presieve.CoverByImageStructure.fac

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `presieve.cover_by_image G U` is the presieve
of `U` consisting of those arrows that factor through images of `G`.
-/
def Presieve.coverByImage (G : C ⥤ D) (U : D) : Presieve U := fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)
#align category_theory.presieve.cover_by_image CategoryTheory.Presieve.coverByImage

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `sieve.cover_by_image G U` is the sieve of `U`
consisting of those arrows that factor through images of `G`.
-/
def Sieve.coverByImage (G : C ⥤ D) (U : D) : Sieve U :=
  ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩
#align category_theory.sieve.cover_by_image CategoryTheory.Sieve.coverByImage

theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩
#align category_theory.presieve.in_cover_by_image CategoryTheory.Presieve.in_coverByImage

/-- A functor `G : (C, J) ⥤ (D, K)` is called `cover_dense` if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
structure CoverDense (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  is_cover : ∀ U : D, Sieve.coverByImage G U ∈ K U
#align category_theory.cover_dense CategoryTheory.CoverDense

open Presieve Opposite

namespace CoverDense

variable {K}

variable {A : Type _} [Category A] {G : C ⥤ D} (H : CoverDense K G)

-- this is not marked with `@[ext]` because `H` can not be inferred from the type
theorem ext (H : CoverDense K G) (ℱ : SheafOfTypes K) (X : D) {s t : ℱ.val.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op s = ℱ.val.map f.op t) : s = t := by
  apply (ℱ.cond (Sieve.coverByImage G X) (H.is_cover X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]
#align category_theory.cover_dense.ext CategoryTheory.CoverDense.ext

theorem functorPullback_pushforward_covering [Full G] (H : CoverDense K G) {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X) := by
  refine' K.superset_covering _ (K.bind_covering T.property fun Y f _ => H.is_cover Y)
  rintro Y _ ⟨Z, _, f, hf, ⟨W, g, f', ⟨rfl⟩⟩, rfl⟩
  use W; use G.preimage (f' ≫ f); use g
  constructor
  · simpa using T.val.downward_closed hf f'
  · simp
#align category_theory.cover_dense.functor_pullback_pushforward_covering CategoryTheory.CoverDense.functorPullback_pushforward_covering

/-- (Implementation). Given an hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps!]
def homOver {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ ℱ ⋙ coyoneda.obj (op X) ⟶ G.op ⋙ (sheafOver ℱ' X).val :=
  whiskerRight α (coyoneda.obj (op X))
#align category_theory.cover_dense.hom_over CategoryTheory.CoverDense.homOver

/-- (Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps!]
def isoOver {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ (sheafOver ℱ X).val ≅ G.op ⋙ (sheafOver ℱ' X).val :=
  isoWhiskerRight α (coyoneda.obj (op X))
#align category_theory.cover_dense.iso_over CategoryTheory.CoverDense.isoOver

theorem sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT)
    (x : FamilyOfElements _ T) (hx) (t) (h : x.IsAmalgamation t) :
    t = (ℱ.cond X T hT).amalgamate x hx :=
  (ℱ.cond X T hT).isSeparatedFor x t _ h ((ℱ.cond X T hT).isAmalgamation hx)
#align category_theory.cover_dense.sheaf_eq_amalgamation CategoryTheory.CoverDense.sheaf_eq_amalgamation

-- porting note: removed `include H`

variable [Full G]

namespace Types

variable {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : SheafOfTypes.{v} K} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val)

/-
pushforward_family :
  Π {C : Type u_10} [_inst_1 : category C] {D : Type u_12} [_inst_2 : category D] {K : grothendieck_topology D}
  {G : C ⥤ D},
    cover_dense K G →
    Π [_inst_5 : full G] {ℱ : Dᵒᵖ ⥤ Type u_9} {ℱ' : SheafOfTypes K},
      (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) →
      Π {X : D}, ℱ.obj (op X) → family_of_elements ℱ'.val (cover_by_image G X)
-/
/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
-- porting note: removed `@[simp, nolint unused_arguments]`
noncomputable def pushforwardFamily {X} (x : ℱ.obj (op X)) :
    FamilyOfElements ℱ'.val (coverByImage G X) := fun _ _ hf =>
  ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x : _)
#align category_theory.cover_dense.types.pushforward_family CategoryTheory.CoverDense.Types.pushforwardFamily

--pp_extended_field_notation Quiver.Hom.op
pp_extended_field_notation Functor.op
pp_extended_field_notation Functor.preimage

/-- (Implementation). The `pushforward_family` defined is compatible. -/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) :
    (pushforwardFamily α x).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  apply H.ext
  intro Y f
  simp only [pushforwardFamily, ← FunctorToTypes.map_comp_apply, ← op_comp]
  change (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _ = (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _
  rw [← G.image_preimage (f ≫ g₁ ≫ _)]
  rw [← G.image_preimage (f ≫ g₂ ≫ _)]
  erw [← α.naturality (G.preimage _).op]
  erw [← α.naturality (G.preimage _).op]
  refine' congr_fun _ x
  /-
  3 ⊢ ℱ.map (nonempty.some h₁).map.op ≫ (G.op ⋙ ℱ).map (G.preimage (f ≫ g₁ ≫ (nonempty.some h₁).lift)).op ≫ α.app (op Y) = λ (x : ℱ.obj (op X)), (ℱ.map (nonempty.some h₂).map.op ≫ (G.op ⋙ ℱ).map (G.preimage (f ≫ g₂ ≫ (nonempty.some h₂).lift)).op ≫ α.app (op Y)) x
  -/
  simp only [Quiver.Hom.unop_op, Functor.comp_map, ← op_comp, ← Category.assoc, Functor.op_map, ←
    ℱ.map_comp, G.image_preimage]
  /-
  3 ⊢ ℱ.map (((f ≫ g₁) ≫ (nonempty.some h₁).lift) ≫ (nonempty.some h₁).map).op ≫ α.app (op Y) = ℱ.map (((f ≫ g₂) ≫ (nonempty.some h₂).lift) ≫ (nonempty.some h₂).map).op ≫ α.app (op Y)
  4 ⊢ (ℱ.map (Quiver.Hom.op (Nonempty.some h₁).map) ≫ ℱ.map (Quiver.Hom.op ((f ≫ g₁) ≫ (Nonempty.some h₁).lift))) ≫
    α.app (op Y) =
  (ℱ.map (Quiver.Hom.op (Nonempty.some h₂).map) ≫ ℱ.map (Quiver.Hom.op ((f ≫ g₂) ≫ (Nonempty.some h₂).lift))) ≫
    α.app (op Y)-/
  congr 3
  simp [e]
#align category_theory.cover_dense.types.pushforward_family_compatible CategoryTheory.CoverDense.Types.pushforwardFamily_compatible

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforward_family`. -/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := fun x =>
  (ℱ'.cond _ (H.is_cover X)).amalgamate (pushforwardFamily α x)
    (pushforwardFamily_compatible H α x)
#align category_theory.cover_dense.types.app_hom CategoryTheory.CoverDense.Types.appHom

@[simp]
theorem pushforwardFamily_apply {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) := by
  unfold pushforwardFamily
  refine' congr_fun _ x
  rw [← G.image_preimage (Nonempty.some _ : presieve.cover_by_image_structure _ _).lift]
  change ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ = ℱ.map f.op ≫ α.app (op Y)
  erw [← α.naturality (G.preimage _).op]
  simp only [← functor.map_comp, ← category.assoc, functor.comp_map, G.image_preimage, G.op_map,
    Quiver.Hom.unop_op, ← op_comp, presieve.cover_by_image_structure.fac]
#align category_theory.cover_dense.types.pushforward_family_apply CategoryTheory.CoverDense.Types.pushforwardFamily_apply

@[simp]
theorem appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
    ℱ'.val.map f (appHom H α X x) = α.app (op Y) (ℱ.map f x) := by
  refine'
    ((ℱ'.cond _ (H.is_cover X)).valid_glue (pushforwardFamily_compatible H α x) f.unop
          (Presieve.in_coverByImage G f.unop)).trans
      _
  apply pushforwardFamily_apply
#align category_theory.cover_dense.types.app_hom_restrict CategoryTheory.CoverDense.Types.appHom_restrict

@[simp]
theorem appHom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
    appHom H α X ≫ ℱ'.val.map f = ℱ.map f ≫ α.app (op Y) := by
  ext
  apply appHom_restrict
#align category_theory.cover_dense.types.app_hom_valid_glue CategoryTheory.CoverDense.Types.appHom_valid_glue

/--
(Implementation). The maps given in `app_iso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps]
noncomputable def appIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : D) :
    ℱ.val.obj (op X) ≅ ℱ'.val.obj (op X) where
  hom := appHom H i.hom X
  inv := appHom H i.inv X
  hom_inv_id := by
    ext x
    apply H.ext
    intro Y f
    simp
  inv_hom_id := by
    ext x
    apply H.ext
    intro Y f
    simp
#align category_theory.cover_dense.types.app_iso CategoryTheory.CoverDense.Types.appIso

/-- Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation between sheaves.
-/
@[simps]
noncomputable def presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val where
  app X := appHom H α (unop X)
  naturality X Y f := by
    ext x
    apply H.ext ℱ' (unop Y)
    intro Y' f'
    simp only [appHom_restrict, types_comp_apply, ← FunctorToTypes.map_comp_apply]
    -- porting note: Lean 3 proof continued with a rewrite but we're done here
#align category_theory.cover_dense.types.presheaf_hom CategoryTheory.CoverDense.Types.presheafHom

/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full and
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def presheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val :=
  NatIso.ofComponents (fun X => appIso H i (unop X)) (presheafHom H i.hom).naturality
#align category_theory.cover_dense.types.presheaf_iso CategoryTheory.CoverDense.Types.presheafIso

/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full and
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between sheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ'
    where
  hom := ⟨(presheafIso H i).Hom⟩
  inv := ⟨(presheafIso H i).inv⟩
  hom_inv_id := by
    ext1
    apply (presheafIso H i).hom_inv_id
  inv_hom_id := by
    ext1
    apply (presheafIso H i).inv_hom_id
#align category_theory.cover_dense.types.sheaf_iso CategoryTheory.CoverDense.Types.sheafIso

end Types

open Types

variable {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps]
noncomputable def sheafCoyonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ ⟶
      coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ'.val where
  app X := presheafHom H (homOver α (unop X))
  naturality' X Y f := by
    ext (U x)
    change
      app_hom H (hom_over α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ app_hom H (hom_over α (unop X)) (unop U) x
    symm
    apply sheaf_eq_amalgamation
    apply H.is_cover
    intro Y' f' hf'
    change unop X ⟶ ℱ.obj (op (unop _)) at x
    dsimp
    simp only [pushforward_family, functor.comp_map, coyoneda_obj_map, hom_over_app, category.assoc]
    congr 1
    conv_lhs => rw [← hf'.some.fac]
    simp only [← category.assoc, op_comp, functor.map_comp]
    congr 1
    refine' (app_hom_restrict H (hom_over α (unop X)) hf'.some.map.op x).trans _
    simp
#align category_theory.cover_dense.sheaf_coyoneda_hom CategoryTheory.CoverDense.sheafCoyonedaHom

/--
(Implementation). `sheaf_coyoneda_hom` but the order of the arguments of the functor are swapped.
-/
noncomputable def sheafYonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⋙ yoneda ⟶ ℱ'.val ⋙ yoneda := by
  let α := sheaf_coyoneda_hom H α
  refine'
    { app := _
      naturality' := _ }
  · intro U
    refine'
      { app := fun X => (α.app X).app U
        naturality' := fun X Y f => by simpa using congr_app (α.naturality f) U }
  · intro U V i
    ext (X x)
    exact congr_fun ((α.app X).naturality i) x
#align category_theory.cover_dense.sheaf_yoneda_hom CategoryTheory.CoverDense.sheafYonedaHom

/-- Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation
between presheaves.
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
  let α' := sheafYonedaHom H α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality' := fun X Y f => yoneda.map_injective (by simpa using α'.naturality f) }
#align category_theory.cover_dense.sheaf_hom CategoryTheory.CoverDense.sheafHom

/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val := by
  have : ∀ X : Dᵒᵖ, is_iso ((sheaf_hom H i.hom).app X) := by
    intro X
    apply is_iso_of_reflects_iso _ yoneda
    use (sheaf_yoneda_hom H i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheaf_hom, nat_trans.comp_app, nat_trans.id_app, functor.image_preimage]
    exact ((presheaf_iso H (iso_over i (unop x))).app X).hom_inv_id
    exact ((presheaf_iso H (iso_over i (unop x))).app X).inv_hom_id
    infer_instance
  haveI : is_iso (sheaf_hom H i.hom) := by apply nat_iso.is_iso_of_is_iso_app
  apply as_iso (sheaf_hom H i.hom)
#align category_theory.cover_dense.presheaf_iso CategoryTheory.CoverDense.presheafIso

/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ' where
  Hom := ⟨(presheafIso H i).Hom⟩
  inv := ⟨(presheafIso H i).inv⟩
  hom_inv_id' := by
    ext1
    apply (presheaf_iso H i).hom_inv_id
  inv_hom_id' := by
    ext1
    apply (presheaf_iso H i).inv_hom_id
#align category_theory.cover_dense.sheaf_iso CategoryTheory.CoverDense.sheafIso

/-- The constructed `sheaf_hom α` is equal to `α` when restricted onto `C`.
-/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : whiskerLeft G.op (sheafHom H α) = α :=
  by
  ext X
  apply yoneda.map_injective
  ext U
  erw [yoneda.image_preimage]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  simp only [pushforward_family, functor.comp_map, yoneda_map_app, coyoneda_obj_map, op_comp,
    functor_to_types.map_comp_apply, hom_over_app, ← category.assoc]
  congr 1
  simp only [category.assoc]
  congr 1
  rw [← G.image_preimage hf.some.map]
  symm
  apply α.naturality (G.preimage hf.some.map).op
  infer_instance
#align category_theory.cover_dense.sheaf_hom_restrict_eq CategoryTheory.CoverDense.sheafHom_restrict_eq

/-- If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
theorem sheafHom_eq (α : ℱ ⟶ ℱ'.val) : sheafHom H (whiskerLeft G.op α) = α := by
  ext X
  apply yoneda.map_injective
  swap; · infer_instance
  ext U
  erw [yoneda.image_preimage]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp
#align category_theory.cover_dense.sheaf_hom_eq CategoryTheory.CoverDense.sheafHom_eq

/-- A full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val) where
  toFun := sheafHom H
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq H
  right_inv := sheafHom_eq H
#align category_theory.cover_dense.restrict_hom_equiv_hom CategoryTheory.CoverDense.restrictHomEquivHom

/-- Given a full and cover-dense functor `G` and a natural transformation of sheaves `α : ℱ ⟶ ℱ'`,
if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.val)) :
    IsIso α := by
  convert is_iso.of_iso (sheaf_iso H (as_iso (whisker_left G.op α.val))) using 1
  ext1
  apply (sheaf_hom_eq _ _).symm
#align category_theory.cover_dense.iso_of_restrict_iso CategoryTheory.CoverDense.iso_of_restrict_iso

/-- A fully faithful cover-dense functor preserves compatible families. -/
theorem compatiblePreserving [Faithful G] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply H.ext
  intro W i
  simp only [← functor_to_types.map_comp_apply, ← op_comp]
  rw [← G.image_preimage (i ≫ f₁)]
  rw [← G.image_preimage (i ≫ f₂)]
  apply hx
  apply G.map_injective
  simp [Eq]
#align category_theory.cover_dense.compatible_preserving CategoryTheory.CoverDense.compatiblePreserving

noncomputable instance Sites.Pullback.full [Faithful G] (Hp : CoverPreserving J K G) :
    Full (Sites.pullback A H.CompatiblePreserving Hp) where
  preimage ℱ ℱ' α := ⟨H.sheafHom α.val⟩
  witness' ℱ ℱ' α := Sheaf.Hom.ext _ _ <| H.sheafHom_restrict_eq α.val
#align category_theory.cover_dense.sites.pullback.full CategoryTheory.CoverDense.Sites.Pullback.full

instance Sites.Pullback.faithful [Faithful G] (Hp : CoverPreserving J K G) :
    Faithful (Sites.pullback A H.CompatiblePreserving Hp)
    where map_injective' := by
    intro ℱ ℱ' α β e
    ext1
    apply_fun fun e => e.val  at e
    dsimp at e
    rw [← H.sheaf_hom_eq α.val, ← H.sheaf_hom_eq β.val, e]
#align category_theory.cover_dense.sites.pullback.faithful CategoryTheory.CoverDense.Sites.Pullback.faithful

end CoverDense

end CategoryTheory

namespace CategoryTheory.CoverDense

open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

variable {G : C ⥤ D} [Full G] [Faithful G]

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable {A : Type w} [Category.{max u v} A] [Limits.HasLimits A]

variable (Hd : CoverDense K G) (Hp : CoverPreserving J K G) (Hl : CoverLifting J K G)

include Hd Hp Hl

/-- Given a functor between small sites that is cover-dense, cover-preserving, and cover-lifting,
it induces an equivalence of category of sheaves valued in a complete category.
-/
@[simps Functor inverse]
noncomputable def sheafEquivOfCoverPreservingCoverLifting : Sheaf J A ≌ Sheaf K A := by
  symm
  let α := Sites.pullbackCopullbackAdjunction.{w, v, u} A Hp Hl Hd.compatible_preserving
  have : ∀ X : Sheaf J A, is_iso (α.counit.app X) := by
    intro ℱ
    apply (config := { instances := false }) reflects_isomorphisms.reflects (Sheaf_to_presheaf J A)
    exact is_iso.of_iso ((@as_iso _ _ _ _ _ (Ran.reflective A G.op)).app ℱ.val)
  haveI : is_iso α.counit := nat_iso.is_iso_of_is_iso_app _
  exact
    { Functor := sites.pullback A Hd.compatible_preserving Hp
      inverse := sites.copullback A Hl
      unitIso := as_iso α.unit
      counitIso := as_iso α.counit
      functor_unitIso_comp' := fun ℱ => by convert α.left_triangle_components }
#align category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting CategoryTheory.CoverDense.sheafEquivOfCoverPreservingCoverLifting

end CategoryTheory.CoverDense
