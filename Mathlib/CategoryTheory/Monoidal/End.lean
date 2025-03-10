/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Andrew Yang

! This file was ported from Lean 3 source module category_theory.monoidal.End
! leanprover-community/mathlib commit 85075bccb68ab7fa49fb05db816233fb790e4fe9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/


universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).
-/
def endofunctorMonoidalCategory : MonoidalCategory (C ⥤ C) where
  tensorObj F G := F ⋙ G
  tensorHom α β := α ◫ β
  tensorUnit' := 𝟭 C
  associator F G H := Functor.associator F G H
  leftUnitor F := Functor.leftUnitor F
  rightUnitor F := Functor.rightUnitor F
#align category_theory.endofunctor_monoidal_category CategoryTheory.endofunctorMonoidalCategory

open CategoryTheory.MonoidalCategory

attribute [local instance] endofunctorMonoidalCategory

-- porting note: used `dsimp [endofunctorMonoidalCategory]` when necessary instead
-- attribute [local reducible] endofunctorMonoidalCategory

/-- Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
@[simps!]
def tensoringRightMonoidal [MonoidalCategory.{v} C] : MonoidalFunctor C (C ⥤ C) :=
  {-- We could avoid needing to do this explicitly by
      -- constructing a partially applied analogue of `associatorNatIso`.
      tensoringRight C with
    ε := (rightUnitorNatIso C).inv
    μ := fun X Y =>
      { app := fun Z => (α_ Z X Y).hom
        naturality := fun Z Z' f => by
          dsimp [endofunctorMonoidalCategory]
          rw [associator_naturality]
          simp }
    μ_natural := fun f g => by
      ext Z
      dsimp [endofunctorMonoidalCategory]
      simp only [← id_tensor_comp_tensor_id g f, id_tensor_comp, ← tensor_id, Category.assoc,
        associator_naturality, associator_naturality_assoc]
    associativity := fun X Y Z => by
      ext W
      dsimp [endofunctorMonoidalCategory]
      simp [pentagon]
    left_unitality := fun X => by
      ext Y
      dsimp [endofunctorMonoidalCategory]
      rw [Category.id_comp, triangle, ← tensor_comp]
      aesop_cat
    right_unitality := fun X => by
      ext Y; dsimp [endofunctorMonoidalCategory]
      rw [tensor_id, Category.comp_id, rightUnitor_tensor_inv, Category.assoc,
        Iso.inv_hom_id_assoc, ← id_tensor_comp, Iso.inv_hom_id, tensor_id]
    ε_isIso := by infer_instance
    μ_isIso := fun X Y =>
      ⟨⟨{   app := fun Z => (α_ Z X Y).inv
            naturality := fun Z Z' f => by
              dsimp [endofunctorMonoidalCategory]
              rw [← associator_inv_naturality]
              simp },
          by aesop_cat⟩⟩ }
#align category_theory.tensoring_right_monoidal CategoryTheory.tensoringRightMonoidal

variable {C}

variable {M : Type _} [Category M] [MonoidalCategory M] (F : MonoidalFunctor M (C ⥤ C))

@[reassoc (attr := simp)]
theorem μ_hom_inv_app (i j : M) (X : C) : (F.μ i j).app X ≫ (F.μIso i j).inv.app X = 𝟙 _ :=
  (F.μIso i j).hom_inv_id_app X
#align category_theory.μ_hom_inv_app CategoryTheory.μ_hom_inv_app

@[reassoc (attr := simp)]
theorem μ_inv_hom_app (i j : M) (X : C) : (F.μIso i j).inv.app X ≫ (F.μ i j).app X = 𝟙 _ :=
  (F.μIso i j).inv_hom_id_app X
#align category_theory.μ_inv_hom_app CategoryTheory.μ_inv_hom_app

@[reassoc (attr := simp)]
theorem ε_hom_inv_app (X : C) : F.ε.app X ≫ F.εIso.inv.app X = 𝟙 _ :=
  F.εIso.hom_inv_id_app X
#align category_theory.ε_hom_inv_app CategoryTheory.ε_hom_inv_app

@[reassoc (attr := simp)]
theorem ε_inv_hom_app (X : C) : F.εIso.inv.app X ≫ F.ε.app X = 𝟙 _ :=
  F.εIso.inv_hom_id_app X
#align category_theory.ε_inv_hom_app CategoryTheory.ε_inv_hom_app

@[reassoc (attr := simp)]
theorem ε_naturality {X Y : C} (f : X ⟶ Y) : F.ε.app X ≫ (F.obj (𝟙_ M)).map f = f ≫ F.ε.app Y :=
  (F.ε.naturality f).symm
#align category_theory.ε_naturality CategoryTheory.ε_naturality

@[reassoc (attr := simp)]
theorem ε_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (MonoidalFunctor.εIso F).inv.app X ≫ (𝟙_ (C ⥤ C)).map f = F.εIso.inv.app X ≫ f := by
  aesop_cat
#align category_theory.ε_inv_naturality CategoryTheory.ε_inv_naturality

@[reassoc (attr := simp)]
theorem μ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
    (F.obj n).map ((F.obj m).map f) ≫ (F.μ m n).app Y = (F.μ m n).app X ≫ (F.obj _).map f :=
  (F.toLaxMonoidalFunctor.μ m n).naturality f
#align category_theory.μ_naturality CategoryTheory.μ_naturality

-- This is a simp lemma in the reverse direction via `NatTrans.naturality`.
@[reassoc]
theorem μ_inv_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
    (F.μIso m n).inv.app X ≫ (F.obj n).map ((F.obj m).map f) =
      (F.obj _).map f ≫ (F.μIso m n).inv.app Y :=
  ((F.μIso m n).inv.naturality f).symm
#align category_theory.μ_inv_naturality CategoryTheory.μ_inv_naturality

-- This is not a simp lemma since it could be proved by the lemmas later.
@[reassoc]
theorem μ_naturality₂ {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) :
    (F.map g).app ((F.obj m).obj X) ≫ (F.obj n').map ((F.map f).app X) ≫ (F.μ m' n').app X =
      (F.μ m n).app X ≫ (F.map (f ⊗ g)).app X := by
  have := congr_app (F.toLaxMonoidalFunctor.μ_natural f g) X
  dsimp [endofunctorMonoidalCategory] at this
  simpa using this
#align category_theory.μ_naturality₂ CategoryTheory.μ_naturality₂

@[reassoc (attr := simp)]
theorem μ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) :
    (F.obj n).map ((F.map f).app X) ≫ (F.μ m' n).app X =
      (F.μ m n).app X ≫ (F.map (f ⊗ 𝟙 n)).app X := by
  rw [← μ_naturality₂ F f (𝟙 n) X]
  simp
#align category_theory.μ_naturalityₗ CategoryTheory.μ_naturalityₗ

@[reassoc (attr := simp)]
theorem μ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) :
    (F.map g).app ((F.obj m).obj X) ≫ (F.μ m n').app X =
      (F.μ m n).app X ≫ (F.map (𝟙 m ⊗ g)).app X := by
  rw [← μ_naturality₂ F (𝟙 m) g X]
  simp
#align category_theory.μ_naturalityᵣ CategoryTheory.μ_naturalityᵣ

@[reassoc (attr := simp)]
theorem μ_inv_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) :
    (F.μIso m n).inv.app X ≫ (F.obj n).map ((F.map f).app X) =
      (F.map (f ⊗ 𝟙 n)).app X ≫ (F.μIso m' n).inv.app X := by
  rw [← IsIso.comp_inv_eq, Category.assoc, ← IsIso.eq_inv_comp]
  simp
#align category_theory.μ_inv_naturalityₗ CategoryTheory.μ_inv_naturalityₗ

@[reassoc (attr := simp)]
theorem μ_inv_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) :
    (F.μIso m n).inv.app X ≫ (F.map g).app ((F.obj m).obj X) =
      (F.map (𝟙 m ⊗ g)).app X ≫ (F.μIso m n').inv.app X := by
  rw [← IsIso.comp_inv_eq, Category.assoc, ← IsIso.eq_inv_comp]
  simp
#align category_theory.μ_inv_naturalityᵣ CategoryTheory.μ_inv_naturalityᵣ

@[reassoc]
theorem left_unitality_app (n : M) (X : C) :
    (F.obj n).map (F.ε.app X) ≫ (F.μ (𝟙_ M) n).app X ≫ (F.map (λ_ n).hom).app X = 𝟙 _ := by
  have := congr_app (F.toLaxMonoidalFunctor.left_unitality n) X
  dsimp [endofunctorMonoidalCategory] at this
  simpa using this.symm
#align category_theory.left_unitality_app CategoryTheory.left_unitality_app

-- porting note: linter claims `simp can prove it`, but cnot
@[reassoc (attr := simp, nolint simpNF)]
theorem obj_ε_app (n : M) (X : C) :
    (F.obj n).map (F.ε.app X) = (F.map (λ_ n).inv).app X ≫ (F.μIso (𝟙_ M) n).inv.app X := by
  refine' Eq.trans _ (Category.id_comp _)
  rw [← Category.assoc, ← IsIso.comp_inv_eq, ← IsIso.comp_inv_eq, Category.assoc]
  convert left_unitality_app F n X
  · simp
  · simp
#align category_theory.obj_ε_app CategoryTheory.obj_ε_app

-- porting note: linter claims `simp can prove it`, but cnot
@[reassoc (attr := simp, nolint simpNF)]
theorem obj_ε_inv_app (n : M) (X : C) :
    (F.obj n).map (F.εIso.inv.app X) = (F.μ (𝟙_ M) n).app X ≫ (F.map (λ_ n).hom).app X := by
  rw [← cancel_mono ((F.obj n).map (F.ε.app X)), ← Functor.map_comp]
  simp
  rfl
#align category_theory.obj_ε_inv_app CategoryTheory.obj_ε_inv_app

@[reassoc]
theorem right_unitality_app (n : M) (X : C) :
    F.ε.app ((F.obj n).obj X) ≫ (F.μ n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X = 𝟙 _ := by
  have := congr_app (F.toLaxMonoidalFunctor.right_unitality n) X
  dsimp [endofunctorMonoidalCategory] at this
  simpa using this.symm
#align category_theory.right_unitality_app CategoryTheory.right_unitality_app

@[simp]
theorem ε_app_obj (n : M) (X : C) :
    F.ε.app ((F.obj n).obj X) = (F.map (ρ_ n).inv).app X ≫ (F.μIso n (𝟙_ M)).inv.app X := by
  refine' Eq.trans _ (Category.id_comp _)
  rw [← Category.assoc, ← IsIso.comp_inv_eq, ← IsIso.comp_inv_eq, Category.assoc]
  convert right_unitality_app F n X using 1
  simp
#align category_theory.ε_app_obj CategoryTheory.ε_app_obj

@[simp]
theorem ε_inv_app_obj (n : M) (X : C) :
    F.εIso.inv.app ((F.obj n).obj X) = (F.μ n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X := by
  rw [← cancel_mono (F.ε.app ((F.obj n).obj X)), ε_inv_hom_app]
  simp
  rfl
#align category_theory.ε_inv_app_obj CategoryTheory.ε_inv_app_obj

@[reassoc]
theorem associativity_app (m₁ m₂ m₃ : M) (X : C) :
    (F.obj m₃).map ((F.μ m₁ m₂).app X) ≫
        (F.μ (m₁ ⊗ m₂) m₃).app X ≫ (F.map (α_ m₁ m₂ m₃).hom).app X =
      (F.μ m₂ m₃).app ((F.obj m₁).obj X) ≫ (F.μ m₁ (m₂ ⊗ m₃)).app X := by
  have := congr_app (F.toLaxMonoidalFunctor.associativity m₁ m₂ m₃) X
  dsimp [endofunctorMonoidalCategory] at this
  simpa using this
#align category_theory.associativity_app CategoryTheory.associativity_app

-- porting note: linter claims `simp can prove it`, but cnot
@[reassoc (attr := simp, nolint simpNF)]
theorem obj_μ_app (m₁ m₂ m₃ : M) (X : C) :
    (F.obj m₃).map ((F.μ m₁ m₂).app X) =
      (F.μ m₂ m₃).app ((F.obj m₁).obj X) ≫
        (F.μ m₁ (m₂ ⊗ m₃)).app X ≫
          (F.map (α_ m₁ m₂ m₃).inv).app X ≫ (F.μIso (m₁ ⊗ m₂) m₃).inv.app X := by
  rw [← associativity_app_assoc]
  dsimp [endofunctorMonoidalCategory]
  simp
  dsimp [endofunctorMonoidalCategory]
  simp
#align category_theory.obj_μ_app CategoryTheory.obj_μ_app

-- porting note: linter claims `simp can prove it`, but cnot
@[reassoc (attr := simp, nolint simpNF)]
theorem obj_μ_inv_app (m₁ m₂ m₃ : M) (X : C) :
    (F.obj m₃).map ((F.μIso m₁ m₂).inv.app X) =
      (F.μ (m₁ ⊗ m₂) m₃).app X ≫
        (F.map (α_ m₁ m₂ m₃).hom).app X ≫
          (F.μIso m₁ (m₂ ⊗ m₃)).inv.app X ≫ (F.μIso m₂ m₃).inv.app ((F.obj m₁).obj X) := by
  rw [← IsIso.inv_eq_inv]
  convert obj_μ_app F m₁ m₂ m₃ X using 1
  · refine' IsIso.inv_eq_of_hom_inv_id _
    rw [← Functor.map_comp]
    simp
  · simp only [MonoidalFunctor.μIso_hom, Category.assoc, NatIso.inv_inv_app, IsIso.inv_comp]
    congr
    · refine' IsIso.inv_eq_of_hom_inv_id _
      simp
    · refine' IsIso.inv_eq_of_hom_inv_id _
      simp
      rfl
#align category_theory.obj_μ_inv_app CategoryTheory.obj_μ_inv_app

@[reassoc (attr := simp)]
theorem obj_zero_map_μ_app {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) :
    (F.obj (𝟙_ M)).map f ≫ (F.μ m (𝟙_ M)).app _ =
    F.εIso.inv.app _ ≫ f ≫ (F.map (ρ_ m).inv).app _ := by
  rw [← IsIso.inv_comp_eq, ← IsIso.comp_inv_eq]
  simp
#align category_theory.obj_zero_map_μ_app CategoryTheory.obj_zero_map_μ_app

@[simp]
theorem obj_μ_zero_app (m₁ m₂ : M) (X : C) :
    (F.μ (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫ (F.μ m₁ (𝟙_ M ⊗ m₂)).app X ≫
    (F.map (α_ m₁ (𝟙_ M) m₂).inv).app X ≫ (F.μIso (m₁ ⊗ 𝟙_ M) m₂).inv.app X =
    (F.μ (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫
    (F.map (λ_ m₂).hom).app ((F.obj m₁).obj X) ≫ (F.obj m₂).map ((F.map (ρ_ m₁).inv).app X) := by
  rw [← obj_ε_inv_app_assoc, ← Functor.map_comp]
  congr; simp
#align category_theory.obj_μ_zero_app CategoryTheory.obj_μ_zero_app

/-- If `m ⊗ n ≅ 𝟙_M`, then `F.obj m` is a left inverse of `F.obj n`. -/
@[simps!]
noncomputable def unitOfTensorIsoUnit (m n : M) (h : m ⊗ n ≅ 𝟙_ M) : F.obj m ⋙ F.obj n ≅ 𝟭 C :=
  F.μIso m n ≪≫ F.toFunctor.mapIso h ≪≫ F.εIso.symm
#align category_theory.unit_of_tensor_iso_unit CategoryTheory.unitOfTensorIsoUnit

/-- If `m ⊗ n ≅ 𝟙_M` and `n ⊗ m ≅ 𝟙_M` (subject to some commuting constraints),
  then `F.obj m` and `F.obj n` forms a self-equivalence of `C`. -/
@[simps]
noncomputable def equivOfTensorIsoUnit (m n : M) (h₁ : m ⊗ n ≅ 𝟙_ M) (h₂ : n ⊗ m ≅ 𝟙_ M)
    (H : (h₁.hom ⊗ 𝟙 m) ≫ (λ_ m).hom = (α_ m n m).hom ≫ (𝟙 m ⊗ h₂.hom) ≫ (ρ_ m).hom) : C ≌ C
    where
  functor := F.obj m
  inverse := F.obj n
  unitIso := (unitOfTensorIsoUnit F m n h₁).symm
  counitIso := unitOfTensorIsoUnit F n m h₂
  functor_unitIso_comp := by
    intro X
    dsimp
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, ε_inv_app_obj, Category.assoc,
      obj_μ_inv_app, Functor.map_comp, μ_inv_hom_app_assoc, obj_ε_app,
      unitOfTensorIsoUnit_inv_app]
    simp [← NatTrans.comp_app, ← F.toFunctor.map_comp, ← H, -Functor.map_comp]
#align category_theory.equiv_of_tensor_iso_unit CategoryTheory.equivOfTensorIsoUnit

end CategoryTheory
