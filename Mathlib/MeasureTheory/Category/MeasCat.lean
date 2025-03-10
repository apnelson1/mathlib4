/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module measure_theory.category.Meas
! leanprover-community/mathlib commit d6814c584384ddf2825ff038e868451a7c956f31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# The category of measurable spaces

Measurable spaces and measurable functions form a (concrete) category `MeasCat`.

## Main definitions

* `Measure : MeasCat ⥤ MeasCat`: the functor which sends a measurable space `X`
to the space of measures on `X`; it is a monad (the "Giry monad").

* `Borel : TopCat ⥤ MeasCat`: sends a topological space `X` to `X` equipped with the
`σ`-algebra of Borel sets (the `σ`-algebra generated by the open subsets of `X`).

## Tags

measurable space, giry monad, borel
-/


noncomputable section

open CategoryTheory MeasureTheory

open scoped ENNReal

universe u v

set_option linter.uppercaseLean3 false -- `Meas` `Top` `Borel`

/-- The category of measurable spaces and measurable functions. -/
def MeasCat : Type (u + 1) :=
  Bundled MeasurableSpace
#align Meas MeasCat

namespace MeasCat

instance : CoeSort MeasCat (Type _) :=
  Bundled.coeSort

instance (X : MeasCat) : MeasurableSpace X :=
  X.str

/-- Construct a bundled `MeasCat` from the underlying type and the typeclass. -/
def of (α : Type u) [ms : MeasurableSpace α] : MeasCat :=
  ⟨α, ms⟩
#align Meas.of MeasCat.of

@[simp]
theorem coe_of (X : Type u) [MeasurableSpace X] : (of X : Type u) = X :=
  rfl
#align Meas.coe_of MeasCat.coe_of

instance unbundledHom : UnbundledHom @Measurable :=
  ⟨@measurable_id, @Measurable.comp⟩
#align Meas.unbundled_hom MeasCat.unbundledHom

deriving instance LargeCategory for MeasCat

-- Porting note: `deriving instance ConcreteCategory for MeasCat` didn't work. Define it manually.
instance : ConcreteCategory MeasCat := by
  unfold MeasCat
  infer_instance

instance : Inhabited MeasCat :=
  ⟨MeasCat.of Empty⟩

/-- `Measure X` is the measurable space of measures over the measurable space `X`. It is the
weakest measurable space, s.t. `fun μ ↦ μ s` is measurable for all measurable sets `s` in `X`. An
important purpose is to assign a monadic structure on it, the Giry monad. In the Giry monad,
the pure values are the Dirac measure, and the bind operation maps to the integral:
`(μ >>= ν) s = ∫ x. (ν x) s dμ`.

In probability theory, the `MeasCat`-morphisms `X → Prob X` are (sub-)Markov kernels (here `Prob` is
the restriction of `Measure` to (sub-)probability space.)
-/
def Measure : MeasCat ⥤ MeasCat where
  obj X := ⟨@MeasureTheory.Measure X.1 X.2, inferInstance⟩
  map f := ⟨Measure.map (⇑f), Measure.measurable_map f.1 f.2⟩
  map_id := fun ⟨α, I⟩ => Subtype.eq <| funext fun μ => @Measure.map_id α I μ
  map_comp := fun ⟨_, hf⟩ ⟨_, hg⟩ => Subtype.eq <| funext fun _ => (Measure.map_map hg hf).symm
#align Meas.Measure MeasCat.Measure

/-- The Giry monad, i.e. the monadic structure associated with `Measure`. -/
def Giry : CategoryTheory.Monad MeasCat where
  toFunctor := Measure
  η' :=
    { app := fun X => ⟨@Measure.dirac X.1 X.2, Measure.measurable_dirac⟩
      naturality := fun _ _ ⟨_, hf⟩ => Subtype.eq <| funext fun a => (Measure.map_dirac hf a).symm }
  μ' :=
    { app := fun X => ⟨@Measure.join X.1 X.2, Measure.measurable_join⟩
      naturality := fun _ _ ⟨_, hf⟩ => Subtype.eq <| funext fun μ => Measure.join_map_map hf μ }
  assoc' _ := Subtype.eq <| funext fun _ => Measure.join_map_join _
  left_unit' _ := Subtype.eq <| funext fun _ => Measure.join_dirac _
  right_unit' _ := Subtype.eq <| funext fun _ => Measure.join_map_dirac _
#align Meas.Giry MeasCat.Giry

/-- An example for an algebra on `Measure`: the nonnegative Lebesgue integral is a hom, behaving
nicely under the monad operations. -/
def Integral : Giry.Algebra where
  A := MeasCat.of ℝ≥0∞
  a := ⟨fun m : MeasureTheory.Measure ℝ≥0∞ ↦ ∫⁻ x, x ∂m, Measure.measurable_lintegral measurable_id⟩
  unit := Subtype.eq <| funext fun r : ℝ≥0∞ => lintegral_dirac' _ measurable_id
  assoc := Subtype.eq <| funext fun μ : MeasureTheory.Measure (MeasureTheory.Measure ℝ≥0∞) =>
    show (∫⁻ x, x ∂μ.join) = ∫⁻ x, x ∂Measure.map (fun m => ∫⁻ x, x ∂m) μ by
      rw [Measure.lintegral_join, lintegral_map] <;>
        apply_rules [measurable_id, Measure.measurable_lintegral]
#align Meas.Integral MeasCat.Integral

end MeasCat

instance TopCat.hasForgetToMeasCat : HasForget₂ TopCat.{u} MeasCat.{u} :=
  BundledHom.mkHasForget₂ borel (fun f => ⟨f.1, f.2.borel_measurable⟩) (fun _ => rfl)
#align Top.has_forget_to_Meas TopCat.hasForgetToMeasCat

/-- The Borel functor, the canonical embedding of topological spaces into measurable spaces. -/
@[reducible]
def Borel : TopCat.{u} ⥤ MeasCat.{u} :=
  forget₂ TopCat.{u} MeasCat.{u}
#align Borel Borel
