/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle

! This file was ported from Lean 3 source module linear_algebra.trace
! leanprover-community/mathlib commit 4cf7ca0e69e048b006674cf4499e5c7d296a89e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProductBasis
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.LinearAlgebra.Projection

/-!
# Trace of a linear map

This file defines the trace of a linear map.

See also `LinearAlgebra/Matrix/Trace.lean` for the trace of a matrix.

## Tags

linear_map, trace, diagonal

-/


noncomputable section

universe u v w

namespace LinearMap

open BigOperators

open Matrix

open FiniteDimensional

open TensorProduct

section

variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]

variable {ι : Type w} [DecidableEq ι] [Fintype ι]

variable {κ : Type _} [DecidableEq κ] [Fintype κ]

variable (b : Basis ι R M) (c : Basis κ R M)

/-- The trace of an endomorphism given a basis. -/
def traceAux : (M →ₗ[R] M) →ₗ[R] R :=
  Matrix.traceLinearMap ι R R ∘ₗ ↑(LinearMap.toMatrix b b)
#align linear_map.trace_aux LinearMap.traceAux

-- Can't be `simp` because it would cause a loop.
theorem traceAux_def (b : Basis ι R M) (f : M →ₗ[R] M) :
    traceAux R b f = Matrix.trace (LinearMap.toMatrix b b f) :=
  rfl
#align linear_map.trace_aux_def LinearMap.traceAux_def

theorem traceAux_eq : traceAux R b = traceAux R c :=
  LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix b b f) =
          Matrix.trace (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) := by
        rw [LinearMap.id_comp, LinearMap.comp_id]
      _ = Matrix.trace (LinearMap.toMatrix c b LinearMap.id ⬝ LinearMap.toMatrix c c f ⬝
          LinearMap.toMatrix b c LinearMap.id) := by
        rw [LinearMap.toMatrix_comp _ c, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f ⬝ LinearMap.toMatrix b c LinearMap.id ⬝
          LinearMap.toMatrix c b LinearMap.id) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.toMatrix_comp _ b, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f) := by rw [LinearMap.comp_id, LinearMap.comp_id]
#align linear_map.trace_aux_eq LinearMap.traceAux_eq

open Classical

variable (M)

/-- Trace of an endomorphism independent of basis. -/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
  if H : ∃ s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0
#align linear_map.trace LinearMap.trace

variable {M}

/-- Auxiliary lemma for `trace_eq_matrix_trace`. -/
theorem trace_eq_matrix_trace_of_finset {s : Finset M} (b : Basis s R M) (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace, dif_pos this, ← traceAux_def]
  congr 1
  apply traceAux_eq
#align linear_map.trace_eq_matrix_trace_of_finset LinearMap.trace_eq_matrix_trace_of_finset

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  rw [trace_eq_matrix_trace_of_finset R b.reindexFinsetRange, ← traceAux_def, ← traceAux_def,
    traceAux_eq R b b.reindexFinsetRange]
#align linear_map.trace_eq_matrix_trace LinearMap.trace_eq_matrix_trace

theorem trace_mul_comm (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) :=
  if H : ∃ s : Finset M, Nonempty (Basis s R M) then by
    let ⟨s, ⟨b⟩⟩ := H
    simp_rw [trace_eq_matrix_trace R b, LinearMap.toMatrix_mul]
    apply Matrix.trace_mul_comm
  else by rw [trace, dif_neg H, LinearMap.zero_apply, LinearMap.zero_apply]
#align linear_map.trace_mul_comm LinearMap.trace_mul_comm

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
theorem trace_conj (g : M →ₗ[R] M) (f : (M →ₗ[R] M)ˣ) :
    trace R M (↑f * g * ↑f⁻¹) = trace R M g := by
  rw [trace_mul_comm]
  simp
#align linear_map.trace_conj LinearMap.trace_conj

end

section

variable {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M]

variable (N : Type _) [AddCommGroup N] [Module R N]

variable {ι : Type _}

/-- The trace of a linear map correspond to the contraction pairing under the isomorphism
 `End(M) ≃ M* ⊗ M`-/
theorem trace_eq_contract_of_basis [Finite ι] (b : Basis ι R M) :
    LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M := by
  classical
    cases nonempty_fintype ι
    apply Basis.ext (Basis.tensorProduct (Basis.dualBasis b) b)
    rintro ⟨i, j⟩
    simp only [Function.comp_apply, Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp]
    rw [trace_eq_matrix_trace R b, toMatrix_dualTensorHom]
    by_cases hij : i = j
    · rw [hij]
      simp
    rw [Matrix.StdBasisMatrix.trace_zero j i (1 : R) hij]
    simp [Finsupp.single_eq_pi_single, hij]
#align linear_map.trace_eq_contract_of_basis LinearMap.trace_eq_contract_of_basis

/-- The trace of a linear map correspond to the contraction pairing under the isomorphism
 `End(M) ≃ M* ⊗ M`-/
theorem trace_eq_contract_of_basis' [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquivOfBasis b).symm.toLinearMap := by
  simp [LinearEquiv.eq_comp_toLinearMap_symm, trace_eq_contract_of_basis b]
#align linear_map.trace_eq_contract_of_basis' LinearMap.trace_eq_contract_of_basis'

variable (R M)

variable [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N] [Nontrivial R]

/-- When `M` is finite free, the trace of a linear map correspond to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`-/
@[simp]
theorem trace_eq_contract : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M :=
  trace_eq_contract_of_basis (Module.Free.chooseBasis R M)
#align linear_map.trace_eq_contract LinearMap.trace_eq_contract

@[simp]
theorem trace_eq_contract_apply (x : Module.Dual R M ⊗[R] M) :
    (LinearMap.trace R M) ((dualTensorHom R M M) x) = contractLeft R M x := by
  rw [← comp_apply, trace_eq_contract]
#align linear_map.trace_eq_contract_apply LinearMap.trace_eq_contract_apply

open Classical

/-- When `M` is finite free, the trace of a linear map correspond to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`-/
theorem trace_eq_contract' :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap :=
  trace_eq_contract_of_basis' (Module.Free.chooseBasis R M)
#align linear_map.trace_eq_contract' LinearMap.trace_eq_contract'

/-- The trace of the identity endomorphism is the dimension of the free module -/
@[simp]
theorem trace_one : trace R M 1 = (finrank R M : R) := by
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b, toMatrix_one, finrank_eq_card_chooseBasisIndex]
  simp
#align linear_map.trace_one LinearMap.trace_one

/-- The trace of the identity endomorphism is the dimension of the free module -/
@[simp]
theorem trace_id : trace R M id = (finrank R M : R) := by rw [← one_eq_id, trace_one]
#align linear_map.trace_id LinearMap.trace_id

@[simp]
theorem trace_transpose : trace R (Module.Dual R M) ∘ₗ Module.Dual.transpose = trace R M := by
  let e := dualTensorHomEquiv R M M
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine' (cancel_right h).1 _
  ext (f m); simp
#align linear_map.trace_transpose LinearMap.trace_transpose

theorem trace_prodMap :
    trace R (M × N) ∘ₗ prodMapLinear R M N M N R =
      (coprod id id : R × R →ₗ[R] R) ∘ₗ prodMap (trace R M) (trace R N) := by
  let e := (dualTensorHomEquiv R M M).prod (dualTensorHomEquiv R N N)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine' (cancel_right h).1 _
  ext
  · simp only [dualTensorHomEquiv, AlgebraTensorModule.curry_apply_apply, coe_comp,
      LinearEquiv.coe_toLinearMap, coe_inl, Function.comp_apply, LinearEquiv.prod_apply,
      dualTensorHomEquivOfBasis_apply, map_zero, prodMapLinear_apply, dualTensorHom_prodMap_zero,
      trace_eq_contract_apply, contractLeft_apply, fst_apply, prodMap_apply, coprod_apply, id_coe,
      id.def, add_zero]
  · simp only [dualTensorHomEquiv, AlgebraTensorModule.curry_apply_apply, coe_comp,
      LinearEquiv.coe_toLinearMap, coe_inr, Function.comp_apply, LinearEquiv.prod_apply, map_zero,
      dualTensorHomEquivOfBasis_apply, prodMapLinear_apply, zero_prodMap_dualTensorHom,
      trace_eq_contract_apply, contractLeft_apply, snd_apply, prodMap_apply, coprod_apply, id_coe,
      id.def, zero_add]
#align linear_map.trace_prod_map LinearMap.trace_prodMap

variable {R M N}

theorem trace_prodMap' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M × N) (prodMap f g) = trace R M f + trace R N g := by
  have h := ext_iff.1 (trace_prodMap R M N) (f, g)
  simp only [coe_comp, Function.comp_apply, prodMap_apply, coprod_apply, id_coe, id.def,
    prodMapLinear_apply] at h
  exact h
#align linear_map.trace_prod_map' LinearMap.trace_prodMap'

variable (R M N)

open TensorProduct Function

theorem trace_tensorProduct : compr₂ (mapBilinear R M N M N) (trace R (M ⊗ N)) =
    compl₁₂ (lsmul R R : R →ₗ[R] R →ₗ[R] R) (trace R M) (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R M M) from (dualTensorHomEquiv R M M).surjective)
        (show Surjective (dualTensorHom R N N) from (dualTensorHomEquiv R N N).surjective)).1
  ext (f m g n)
  simp only [AlgebraTensorModule.curry_apply_apply, toFun_eq_coe, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, mapBilinear_apply,
    trace_eq_contract_apply, contractLeft_apply, lsmul_apply, Algebra.id.smul_eq_mul,
    map_dualTensorHom, dualDistrib_apply]
#align linear_map.trace_tensor_product LinearMap.trace_tensorProduct

theorem trace_comp_comm :
    compr₂ (llcomp R M N M) (trace R M) = compr₂ (llcomp R N M N).flip (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R N M) from (dualTensorHomEquiv R N M).surjective)
        (show Surjective (dualTensorHom R M N) from (dualTensorHomEquiv R M N).surjective)).1
  ext (g m f n)
  simp only [AlgebraTensorModule.curry_apply_apply, compl₁₂_apply, compr₂_apply, llcomp_apply',
    comp_dualTensorHom, map_smulₛₗ, RingHom.id_apply, trace_eq_contract_apply, contractLeft_apply,
    smul_eq_mul, mul_comm, flip_apply]
#align linear_map.trace_comp_comm LinearMap.trace_comp_comm

variable {R M N}

@[simp]
theorem trace_transpose' (f : M →ₗ[R] M) :
    trace R _ (Module.Dual.transpose (R := R) f) = trace R M f := by
  rw [← comp_apply, trace_transpose]
#align linear_map.trace_transpose' LinearMap.trace_transpose'

theorem trace_tensorProduct' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M ⊗ N) (map f g) = trace R M f * trace R N g := by
  have h := ext_iff.1 (ext_iff.1 (trace_tensorProduct R M N) f) g
  simp only [compr₂_apply, mapBilinear_apply, compl₁₂_apply, lsmul_apply,
    Algebra.id.smul_eq_mul] at h
  exact h
#align linear_map.trace_tensor_product' LinearMap.trace_tensorProduct'

theorem trace_comp_comm' (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g) := by
  have h := ext_iff.1 (ext_iff.1 (trace_comp_comm R M N) g) f
  simp only [llcomp_apply', compr₂_apply, flip_apply] at h
  exact h
#align linear_map.trace_comp_comm' LinearMap.trace_comp_comm'

@[simp]
theorem trace_conj' (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) : trace R N (e.conj f) = trace R M f := by
  rw [e.conj_apply, trace_comp_comm', ← comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, id_comp]
#align linear_map.trace_conj' LinearMap.trace_conj'

theorem IsProj.trace {p : Submodule R M} {f : M →ₗ[R] M} (h : IsProj p f) [Module.Free R p]
    [Module.Finite R p] [Module.Free R (ker f)] [Module.Finite R (ker f)] :
    trace R M f = (finrank R p : R) := by
  rw [h.eq_conj_prodMap, trace_conj', trace_prodMap', trace_id, map_zero, add_zero]
#align linear_map.is_proj.trace LinearMap.IsProj.trace

end

end LinearMap
