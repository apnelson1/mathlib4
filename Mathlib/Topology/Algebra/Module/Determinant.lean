/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth

! This file was ported from Lean 3 source module topology.algebra.module.determinant
! leanprover-community/mathlib commit 4b262b8463002087e407be07080b91d213361e64
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of a continuous linear map.
-/


namespace ContinuousLinearMap

/-- The determinant of a continuous linear map, mainly as a convenience device to be able to
write `A.det` instead of `(A : M →ₗ[R] M).det`. -/
@[reducible]
noncomputable def det {R : Type _} [CommRing R] {M : Type _} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M →L[R] M) : R :=
  LinearMap.det (A : M →ₗ[R] M)
#align continuous_linear_map.det ContinuousLinearMap.det

end ContinuousLinearMap

namespace ContinuousLinearEquiv

@[simp]
theorem det_coe_symm {R : Type _} [Field R] {M : Type _} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M ≃L[R] M) : (A.symm : M →L[R] M).det = (A : M →L[R] M).det⁻¹ :=
  LinearEquiv.det_coe_symm A.toLinearEquiv
#align continuous_linear_equiv.det_coe_symm ContinuousLinearEquiv.det_coe_symm

end ContinuousLinearEquiv
