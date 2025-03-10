/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.monad.basic
! leanprover-community/mathlib commit 70d50ecfd4900dd6d328da39ab7ebd516abe4025
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Control.SimpSet
import Mathlib.Tactic.Common

/-!
# Monad

## Attributes

 * ext
 * functor_norm
 * monad_norm

## Implementation Details

Set of rewrite rules and automation for monads in general and
`ReaderT`, `StateT`, `ExceptT` and `OptionT` in particular.

The rewrite rules for monads are carefully chosen so that `simp with
functor_norm` will not introduce monadic vocabulary in a context where
applicatives would do just fine but will handle monadic notation
already present in an expression.

In a context where monadic reasoning is desired `simp with monad_norm`
will translate functor and applicative notation into monad notation
and use regular `functor_norm` rules as well.

## Tags

functor, applicative, monad, simp

-/

attribute [ext] ReaderT.ext StateT.ext ExceptT.ext Option.ext

attribute [functor_norm] bind_assoc pure_bind bind_pure

attribute [monad_norm] seq_eq_bind_map


@[monad_norm]
theorem map_eq_bind_pure_comp (m : Type u → Type v) [Monad m] [LawfulMonad m]
    (f : α → β) (x : m α) : f <$> x = x >>= pure ∘ f :=
  (bind_pure_comp f x).symm
#align map_eq_bind_pure_comp map_eq_bind_pure_comp

/-- run a `StateT` program and discard the final state -/
def StateT.eval {m : Type u → Type v} [Functor m] (cmd : StateT σ m α) (s : σ) : m α :=
  Prod.fst <$> cmd.run s
#align state_t.eval StateT.eval

/-- reduce the equivalence between two state monads to the equivalence between
their respective function spaces -/
def StateT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
    (F : (σ₁ → m₁ (α₁ × σ₁)) ≃ (σ₂ → m₂ (α₂ × σ₂))) : StateT σ₁ m₁ α₁ ≃ StateT σ₂ m₂ α₂ :=
  F
#align state_t.equiv StateT.equiv

/-- reduce the equivalence between two reader monads to the equivalence between
their respective function spaces -/
def ReaderT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
    (F : (ρ₁ → m₁ α₁) ≃ (ρ₂ → m₂ α₂)) : ReaderT ρ₁ m₁ α₁ ≃ ReaderT ρ₂ m₂ α₂ :=
  F
#align reader_t.equiv ReaderT.equiv
