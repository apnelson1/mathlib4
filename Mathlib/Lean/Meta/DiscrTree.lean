/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Meta.DiscrTree
import Mathlib.Lean.Expr.Traverse

/-!
# Additions to `Lean.Meta.DiscrTree`
-/

namespace Lean.Meta.DiscrTree

/--
Inserts a new key into a discrimination tree,
but only if it is not of the form `#[*]` or `#[=, *, *, *]`.
-/
def insertIfSpecific [BEq α] (d : DiscrTree α s)
    (keys : Array (DiscrTree.Key s)) (v : α) : DiscrTree α s :=
  if keys == #[Key.star] || keys == #[Key.const `Eq 3, Key.star, Key.star, Key.star] then
    d
  else
    d.insertCore keys v

/--
Find keys which match the expression, or some subexpression.
-/
partial def getSubexpressionMatches (d : DiscrTree α s) (e : Expr) : MetaM (Array α) := do
  e.foldlM (fun a f => do pure <| a ++ (← d.getSubexpressionMatches f)) (← d.getMatch e)
variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α s) (f : Array α → m (Array β)) :
    m (DiscrTree.Trie β s) := do
  match t with
  | .node vs children =>
    return .node (← f vs) (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α s) (f : Array α → m (Array β)) : m (DiscrTree β s) := do
  pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α s) (f : Array α → Array β) : DiscrTree β s :=
  d.mapArraysM fun A => (pure (f A) : Id (Array β))

end Lean.Meta.DiscrTree
