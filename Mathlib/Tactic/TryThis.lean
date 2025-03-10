/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.TryThis
import Lean.Meta.Tactic.Util

/-!
# Additions to "Try this" support

This file could be upstreamed to `Std`.
-/

open Lean Elab Elab.Tactic PrettyPrinter Meta Std.Tactic.TryThis

/-- Add a suggestion for `have : t := e`. -/
def addHaveSuggestion (ref : Syntax) (t? : Option Expr) (e : Expr) :
    TermElabM Unit := do
  let estx ← delabToRefinableSyntax e
  let prop ← isProp (← inferType e)
  let tac ← if let some t := t? then
    let tstx ← delabToRefinableSyntax t
    if prop then
      `(tactic| have : $tstx := $estx)
    else
      `(tactic| let this : $tstx := $estx)
  else
    if prop then
      `(tactic| have := $estx)
    else
      `(tactic| let this := $estx)
  addSuggestion ref tac

/-- Add a suggestion for `rw [h]`. -/
def addRewriteSuggestion (ref : Syntax) (e : Expr) (symm : Bool) (type? : Option Expr := none) :
    TermElabM Unit := do
  let estx ← delabToRefinableSyntax e
  let tac ← if symm then `(tactic| rw [← $estx]) else `(tactic| rw [$estx:term])
  let mut tacMsg := if symm then m!"rw [← {e}]" else m!"rw [{e}]"
  let mut extraMsg := ""
  if let some type := type? then
    tacMsg := tacMsg ++ m!"\n-- {type}"
    extraMsg := extraMsg ++ s!"\n-- {← PrettyPrinter.ppExpr type}"
  addSuggestion ref tac (suggestionForMessage? := tacMsg) (extraMsg := extraMsg)
