import Mathlib.Tactic.LiftLets
import Std.Tactic.GuardExpr

example : (let x := 1; x) = 1 := by
  lift_lets
  guard_target =ₛ let x := 1; x = 1
  intro _x
  rfl

example : (let x := 1; x) = (let y := 1; y) := by
  lift_lets
  guard_target =ₛ let x := 1; let y := 1; x = y
  intro _x _y
  rfl

example : (fun x => let a := x; let y := 1; a + y) 2 = 2 + 1 := by
  lift_lets
  guard_target =ₛ let y := 1; (fun x ↦ let a := x; a + y) 2 = 2 + 1
  intro _y
  rfl

example : (fun (_ : let ty := Nat; ty) => Nat) (2 : Nat) := by
  lift_lets
  guard_target =ₛ let ty := Nat; (fun (_ : ty) ↦ Nat) (2 : Nat)
  exact 0

example : (fun (x : let ty := Nat; ty) => Fin x) (2 : Nat) := by
  lift_lets
  guard_target =ₛ let ty := Nat; (fun (x : ty) ↦ Fin x) (2 : Nat)
  exact 0


example : (id : Nat → Nat) = (fun (x : let ty := Nat; ty) => x) := by
  lift_lets
  guard_target =ₛ let ty := Nat; (id: Nat → Nat) = fun (x : ty) ↦ x
  rfl

example : (x : let ty := Nat; ty) → let y := (1 : Nat); Fin (y + Nat.succ x) := by
  lift_lets
  guard_target =ₛ let ty := Nat; let y := 1; (x : ty) → Fin (y + Nat.succ x)
  intro ty y x
  rw [Nat.add_succ, Nat.succ_eq_add_one]
  exact 0

example : (x : Nat) → (y : Nat) → let z := x + 1; let w := 3; Fin (z + w) := by
  lift_lets
  guard_target =ₛ let w := 3; (x : Nat) → let z := x + 1; Nat → Fin (z + w)
  intro w x z _y
  simp
  exact 0

example : (x : Nat) → let z := x + 1; (y : Nat) → let w := 3; Fin (z + w) := by
  lift_lets
  guard_target =ₛ let w := 3; (x : Nat) → let z := x + 1; Nat → Fin (z + w)
  intro w x z _y
  simp
  exact 0

example : (let x := 1; x) = (let x := 1; x) := by
  lift_lets
  guard_target =ₛ let x := 1; x = x
  rfl

example : (let x := 1; x) = (let y := 1; y) := by
  lift_lets
  guard_target =ₛ let x := 1; let y := 1; x = y
  rfl

example (h : (let x := 1; x) = y) : True := by
  lift_lets at h
  guard_hyp h :ₛ let x := 1; x = y
  trivial
