/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module algebra.order.lattice_group
! leanprover-community/mathlib commit 5dc275ec639221ca4d5f56938eb966f6ad9bc89f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Order.Closure

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory, concentrating on the commutative case.

## Main statements

- `pos_div_neg`: Every element `a` of a lattice ordered commutative group has a decomposition
  `a⁺-a⁻` into the difference of the positive and negative component.
- `pos_inf_neg_eq_one`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality.

It is shown that the inf and sup operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered commutative group
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered commutative group
- `|a| = a⊔(-a)`: The *absolute value* of an element `a` of a lattice ordered commutative group

## Implementation notes

A lattice ordered commutative group is a type `α` satisfying:

* `[Lattice α]`
* `[CommGroup α]`
* `[CovariantClass α α (*) (≤)]`

The remainder of the file establishes basic properties of lattice ordered commutative groups. A
number of these results also hold in the non-commutative case ([Birkhoff][birkhoff1942],
[Fuchs][fuchs1963]) but we have not developed that here, since we are primarily interested in vector
lattices.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, ordered, group
-/


-- Needed for squares
-- Needed for squares
universe u

variable {α : Type u} [Lattice α] [CommGroup α]

-- Special case of Bourbaki A.VI.9 (1)
-- c + (a ⊔ b) = (c + a) ⊔ (c + b)
@[to_additive]
theorem mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c * b :=
  (OrderIso.mulLeft _).map_sup _ _
#align mul_sup mul_sup
#align add_sup add_sup

@[to_additive]
theorem sup_mul [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c :=
  (OrderIso.mulRight _).map_sup _ _
#align sup_mul sup_mul
#align sup_add sup_add

@[to_additive]
theorem mul_inf [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a ⊓ b) = c * a ⊓ c * b :=
  (OrderIso.mulLeft _).map_inf _ _
#align mul_inf mul_inf
#align add_inf add_inf

@[to_additive]
theorem inf_mul [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : (a ⊓ b) * c = a * c ⊓ b * c :=
  (OrderIso.mulRight _).map_inf _ _
#align inf_mul inf_mul
#align inf_add inf_add

-- Special case of Bourbaki A.VI.9 (2)
-- -(a ⊔ b)=(-a) ⊓ (-b)
@[to_additive]
theorem inv_sup_eq_inv_inf_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ :=
  (OrderIso.inv α).map_sup _ _
#align inv_sup_eq_inv_inf_inv inv_sup_eq_inv_inf_inv
#align neg_sup_eq_neg_inf_neg neg_sup_eq_neg_inf_neg

-- -(a ⊓ b) = -a ⊔ -b
@[to_additive]
theorem inv_inf_eq_sup_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ :=
  (OrderIso.inv α).map_inf _ _
#align inv_inf_eq_sup_inv inv_inf_eq_sup_inv
#align neg_inf_eq_sup_neg neg_inf_eq_sup_neg

-- Bourbaki A.VI.10 Prop 7
-- a ⊓ b + (a ⊔ b) = a + b
@[to_additive]
theorem inf_mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b :=
  calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b), mul_inv_cancel_right, mul_inv_cancel_comm]
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf_eq_sup_inv, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]
#align inf_mul_sup inf_mul_sup
#align inf_add_sup inf_add_sup

namespace LatticeOrderedCommGroup

-- see Note [lower instance priority]
/--
Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `a ⊔ 1` is said to be the *positive component* of `a`, denoted `a⁺`.
-/
@[to_additive
      "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type
      `α`,the element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`."]
instance (priority := 100) hasOneLatticeHasPosPart : PosPart α :=
  ⟨fun a => a ⊔ 1⟩
#align lattice_ordered_comm_group.has_one_lattice_has_pos_part LatticeOrderedCommGroup.hasOneLatticeHasPosPart
#align lattice_ordered_comm_group.has_zero_lattice_has_pos_part LatticeOrderedCommGroup.hasZeroLatticeHasPosPart

@[to_additive pos_part_def]
theorem m_pos_part_def (a : α) : a⁺ = a ⊔ 1 :=
  rfl
#align lattice_ordered_comm_group.m_pos_part_def LatticeOrderedCommGroup.m_pos_part_def
#align lattice_ordered_comm_group.pos_part_def LatticeOrderedCommGroup.pos_part_def

-- see Note [lower instance priority]
/--
Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `(-a) ⊔ 1` is said to be the *negative component* of `a`, denoted `a⁻`.
-/
@[to_additive
      "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type
      `α`, the element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`."]
instance (priority := 100) hasOneLatticeHasNegPart : NegPart α :=
  ⟨fun a => a⁻¹ ⊔ 1⟩
#align lattice_ordered_comm_group.has_one_lattice_has_neg_part LatticeOrderedCommGroup.hasOneLatticeHasNegPart
#align lattice_ordered_comm_group.has_zero_lattice_has_neg_part LatticeOrderedCommGroup.hasZeroLatticeHasNegPart

@[to_additive neg_part_def]
theorem m_neg_part_def (a : α) : a⁻ = a⁻¹ ⊔ 1 :=
  rfl
#align lattice_ordered_comm_group.m_neg_part_def LatticeOrderedCommGroup.m_neg_part_def
#align lattice_ordered_comm_group.neg_part_def LatticeOrderedCommGroup.neg_part_def

@[to_additive (attr := simp)]
theorem pos_one : (1 : α)⁺ = 1 :=
  sup_idem
#align lattice_ordered_comm_group.pos_one LatticeOrderedCommGroup.pos_one
#align lattice_ordered_comm_group.pos_zero LatticeOrderedCommGroup.pos_zero

@[to_additive (attr := simp)]
theorem neg_one : (1 : α)⁻ = 1 := by rw [m_neg_part_def, inv_one, sup_idem]
#align lattice_ordered_comm_group.neg_one LatticeOrderedCommGroup.neg_one
#align lattice_ordered_comm_group.neg_zero LatticeOrderedCommGroup.neg_zero

-- a⁻ = -(a ⊓ 0)
@[to_additive]
theorem neg_eq_inv_inf_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁻ = (a ⊓ 1)⁻¹ := by
  rw [m_neg_part_def, ← inv_inj, inv_sup_eq_inv_inf_inv, inv_inv, inv_inv, inv_one]
#align lattice_ordered_comm_group.neg_eq_inv_inf_one LatticeOrderedCommGroup.neg_eq_inv_inf_one
#align lattice_ordered_comm_group.neg_eq_neg_inf_zero LatticeOrderedCommGroup.neg_eq_neg_inf_zero

@[to_additive le_abs]
theorem le_mabs (a : α) : a ≤ |a| :=
  le_sup_left
#align lattice_ordered_comm_group.le_mabs LatticeOrderedCommGroup.le_mabs
#align lattice_ordered_comm_group.le_abs LatticeOrderedCommGroup.le_abs

-- -a ≤ |a|
@[to_additive]
theorem inv_le_abs (a : α) : a⁻¹ ≤ |a| :=
  le_sup_right
#align lattice_ordered_comm_group.inv_le_abs LatticeOrderedCommGroup.inv_le_abs
#align lattice_ordered_comm_group.neg_le_abs LatticeOrderedCommGroup.neg_le_abs

-- 0 ≤ a⁺
@[to_additive pos_nonneg]
theorem one_le_pos (a : α) : 1 ≤ a⁺ :=
  le_sup_right
#align lattice_ordered_comm_group.one_le_pos LatticeOrderedCommGroup.one_le_pos
#align lattice_ordered_comm_group.pos_nonneg LatticeOrderedCommGroup.pos_nonneg

-- 0 ≤ a⁻
@[to_additive neg_nonneg]
theorem one_le_neg (a : α) : 1 ≤ a⁻ :=
  le_sup_right
#align lattice_ordered_comm_group.one_le_neg LatticeOrderedCommGroup.one_le_neg
#align lattice_ordered_comm_group.neg_nonneg LatticeOrderedCommGroup.neg_nonneg

-- pos_nonpos_iff
@[to_additive]
theorem pos_le_one_iff {a : α} : a⁺ ≤ 1 ↔ a ≤ 1 := by
  rw [m_pos_part_def, sup_le_iff, and_iff_left le_rfl]
#align lattice_ordered_comm_group.pos_le_one_iff LatticeOrderedCommGroup.pos_le_one_iff
#align lattice_ordered_comm_group.pos_nonpos_iff LatticeOrderedCommGroup.pos_nonpos_iff

-- neg_nonpos_iff
@[to_additive]
theorem neg_le_one_iff {a : α} : a⁻ ≤ 1 ↔ a⁻¹ ≤ 1 := by
  rw [m_neg_part_def, sup_le_iff, and_iff_left le_rfl]
#align lattice_ordered_comm_group.neg_le_one_iff LatticeOrderedCommGroup.neg_le_one_iff
#align lattice_ordered_comm_group.neg_nonpos_iff LatticeOrderedCommGroup.neg_nonpos_iff

@[to_additive]
theorem pos_eq_one_iff {a : α} : a⁺ = 1 ↔ a ≤ 1 :=
  sup_eq_right
#align lattice_ordered_comm_group.pos_eq_one_iff LatticeOrderedCommGroup.pos_eq_one_iff
#align lattice_ordered_comm_group.pos_eq_zero_iff LatticeOrderedCommGroup.pos_eq_zero_iff

@[to_additive]
theorem neg_eq_one_iff' {a : α} : a⁻ = 1 ↔ a⁻¹ ≤ 1 :=
  sup_eq_right
#align lattice_ordered_comm_group.neg_eq_one_iff' LatticeOrderedCommGroup.neg_eq_one_iff'
#align lattice_ordered_comm_group.neg_eq_zero_iff' LatticeOrderedCommGroup.neg_eq_zero_iff'

@[to_additive]
theorem neg_eq_one_iff [CovariantClass α α Mul.mul LE.le] {a : α} : a⁻ = 1 ↔ 1 ≤ a := by
  rw [le_antisymm_iff, neg_le_one_iff, inv_le_one', and_iff_left (one_le_neg _)]
#align lattice_ordered_comm_group.neg_eq_one_iff LatticeOrderedCommGroup.neg_eq_one_iff
#align lattice_ordered_comm_group.neg_eq_zero_iff LatticeOrderedCommGroup.neg_eq_zero_iff

@[to_additive le_pos]
theorem m_le_pos (a : α) : a ≤ a⁺ :=
  le_sup_left
#align lattice_ordered_comm_group.m_le_pos LatticeOrderedCommGroup.m_le_pos
#align lattice_ordered_comm_group.le_pos LatticeOrderedCommGroup.le_pos

-- -a ≤ a⁻
@[to_additive]
theorem inv_le_neg (a : α) : a⁻¹ ≤ a⁻ :=
  le_sup_left
#align lattice_ordered_comm_group.inv_le_neg LatticeOrderedCommGroup.inv_le_neg
#align lattice_ordered_comm_group.neg_le_neg LatticeOrderedCommGroup.neg_le_neg

-- Bourbaki A.VI.12
--  a⁻ = (-a)⁺
@[to_additive]
theorem neg_eq_pos_inv (a : α) : a⁻ = a⁻¹⁺ :=
  rfl
#align lattice_ordered_comm_group.neg_eq_pos_inv LatticeOrderedCommGroup.neg_eq_pos_inv
#align lattice_ordered_comm_group.neg_eq_pos_neg LatticeOrderedCommGroup.neg_eq_pos_neg

-- a⁺ = (-a)⁻
@[to_additive]
theorem pos_eq_neg_inv (a : α) : a⁺ = a⁻¹⁻ := by rw [neg_eq_pos_inv, inv_inv]
#align lattice_ordered_comm_group.pos_eq_neg_inv LatticeOrderedCommGroup.pos_eq_neg_inv
#align lattice_ordered_comm_group.pos_eq_neg_neg LatticeOrderedCommGroup.pos_eq_neg_neg

-- We use this in Bourbaki A.VI.12  Prop 9 a)
-- c + (a ⊓ b) = (c + a) ⊓ (c + b)
@[to_additive]
theorem mul_inf_eq_mul_inf_mul [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    c * (a ⊓ b) = c * a ⊓ c * b := by
  refine' le_antisymm _ _
  rw [le_inf_iff, mul_le_mul_iff_left, mul_le_mul_iff_left]
  simp
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_self, one_mul, le_inf_iff,
    inv_mul_le_iff_le_mul, inv_mul_le_iff_le_mul]
  simp
#align lattice_ordered_comm_group.mul_inf_eq_mul_inf_mul LatticeOrderedCommGroup.mul_inf_eq_mul_inf_mul
#align lattice_ordered_comm_group.add_inf_eq_add_inf_add LatticeOrderedCommGroup.add_inf_eq_add_inf_add

-- Bourbaki A.VI.12  Prop 9 a)
-- a = a⁺ - a⁻
@[to_additive (attr := simp)]
theorem pos_div_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺ / a⁻ = a := by
  symm
  rw [div_eq_mul_inv]
  apply eq_mul_inv_of_mul_eq
  rw [m_neg_part_def, mul_sup, mul_one, mul_right_inv, sup_comm, m_pos_part_def]
#align lattice_ordered_comm_group.pos_div_neg LatticeOrderedCommGroup.pos_div_neg
#align lattice_ordered_comm_group.pos_sub_neg LatticeOrderedCommGroup.pos_sub_neg

-- Bourbaki A.VI.12  Prop 9 a)
-- a⁺ ⊓ a⁻ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive]
theorem pos_inf_neg_eq_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺ ⊓ a⁻ = 1 := by
  rw [← mul_right_inj (a⁻)⁻¹, mul_inf, mul_one, mul_left_inv, mul_comm, ← div_eq_mul_inv,
    pos_div_neg, neg_eq_inv_inf_one, inv_inv]
#align lattice_ordered_comm_group.pos_inf_neg_eq_one LatticeOrderedCommGroup.pos_inf_neg_eq_one
#align lattice_ordered_comm_group.pos_inf_neg_eq_zero LatticeOrderedCommGroup.pos_inf_neg_eq_zero

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊔b = b + (a - b)⁺
@[to_additive]
theorem sup_eq_mul_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ⊔ b = b * (a / b)⁺ :=
  calc
    a ⊔ b = b * (a / b) ⊔ b * 1 :=
      by rw [mul_one b, div_eq_mul_inv, mul_comm a, mul_inv_cancel_left]
    _ = b * (a / b ⊔ 1) := by rw [← mul_sup (a / b) 1 b]
#align lattice_ordered_comm_group.sup_eq_mul_pos_div LatticeOrderedCommGroup.sup_eq_mul_pos_div
#align lattice_ordered_comm_group.sup_eq_add_pos_sub LatticeOrderedCommGroup.sup_eq_add_pos_sub

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊓b = a - (a - b)⁺
@[to_additive]
theorem inf_eq_div_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ⊓ b = a / (a / b)⁺ :=
  calc
    a ⊓ b = a * 1 ⊓ a * (b / a) :=
      by rw [mul_one a, div_eq_mul_inv, mul_comm b, mul_inv_cancel_left]
    _ = a * (1 ⊓ b / a) := by rw [← mul_inf 1 (b / a) a]
    _ = a * (b / a ⊓ 1) := by rw [inf_comm]
    _ = a * ((a / b)⁻¹ ⊓ 1) := by
      rw [div_eq_mul_inv]
      nth_rw 1 [← inv_inv b]
      rw [← mul_inv, mul_comm b⁻¹, ← div_eq_mul_inv]
    _ = a * ((a / b)⁻¹ ⊓ 1⁻¹) := by rw [inv_one]
    _ = a / (a / b ⊔ 1) := by rw [← inv_sup_eq_inv_inf_inv, ← div_eq_mul_inv]
#align lattice_ordered_comm_group.inf_eq_div_pos_div LatticeOrderedCommGroup.inf_eq_div_pos_div
#align lattice_ordered_comm_group.inf_eq_sub_pos_sub LatticeOrderedCommGroup.inf_eq_sub_pos_sub

-- Bourbaki A.VI.12 Prop 9 c)
@[to_additive le_iff_pos_le_neg_ge]
theorem m_le_iff_pos_le_neg_ge [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ := by
  constructor <;> intro h
  · constructor
    · exact sup_le (h.trans (m_le_pos b)) (one_le_pos b)
    · rw [← inv_le_inv_iff] at h
      exact sup_le (h.trans (inv_le_neg a)) (one_le_neg a)
  · rw [← pos_div_neg a, ← pos_div_neg b]
    exact div_le_div'' h.1 h.2
#align lattice_ordered_comm_group.m_le_iff_pos_le_neg_ge LatticeOrderedCommGroup.m_le_iff_pos_le_neg_ge
#align lattice_ordered_comm_group.le_iff_pos_le_neg_ge LatticeOrderedCommGroup.le_iff_pos_le_neg_ge

@[to_additive neg_abs]
theorem m_neg_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |a|⁻ = 1 := by
  refine' le_antisymm _ _
  · rw [← pos_inf_neg_eq_one a]
    apply le_inf
    · rw [pos_eq_neg_inv]
      exact ((m_le_iff_pos_le_neg_ge _ _).mp (inv_le_abs a)).right
    · exact And.right (Iff.mp (m_le_iff_pos_le_neg_ge _ _) (le_mabs a))
  · exact one_le_neg _
#align lattice_ordered_comm_group.m_neg_abs LatticeOrderedCommGroup.m_neg_abs
#align lattice_ordered_comm_group.neg_abs LatticeOrderedCommGroup.neg_abs

@[to_additive pos_abs]
theorem m_pos_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |a|⁺ = |a| := by
  nth_rw 2 [← pos_div_neg (|a|)]
  rw [div_eq_mul_inv]
  symm
  rw [mul_right_eq_self, inv_eq_one]
  exact m_neg_abs a
#align lattice_ordered_comm_group.m_pos_abs LatticeOrderedCommGroup.m_pos_abs
#align lattice_ordered_comm_group.pos_abs LatticeOrderedCommGroup.pos_abs

@[to_additive abs_nonneg]
theorem one_le_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : 1 ≤ |a| := by
  rw [← m_pos_abs]
  exact one_le_pos _
#align lattice_ordered_comm_group.one_le_abs LatticeOrderedCommGroup.one_le_abs
#align lattice_ordered_comm_group.abs_nonneg LatticeOrderedCommGroup.abs_nonneg

-- The proof from Bourbaki A.VI.12 Prop 9 d)
-- |a| = a⁺ - a⁻
@[to_additive]
theorem pos_mul_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |a| = a⁺ * a⁻ := by
  rw [m_pos_part_def, sup_mul, one_mul, m_neg_part_def, mul_sup, mul_one, mul_inv_self, sup_assoc,
    ← @sup_assoc _ _ a, sup_eq_right.2 le_sup_right]
  exact (sup_eq_left.2 <| one_le_abs a).symm
#align lattice_ordered_comm_group.pos_mul_neg LatticeOrderedCommGroup.pos_mul_neg
#align lattice_ordered_comm_group.pos_add_neg LatticeOrderedCommGroup.pos_add_neg

-- a ⊔ b - (a ⊓ b) = |b - a|
@[to_additive]
theorem sup_div_inf_eq_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b) / (a ⊓ b) = |b / a| := by
  rw [sup_eq_mul_pos_div, inf_comm, inf_eq_div_pos_div, div_eq_mul_inv, div_eq_mul_inv b ((b / a)⁺),
    mul_inv_rev, inv_inv, mul_comm, ← mul_assoc, inv_mul_cancel_right, pos_eq_neg_inv (a / b),
    div_eq_mul_inv a b, mul_inv_rev, ← div_eq_mul_inv, inv_inv, ← pos_mul_neg]
#align lattice_ordered_comm_group.sup_div_inf_eq_abs_div LatticeOrderedCommGroup.sup_div_inf_eq_abs_div
#align lattice_ordered_comm_group.sup_sub_inf_eq_abs_sub LatticeOrderedCommGroup.sup_sub_inf_eq_abs_sub

-- 2•(a ⊔ b) = a + b + |b - a|
@[to_additive two_sup_eq_add_add_abs_sub]
theorem sup_sq_eq_mul_mul_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b) ^ 2 = a * b * |b / a| := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, ← mul_assoc, mul_comm, mul_assoc,
    ← pow_two, inv_mul_cancel_left]
#align lattice_ordered_comm_group.sup_sq_eq_mul_mul_abs_div LatticeOrderedCommGroup.sup_sq_eq_mul_mul_abs_div
#align lattice_ordered_comm_group.two_sup_eq_add_add_abs_sub LatticeOrderedCommGroup.two_sup_eq_add_add_abs_sub

-- 2•(a ⊓ b) = a + b - |b - a|
@[to_additive two_inf_eq_add_sub_abs_sub]
theorem inf_sq_eq_mul_div_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊓ b) ^ 2 = a * b / |b / a| := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev,
    inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, ← pow_two]
#align lattice_ordered_comm_group.inf_sq_eq_mul_div_abs_div LatticeOrderedCommGroup.inf_sq_eq_mul_div_abs_div
#align lattice_ordered_comm_group.two_inf_eq_add_sub_abs_sub LatticeOrderedCommGroup.two_inf_eq_add_sub_abs_sub

/-- Every lattice ordered commutative group is a distributive lattice
-/
@[to_additive "Every lattice ordered commutative additive group is a distributive lattice"]
def latticeOrderedCommGroupToDistribLattice (α : Type u) [s : Lattice α] [CommGroup α]
    [CovariantClass α α (· * ·) (· ≤ ·)] : DistribLattice α :=
  { s with
    le_sup_inf := by
      intros x y z
      rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)), inf_mul_sup x (y ⊓ z), ← inv_mul_le_iff_le_mul,
        le_inf_iff]
      constructor
      · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
        apply mul_le_mul'
        · apply inf_le_inf_left
          apply inf_le_left
        · apply inf_le_left
      · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
        apply mul_le_mul'
        · apply inf_le_inf_left
          apply inf_le_right
        · apply inf_le_right }
#align lattice_ordered_comm_group.lattice_ordered_comm_group_to_distrib_lattice LatticeOrderedCommGroup.latticeOrderedCommGroupToDistribLattice
#align lattice_ordered_comm_group.lattice_ordered_add_comm_group_to_distrib_lattice LatticeOrderedCommGroup.latticeOrderedAddCommGroupToDistribLattice

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
-- |a ⊔ c - (b ⊔ c)| + |a ⊓ c-b ⊓ c| = |a - b|
@[to_additive]
theorem abs_div_sup_mul_abs_div_inf [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)| * |(a ⊓ c) / (b ⊓ c)| = |a / b| := by
  letI : DistribLattice α := LatticeOrderedCommGroup.latticeOrderedCommGroupToDistribLattice α
  calc
    |(a ⊔ c) / (b ⊔ c)| * |(a ⊓ c) / (b ⊓ c)| =
        (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * |(a ⊓ c) / (b ⊓ c)| :=
      by rw [sup_div_inf_eq_abs_div]
    _ = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * ((b ⊓ c ⊔ a ⊓ c) / (b ⊓ c ⊓ (a ⊓ c))) :=
      by rw [sup_div_inf_eq_abs_div (b ⊓ c) (a ⊓ c)]
    _ = (b ⊔ a ⊔ c) / (b ⊓ a ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) := by
      rw [← sup_inf_right, ← inf_sup_right, sup_assoc, @sup_comm _ _ c (a ⊔ c), sup_right_idem,
        sup_assoc, inf_assoc, @inf_comm _ _ c (a ⊓ c), inf_right_idem, inf_assoc]
    _ = (b ⊔ a ⊔ c) * ((b ⊔ a) ⊓ c) / ((b ⊓ a ⊔ c) * (b ⊓ a ⊓ c)) := by rw [div_mul_div_comm]
    _ = (b ⊔ a) * c / ((b ⊓ a) * c) :=
      by rw [mul_comm, inf_mul_sup, mul_comm (b ⊓ a ⊔ c), inf_mul_sup]
    _ = (b ⊔ a) / (b ⊓ a) :=
      by rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← div_eq_mul_inv]
    _ = |a / b| := by rw [sup_div_inf_eq_abs_div]
#align lattice_ordered_comm_group.abs_div_sup_mul_abs_div_inf LatticeOrderedCommGroup.abs_div_sup_mul_abs_div_inf
#align lattice_ordered_comm_group.abs_sub_sup_add_abs_sub_inf LatticeOrderedCommGroup.abs_sub_sup_add_abs_sub_inf

-- pos_of_nonneg
/-- If `a` is positive, then it is equal to its positive component `a⁺`. -/
@[to_additive "If `a` is positive, then it is equal to its positive component `a⁺`."]
theorem pos_of_one_le (a : α) (h : 1 ≤ a) : a⁺ = a := by
  rw [m_pos_part_def]
  exact sup_of_le_left h
#align lattice_ordered_comm_group.pos_of_one_le LatticeOrderedCommGroup.pos_of_one_le
#align lattice_ordered_comm_group.pos_of_nonneg LatticeOrderedCommGroup.pos_of_nonneg

-- pos_eq_self_of_pos_pos
@[to_additive]
theorem pos_eq_self_of_one_lt_pos {α} [LinearOrder α] [CommGroup α] {x : α} (hx : 1 < x⁺) :
    x⁺ = x := by
  rw [m_pos_part_def, right_lt_sup, not_le] at hx
  rw [m_pos_part_def, sup_eq_left]
  exact hx.le
#align lattice_ordered_comm_group.pos_eq_self_of_one_lt_pos LatticeOrderedCommGroup.pos_eq_self_of_one_lt_pos
#align lattice_ordered_comm_group.pos_eq_self_of_pos_pos LatticeOrderedCommGroup.pos_eq_self_of_pos_pos

-- 0 ≤ a implies a⁺ = a
-- pos_of_nonpos
@[to_additive]
theorem pos_of_le_one (a : α) (h : a ≤ 1) : a⁺ = 1 :=
  pos_eq_one_iff.mpr h
#align lattice_ordered_comm_group.pos_of_le_one LatticeOrderedCommGroup.pos_of_le_one
#align lattice_ordered_comm_group.pos_of_nonpos LatticeOrderedCommGroup.pos_of_nonpos

@[to_additive neg_of_inv_nonneg]
theorem neg_of_one_le_inv (a : α) (h : 1 ≤ a⁻¹) : a⁻ = a⁻¹ := by
  rw [neg_eq_pos_inv]
  exact pos_of_one_le _ h
#align lattice_ordered_comm_group.neg_of_one_le_inv LatticeOrderedCommGroup.neg_of_one_le_inv
#align lattice_ordered_comm_group.neg_of_inv_nonneg LatticeOrderedCommGroup.neg_of_inv_nonneg

-- neg_of_neg_nonpos
@[to_additive]
theorem neg_of_inv_le_one (a : α) (h : a⁻¹ ≤ 1) : a⁻ = 1 :=
  neg_eq_one_iff'.mpr h
#align lattice_ordered_comm_group.neg_of_inv_le_one LatticeOrderedCommGroup.neg_of_inv_le_one
#align lattice_ordered_comm_group.neg_of_neg_nonpos LatticeOrderedCommGroup.neg_of_neg_nonpos

-- neg_of_nonpos
@[to_additive]
theorem neg_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : a ≤ 1) : a⁻ = a⁻¹ :=
  sup_eq_left.2 <| one_le_inv'.2 h
#align lattice_ordered_comm_group.neg_of_le_one LatticeOrderedCommGroup.neg_of_le_one
#align lattice_ordered_comm_group.neg_of_nonpos LatticeOrderedCommGroup.neg_of_nonpos

-- neg_of_nonneg'
@[to_additive]
theorem neg_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : a⁻ = 1 :=
  neg_eq_one_iff.mpr h
#align lattice_ordered_comm_group.neg_of_one_le LatticeOrderedCommGroup.neg_of_one_le
#align lattice_ordered_comm_group.neg_of_nonneg LatticeOrderedCommGroup.neg_of_nonneg

-- 0 ≤ a implies |a| = a
@[to_additive abs_of_nonneg]
theorem mabs_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : |a| = a :=
  sup_eq_left.2 <| Left.inv_le_self h
#align lattice_ordered_comm_group.mabs_of_one_le LatticeOrderedCommGroup.mabs_of_one_le
#align lattice_ordered_comm_group.abs_of_nonneg LatticeOrderedCommGroup.abs_of_nonneg

/-- The unary operation of taking the absolute value is idempotent. -/
@[to_additive (attr := simp) abs_abs
  "The unary operation of taking the absolute value is idempotent."]
theorem mabs_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |(|a|)| = |a| :=
  mabs_of_one_le _ (one_le_abs _)
#align lattice_ordered_comm_group.mabs_mabs LatticeOrderedCommGroup.mabs_mabs
#align lattice_ordered_comm_group.abs_abs LatticeOrderedCommGroup.abs_abs

@[to_additive abs_sup_sub_sup_le_abs]
theorem mabs_sup_div_sup_le_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)| ≤ |a / b| := by
  apply le_of_mul_le_of_one_le_left
  · rw [abs_div_sup_mul_abs_div_inf]
  · exact one_le_abs _
#align lattice_ordered_comm_group.mabs_sup_div_sup_le_mabs LatticeOrderedCommGroup.mabs_sup_div_sup_le_mabs
#align lattice_ordered_comm_group.abs_sup_sub_sup_le_abs LatticeOrderedCommGroup.abs_sup_sub_sup_le_abs

@[to_additive abs_inf_sub_inf_le_abs]
theorem mabs_inf_div_inf_le_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊓ c) / (b ⊓ c)| ≤ |a / b| := by
  apply le_of_mul_le_of_one_le_right
  · rw [abs_div_sup_mul_abs_div_inf]
  · exact one_le_abs _
#align lattice_ordered_comm_group.mabs_inf_div_inf_le_mabs LatticeOrderedCommGroup.mabs_inf_div_inf_le_mabs
#align lattice_ordered_comm_group.abs_inf_sub_inf_le_abs LatticeOrderedCommGroup.abs_inf_sub_inf_le_abs

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
-- |(a ⊔ c) - (b ⊔ c)| ⊔ |(a ⊓ c) - (b ⊓ c)| ≤ |a - b|
@[to_additive Birkhoff_inequalities]
theorem m_Birkhoff_inequalities [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)| ⊔ |(a ⊓ c) / (b ⊓ c)| ≤ |a / b| :=
  sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)
set_option linter.uppercaseLean3 false in
#align lattice_ordered_comm_group.m_Birkhoff_inequalities LatticeOrderedCommGroup.m_Birkhoff_inequalities
set_option linter.uppercaseLean3 false in
#align lattice_ordered_comm_group.Birkhoff_inequalities LatticeOrderedCommGroup.Birkhoff_inequalities

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/-- The absolute value satisfies the triangle inequality.
-/
@[to_additive abs_add_le "The absolute value satisfies the triangle inequality."]
theorem mabs_mul_le [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : |a * b| ≤ |a| * |b| := by
  apply sup_le
  · exact mul_le_mul' (le_mabs a) (le_mabs b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_abs _) (inv_le_abs _)
#align lattice_ordered_comm_group.mabs_mul_le LatticeOrderedCommGroup.mabs_mul_le
#align lattice_ordered_comm_group.abs_add_le LatticeOrderedCommGroup.abs_add_le

-- |a - b| = |b - a|
@[to_additive]
theorem abs_inv_comm (a b : α) : |a / b| = |b / a| := by
  dsimp only [Abs.abs]
  rw [inv_div a b, ← inv_inv (a / b), inv_div, sup_comm]
#align lattice_ordered_comm_group.abs_inv_comm LatticeOrderedCommGroup.abs_inv_comm
#align lattice_ordered_comm_group.abs_neg_comm LatticeOrderedCommGroup.abs_neg_comm

-- | |a| - |b| | ≤ |a - b|
@[to_additive]
theorem abs_abs_div_abs_le [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
|(|a| / |b|)| ≤ |a / b| := by
  rw [abs_eq_sup_inv, sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert mabs_mul_le (a / b) b
    rw [div_mul_cancel']
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, abs_inv_comm]
    convert mabs_mul_le (b / a) a
    · rw [div_mul_cancel']
#align lattice_ordered_comm_group.abs_abs_div_abs_le LatticeOrderedCommGroup.abs_abs_div_abs_le
#align lattice_ordered_comm_group.abs_abs_sub_abs_le LatticeOrderedCommGroup.abs_abs_sub_abs_le

end LatticeOrderedCommGroup

namespace LatticeOrderedAddCommGroup

variable {β : Type u} [Lattice β] [AddCommGroup β]

section solid

/-- A subset `s ⊆ β`, with `β` an `AddCommGroup` with a `Lattice` structure, is solid if for
all `x ∈ s` and all `y ∈ β` such that `|y| ≤ |x|`, then `y ∈ s`. -/
def IsSolid (s : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s
#align lattice_ordered_add_comm_group.is_solid LatticeOrderedAddCommGroup.IsSolid

/-- The solid closure of a subset `s` is the smallest superset of `s` that is solid. -/
def solidClosure (s : Set β) : Set β := { y | ∃ x ∈ s, |y| ≤ |x| }
#align lattice_ordered_add_comm_group.solid_closure LatticeOrderedAddCommGroup.solidClosure

theorem isSolid_solidClosure (s : Set β) : IsSolid (solidClosure s) :=
  fun _ ⟨y, hy, hxy⟩ _ hzx => ⟨y, hy, hzx.trans hxy⟩
#align lattice_ordered_add_comm_group.is_solid_solid_closure LatticeOrderedAddCommGroup.isSolid_solidClosure

theorem solidClosure_min (s t : Set β) (h1 : s ⊆ t) (h2 : IsSolid t) : solidClosure s ⊆ t :=
  fun _ ⟨_, hy, hxy⟩ => h2 (h1 hy) hxy
#align lattice_ordered_add_comm_group.solid_closure_min LatticeOrderedAddCommGroup.solidClosure_min

end solid

end LatticeOrderedAddCommGroup
