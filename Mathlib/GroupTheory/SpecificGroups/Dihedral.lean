/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam

! This file was ported from Lean 3 source module group_theory.specific_groups.dihedral
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Exponent

/-!
# Dihedral Groups

We define the dihedral groups `DihedralGroup n`, with elements `r i` and `sr i` for `i : ZMod n`.

For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/


/-- For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/
inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq
#align dihedral_group DihedralGroup

namespace DihedralGroup

variable {n : ℕ}

/-- Multiplication of the dihedral group.
-/
private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

/-- The identity `1` is the rotation by `0`.
-/
private def one : DihedralGroup n :=
  r 0

instance : Inhabited (DihedralGroup n) :=
  ⟨one⟩

/-- The inverse of a an element of the dihedral group.
-/
private def inv : DihedralGroup n → DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

/-- The group structure on `DihedralGroup n`.
-/
instance : Group (DihedralGroup n) where
  mul := mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro (a | a)
    exact congr_arg r (zero_add a)
    exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    exact congr_arg r (add_zero a)
    exact congr_arg sr (add_zero a)
  inv := inv
  mul_left_inv := by
    rintro (a | a)
    exact congr_arg r (neg_add_self a)
    exact congr_arg r (sub_self a)

@[simp]
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl
#align dihedral_group.r_mul_r DihedralGroup.r_mul_r

@[simp]
theorem r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl
#align dihedral_group.r_mul_sr DihedralGroup.r_mul_sr

@[simp]
theorem sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl
#align dihedral_group.sr_mul_r DihedralGroup.sr_mul_r

@[simp]
theorem sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl
#align dihedral_group.sr_mul_sr DihedralGroup.sr_mul_sr

theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl
#align dihedral_group.one_def DihedralGroup.one_def

private def fintypeHelper : Sum (ZMod n) (ZMod n) ≃ DihedralGroup n where
  invFun i := match i with
    | r j => Sum.inl j
    | sr j => Sum.inr j
  toFun i := match i with
    | Sum.inl j => r j
    | Sum.inr j => sr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- If `0 < n`, then `DihedralGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by simp_rw [ne_eq]⟩⟩

/-- If `0 < n`, then `DihedralGroup n` has `2n` elements.
-/
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]
#align dihedral_group.card DihedralGroup.card

@[simp]
theorem r_one_pow (k : ℕ) : (r 1 : DihedralGroup n) ^ k = r k := by
  induction' k with k IH
  · rw [Nat.cast_zero]
    rfl
  · rw [pow_succ, IH, r_mul_r]
    congr 1
    norm_cast
    rw [Nat.one_add]
#align dihedral_group.r_one_pow DihedralGroup.r_one_pow

-- @[simp] -- Porting note: simp changes the goal to `r 0 = 1`. `r_one_pow_n` is no longer useful.
theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1 := by
  rw [r_one_pow, one_def]
  congr 1
  exact ZMod.nat_cast_self _
#align dihedral_group.r_one_pow_n DihedralGroup.r_one_pow_n

-- @[simp] -- Porting note: simp changes the goal to `r 0 = 1`. `sr_mul_self` is no longer useful.
theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1 := by rw [sr_mul_sr, sub_self, one_def]
#align dihedral_group.sr_mul_self DihedralGroup.sr_mul_self

/-- If `0 < n`, then `sr i` has order 2.
-/
@[simp]
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, sr_mul_self]
  · -- Porting note: Previous proof was `decide`
    revert n
    simp_rw [one_def, ne_eq, forall_const]
#align dihedral_group.order_of_sr DihedralGroup.orderOf_sr

/-- If `0 < n`, then `r 1` has order `n`.
-/
@[simp]
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow, one_def]
    apply mt r.inj
    simpa using hn.ne'
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
      orderOf_dvd_of_pow_eq_one <| @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero, ZMod.val_nat_cast, Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).ne
#align dihedral_group.order_of_r_one DihedralGroup.orderOf_r_one

/-- If `0 < n`, then `i : ZMod n` has order `n / gcd n i`.
-/
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val := by
  conv_lhs => rw [← ZMod.nat_cast_zmod_val i]
  rw [← r_one_pow, orderOf_pow, orderOf_r_one]
#align dihedral_group.order_of_r DihedralGroup.orderOf_r

theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2 := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      refine' Nat.dvd_trans ⟨gcd n m.val, _⟩ (dvd_lcm_left n 2)
      · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert Monoid.order_dvd_exponent (r (1 : ZMod n))
      exact orderOf_r_one.symm
    · convert Monoid.order_dvd_exponent (sr (0 : ZMod n))
      exact (orderOf_sr 0).symm
#align dihedral_group.exponent DihedralGroup.exponent

end DihedralGroup
