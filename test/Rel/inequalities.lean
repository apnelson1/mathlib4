/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Rel

/-! ## Inequalities -/

open Nat
set_option linter.unusedVariables false
-- set_option trace.Meta.Tactic.solveByElim true

example {x : ℤ} (hx : x ≥ 12) : x * x ^ 2 ≥ 12 * x ^ 2 := by rel [hx]

example {x y : ℤ} (hx : x ≥ 12) : y + x * x ≥ y + 12 * x := by rel [hx]

example {x : ℤ} (hx : x > 12) : x * x ^ 2 > 12 * x ^ 2 := by rel [hx]

example {x y : ℤ} (hx : x > 12) : y + x * x > y + 12 * x := by rel [hx]

-- not solved by `nlinarith` because of the cube
example {n m : ℤ} (hn : n ≥ 10) : n * n ^ 3 - m ≥ 10 * n ^ 3 - m := by rel [hn]

example {k m n : ℤ} (hn : n ≥ 10) : m + 7 * n * n ^ 2 - k ≥ m + 7 * 10 * n ^ 2 - k := by rel [hn]

example {x y : ℤ} (hx : x ≥ 12) : x ≥ 12 := by rel [hx]

example {x y : ℤ} (hx : x ≥ 12) : y + 8 * x ≥ y + 8 * 12 := by rel [hx]

-- not solved by `nlinarith` because of the cube and the absolute value
example {a b c x  y : ℤ} (hb : b ≥ 4) (hxy : x ≤ y) :
    c + (3 * |a| ^ 3 * b + b * 7 + 14) * x ≤ c + (3 * |a| ^ 3 * b + b * 7 + 14) * y := by
  rel [hxy]

example {x y : ℤ} (hy : 3 ≤ y) (hx : x ≥ 9) : y + 2 * x ≥ 3 + 2 * 9 := by rel [hx, hy]

example {a b : ℤ} (h2 : b ≥ 3) : 2 * b + 5 ≥ 2 * 3 + 5 := by rel [h2]

example {x y : ℝ} (h1 : x ≤ 3) : 4 * x - 3 ≤ 4 * 3 - 3 := by rel [h1]

example {x : ℝ} (h : x < 1) : 3 * x ≤ 3 * 1 := by rel [h]

example {x y : ℝ} (h1 : x < 3) : 4 * x - 3 < 4 * 3 - 3 := by rel [h1]

example {x : ℝ} (h : x < 1) : 3 * x < 3 * 1 := by rel [h]

example {x y : ℝ} (h1 : 1 ≤ y) (h2 : x < 2) : x * y ≤ 2 * y := by rel [h2]

-- for this test to pass, need the check to ensure that leading function application is
-- syntactically (not just definitionally) the same on both sides.
example {a b c : ℚ} (h2 : 2 ≤ a + b) : 2 + c ≤ (a + b) + c := by rel [h2]

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : 4 ≤ b) : (3 + 4) / 2 ≤ (a + b) / 2 := by rel [h1, h2]

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a : ℚ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by rel [h1]

example {a : ℝ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by rel [h1]

example {x y : ℝ} (h : 3 ≤ x) (h' : 1 ≤ y) : (3 + 1) / 2 ≤ (x + y) / 2 := by rel [h, h']

example {x y : ℝ} (h : x ≤ 3) : 0.1 * x ≤ 0.1 * 3 := by rel [h]

example {x y : ℝ} (h : x ≤ 3) : x / 10 ≤ 3 / 10 := by rel [h]

example {x y : ℝ} (h : x ≤ 3) : 1 / 10 * x ≤ 1 / 10 * 3 := by rel [h]

-- this tests that the tactic prioritizes applying hypotheses (such as, here, `0 ≤ a ^ 6`) over the
-- greedy application of nonnegativity lemmas
example {a b : ℚ} (h : 0 ≤ a ^ 6) : 0 + b ≤ a ^ 6 + b := by rel [h]

-- another priority test
example {k m n : ℤ}  (H : m ^ 2 ≤ n ^ 2) : k + m ^ 2 ≤ k + n ^ 2 := by rel [H]
