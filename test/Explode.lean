import Mathlib.Tactic.Explode.Index

-- #check Mathlib.Explode.Thm

-- OLD, CURRENT
-- 0│   │ p  ├ Prop
-- 1│   │ hP ├ p
-- 2│1,1│ ∀I │ p → p
-- 3│0,2│ ∀I │ ∀ (p : Prop), p → p
theorem theorem_1 : ∀ (p : Prop), p → p :=
  λ (p : Prop) => (λ hP : p => hP)

-- OLD, CURRENT
-- 0│       │ p         ├ Prop
-- 1│       │ q         ├ Prop
-- 2│       │ hP        ├ p
-- 3│       │ hQ        ├ q
-- 4│0,1,2,3│ and.intro │ p ∧ q
-- 5│3,4    │ ∀I        │ q → p ∧ q
-- 6│2,5    │ ∀I        │ p → q → p ∧ q
-- 7│1,6    │ ∀I        │ ∀ (q : Prop), p → q → p ∧ q
-- 8│0,7    │ ∀I        │ ∀ (p q : Prop), p → q → p ∧ q
theorem theorem_2 : ∀ (p : Prop) (q : Prop), p → q → p ∧ q :=
  λ p => λ q => λ hP => λ hQ => And.intro hP hQ

-- OLD, CURRENT
-- 0 │       │ a         ├ Prop
-- 1 │       │ h         ├ a
-- 2 │       │ True      │ Prop
-- 3 │       │ hl        │ ┌ a
-- 4 │       │ trivial   │ │ True
-- 5 │3,4    │ ∀I        │ a → True
-- 6 │       │ hr        │ ┌ True
-- 7 │6,1    │ ∀I        │ True → a
-- 8 │0,2,5,7│ Iff.intro │ a ↔ True
-- 9 │1,8    │ ∀I        │ a → (a ↔ True)
-- 10│0,9    │ ∀I        │ ∀ (a : Prop), a → (a ↔ True)
theorem theorem_3 (a : Prop) (h : a) : a ↔ True :=
  Iff.intro
    (λ hl => trivial)
    (λ hr => h)

-- OLD, CURRENT
-- 0 │    │ U              ├ Prop
-- 1 │    │ W              ├ Prop
-- 2 │    │ hPQ            ├ U → W
-- 3 │    │ hNQ            ├ ¬W
-- 4 │    │ hP             ├ U
-- 5 │    │ false          │ Prop
-- 6 │2,4 │ ∀E             │ W
-- 7 │3,6 │ ∀E             │ false
-- 8 │5,7 │ false.elim.{0} │ false
-- 9 │4,8 │ ∀I             │ U → false
-- 10│3,9 │ ∀I             │ ¬W → U → false
-- 11│2,10│ ∀I             │ (U → W) → ¬W → U → false
-- 12│1,11│ ∀I             │ ∀ (W : Prop), (U → W) → ¬W → U → false
-- 13│0,12│ ∀I             │ ∀ (U W : Prop), (U → W) → ¬W → U → false
theorem theorem_4 : ∀ p q : Prop, (p → q) → (¬q → ¬p) :=
  λ U => λ W => λ hPQ => λ hNQ => λ hP => False.elim (hNQ (hPQ hP))

-- OLD, CURRENT
-- 0 │            │ p              ├ Prop
-- 1 │            │ q              ├ Prop
-- 2 │            │ hNQNP          ├ ¬q → ¬p
-- 3 │            │ hP             ├ p
-- 4 │1           │ Not            │ Prop
-- 5 │1           │ Classical.em   │ q ∨ ¬q
-- 6 │            │ hQ             │ ┌ q
-- 7 │6,6         │ ∀I             │ q → q
-- 8 │            │ hNQ            │ ┌ ¬q
-- 9 │2,8,3       │ ∀E             │ │ False
-- 10│1,9         │ False.elim.{0} │ │ q
--------- Notice old #explode only had reference 8 - this is fixed now
-- 11│8,10        │ ∀I             │ ¬q → q
-- 12│1,4,1,5,7,11│ Or.elim        │ q
-- 13│3,12        │ ∀I             │ p → q
-- 14│2,13        │ ∀I             │ (¬q → ¬p) → p → q
-- 15│1,14        │ ∀I             │ ∀ (q : Prop), (¬q → ¬p) → p → q
-- 16│0,15        │ ∀I             │ ∀ (p q : Prop), (¬q → ¬p) → p → q
theorem theorem_5 : ∀ p q : Prop, (¬q → ¬p) → (p → q) :=
  λ p => λ q =>
  λ hNQNP =>
  λ hP =>
    Or.elim (Classical.em q)
    (λ hQ => hQ)
    (λ hNQ =>
      let hNP := hNQNP hNQ
      False.elim (hNP hP)
    )

#explode theorem_5
