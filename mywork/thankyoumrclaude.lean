module

public import Mathlib.Tactic

-- Warm-up (intro, exact, apply, specialize)

example (P Q : Prop) : P → (Q → P) := by
  intro hP hQ
  exact hP

example (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP
  apply hQR
  apply hPQ
  exact hP

example (P Q R : Prop) : (P → Q → R) → (Q → P → R) := by
  intro hPQR hQ hP
  specialize hPQR hP
  specialize hPQR hQ
  exact hPQR

example (P Q : Prop) : ¬P → (P → Q) := by
  intro hnP hP
  by_contra hnQ
  apply hnP
  exact hP

-- Splitting and combining (constructor, rcases, left, right)

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro hPQ
  rcases hPQ with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro hPQ
  rcases hPQ with hP | hQ
  · right
    exact hP
  · left
    exact hQ

example (P Q R : Prop) : (P ∧ Q) ∨ R → (P ∨ R) ∧ (Q ∨ R) := by
  intro hPQR
  rcases hPQR with hPQ | hR
  · rcases hPQ with ⟨hP, hQ⟩
    constructor
    · left
      exact hP
    · left
      exact hQ
  · constructor
    · right
      exact hR
    · right
      exact hR

example (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro hPQR
  rcases hPQR with ⟨hP, hQR⟩
  by_cases hR : R
  · right
    constructor
    · exact hP
    · exact hR
  · left
    constructor
    · exact hP
    · rcases hQR with hQ | hRR
      · exact hQ
      · by_contra hQQ
        apply hR
        exact hRR

-- Negation (by_contra, specialize)

example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hPQ hnQ
  by_contra hnP
  apply hnQ
  apply hPQ
  exact hnP

example (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro hPQ
  constructor
  · by_contra hnP
    apply hPQ
    left
    exact hnP
  · by_contra hnQ
    apply hPQ
    right
    exact hnQ

example (P Q : Prop) : ¬(P ∧ Q) → (P → ¬Q) := by
  intro hPQ hP
  by_contra hnQ
  apply hPQ
  constructor
  · exact hP
  · exact hnQ

example (P : Prop) : ¬¬P → P := by
  intro hP
  by_contra hnP
  apply hP
  exact hnP

example (P Q : Prop) : (¬Q → ¬P) → (P → Q) := by
  intro hQP hP
  by_contra hQ
  specialize hQP hQ
  apply hQP
  exact hP

-- Case splitting (by_cases)

example (P Q : Prop) : ¬(P ∧ Q) → ¬P ∨ ¬Q := by
  intro hPQ
  by_cases hP : P
  · right
    by_contra hQ
    apply hPQ
    constructor
    · exact hP
    · exact hQ
  · left
    exact hP

example (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  by_cases hP : P
  · right
    by_cases hQ : Q
    · intro hPQ
      exact hP
    · intro hnQ
      exact hP
  · left
    intro hnP
    by_contra hQ
    apply hP
    exact hnP

example (P Q : Prop) : ((P → Q) → P) → P := by
  intro hPQP
  by_cases hP : P
  · exact hP
  · apply hPQP
    intro hnP
    by_contra hQ
    apply hP
    exact hnP

-- Quantifiers (rcases, specialize, intro, by_contra, use)

example (α : Type*) (P Q : α → Prop) : (∀ a, P a ∧ Q a) → ∀ a, P a := by
  intro h a
  specialize h a
  rcases h with ⟨hP, hQ⟩
  exact hP

example (α : Type*) (P : α → Prop) : (∃ a, P a) → ¬ ∀ a, ¬ P a := by
  intro h h1
  rcases h with ⟨a, ha⟩
  specialize h1 a
  apply h1
  exact ha

example (α : Type*) (P : α → Prop) : (∀ a, P a) → ¬ ∃ a, ¬ P a := by
  intro h h1
  rcases h1 with ⟨a, ha⟩
  specialize h a
  apply ha
  exact h

example (α : Type*) (P Q : α → Prop) : (∃ a, P a ∧ Q a) → (∃ a, P a) := by
  intro h
  rcases h with ⟨a, ha⟩
  rcases ha with ⟨hP, hQ⟩
  use a

-- Propositional

example (P Q : Prop) : (P → Q) → (¬P → Q) → Q := by
  intro hPQ hnPQ
  by_cases hP : P
  · apply hPQ
    exact hP
  · apply hnPQ
    exact hP

example (P Q : Prop) : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro h h1
  rcases h with ⟨hP, hQ⟩
  rcases h1 with hPP | hQQ
  · apply hP
    exact hPP
  · apply hQ
    exact hQQ

example (P Q : Prop) : ¬(P → Q) → P ∧ ¬Q := by
  intro h
  constructor
  · by_cases hQ : Q
    · have : P → Q := by
        by_cases hP : P
        · intro h1
          exact hQ
        · intro h1


example (P Q : Prop) : (P → Q) → ¬P ∨ Q := by
  sorry

example (P Q R : Prop) : ((P → Q) → R) → (P → R) → R := by
  sorry

example (P Q R : Prop) : (P → Q ∨ R) → (P → Q) ∨ (P → R) := by
  sorry

example (P Q R S : Prop) : (P → Q) ∧ (R → S) → (P ∨ R) → (Q ∨ S) := by
  sorry

-- Quantifiers

example (α : Type*) (P Q : α → Prop) : (∃ a, P a) → (∀ a, P a → Q a) → ∃ a, Q a := by
  sorry

example (α : Type*) (P Q : α → Prop) : (∀ a, P a ∨ Q a) → (∀ a, P a) ∨ (∃ a, Q a) := by
  sorry

-- The "drinker paradox": in any non-empty bar, there is someone such that
-- if they are drinking, then everyone is drinking.
example (α : Type*) (P : α → Prop) (a₀ : α) : ∃ a, (P a → ∀ b, P b) := by
  sorry
