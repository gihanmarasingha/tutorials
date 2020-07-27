import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split, {
    intros hpq hnq hp,
    exact hnq (hpq hp),
  }, {
    intros hnqnp hp,
    by_contradiction hnq,
    exact (hnqnp hnq) hp,
  }
end

-- 0056
/- The model solutions handle the first case more efficiently bu using a double contradiction. -/
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  split, {
    intro hnpq,
    by_cases hp : P, {
      by_cases hq : Q,
        exact ⟨hp, λ q, hnpq (λ p, q) ⟩,
        exact ⟨hp, hq⟩,
    }, {
      exfalso,
      have hpq : P → Q,
        intro p,
        exfalso, exact hp p,
      exact hnpq hpq,
    }
  }, {
    rintros ⟨hp,hnq⟩ hnpq,
    exact hnq (hnpq hp),
  }
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  sorry
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  sorry
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  sorry
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  sorry
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  sorry
end

end negation_quantifiers

