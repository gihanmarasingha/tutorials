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


/- My comments: 
  What wasn't obvious to me before starting this question is that = has higher order of precedence that → or ↔.

  So,
    propext : (A ↔ B) → (A = B)
  and the question asks us to prove ¬P ↔ (P = false).
-/


-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  split, {
    intro hnp,
    suffices h : P ↔ false,
      exact propext h,
    split; contradiction,
  }, {
    rintro ⟨h,rfl⟩,
    contradiction,
  }
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split, {
    intro hna,
    by_contradiction hnex,
    apply hna,
    intro x,
    by_contradiction h,
    apply hnex,
    use x,
  }, {
    rintros ⟨x,hn⟩ hax,
    exact hn (hax x),
  }
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  split, {
    intros hnex x hnp,
    apply hnex,
    use x,
    exact hnp,
  }, {
    rintros hax ⟨x,hx⟩,
    exact (hax x) hx,
  }
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  split, {
    intros hnex ε ε_pos hnp,
    apply hnex,
    use ε,
    exact ⟨ε_pos, hnp⟩,
  }, {
    rintros ha ⟨ε,⟨ε_pos,hp⟩⟩,
    exact (ha ε ε_pos) hp,
  }
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  split, {
    intro hna,
    by_contradiction hex,
    apply hna,
    intros x x_pos,
    by_contradiction hp,
    apply hex,
    use x,
    exact ⟨x_pos, hp⟩,
  }, {
    rintros ⟨x,x_pos,hnp⟩ hax,
    exact hnp (hax x x_pos),
  }
end

end negation_quantifiers

