import tuto_lib


section
/-
The first part of this file makes sure you can negate quantified statements
in your head without the help of `push_neg`.

You need to complete the statement and then use the `check_me` tactic
to check your answer. This tactic exists only for those exercises,
it mostly calls `push_neg` and then cleans up a bit.

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
-/

-- In this section, u denotes a sequence of real numbers
-- f is a function from ℝ to ℝ
-- x₀ and l are real numbers
variables (u : ℕ → ℝ) (f : ℝ → ℝ) (x₀ l : ℝ)

/- Negation of "u tends to l" -/
-- 0062
example : ¬ (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε) ↔
∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| > ε
:=
begin
  check_me,
end

/- Negation of "f is continuous at x₀" -/
-- 0063
example : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ →  |f x - f x₀| ≤ ε) ↔
∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ |f x - f x₀| > ε
:=
begin
  check_me,
end

/-
In the next exercise, we need to keep in mind that
`∀ x x', ...` is the abbreviation of
`∀ x, ∀ x', ... `. 

Also, `∃ x x', ...` is the abbreviation of `∃ x, ∃ x', ...`.
-/

/- Negation of "f is uniformly continuous on ℝ" -/
-- 0064
example : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x x', |x' - x| ≤ δ →  |f x' - f x| ≤ ε) ↔
∃ ε > 0, ∀ δ > 0, ∃ x x', |x' - x| ≤ δ ∧ |f x' - f x| > ε
:=
begin
  check_me,
end

/- Negation of "f is sequentially continuous at x₀" -/
-- 0065
example : ¬ (∀ u : ℕ → ℝ, (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ ε) → (∀ ε > 0, ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε))  ↔
  ∃ u : ℕ → ℝ, (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ ε) ∧
  (∃ ε > 0, ∀ N, ∃ n ≥ N, |(f ∘ u) n - f x₀| > ε)
:=
begin
  check_me,
end
end -- end of section

/-
We now turn to elementary applications of negations to limits of sequences.
Remember that `linarith` can find easy numerical contradictions.

Also recall the following lemmas:

abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

/-- The sequence `u` tends to `+∞`. -/
def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A
-/

-- 0066
/- My comment: the model solutions do not use push_neg or proof by contradiction-/
example {u : ℕ → ℝ} : tendsto_infinity u → ∀ l, ¬ seq_limit u l :=
begin
  intros htinf l,
  unfold seq_limit,
  push_neg,
  cases htinf (2+l) with M hn,
  use [1, (by linarith)],
  intro N,
  use (max N M),
  split, {
    exact le_max_left N M,
  }, {
    by_contradiction H,
    simp [abs_le] at H,
    cases H,
    have : 2 +l < 2 + l,
    calc 2 + l ≤ u (max N M) : hn (max N M) (le_max_right N M)
           ... < 2 + l : by linarith,
    linarith,
  }


end

def nondecreasing_seq (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

-- 0067
example (u : ℕ → ℝ) (l : ℝ) (h : seq_limit u l) (h' : nondecreasing_seq u) :
  ∀ n, u n ≤ l :=
begin
  intro k,
  by_contradiction H,
  cases h ((u k -l)/2) (by linarith) with N hN,
  let p := max k N,
  specialize hN p (le_max_right k N),
  specialize h' k p (le_max_left k N),
  rw abs_le at hN,
  linarith,
end

/-
In the following exercises, `A : set ℝ` means that A is a set of real numbers.
We can use the usual notation x ∈ A.

The notation `∀ x ∈ A, ...` is the abbreviation of `∀ x, x ∈ A → ... `

The notation `∃ x ∈ A, ...` is the abbreviation of `∃ x, x ∈ A ∧ ... `.
More precisely it is the abbreviation of `∃ x (H : x ∈ A), ...`
which is Lean's strange way of saying `∃ x, x ∈ A ∧ ... `. 
You can convert between these forms using the lemma 
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q

We'll work with upper bounds and supremums.
Again we'll introduce specialized definitions for the sake of exercises, but mathlib
has more general versions.


def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y


Remark: one can easily show that a set of real numbers has at most one sup,
but we won't need this.
-/

-- 0068
/- My comment: the model solution is much shorter and uses contrapose! -/
example {A : set ℝ} {x : ℝ} (hx : is_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  by_contradiction H,
  push_neg at H,
  cases hx with _ hsup,
  specialize hsup y H,
  linarith,
end

/-
Let's do a variation on an example from file 07 that will be useful in the last
exercise below.
-/

-- 0069
lemma le_of_le_add_all' {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  contrapose!,
  intro hxy,
  use ((y-x)/2),
  split;
    linarith,
end

-- 0070
example {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y :=
begin
  apply le_of_le_add_all',
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  specialize hN N (by linarith),
  specialize ineg N,
  rw abs_le at hN,
  cases hN with h _,
  linarith,
end

