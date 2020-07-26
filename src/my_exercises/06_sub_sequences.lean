import tuto_lib
/-
This file continues the elementary study of limits of sequences. 
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub (x y : ℝ) : |x - y| = |y - x|

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

and the definition:

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

You can also use a property proved in the previous file:

unique_limit : seq_limit u l → seq_limit u l' → l = l'

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m
-/


variable { φ : ℕ → ℕ}

example (a b : ℕ) : a < b → a.succ ≤ b :=
begin
  exact nat.succ_le_iff.mpr
end


/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete 
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
-- I've written my own solution below. Massot's is simpler.
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros he n,
  induction n with k hk,
    linarith, -- base case
    have : φ k < φ (k.succ) :=
      he k k.succ _,
    have : k < φ (k.succ) := by linarith,
    exact nat.succ_le_of_lt this,
    exact lt_add_one k,    
end

/-- Extractions take arbitrarily large values for arbitrarily large 
inputs. -/
-- 0039
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros he N N',
  use (max N N'),
  split, {
    exact le_max_right _ _,
  }, {
    have : φ (max N N') ≥ max N N' :=
      id_le_extraction' he (max N N'),
    have : max N N' ≥ N := le_max_left _ _,
    linarith,
  }

end

/-- A real number `a` is a cluster point of a sequence `u` 
if `u` has a subsequence converging to `a`. 

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
-/

variables {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but displays it as the confusing:
`∃ (n : ℕ) (H : n ≥ N)`
One gets used to it. Alternatively, one can get rid of it using the lemma
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
-- 0040
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros hcp ε ε_pos N,
  rcases hcp with ⟨φ, ⟨hexf,hseq⟩⟩,
  rcases (hseq ε ε_pos) with ⟨N₀, hn⟩,
  rcases (extraction_ge hexf N N₀) with ⟨m,⟨H,hphi⟩⟩,
  use (φ m),
  split, {
    exact hphi,
  }, {
    specialize hn m,
    exact hn H,
  }
end

/-
The above exercice can be done in five lines. 
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/

/-- If `u` tends to `l` then its subsequences tend to `l`. -/
-- 0041
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases (h ε ε_pos) with N h2,
  use N,
  intros n hn,
  apply h2,
  linarith [id_le_extraction' hφ n],
end

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
-- 0042
/- I give two proofs. The first proof is quick and uses the results we've already proved. The second is longer! -/

lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  rcases ha with ⟨φ,⟨hφ, hφa⟩⟩,
  have hφl : seq_limit (u ∘ φ) l :=
    subseq_tendsto_of_tendsto' hl  hφ,
  exact unique_limit hφa hφl,
end

example (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  apply eq_of_abs_sub_le_all,
  intros ε ε_pos,
  cases (hl (ε/2) (by linarith)) with N₁ hN₁,
  rcases ha with ⟨φ,⟨hφ,hseqφ⟩⟩,
  cases (hseqφ (ε/2) (by linarith)) with N₂ hN₂,
  specialize hN₂ (max N₁ N₂),
  specialize hN₁ (φ (max N₁ N₂)),
  have hf :  N₁ ≤ φ (max N₁ N₂) :=
    calc N₁ ≤ max N₁ N₂ : le_max_left _ _
        ... ≤ φ (max N₁ N₂) : id_le_extraction' hφ _,
  calc
    |a - l| = |(a - u (φ (max N₁ N₂))) + (u (φ (max N₁ N₂)) -l )| : by ring
        ... ≤ |(a - u (φ (max N₁ N₂)))| + |(u (φ (max N₁ N₂)) -l )| : by simp [abs_add]
        ... = |u (φ (max N₁ N₂))- a| + |u (φ (max N₁ N₂)) -l| : by simp [abs_sub]
        ... ≤ ε/2 + |u (φ (max N₁ N₂)) -l| : by simp [hN₂ (le_max_right _ _)]
        ... ≤ ε/2 + ε/2 : by linarith [hN₁ hf]
        ... ≤ ε : by linarith,
end


/-- Cauchy_sequence sequence -/
def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  rintro ⟨l, hseql⟩,
  intros ε ε_pos,
  cases (hseql (ε/2) (by linarith)) with N hN,
  use N,
  intros p q hp hq,
  calc |u p - u q| = |(u p - l) + (l - u q)| : by ring
               ... ≤ |u p - l| + |l - u q| : by apply abs_add
               ... = |u p - l| + |u q - l| : by simp [abs_sub]
               ... ≤ ε/2 + |u q - l| : by simp [hN p hp]
               ... ≤ ε/2 + ε/2 : by linarith [hN q hq]
               ... ≤ ε : by linarith,
end


/- 
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/
-- 0044
example (hu : cauchy_sequence u) (hl : cluster_point u l) : seq_limit u l :=
begin
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N₁ hN₁,
  rcases near_cluster hl (ε/2) (by linarith) N₁ with ⟨p,hpN₁,hp⟩,
  use N₁,
  intros n hn,
  have : n ≥ N₁, linarith,
  calc |u n - l| = |(u n - u p) +  (u p - l)| : by ring
             ... ≤ |u n - u p| + |u p - l| : by simp [abs_add]
             ... ≤ ε/2 + |u p - l| : by simp [hN₁ n p (by linarith) hpN₁]
             ... ≤ ε/2 + ε/2: by linarith [hp]
             ... ≤ ε : by ring,
end