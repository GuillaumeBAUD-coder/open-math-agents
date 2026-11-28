import Mathlib

/-!
# Dihedral shuffle squares: every even ternary word?

Source: J. Grytczuk, B. Pawlik, M. Pleszczyński, *Variations on shuffle squares*,
https://arxiv.org/abs/2308.13882 (Conjecture 2, v2)
Credit: @SulkBash

## The problem (as the source states it)

* **Permutations of words.** For a permutation $\gamma$ of $[n]$ and a word
  $W = w_1 w_2 \cdots w_n$, put $\gamma(W) = w_{\gamma_1} w_{\gamma_2} \cdots w_{\gamma_n}$.
* **Similarity.** Two words $U, V$ of length $n$ are $\gamma$-similar if $U = \gamma(V)$ or
  $V = \gamma(U)$.
* **Shuffle squares.** A word $W$ is a *shuffle $\gamma$-square* if it can be split into two
  subwords that are $\gamma$-similar. A word is *even* if every letter occurs in it an even number
  of times.
* **Dihedral.** $D_n \le S_n$ consists of the $2n$ permutations corresponding to symmetries of a
  regular polygon with $n$ vertices. A *dihedral shuffle square* of length $2n$ is a shuffle
  $\gamma$-square with $\gamma \in D_n$.

**Conjecture 2.** Every even ternary word is a shuffle $\gamma$-square for a dihedral permutation
$\gamma$.

## Formalization notes

* **Words.** An even word has even length, so we consider words `W : Fin (2 * n) → Fin 3` of
  length `2n`, over the ternary alphabet `Fin 3`. `W` is even when each letter `a` occurs an even
  number of times. Positions are `0, …, 2n-1`.
* **Splitting.** "Split into two subwords" means: two strictly increasing index maps
  `f g : Fin n → Fin (2n)` with disjoint ranges, which together cover all `2n` positions. The two
  subwords are `U = W ∘ f` and `V = W ∘ g`.
* **Permuting.** $\gamma(V) = V \circ \gamma$ as a function `Fin n → Fin 3`, so $\gamma$-similarity
  is `W ∘ f = W ∘ g ∘ γ ∨ W ∘ g = W ∘ f ∘ γ`.
* **Dihedral permutations.** Label the vertices of the regular `n`-gon by `Fin n` in cyclic
  order. Its symmetries are the rotations `i ↦ c + i` and the reflections `i ↦ c - i`, with
  arithmetic in `Fin n` (mod `n`). `IsDihedral γ` says `γ` is one of these.
* **The empty word.** We take `n ≥ 1`. The empty word is trivially a shuffle square, splitting
  into two empty words, but "a regular polygon with `0` vertices" is meaningless; in the encoding
  above `D_0` would be empty.
-/

namespace OMA.S_arxiv_2308_13882

/-- `γ ∈ D_n`: a rotation `i ↦ c + i` or a reflection `i ↦ c - i` of the vertices `Fin n` of a
regular `n`-gon. -/
def IsDihedral {n : ℕ} (γ : Fin n → Fin n) : Prop :=
  ∃ c : Fin n, (∀ i, γ i = c + i) ∨ (∀ i, γ i = c - i)

/-- `W` (of length `2n`) is a shuffle `γ`-square: it splits into two complementary subwords
`U = W ∘ f` and `V = W ∘ g` with `U = γ(V)` or `V = γ(U)`, where `γ(V) = V ∘ γ`. -/
def IsShuffleSquareBy {α : Type*} {n : ℕ} (W : Fin (2 * n) → α) (γ : Fin n → Fin n) : Prop :=
  ∃ f g : Fin n → Fin (2 * n), StrictMono f ∧ StrictMono g ∧ (∀ i j, f i ≠ g j) ∧
    (W ∘ f = W ∘ g ∘ γ ∨ W ∘ g = W ∘ f ∘ γ)

/-- Conjecture 2 of Grytczuk–Pawlik–Pleszczyński: every nonempty even ternary word is a dihedral
shuffle square. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∀ W : Fin (2 * n) → Fin 3,
      (∀ a : Fin 3, Even ((Finset.univ.filter fun i => W i = a).card)) →
        ∃ γ : Fin n → Fin n, IsDihedral γ ∧ IsShuffleSquareBy W γ := by
  sorry

end OMA.S_arxiv_2308_13882
