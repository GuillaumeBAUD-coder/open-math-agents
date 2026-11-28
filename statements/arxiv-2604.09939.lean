import Mathlib

namespace OMA.S_arxiv_2604_09939

/-- A real normed vector lattice (normed Riesz space): a real normed space equipped with a
compatible lattice order such that `|x| ≤ |y| → ‖x‖ ≤ ‖y‖`, where `|x| = x ⊔ (-x)`. -/
structure NormedLattice where
  carrier : Type
  instNormedAddCommGroup : NormedAddCommGroup carrier
  instNormedSpace : NormedSpace ℝ carrier
  instLattice : Lattice carrier
  add_le_add_left :
    letI := instNormedAddCommGroup
    letI := instLattice
    ∀ a b : carrier, a ≤ b → ∀ c : carrier, c + a ≤ c + b
  smul_le_smul_of_nonneg :
    letI := instNormedAddCommGroup
    letI := instNormedSpace
    letI := instLattice
    ∀ (r : ℝ), 0 ≤ r → ∀ a b : carrier, a ≤ b → r • a ≤ r • b
  norm_le_of_abs_le :
    letI := instNormedAddCommGroup
    letI := instLattice
    ∀ a b : carrier, a ⊔ (-a) ≤ b ⊔ (-b) → ‖a‖ ≤ ‖b‖

/-- Modulus `|x| = x ⊔ (-x)` in a normed lattice. -/
def nlAbs (X : NormedLattice) (x : X.carrier) : X.carrier :=
  letI := X.instNormedAddCommGroup
  letI := X.instLattice
  x ⊔ (-x)

/-- Positive part `x⁺ = x ⊔ 0` in a normed lattice. -/
def nlPos (X : NormedLattice) (x : X.carrier) : X.carrier :=
  letI := X.instNormedAddCommGroup
  letI := X.instLattice
  x ⊔ 0

/-- A sequence in a normed lattice `X` is order-bounded if it lies in an order interval `[u, v]`. -/
def IsOrderBounded (X : NormedLattice) (x : ℕ → X.carrier) : Prop :=
  letI := X.instLattice
  ∃ u v : X.carrier, ∀ n : ℕ, u ≤ x n ∧ x n ≤ v

/-- Property (i) of Proposition 3 of arXiv:2604.09939: every norm-null sequence in `X` has an
order-bounded subsequence. -/
def HasNullOrderBoundedSubseq (X : NormedLattice) : Prop :=
  letI := X.instNormedAddCommGroup
  ∀ x : ℕ → X.carrier, Filter.Tendsto (fun n => ‖x n‖) Filter.atTop (nhds 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsOrderBounded X (x ∘ φ)

/-- A normed lattice `X` is majorizing in its norm completion `X̃`: every element of `X̃`
(represented by a norm-Cauchy sequence `(x_n)` in `X`) is bounded above in `X̃` by some `u ∈ X`
(i.e. `(x_n - u)⁺ → 0` in norm, so `u - lim x_n` lies in the closed positive cone `X̃₊`). -/
def IsMajorizingInCompletion (X : NormedLattice) : Prop :=
  letI := X.instNormedAddCommGroup
  ∀ x : ℕ → X.carrier, CauchySeq x →
    ∃ u : X.carrier, Filter.Tendsto (fun n => ‖nlPos X (x n - u)‖) Filter.atTop (nhds 0)

/-- A sequence `(x_n)` in `X` converges relatively uniformly to `x` with regulator `u ≥ 0`
if `|x_n - x| ≤ ε • u` eventually for every `ε > 0`. -/
def ConvergesRU (X : NormedLattice) (x : ℕ → X.carrier) (lim : X.carrier) : Prop :=
  letI := X.instNormedAddCommGroup
  letI := X.instNormedSpace
  letI := X.instLattice
  ∃ u : X.carrier, 0 ≤ u ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, nlAbs X (x n - lim) ≤ ε • u

/-- A subset `C ⊆ X` is relatively uniformly closed if it contains all limits of relatively
uniformly convergent sequences in `C`. -/
def IsRUClosed (X : NormedLattice) (C : Set X.carrier) : Prop :=
  ∀ (x : ℕ → X.carrier) (lim : X.carrier), (∀ n, x n ∈ C) → ConvergesRU X x lim → lim ∈ C

/-- An ideal of subsets of `ℕ`. -/
def IsIdealOnNat (I : Set (Set ℕ)) : Prop :=
  ∅ ∈ I ∧
  (∀ A B : Set ℕ, A ⊆ B → B ∈ I → A ∈ I) ∧
  (∀ A B : Set ℕ, A ∈ I → B ∈ I → A ∪ B ∈ I)

/-- A non-meager P-ideal on `ℕ` (using the Just–Mathias–Prikry–Simon 1990 Proposition 2.3
characterization adopted as the definition in arXiv:2604.09939): a proper ideal containing all
finite sets such that every sequence `(A_n) ⊆ I` with `A_n ⊆ [n, ∞)` has an infinite subset
`M ⊆ ℕ` with `⋃_{n ∈ M} A_n ∈ I`. -/
def IsNonMeagerPIdeal (I : Set (Set ℕ)) : Prop :=
  IsIdealOnNat I ∧
  Set.univ ∉ I ∧
  (∀ A : Set ℕ, A.Finite → A ∈ I) ∧
  ∀ A : ℕ → Set ℕ, (∀ n : ℕ, A n ∈ I) → (∀ n : ℕ, ∀ k ∈ A n, n ≤ k) →
    ∃ M : Set ℕ, M.Infinite ∧ (⋃ n ∈ M, A n) ∈ I

/-- Main results of Eugene Bilokopytov and Viktor Bohdanskyi (arXiv:2604.09939, settling
Question 8.17 of Bilokopytov–Troitsky):
1. Proposition 2: For any normed lattice `X`, being majorizing in its norm completion is
   equivalent to (ii) every norm-Cauchy sequence having an order-bounded subsequence,
   (iii) every increasing norm-Cauchy sequence being order-bounded, and (iv) every norm-summable
   sequence being order-bounded.
2. Proposition 3: For any normed lattice `X`, every norm-null sequence has an order-bounded
   subsequence if and only if every relatively uniformly closed subset of `X` is norm-closed.
3. Main Theorem (Theorem 6): There exists a non-meager P-ideal on `ℕ` if and only if there
   exists a normed lattice `X` in which every norm-null sequence has an order-bounded subsequence
   but `X` is not majorizing in its norm completion. -/
theorem main :
    (∀ X : NormedLattice,
      letI := X.instNormedAddCommGroup
      letI := X.instLattice
      (IsMajorizingInCompletion X ↔
        ∀ x : ℕ → X.carrier, CauchySeq x → ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsOrderBounded X (x ∘ φ)) ∧
      (IsMajorizingInCompletion X ↔
        ∀ x : ℕ → X.carrier, Monotone x → CauchySeq x → IsOrderBounded X x) ∧
      (IsMajorizingInCompletion X ↔
        ∀ x : ℕ → X.carrier, Summable (fun n => ‖x n‖) → IsOrderBounded X x)) ∧
    (∀ X : NormedLattice,
      letI := X.instNormedAddCommGroup
      HasNullOrderBoundedSubseq X ↔ ∀ C : Set X.carrier, IsRUClosed X C → IsClosed C) ∧
    ((∃ I : Set (Set ℕ), IsNonMeagerPIdeal I) ↔
      (∃ X : NormedLattice, HasNullOrderBoundedSubseq X ∧ ¬ IsMajorizingInCompletion X)) := by
  sorry

end OMA.S_arxiv_2604_09939
