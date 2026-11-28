import Mathlib

/-!
# Maximum joint entropy at a fixed agreement probability

Source: https://mathoverflow.net/questions/293913

The independent variables are represented by two laws on a finite alphabet.
The joint entropy is the sum of the marginal entropies by independence.
For overlap above the uniform value, the maximizing law has one heavier
symbol. Below the uniform value, the exact maximum is the largest score
from the stationary equations in at most three levels. The statement
also gives the attaining laws at the three endpoints and treats the
one-symbol alphabet.
-/

namespace OMA.S_mo_293913

open Real Set Finset

abbrev Law (n : ℕ) := Fin n → ℝ
abbrev LawPair (n : ℕ) := Law n × Law n

noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

def overlap {n : ℕ} (p q : Law n) : ℝ := ∑ i, p i * q i

noncomputable def jointEntropy {n : ℕ} (pq : LawPair n) : ℝ :=
  entropy pq.1 + entropy pq.2

def feasible (n : ℕ) (ε : ℝ) : Set (LawPair n) :=
  (stdSimplex ℝ (Fin n)).prod (stdSimplex ℝ (Fin n)) ∩ {pq | overlap pq.1 pq.2 = ε}

noncomputable def uniform (n : ℕ) : Law n := fun _ => (n : ℝ)⁻¹

def atom {n : ℕ} (i : Fin n) : Law n := Pi.single i 1

noncomputable def uniformMix {n : ℕ} (p : Law n) (t : ℝ) : Law n :=
  fun i => (1 - t) * uniform n i + t * p i

noncomputable def heavyWeight (n : ℕ) (ε : ℝ) : ℝ :=
  sqrt ((ε - (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹))

noncomputable def heavyLaw {n : ℕ} (i : Fin n) (ε : ℝ) : Law n :=
  uniformMix (atom i) (heavyWeight n ε)

noncomputable def stationaryRoot (B c x : ℝ) : ℝ := log x + c * exp (B - c * x)

/-- Values produced by the stationary equations and at most three distinct levels. -/
def stationaryCandidates (n : ℕ) (ε : ℝ) : Set ℝ :=
  {v | ∃ (A B c : ℝ) (S : Finset ℝ) (m : ℝ → ℕ),
    0 < c ∧ S.card ≤ 3 ∧ (∀ x ∈ S, 0 < x ∧ stationaryRoot B c x = A) ∧
    (∑ x ∈ S, m x) = n ∧
    (∑ x ∈ S, (m x : ℝ) * x) = 1 ∧
    (∑ x ∈ S, (m x : ℝ) * exp (B - c * x)) = 1 ∧
    (∑ x ∈ S, (m x : ℝ) * (x * exp (B - c * x))) = ε ∧
    v = -A - B + 2 * c * ε}

noncomputable def uniformOn {n : ℕ} (S : Finset (Fin n)) : Law n :=
  fun i => if i ∈ S then (S.card : ℝ)⁻¹ else 0

end OMA.S_mo_293913

namespace OMA.S_mo_293913

open Real Set Finset

theorem main :
    (∀ (ε : ℝ) (p q : Law 1), (p,q) ∈ feasible 1 ε → ε = 1 ∧ jointEntropy (p,q) = 0) ∧
    (∀ n : ℕ, 2 ≤ n → ∃ S : Finset (Fin n), S.card = n / 2 ∧
      (uniformOn S, uniformOn Sᶜ) ∈ feasible n 0 ∧
      jointEntropy (uniformOn S, uniformOn Sᶜ) =
        log (((n / 2 : ℕ) : ℝ) * ((n - n / 2 : ℕ) : ℝ)) ∧
      IsMaxOn jointEntropy (feasible n 0) (uniformOn S, uniformOn Sᶜ)) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < (n : ℝ)⁻¹ →
      ∃ v, IsGreatest (stationaryCandidates n ε) v ∧
        ∃ pq ∈ feasible n ε, jointEntropy pq = v ∧ IsMaxOn jointEntropy (feasible n ε) pq) ∧
    (∀ n : ℕ, 2 ≤ n → (uniform n, uniform n) ∈ feasible n ((n : ℝ)⁻¹) ∧
      jointEntropy (uniform n, uniform n) = 2 * log (n : ℝ) ∧
      IsMaxOn jointEntropy (feasible n ((n : ℝ)⁻¹)) (uniform n, uniform n)) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, (n : ℝ)⁻¹ < ε → ε < 1 → ∀ i : Fin n,
      (heavyLaw i ε, heavyLaw i ε) ∈ feasible n ε ∧
      IsMaxOn jointEntropy (feasible n ε) (heavyLaw i ε, heavyLaw i ε)) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ i : Fin n, (atom i, atom i) ∈ feasible n 1 ∧
      jointEntropy (atom i, atom i) = 0 ∧ IsMaxOn jointEntropy (feasible n 1) (atom i, atom i)) := by
  sorry

end OMA.S_mo_293913
