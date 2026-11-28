import OMAReductions.R_OeisA103151_conjecture_R1
import Mathlib.Tactic

/-!
# Reduction of the `n ≡ 2 (mod 3)` case of A103151

In this residue class the decomposition `2n + 1 = 2(n - 1) + 3` is available.
Whenever `n - 1` is prime, it immediately contributes that prime as `p`; this
positive case is proved here.  The remaining composite case is split by the
parity of `n`, equivalently by the two residue classes of `n` modulo `6`.
-/

namespace OMA.R_OeisA103151_conjecture_R1_H2_R1

open OeisA103151

/-- The composite exceptional case with `n` even. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 3 = 2 → ¬ (n - 1).Prime → n % 2 = 0 → a n ≥ 1

/-- The composite exceptional case with `n` odd. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 3 = 2 → ¬ (n - 1).Prime → n % 2 = 1 → a n ≥ 1

/-- If `n - 1` is prime, then `p = n - 1` is counted by `a n`. -/
theorem prime_predecessor_witness (n : ℕ) (hn : 4 ≤ n) (hnmod : n % 3 = 2)
    (hp : (n - 1).Prime) : a n ≥ 1 := by
  have hn5 : n ≠ 5 := by
    rintro rfl
    norm_num at hp
  have hnmin : 8 ≤ n := by omega
  have hq : 2 * n + 1 - 2 * (n - 1) = 3 := by omega
  have hmem : n - 1 ∈ Finset.filter (fun p : ℕ =>
      p.Prime ∧ p ≠ 2 ∧ 2 * p < 2 * n + 1 ∧ Nat.Prime (2 * n + 1 - 2 * p))
      (Finset.range (n + 1)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hp, by omega, by omega, ?_⟩
    rw [hq]
    decide
  have hpos : 0 < a n := by
    unfold a
    exact Finset.card_pos.mpr ⟨n - 1, hmem⟩
  omega

theorem main : H1 → H2 → OMA.R_OeisA103151_conjecture_R1.H2 := by
  intro h1 h2 n hn hnmod
  by_cases hp : (n - 1).Prime
  · exact prime_predecessor_witness n hn hnmod hp
  · have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · exact h1 n hn hnmod hp hpar
    · exact h2 n hn hnmod hp hpar

end OMA.R_OeisA103151_conjecture_R1_H2_R1
