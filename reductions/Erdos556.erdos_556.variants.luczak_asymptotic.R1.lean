import FormalConjectures.ErdosProblems.«556»

/-! The large even and odd cycle embedding bounds imply Łuczak’s asymptotic upper bound. -/

namespace OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_R1

open Filter SimpleGraph

/- The upper-bound half of the large even cycle theorem of Benevides and
Skokan. The colors are given as three spanning subgraphs of a complete graph. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, Even n →
    ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)),
      (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
      ∃ i, (cycleGraph n).IsContained (c i)

/- The upper-bound half of the large odd cycle theorem of Kohayakawa,
Simonovits and Skokan. The lower-bound construction is unnecessary here. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, Odd n →
    ∀ c : Fin 3 → SimpleGraph (Fin (4 * n - 3)),
      (⊤ : SimpleGraph (Fin (4 * n - 3))).IsEdgeColouring c →
      ∃ i, (cycleGraph n).IsContained (c i)

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.luczak_asymptotic := by
  intro he ho ε hε
  filter_upwards [he, ho] with n hen hon
  have hn : multicolourRamsey (cycleGraph n) 3 ≤ 4 * n := by
    rcases Nat.even_or_odd n with h | h
    · have hu : multicolourRamsey (cycleGraph n) 3 ≤ 2 * n := by
        unfold multicolourRamsey
        exact Nat.sInf_le (hen h)
      exact hu.trans (by omega)
    · have hu : multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3 := by
        unfold multicolourRamsey
        exact Nat.sInf_le (hon h)
      exact hu.trans (Nat.sub_le _ _)
  have hn' : (multicolourRamsey (cycleGraph n) 3 : ℝ) ≤ 4 * (n : ℝ) := by
    exact_mod_cast hn
  exact hn'.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n))

end OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_R1
