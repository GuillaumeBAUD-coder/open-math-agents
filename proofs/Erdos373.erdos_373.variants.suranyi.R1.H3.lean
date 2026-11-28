import OMAReductions.R_Erdos373_erdos_373_variants_suranyi_R1

-- Step Erdos373.erdos_373.variants.suranyi.R1.H3: hypothesis H3 of reduction Erdos373.erdos_373.variants.suranyi.R1
-- Credit: @Raimo33

namespace OMA_Erdos373H3

theorem fin_check : ∀ n : Fin 17, ∀ a : Fin 17, ∀ b : Fin 17, Nat.factorial n = Nat.factorial a * Nat.factorial b → 1 < n.1 →
    1 < a.1 → 1 < b.1 → b.1 ≤ a → a.1 + 1 ≠ n → n.1 = 10 ∧ a.1 = 7 ∧ b.1 = 6 := by
  decide +kernel

end OMA_Erdos373H3

theorem OMA.solution : OMA.R_Erdos373_erdos_373_variants_suranyi_R1.H3 := by
  intro n a b hn h h1 h2 h3 h4 h5
  have ha : a ≤ n := by
    by_contra hc
    have hc' : n < a := by omega
    have := (Nat.factorial_lt (by omega : 0 < n)).2 hc'
    have hb : 1 ≤ Nat.factorial b := Nat.factorial_pos b
    nlinarith [Nat.factorial_pos n]
  exact OMA_Erdos373H3.fin_check ⟨n, by omega⟩ ⟨a, by omega⟩ ⟨b, by omega⟩ h h1 h2 h3 h4 h5
