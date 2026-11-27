import FormalConjectures.OEIS.«108569»

-- Reduction of the odd Euler-totient conjecture to cube-free witnesses.
-- Credit: @Tchikrazi

namespace OMA.R_OeisA108569_conjecture_R1

/-- No odd cube-free number greater than one satisfies the defining equation. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ n) →
    ¬ OeisA108569.A n

/-- A witness with a cubed prime factor descends to a smaller odd witness. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → OeisA108569.A n →
    (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ n) →
    ∃ m : ℕ, 1 < m ∧ m < n ∧ Odd m ∧ OeisA108569.A m

theorem main : H1 → H2 → type_of% @OeisA108569.conjecture := by
  intro h1 h2
  have no_odd : ∀ k : ℕ, 1 < k → Odd k → ¬ OeisA108569.A k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk ho ha
      by_cases hp : ∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ k
      · obtain ⟨m, hm, hmk, hmo, hma⟩ := h2 k hk ho ha hp
        exact ih m hmk hm hmo hma
      · apply h1 k hk ho _ ha
        intro p hprime hdiv
        exact hp ⟨p, hprime, hdiv⟩
  intro i hi
  change Even (Nat.nth OeisA108569.A i)
  by_cases hz : Nat.nth OeisA108569.A i = 0
  · rw [hz]
    exact ⟨0, rfl⟩
  · have ha := Nat.nth_mem_of_ne_zero hz
    have hcount := Nat.count_nth (Nat.lt_card_toFinset_of_nth_ne_zero hz)
    have hgt : 1 < Nat.nth OeisA108569.A i := by
      have hpos := ha.1
      by_contra hn
      have heq : Nat.nth OeisA108569.A i = 1 := by omega
      have hc : Nat.count OeisA108569.A 1 = 0 := by decide
      rw [heq, hc] at hcount
      omega
    by_contra he
    exact no_odd _ hgt (Nat.not_even_iff_odd.mp he) ha

end OMA.R_OeisA108569_conjecture_R1
