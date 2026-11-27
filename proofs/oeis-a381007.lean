import OMAStatements.S_oeis_a381007

namespace OMA.S_oeis_a381007

lemma legA_succ (m : ℕ) : legA (m + 1) = 16 * (2 ^ (2 * m)) ^ 2 + 8 * 2 ^ (2 * m) := by
  unfold legA
  rw [show 4 * (m + 1) = 2 * m * 2 + 4 by ring, show 2 * (m + 1) + 1 = 2 * m + 3 by ring,
    pow_add, pow_mul, pow_add]
  ring

lemma hyp_succ (m : ℕ) :
    hyp (m + 1) = 20 * (2 ^ (2 * m)) ^ 2 + 4 * 2 ^ (2 * m) + 1 := by
  unfold hyp
  rw [show 4 * (m + 1) - 2 = 2 * m * 2 + 2 by omega, show 4 * (m + 1) = 2 * m * 2 + 4 by ring,
    show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, pow_add, pow_add, pow_mul]
  ring

lemma key (t : ℤ) : IsCoprime (16 * t ^ 2 + 8 * t) (20 * t ^ 2 + 4 * t + 1) := by
  have h0 : IsCoprime (2 : ℤ) (20 * t ^ 2 + 4 * t + 1) := ⟨-(10 * t ^ 2 + 2 * t), 1, by ring⟩
  have h1 : IsCoprime ((2 : ℤ) ^ 3) (20 * t ^ 2 + 4 * t + 1) := h0.pow_left
  have h2 : IsCoprime t (20 * t ^ 2 + 4 * t + 1) := ⟨-(20 * t + 4), 1, by ring⟩
  have h3 : IsCoprime (2 * t + 1) (20 * t ^ 2 + 4 * t + 1) :=
    ⟨(2 * t + 1) + (t ^ 2 + t) * (10 * t - 3), -(t ^ 2 + t), by ring⟩
  have h := (h1.mul_left h2).mul_left h3
  have e : 16 * t ^ 2 + 8 * t = (2 : ℤ) ^ 3 * t * (2 * t + 1) := by ring
  rw [e]
  exact h

theorem solution_main : ∀ n : ℕ, 1 ≤ n → Nat.gcd (Nat.gcd (legA n) (legB n)) (hyp n) = 1 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc : Nat.Coprime (legA (m + 1)) (hyp (m + 1)) := by
    rw [legA_succ, hyp_succ, ← Nat.isCoprime_iff_coprime]
    push_cast
    exact key _
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hc

end OMA.S_oeis_a381007

theorem OMA.solution : type_of% @OMA.S_oeis_a381007.main := OMA.S_oeis_a381007.solution_main
