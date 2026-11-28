import OMAStatements.S_oeis_a090518
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a090518.main := by
  intro n hn
  unfold OMA.S_oeis_a090518.a OMA.S_oeis_a090518.b
  have hne : {k : ℕ | (10 ^ n / k).Prime}.Nonempty := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨5 * 10 ^ m, ?_⟩
    have e : 10 ^ (m + 1) / (5 * 10 ^ m) = 2 := by
      rw [pow_succ, show 10 ^ m * 10 = 2 * (5 * 10 ^ m) by ring]
      exact Nat.mul_div_cancel _ (by positivity)
    show (10 ^ (m + 1) / (5 * 10 ^ m)).Prime
    rw [e]
    exact Nat.prime_two
  have hmem : (10 ^ n / sInf {k : ℕ | (10 ^ n / k).Prime}).Prime := Nat.sInf_mem hne
  have hb : sInf {k : ℕ | (10 ^ n / k).Prime} ≠ 0 := by
    intro h0
    rw [h0, Nat.div_zero] at hmem
    exact Nat.not_prime_zero hmem
  rw [if_neg hb]
  exact hmem.ne_zero
