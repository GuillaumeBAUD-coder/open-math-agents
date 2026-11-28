import OMAStatements.S_oeis_a000232
import Mathlib

namespace OMA.A000232Proof

open OMA.S_oeis_a000232

lemma prime_odd {k : ℕ} (hk : 2 ≤ k) : Odd (Nat.nth Nat.Prime (k - 1)) := by
  have hp := Nat.prime_nth_prime (k - 1)
  have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime (k - 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
  rw [Nat.nth_prime_zero_eq_two] at hlt
  rcases hp.eq_two_or_odd' with h | h
  · omega
  · exact h

/-- Every entry of row `n ≥ 1` except the first is even. -/
lemma even_entries (n : ℕ) (hn : 1 ≤ n) : ∀ k, 2 ≤ k → Even (T n k) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro k hk
    simp only [T]
    rw [even_abs]
    have h1 := prime_odd (k := k + 1) (by omega)
    have h2 := prime_odd hk
    have h1' : Odd ((Nat.nth Nat.Prime (k + 1 - 1) : ℕ) : ℤ) := by exact_mod_cast h1
    have h2' : Odd ((Nat.nth Nat.Prime (k - 1) : ℕ) : ℤ) := by exact_mod_cast h2
    exact h1'.sub_odd h2'
  | succ n hn ih =>
    intro k hk
    simp only [T]
    rw [even_abs]
    exact (ih (k + 1) (by omega)).sub (ih k hk)

/-- The first entry of row `n ≥ 1` is odd. -/
lemma odd_first (n : ℕ) (hn : 1 ≤ n) : Odd (T n 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [T, Nat.add_sub_cancel, Nat.sub_self, Nat.nth_prime_zero_eq_two,
      Nat.nth_prime_one_eq_three]
    decide
  | succ n hn ih =>
    simp only [T]
    rw [odd_abs]
    exact (even_entries n hn 2 le_rfl).sub_odd ih

lemma nonneg (n k : ℕ) (hn : 1 ≤ n) : 0 ≤ T n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [T]
  exact abs_nonneg _

theorem main_proof : (∀ n, 1 ≤ n → 2 < a n) → ∀ n, 1 ≤ n → T n 1 = 1 := by
  intro h n hn
  have ha := h n hn
  have hodd := odd_first n hn
  have h0 := nonneg n 1 hn
  by_contra hne
  have hgt : 2 < T n 1 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hmem : 1 ∈ {k : ℕ | 1 ≤ k ∧ 2 < T n k} := ⟨le_rfl, hgt⟩
  have := Nat.sInf_le hmem
  unfold a at ha
  omega

end OMA.A000232Proof

open OMA.A000232Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a000232.main := main_proof
