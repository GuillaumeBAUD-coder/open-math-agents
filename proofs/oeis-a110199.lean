import OMAStatements.S_oeis_a110199

-- Complete proof of OEIS A110199 via the Catalan linear recurrence
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a110199

private lemma catalan_recurrence (k : ℕ) :
    (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 : (k + 1) * catalan k = Nat.centralBinom k := by
    rw [catalan_eq_centralBinom_div]
    exact Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom k)
  have h2 : (k + 2) * catalan (k + 1) = Nat.centralBinom (k + 1) := by
    rw [catalan_eq_centralBinom_div]
    exact Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom (k + 1))
  have hcb := Nat.succ_mul_centralBinom_succ k
  have hmul : (k + 1) * ((k + 2) * catalan (k + 1)) =
      (k + 1) * (2 * (2 * k + 1) * catalan k) := by
    rw [h2, hcb, ← h1]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hmul

private lemma a_diff_even (m : ℕ) :
    (a (2 * m + 2) : ℤ) - (a (2 * m + 1) : ℤ) = (catalan (m + 1) : ℤ) := by
  unfold a
  have h1 : (2 * m + 2) / 2 + 1 = m + 2 := by omega
  have h2 : (2 * m + 1) / 2 + 1 = m + 1 := by omega
  rw [h1, h2, Finset.sum_range_succ]
  push_cast
  ring

private lemma a_diff_odd (m : ℕ) :
    a (2 * m + 1) = a (2 * m) := by
  unfold a
  have h1 : (2 * m + 1) / 2 + 1 = (2 * m) / 2 + 1 := by omega
  rw [h1]

theorem OMA.solution : type_of% @OMA.S_oeis_a110199.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 2 ≤ k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hn0 : m + 2 + (m + 2) = 2 * (m + 1) + 2 := by omega
    have hn1 : m + 2 + (m + 2) - 1 = 2 * (m + 1) + 1 := by omega
    have hn2 : m + 2 + (m + 2) - 2 = 2 * m + 2 := by omega
    have hn3 : m + 2 + (m + 2) - 3 = 2 * m + 1 := by omega
    have hrec_z : ((m + 3 : ℕ) : ℤ) * (catalan (m + 2) : ℤ) =
        2 * (2 * ((m + 1 : ℕ) : ℤ) + 1) * (catalan (m + 1) : ℤ) := by
      exact_mod_cast catalan_recurrence (m + 1)
    have hd1 := a_diff_even (m + 1)
    have hd2 := a_diff_even m
    rw [hn1, hn2, hn3, hn0]
    have hlin : (-(↑(2 * (m + 1) + 2) + 2 : ℤ)) * ↑(a (2 * (m + 1) + 2)) +
        (↑(2 * (m + 1) + 2) + 2 : ℤ) * ↑(a (2 * (m + 1) + 1)) +
        4 * (↑(2 * (m + 1) + 2) - 1 : ℤ) * ↑(a (2 * m + 2)) +
        4 * (1 - ↑(2 * (m + 1) + 2) : ℤ) * ↑(a (2 * m + 1)) =
        -(2 * ((m + 3 : ℕ) : ℤ)) * ((a (2 * (m + 1) + 2) : ℤ) - (a (2 * (m + 1) + 1) : ℤ)) +
        4 * (2 * ((m + 1 : ℕ) : ℤ) + 1) * ((a (2 * m + 2) : ℤ) - (a (2 * m + 1) : ℤ)) := by
      push_cast; ring
    rw [hlin, hd1, hd2]
    have hcat : catalan (m + 1 + 1) = catalan (m + 2) := rfl
    rw [hcat]
    linarith
  · have hk : 1 ≤ k := by omega
    have h1 : 2 * k + 1 - 1 = 2 * k := by omega
    have h2 : 2 * k + 1 - 2 = 2 * (k - 1) + 1 := by omega
    have h3 : 2 * k + 1 - 3 = 2 * (k - 1) := by omega
    rw [h1, h2, h3, a_diff_odd k, a_diff_odd (k - 1)]
    ring
