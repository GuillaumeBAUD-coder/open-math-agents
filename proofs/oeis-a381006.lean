import OMAStatements.S_oeis_a381006

open OMA.S_oeis_a381006

theorem OMA.solution : type_of% @OMA.S_oeis_a381006.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  set g := Nat.gcd (Nat.gcd (legA (k + 1)) (legB (k + 1))) (hyp (k + 1)) with hg
  have hgB : g ∣ legB (k + 1) := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgC : g ∣ hyp (k + 1) := Nat.gcd_dvd_right _ _
  have e1 : 2 ^ (4 * (k + 1)) = 4 * 2 ^ (4 * (k + 1) - 2) := by
    rw [show 4 * (k + 1) = (4 * (k + 1) - 2) + 2 by omega, pow_add]
    simp only [show 4 * (k + 1) - 2 + 2 - 2 = 4 * (k + 1) - 2 by omega]
    ring
  have e2 : 2 ^ (4 * (k + 1) - 2) = 2 * (2 * 2 ^ (4 * k)) := by
    rw [show 4 * (k + 1) - 2 = 4 * k + 2 by omega, pow_add]; ring
  have e3 : 2 ^ (2 * (k + 1)) = 2 * (2 * 2 ^ (2 * k)) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]; ring
  have e4 : 2 ^ (2 * k) ≤ 2 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e5 : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  have hsum : legB (k + 1) + hyp (k + 1) = 2 ^ (4 * (k + 1) + 1) := by
    simp only [legB, hyp]
    rw [pow_succ, e1]
    omega
  have hdvd : g ∣ 2 ^ (4 * (k + 1) + 1) := hsum ▸ Nat.dvd_add hgB hgC
  obtain ⟨j, hj, hgj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hodd : ¬ 2 ∣ legB (k + 1) := by
    simp only [legB]
    rw [e1, e2, e3]
    omega
  rcases j with _ | j
  · simpa using hgj
  · exact absurd ((show 2 ∣ g by rw [hgj, pow_succ]; exact Dvd.intro_left _ rfl).trans hgB) hodd
