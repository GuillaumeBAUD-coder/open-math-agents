import OMAStatements.S_mo_206157

namespace OMA.P_mo_206157

lemma div_aux (rem q X : ℕ) (h : rem < q) : (rem + q * X) / q = X := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, zero_add]

end OMA.P_mo_206157

open OMA.P_mo_206157

theorem OMA.solution : type_of% @OMA.S_mo_206157.main := by
  intro p hp h13 k hk1 hk4
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 8 ∧ p = 8 * m + r :=
    ⟨p / 8, p % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod p 8).symm⟩
  interval_cases r <;> try omega
  all_goals interval_cases k
  · rw [show (8 * m + 1) ^ 2 - 1 = 0 + 2 ^ 1 * ((8*m) * (4*m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 1) ^ 2 - 1 = 0 + 2 ^ 2 * ((4*m) * (4*m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 1) ^ 2 - 1 = 0 + 2 ^ 3 * ((2*m) * (4*m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 1) ^ 2 - 1 = 0 + 2 ^ 4 * ((m) * (4*m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 3) ^ 2 - 1 = 0 + 2 ^ 1 * ((4*(2*m+1)) * (4*m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 3) ^ 2 - 1 = 0 + 2 ^ 2 * ((2*(2*m+1)) * (4*m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 3) ^ 2 - 1 = 0 + 2 ^ 3 * ((2*m+1) * (4*m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 3) ^ 2 - 1 = 8 + 2 ^ 4 * ((m) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 5) ^ 2 - 1 = 0 + 2 ^ 1 * ((4*(2*m+1)) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 5) ^ 2 - 1 = 0 + 2 ^ 2 * ((2*(2*m+1)) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 5) ^ 2 - 1 = 0 + 2 ^ 3 * ((2*m+1) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 5) ^ 2 - 1 = 8 + 2 ^ 4 * ((4*m+1) * (m+1)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 7) ^ 2 - 1 = 0 + 2 ^ 1 * ((8*(m+1)) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 7) ^ 2 - 1 = 0 + 2 ^ 2 * ((4*(m+1)) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 7) ^ 2 - 1 = 0 + 2 ^ 3 * ((2*(m+1)) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [show (8 * m + 7) ^ 2 - 1 = 0 + 2 ^ 4 * ((m+1) * (4*m+3)) from
        Nat.sub_eq_of_eq_add (by ring), div_aux _ _ _ (by norm_num)]
    exact Nat.not_prime_mul (by omega) (by omega)
