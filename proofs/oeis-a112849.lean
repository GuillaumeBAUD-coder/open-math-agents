import OMAStatements.S_oeis_a112849

-- Credit: @Dariusthedoggie
-- Proof: binomial symmetry and absorption identities reduce the recurrence to rational algebra

namespace OMA.P112849

private lemma choose_half_eq (m : ℕ) (hm : 1 ≤ m) :
    (2 * m - 1).choose (m - 1) = (2 * m - 1).choose m := by
  have hle : m ≤ 2 * m - 1 := by omega
  have hsub : 2 * m - 1 - m = m - 1 := by omega
  rw [← Nat.choose_symm hle, hsub]

private lemma choose_step (m : ℕ) (hm : 1 ≤ m) :
    ((m + 1 : ℕ) : ℚ) * ((2 * m + 1).choose (m + 1) : ℚ) =
      2 * ((2 * m + 1 : ℕ) : ℚ) * ((2 * m - 1).choose m : ℚ) := by
  have h1 : (2 * m + 1).choose (m + 1) * (m + 1) = (2 * m + 1) * (2 * m).choose m := by
    have := Nat.add_one_mul_choose_eq (2 * m) m
    linarith
  have h2 : (2 * m).choose m * m = (2 * m) * (2 * m - 1).choose (m - 1) := by
    have hm1 : 2 * m - 1 + 1 = 2 * m := by omega
    have hm2 : m - 1 + 1 = m := by omega
    have := Nat.add_one_mul_choose_eq (2 * m - 1) (m - 1)
    rw [hm1, hm2] at this
    linarith
  have h3 : (2 * m).choose m = 2 * (2 * m - 1).choose m := by
    rw [choose_half_eq m hm] at h2
    have hmul : (2 * m).choose m * m = (2 * (2 * m - 1).choose m) * m := by linarith
    exact Nat.eq_of_mul_eq_mul_right (by omega) hmul
  have h4 : (m + 1) * (2 * m + 1).choose (m + 1) = 2 * (2 * m + 1) * (2 * m - 1).choose m := by
    rw [mul_comm, h1, h3]
    ring
  exact_mod_cast h4

theorem main_proof : ∀ a : ℕ → ℚ, a 1 = 1 →
    (∀ n : ℕ, 2 ≤ n → a n = 1 + (1 / 2) * ((2 * n - 1).choose (n - 1) : ℚ) +
      (1 / 2) * ((2 * n - 1).choose n : ℚ)) →
    ∀ n : ℕ, 4 ≤ n →
      (n : ℚ) * (3 * (n : ℚ) - 5) * a n + (-15 * (n : ℚ) ^ 2 + 31 * (n : ℚ) - 12) * a (n - 1) +
        2 * (3 * (n : ℚ) - 2) * (2 * (n : ℚ) - 3) * a (n - 2) = 0 := by
  intro a _ ha n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 4 := ⟨n - 4, by omega⟩
  have hsimp : ∀ m : ℕ, 2 ≤ m → a m = 1 + ((2 * m - 1).choose m : ℚ) := by
    intro m hm
    rw [ha m hm, choose_half_eq m (by omega)]
    ring
  have ha0 : a (k + 2) = 1 + ((2 * (k + 2) - 1).choose (k + 2) : ℚ) := hsimp (k + 2) (by omega)
  have ha1 : a (k + 3) = 1 + ((2 * (k + 3) - 1).choose (k + 3) : ℚ) := hsimp (k + 3) (by omega)
  have ha2 : a (k + 4) = 1 + ((2 * (k + 4) - 1).choose (k + 4) : ℚ) := hsimp (k + 4) (by omega)
  have hstep1 := choose_step (k + 2) (by omega)
  have hstep2 := choose_step (k + 3) (by omega)
  have hsub1 : k + 4 - 1 = k + 3 := by omega
  have hsub2 : k + 4 - 2 = k + 2 := by omega
  rw [hsub1, hsub2, ha2, ha1, ha0]
  have h2k3 : 2 * (k + 3) - 1 = 2 * (k + 2) + 1 := by omega
  have h2k4 : 2 * (k + 4) - 1 = 2 * (k + 3) + 1 := by omega
  rw [h2k3, h2k4]
  rw [h2k3] at hstep2
  set c0 : ℚ := ((2 * (k + 2) - 1).choose (k + 2) : ℚ)
  set c1 : ℚ := ((2 * (k + 2) + 1).choose (k + 3) : ℚ)
  set c2 : ℚ := ((2 * (k + 3) + 1).choose (k + 4) : ℚ)
  have hk3 : ((k : ℚ) + 3) ≠ 0 := by positivity
  have hk4 : ((k : ℚ) + 4) ≠ 0 := by positivity
  have hc1 : c1 = 2 * (2 * (k : ℚ) + 5) * c0 / ((k : ℚ) + 3) := by
    rw [eq_div_iff hk3]
    push_cast at hstep1 ⊢
    linarith
  have hc2 : c2 = 2 * (2 * (k : ℚ) + 7) * c1 / ((k : ℚ) + 4) := by
    rw [eq_div_iff hk4]
    push_cast at hstep2 ⊢
    linarith
  rw [hc2, hc1]
  push_cast
  field_simp
  ring

end OMA.P112849

theorem OMA.solution : type_of% @OMA.S_oeis_a112849.main := OMA.P112849.main_proof
