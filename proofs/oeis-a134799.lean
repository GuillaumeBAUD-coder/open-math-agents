import OMAStatements.S_oeis_a134799

-- Problem: A134799: a(n) = 3^((3^n - 1)/2).
-- Upstream: formal-conjectures statements/oeis-a134799.lean:0 (declaration OMA.S_oeis_a134799.main)
-- Credit: @jared-jasinski (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private lemma exp_step (n : ℕ) :
    (3 ^ (n + 1) - 1) / 2 + 1 = 3 * ((3 ^ n - 1) / 2 + 1) - 1 := by
  have h1 : 1 ≤ 3 ^ n := Nat.one_le_pow n 3 (by decide)
  have h2 : 3 ^ n % 2 = 1 := by simp [Nat.pow_mod]
  rw [pow_succ']
  omega

private lemma den_step (q : ℚ) (e : ℕ) (he : 1 ≤ e) (hd : q.den = 3 ^ e) :
    ((3 / 2 : ℚ) * q * (1 - q ^ 2)).den = 3 ^ (3 * e - 1) := by
  set p : ℤ := q.num
  set d : ℕ := q.den
  have h3d : 3 ∣ d := hd ▸ dvd_pow_self 3 (by omega)
  have hp3 : ¬ (3 : ℤ) ∣ p := by
    intro h
    have h1 : 3 ∣ p.natAbs := Int.ofNat_dvd_left.mp h
    have h2 : 3 ∣ Nat.gcd p.natAbs d := Nat.dvd_gcd h1 h3d
    rw [q.reduced.gcd_eq_one] at h2
    omega
  have hd_odd : d % 2 = 1 := by rw [hd]; simp [Nat.pow_mod]
  have h2_dvd : (2 : ℤ) ∣ p * ((d : ℤ) ^ 2 - p ^ 2) := by
    obtain ⟨j, hj⟩ : ∃ j : ℤ, (d : ℤ) = 2 * j + 1 := ⟨(d : ℤ) / 2, by omega⟩
    rcases Int.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k * ((d : ℤ) ^ 2 - p ^ 2), ?_⟩
      rw [hk]
      ring
    · refine ⟨p * (2 * j * (j + 1) - 2 * k * (k + 1)), ?_⟩
      rw [hk, hj]
      ring
  obtain ⟨m, hm⟩ := h2_dvd
  have hm3 : ¬ 3 ∣ m.natAbs := by
    intro h
    have h1 : (3 : ℤ) ∣ m := Int.ofNat_dvd_left.mpr h
    have h2 : (3 : ℤ) ∣ p * ((d : ℤ) ^ 2 - p ^ 2) := hm ▸ dvd_mul_of_dvd_right h1 2
    have h3 : (3 : ℤ) ∣ (d : ℤ) := Int.ofNat_dvd.mpr h3d
    have h4 : (3 : ℤ) ∣ p * (d : ℤ) ^ 2 := dvd_mul_of_dvd_right (dvd_pow h3 (by decide)) p
    have h5 : (3 : ℤ) ∣ p ^ 3 := by
      have : p ^ 3 = p * (d : ℤ) ^ 2 - p * ((d : ℤ) ^ 2 - p ^ 2) := by ring
      rw [this]
      exact dvd_sub h4 h2
    have h6 : 3 ∣ p.natAbs ^ 3 := by
      rw [← Int.natAbs_pow]
      exact Int.ofNat_dvd_left.mp h5
    exact hp3 (Int.ofNat_dvd_left.mpr (Nat.prime_three.dvd_of_dvd_pow h6))
  have hcop : Nat.Coprime m.natAbs (3 ^ (3 * e - 1)) :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hm3).symm.pow_right _
  have hpow : (3 : ℚ) * (3 ^ (3 * e - 1) : ℕ) = (d : ℚ) ^ 3 := by
    have hnat : 3 * 3 ^ (3 * e - 1) = d ^ 3 := by
      rw [hd, ← pow_succ', Nat.sub_add_cancel (by omega), ← pow_mul, mul_comm]
    exact_mod_cast hnat
  have hq : (3 / 2 : ℚ) * q * (1 - q ^ 2) = (m : ℚ) / ((3 ^ (3 * e - 1) : ℕ) : ℚ) := by
    have hq0 : q = (p : ℚ) / (d : ℚ) := (Rat.num_div_den q).symm
    have hmQ : (p : ℚ) * ((d : ℚ) ^ 2 - (p : ℚ) ^ 2) = 2 * (m : ℚ) := by exact_mod_cast hm
    have hd0 : (d : ℚ) ≠ 0 := by positivity
    have hD0 : ((3 ^ (3 * e - 1) : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hq0]
    field_simp
    linear_combination 3 * ((3 ^ (3 * e - 1) : ℕ) : ℚ) * hmQ + 2 * (m : ℚ) * hpow
  set q' : ℚ := (3 / 2 : ℚ) * q * (1 - q ^ 2)
  set D : ℕ := 3 ^ (3 * e - 1)
  have hmulQ : (q'.num : ℚ) * (D : ℚ) = (m : ℚ) * (q'.den : ℚ) := by
    have h1 : (q'.num : ℚ) / (q'.den : ℚ) = (m : ℚ) / (D : ℚ) := by
      rw [Rat.num_div_den, hq]
    have hD0 : (D : ℚ) ≠ 0 := by positivity
    have hq'0 : (q'.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q'.den_nz
    field_simp at h1
    linarith
  have hmulZ : q'.num * (D : ℤ) = m * (q'.den : ℤ) := by exact_mod_cast hmulQ
  have hmulN : q'.num.natAbs * D = m.natAbs * q'.den := by
    have := congrArg Int.natAbs hmulZ
    simpa [Int.natAbs_mul] using this
  have h1 : q'.den ∣ D :=
    q'.reduced.symm.dvd_of_dvd_mul_left ⟨m.natAbs, by linarith⟩
  have h2 : D ∣ q'.den :=
    hcop.symm.dvd_of_dvd_mul_left ⟨q'.num.natAbs, by linarith⟩
  exact Nat.dvd_antisymm h1 h2

theorem OMA.solution : type_of% @OMA.S_oeis_a134799.main := by
  intro n
  rw [OMA.S_oeis_a134799.term, ← pow_succ']
  induction n with
  | zero =>
    norm_num [OMA.S_oeis_a134799.iterate]
  | succ n ih =>
    rw [OMA.S_oeis_a134799.iterate, exp_step n]
    exact den_step (OMA.S_oeis_a134799.iterate n) ((3 ^ n - 1) / 2 + 1) (by omega) ih
