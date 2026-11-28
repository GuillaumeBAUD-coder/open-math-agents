import OMAStatements.S_oeis_a257378

-- Problem: A257378: Smallest odd number k such that k*n*2^n+1 is a prime number.
-- Upstream: formal-conjectures statements/oeis-a257378.lean:0 (declaration OMA.S_oeis_a257378.main)
-- Credit: @datdzrgb (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_oeis_a257378.main := by
  intro n hn
  suffices h : ∃ k : ℕ, Odd k ∧ (k * (n * 2 ^ n) + 1).Prime by
    obtain ⟨k, hk, hp⟩ := h
    exact ⟨k, hk, by rwa [mul_assoc]⟩
  have hNpos : 0 < n * 2 ^ n := by positivity
  have hNeven : 2 ∣ n * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) n
  generalize n * 2 ^ n = N at hNpos hNeven
  have : NeZero (2 * N) := ⟨by omega⟩
  have hcop : Nat.Coprime (N + 1) (2 * N) := by
    obtain ⟨m, rfl⟩ := hNeven
    have h1 : Nat.Coprime (2 * m + 1) 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    have h2 : Nat.Coprime (2 * m + 1) m := by
      have h3 : Nat.Coprime (1 + m * 2) m := by
        rw [Nat.coprime_add_mul_left_left]; exact Nat.coprime_one_left m
      have h4 : 1 + m * 2 = 2 * m + 1 := by ring
      rwa [h4] at h3
    exact Nat.Coprime.mul_right h1 (Nat.Coprime.mul_right h1 h2)
  have hu : IsUnit (((N + 1 : ℕ)) : ZMod (2 * N)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  obtain ⟨p, hp, hpp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 0
  rw [ZMod.natCast_eq_natCast_iff'] at hmod
  rw [Nat.mod_eq_of_lt (a := N + 1) (by omega)] at hmod
  refine ⟨2 * (p / (2 * N)) + 1, ⟨_, rfl⟩, ?_⟩
  have := Nat.div_add_mod p (2 * N)
  have e : (2 * (p / (2 * N)) + 1) * N + 1 = p := by rw [hmod] at this; linarith
  rwa [← e] at hpp
