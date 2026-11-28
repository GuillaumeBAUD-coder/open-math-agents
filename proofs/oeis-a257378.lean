import OMAStatements.S_oeis_a257378

-- Problem: A257378: Smallest odd number k such that k*n*2^n+1 is a prime number.
-- Upstream: formal-conjectures statements/oeis-a257378.lean:0 (declaration OMA.S_oeis_a257378.main)
-- Original Lean proof: @datdzrgb.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_oeis_a257378.main := by
  intro n hn
  simp only [mul_assoc]
  have hNpos : 0 < n * 2 ^ n := by positivity
  have hNeven : 2 ∣ n * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) n
  generalize n * 2 ^ n = N at hNpos hNeven ⊢
  have hcop : Nat.Coprime (N + 1) (2 * N) :=
    ((Nat.prime_two.coprime_iff_not_dvd).2 (by omega)).symm.mul_right
      (Nat.coprime_self_add_left.2 (Nat.coprime_one_left N))
  obtain ⟨p, hp, hpp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (N + 1) (by omega) hcop
  obtain ⟨j, rfl⟩ := (Nat.modEq_iff_exists_eq_add hp.le).mp hmod.symm
  refine ⟨2 * j + 1, ⟨j, rfl⟩, ?_⟩
  convert hpp using 1
  ring
