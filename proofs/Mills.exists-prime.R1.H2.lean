import OMAReductions.R_Mills_exists_prime_R1

-- Step Mills.exists-prime.R1.H2: hypothesis H2 of reduction Mills.exists-prime.R1

/-!
Mills's construction. Put `e n = 3 ^ (n + 1)`, `u n = (q n) ^ (1 / e n)` and
`v n = (q n + 1) ^ (1 / e n)`. The hypotheses say that `u` is increasing, `v` is strictly
decreasing and `u n < v n`. For `A = sup u` we get `u n ≤ A ≤ v (n + 1) < v n`, that is
`q n ≤ A ^ e n < q n + 1`.
-/

theorem OMA.solution : OMA.R_Mills_exists_prime_R1.H2 := by
  unfold OMA.R_Mills_exists_prime_R1.H2
  intro q hq2 hcube hlt
  have he : ∀ n : ℕ, (3 : ℕ) ^ (n + 1) ≠ 0 := fun n => by positivity
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℕ → ℝ, (∀ n, 0 ≤ u n) ∧ ∀ n, u n ^ (3 ^ (n + 1)) = (q n : ℝ) :=
    ⟨fun n => (q n : ℝ) ^ (((3 ^ (n + 1) : ℕ) : ℝ)⁻¹),
      fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _,
      fun n => Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (he n)⟩
  obtain ⟨v, hv0, hv⟩ : ∃ v : ℕ → ℝ, (∀ n, 0 ≤ v n) ∧
      ∀ n, v n ^ (3 ^ (n + 1)) = (q n : ℝ) + 1 :=
    ⟨fun n => ((q n : ℝ) + 1) ^ (((3 ^ (n + 1) : ℕ) : ℝ)⁻¹),
      fun n => Real.rpow_nonneg (by positivity) _,
      fun n => Real.rpow_inv_natCast_pow (by positivity) (he n)⟩
  have hpow : ∀ (n : ℕ) (a : ℝ), a ^ (3 ^ (n + 1 + 1)) = (a ^ (3 ^ (n + 1))) ^ 3 := by
    intro n a
    rw [← pow_mul, pow_succ 3 (n + 1)]
  have hu_mono : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    apply le_of_pow_le_pow_left₀ (he (n + 1)) (hu0 (n + 1))
    rw [hpow n (u n), hu n, hu (n + 1)]
    exact_mod_cast hcube n
  have hv_anti : StrictAnti v := by
    apply strictAnti_nat_of_succ_lt
    intro n
    apply lt_of_pow_lt_pow_left₀ (3 ^ (n + 1 + 1)) (hv0 n)
    rw [hpow n (v n), hv n, hv (n + 1)]
    exact_mod_cast hlt n
  have huv : ∀ n, u n < v n := by
    intro n
    apply lt_of_pow_lt_pow_left₀ (3 ^ (n + 1)) (hv0 n)
    rw [hu n, hv n]
    linarith
  have huv2 : ∀ m n, u m ≤ v n := fun m n =>
    ((hu_mono (le_max_left m n)).trans (huv (max m n)).le).trans
      (hv_anti.antitone (le_max_right m n))
  have hbdd : BddAbove (Set.range u) := by
    refine ⟨v 0, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact huv2 m 0
  refine ⟨⨆ n, u n, ?_, ?_⟩
  · have h1 : 1 < u 0 := by
      apply lt_of_pow_lt_pow_left₀ (3 ^ (0 + 1)) (hu0 0)
      rw [hu 0, one_pow]
      have h2 := hq2 0
      exact_mod_cast (by omega : 1 < q 0)
    exact lt_of_lt_of_le h1 (le_ciSup hbdd 0)
  · intro n
    have hA0 : 0 ≤ ⨆ n, u n := (hu0 0).trans (le_ciSup hbdd 0)
    have hlo : u n ≤ ⨆ n, u n := le_ciSup hbdd n
    have hhi : (⨆ n, u n) < v n :=
      lt_of_le_of_lt (ciSup_le (fun m => huv2 m (n + 1))) (hv_anti (Nat.lt_succ_self n))
    rw [Nat.floor_eq_iff (pow_nonneg hA0 _)]
    constructor
    · rw [← hu n]
      exact pow_le_pow_left₀ (hu0 n) hlo _
    · rw [← hv n]
      exact pow_lt_pow_left₀ hhi hA0 (he n)
