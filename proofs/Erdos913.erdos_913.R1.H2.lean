import OMAReductions.R_Erdos913_erdos_913_R1

-- Step Erdos913.erdos_913.R1.H2: hypothesis H2 of reduction Erdos913.erdos_913.R1
-- Credit: @Ezekia1
-- For an odd prime p with q = 8 * p ^ 2 - 1 prime, take n = q. Then n * (n + 1) = q * 2 ^ 3 * p ^ 2,
-- and the three exponents 1, 3, 2 are distinct. Different p give different n.

theorem OMA.solution : OMA.R_Erdos913_erdos_913_R1.H2 := by
  intro hS
  have hS' : ({ p : ℕ | p.Prime ∧ (8 * p ^ 2 - 1).Prime } \ {2}).Infinite :=
    hS.sdiff (Set.finite_singleton 2)
  have hinj : Set.InjOn (fun p : ℕ => 8 * p ^ 2 - 1)
      ({ p : ℕ | p.Prime ∧ (8 * p ^ 2 - 1).Prime } \ {2}) := by
    intro a ha b hb hab
    have ha0 : 0 < a ^ 2 := pow_pos ha.1.1.pos 2
    have hb0 : 0 < b ^ 2 := pow_pos hb.1.1.pos 2
    have h2 : a ^ 2 = b ^ 2 := by
      simp only at hab
      omega
    exact Nat.pow_left_injective (by norm_num) h2
  refine (hS'.image hinj).mono ?_
  rintro _ ⟨p, ⟨⟨hp, hq⟩, hp2⟩, rfl⟩
  have hp2' : p ≠ 2 := hp2
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hple : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have hn1 : 8 * p ^ 2 - 1 + 1 = 2 ^ 3 * p ^ 2 := by omega
  have hq2 : 8 * p ^ 2 - 1 ≠ 2 := by omega
  have hqp : 8 * p ^ 2 - 1 ≠ p := by omega
  show Set.InjOn ((8 * p ^ 2 - 1) * (8 * p ^ 2 - 1 + 1)).factorization
    ((8 * p ^ 2 - 1) * (8 * p ^ 2 - 1 + 1)).primeFactors
  rw [hn1]
  generalize 8 * p ^ 2 - 1 = q at hq hq2 hqp
  have hF : ∀ r : ℕ, (q * (2 ^ 3 * p ^ 2)).factorization r =
      (if q = r then 1 else 0) + ((if 2 = r then 3 else 0) + (if p = r then 2 else 0)) := by
    intro r
    rw [Nat.factorization_mul hq.ne_zero (by positivity),
      Nat.factorization_mul (by norm_num) (by positivity), hq.factorization,
      Nat.prime_two.factorization_pow, hp.factorization_pow]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  intro a ha b hb hab
  rw [Finset.mem_coe, ← Nat.support_factorization, Finsupp.mem_support_iff, hF] at ha hb
  rw [hF, hF] at hab
  split_ifs at ha hb hab <;> omega
