import OMAReductions.R_Erdos820_erdos_820_variants_erdos_lower_R1

-- Step Erdos820.erdos_820.variants.erdos_lower.R1.H2: hypothesis H2 of reduction Erdos820.erdos_820.variants.erdos_lower.R1

/-!
Let `l = H n` and let `2 ≤ k < l` be a witness with `(k ^ n - 1, l ^ n - 1) = 1`. If `p` is a
prime with `p - 1 ∣ n` dividing neither `k` nor `l`, then by Fermat `p` divides both `k ^ n - 1`
and `l ^ n - 1`, which is impossible. So every such prime divides `k * l`, hence so does their
product, and `k * l < l ^ 2`.
-/

namespace OMA

theorem dvd_pow_sub_one {p a n : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hn : (p - 1) ∣ n) :
    p ∣ a ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa).symm
  have h1 : a ^ (p - 1) ≡ 1 [MOD p] := by
    have h := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at h
  have h2 : a ^ ((p - 1) * m) ≡ 1 [MOD p] := by
    rw [pow_mul]
    simpa using h1.pow m
  have hapos : 0 < a := Nat.pos_of_ne_zero (fun h => hpa (h ▸ dvd_zero p))
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hapos)).1 h2.symm

end OMA

theorem OMA.solution : OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1.H2 := by
  unfold OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1.H2
  intro n hn
  obtain ⟨k, hk2, hkl, hcop⟩ := Erdos820.H_spec hn
  have hdvd : (∏ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n), p) ∣
      k * Erdos820.H n := by
    refine Finset.prod_primes_dvd _ ?_ ?_
    · intro p hp
      exact (Finset.mem_filter.1 hp).2.1.prime
    · intro p hp
      obtain ⟨hpp, hpn⟩ := (Finset.mem_filter.1 hp).2
      by_contra hnot
      have hk : ¬ p ∣ k := fun h => hnot (h.mul_right _)
      have hl : ¬ p ∣ Erdos820.H n := fun h => hnot (h.mul_left _)
      have h1 := OMA.dvd_pow_sub_one hpp hk hpn
      have h2 := OMA.dvd_pow_sub_one hpp hl hpn
      have h3 := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one hcop] at h3
      exact hpp.one_lt.ne' (Nat.dvd_one.1 h3)
  have hpos : 0 < k * Erdos820.H n := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  have hlt : k * Erdos820.H n < Erdos820.H n ^ 2 := by nlinarith
  exact lt_of_le_of_lt hle hlt
