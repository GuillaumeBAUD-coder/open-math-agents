import OMAReductions.R_Erdos1113_erdos_1113_variants_filaseta_finch_kozek_R1

/-!
# Proof of `Erdos1113.erdos_1113.variants.filaseta_finch_kozek.R1.H1`

Proves that every `k` satisfying `k ≡ 78557 [MOD 70050435]` or `k ≡ 271129 [MOD 5592405]` has a
finite prime covering set (`Erdos1113.HasFinitePrimeCoveringSet k`).

- For `k ≡ 78557 [MOD 70050435]`, take `P = {3, 5, 7, 13, 19, 37, 73}`. Every `p ∈ P` divides
  `70050435` and satisfies `2 ^ 36 ≡ 1 [MOD p]`, and for every `r < 36` some `p ∈ P` divides
  `78557 * 2 ^ r + 1`.
- For `k ≡ 271129 [MOD 5592405]`, take `P = {3, 5, 7, 13, 17, 241}`. Every `p ∈ P` divides
  `5592405` and satisfies `2 ^ 24 ≡ 1 [MOD p]`, and for every `r < 24` some `p ∈ P` divides
  `271129 * 2 ^ r + 1`.
-/

namespace Erdos1113FFKR1H1Proof

private lemma two_pow_modEq_of_period {p period n : ℕ} (hper : 2 ^ period ≡ 1 [MOD p]) :
    2 ^ n ≡ 2 ^ (n % period) [MOD p] := by
  have hn : period * (n / period) + n % period = n := Nat.div_add_mod n period
  rw [← hn, pow_add, pow_mul]
  have h1 : (2 ^ period) ^ (n / period) ≡ 1 ^ (n / period) [MOD p] := hper.pow _
  rw [one_pow] at h1
  simpa using h1.mul (Nat.ModEq.refl (2 ^ (n % period)))

private lemma covering_of_table {k k₀ M period : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hmod : k ≡ k₀ [MOD M])
    (hM : ∀ p ∈ P, p ∣ M)
    (hper : ∀ p ∈ P, 2 ^ period ≡ 1 [MOD p])
    (hpos : 0 < period)
    (hcov : ∀ r : Fin period, ∃ p ∈ P, p ∣ k₀ * 2 ^ r.val + 1) :
    Erdos1113.HasFinitePrimeCoveringSet k := by
  refine ⟨P, hprime, fun n => ?_⟩
  obtain ⟨p, hpP, hdvd⟩ := hcov ⟨n % period, Nat.mod_lt n hpos⟩
  refine ⟨p, hpP, ?_⟩
  have hkp : k ≡ k₀ [MOD p] := hmod.of_dvd (hM p hpP)
  have h2p : 2 ^ n ≡ 2 ^ (n % period) [MOD p] := two_pow_modEq_of_period (hper p hpP)
  have hcomb : k * 2 ^ n + 1 ≡ k₀ * 2 ^ (n % period) + 1 [MOD p] :=
    (hkp.mul h2p).add_right 1
  exact Nat.dvd_of_mod_eq_zero (hcomb.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

private lemma selfridge_primes :
    ∀ p ∈ ({3, 5, 7, 13, 19, 37, 73} : Finset ℕ), p.Prime := by
  intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma selfridge_dvd :
    ∀ p ∈ ({3, 5, 7, 13, 19, 37, 73} : Finset ℕ), p ∣ 70050435 := by decide

private lemma selfridge_per :
    ∀ p ∈ ({3, 5, 7, 13, 19, 37, 73} : Finset ℕ), 2 ^ 36 ≡ 1 [MOD p] := by decide

private lemma selfridge_cov :
    ∀ r : Fin 36, ∃ p ∈ ({3, 5, 7, 13, 19, 37, 73} : Finset ℕ), p ∣ 78557 * 2 ^ r.val + 1 := by
  decide +kernel

private lemma fam2_primes :
    ∀ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), p.Prime := by
  intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma fam2_dvd :
    ∀ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), p ∣ 5592405 := by decide

private lemma fam2_per :
    ∀ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), 2 ^ 24 ≡ 1 [MOD p] := by decide

private lemma fam2_cov :
    ∀ r : Fin 24, ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), p ∣ 271129 * 2 ^ r.val + 1 := by
  decide +kernel

end Erdos1113FFKR1H1Proof

theorem OMA.solution : OMA.R_Erdos1113_erdos_1113_variants_filaseta_finch_kozek_R1.H1 := by
  intro k hk
  rcases hk with h1 | h2
  · exact Erdos1113FFKR1H1Proof.covering_of_table {3, 5, 7, 13, 19, 37, 73}
      Erdos1113FFKR1H1Proof.selfridge_primes h1 Erdos1113FFKR1H1Proof.selfridge_dvd
      Erdos1113FFKR1H1Proof.selfridge_per (by decide) Erdos1113FFKR1H1Proof.selfridge_cov
  · exact Erdos1113FFKR1H1Proof.covering_of_table {3, 5, 7, 13, 17, 241}
      Erdos1113FFKR1H1Proof.fam2_primes h2 Erdos1113FFKR1H1Proof.fam2_dvd
      Erdos1113FFKR1H1Proof.fam2_per (by decide) Erdos1113FFKR1H1Proof.fam2_cov
