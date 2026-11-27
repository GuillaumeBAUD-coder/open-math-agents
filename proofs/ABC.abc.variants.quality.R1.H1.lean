import OMAReductions.R_ABC_abc_variants_quality_R1

-- Step ABC.abc.variants.quality.R1.H1: hypothesis H1 of reduction ABC.abc.variants.quality.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ a b c : ℕ, 0 < a → 0 < b → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime →     a + b = c →     1 < ABC.radical (a * b * c) ∧       ((Squarefree c ∨ Squarefree (a * b)) → c ≤ ABC.radical (a * b * c))

namespace OMAABCH1

theorem rad_pos (n : ℕ) : 0 < ABC.radical n := by
  unfold ABC.radical
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

theorem rad_dvd_of_dvd {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) :
    ABC.radical m ∣ ABC.radical n := by
  unfold ABC.radical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono h hn)

theorem rad_sq {n : ℕ} (h : Squarefree n) : ABC.radical n = n := by
  unfold ABC.radical
  simpa using Nat.prod_primeFactors_of_squarefree h

theorem two_le_rad {n : ℕ} (h : 2 ≤ n) : 2 ≤ ABC.radical n := by
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have hmem : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, by omega⟩
  have hd : n.minFac ∣ ABC.radical n := by
    unfold ABC.radical
    simpa using Finset.dvd_prod_of_mem id hmem
  exact le_trans hp.two_le (Nat.le_of_dvd (rad_pos n) hd)

theorem rad_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    ABC.radical (m * n) = ABC.radical m * ABC.radical n := by
  unfold ABC.radical
  rw [Nat.Coprime.primeFactors_mul h]
  exact Finset.prod_union (Nat.Coprime.disjoint_primeFactors h)

end OMAABCH1

open OMAABCH1 in
theorem OMA.solution : OMA.R_ABC_abc_variants_quality_R1.H1 := by
  intro a b c ha hb hcop hsum
  have hc2 : 2 ≤ c := by omega
  have hc0 : c ≠ 0 := by omega
  have habc0 : a * b * c ≠ 0 := by positivity
  refine ⟨lt_of_lt_of_le (by norm_num) (two_le_rad (by nlinarith [Nat.mul_le_mul ha hb])), ?_⟩
  rintro (hsq | hsq)
  · have hd := rad_dvd_of_dvd (Dvd.intro_left (a * b) rfl) habc0
    rw [rad_sq hsq] at hd
    exact Nat.le_of_dvd (rad_pos _) hd
  · have hac : Nat.Coprime a c := hcop (by simp) (by simp) (by omega)
    have hbc : Nat.Coprime b c := hcop (by simp) (by simp) (by omega)
    have habc : Nat.Coprime (a * b) c := Nat.Coprime.mul hac hbc
    rw [rad_mul_coprime habc, rad_sq hsq]
    have h2 := two_le_rad hc2
    nlinarith [Nat.mul_le_mul_left (a * b) h2]
