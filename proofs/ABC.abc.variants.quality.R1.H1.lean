import OMAReductions.R_ABC_abc_variants_quality_R1

-- Step ABC.abc.variants.quality.R1.H1: hypothesis H1 of reduction ABC.abc.variants.quality.R1
-- Credit: @mbilenko03

namespace OMA.ABCqH1

theorem rad_mul {x y : ℕ} (h : Nat.Coprime x y) :
    ABC.radical (x * y) = ABC.radical x * ABC.radical y := by
  unfold ABC.radical
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]

theorem rad_pos (n : ℕ) : 0 < ABC.radical n := by
  unfold ABC.radical
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

theorem two_le_rad {n : ℕ} (hn : 2 ≤ n) : 2 ≤ ABC.radical n := by
  unfold ABC.radical
  have hm : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩
  have h1 : n.minFac ≤ n.primeFactors.prod id :=
    Finset.single_le_prod' (f := id) (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le) hm
  have h2 := (Nat.minFac_prime (show n ≠ 1 by omega)).two_le
  exact h2.trans h1

theorem rad_sqfree {n : ℕ} (h : Squarefree n) : ABC.radical n = n := by
  unfold ABC.radical
  simpa using Nat.prod_primeFactors_of_squarefree h

end OMA.ABCqH1

theorem OMA.solution : OMA.R_ABC_abc_variants_quality_R1.H1 := by
  intro a b c ha hb hpw habc
  have hac : Nat.Coprime a c := hpw (by simp) (by simp) (by omega)
  have hbc : Nat.Coprime b c := hpw (by simp) (by simp) (by omega)
  have hab : Nat.Coprime a b := by
    subst habc
    exact (Nat.coprime_add_self_right).mp (by rw [add_comm]; exact hac)
  have habc' : Nat.Coprime (a * b) c := Nat.Coprime.mul_left hac hbc
  rw [OMA.ABCqH1.rad_mul habc']
  have hc2 : 2 ≤ ABC.radical c := OMA.ABCqH1.two_le_rad (by omega)
  have hr := OMA.ABCqH1.rad_pos (a * b)
  refine ⟨by nlinarith, ?_⟩
  rintro (h | h)
  · rw [OMA.ABCqH1.rad_sqfree h]
    nlinarith
  · rw [OMA.ABCqH1.rad_sqfree h]
    have h3 : a * b * 2 ≤ a * b * ABC.radical c := Nat.mul_le_mul_left _ hc2
    have h4 : a + b ≤ a * b * 2 := by nlinarith
    omega
