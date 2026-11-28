import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1

-- Elementary complementary pair bound; parent reduction by @eltociear, PR #31262.
-- Uses seed_divisibility from @ubuwaits, PR #7448. Helpers are independently proved here.
namespace U3PairBound

lemma prime_mem_of_dvd_product {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  obtain ⟨q, hq, hdq⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hd
  exact ((Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hdq) ▸ hq

lemma pair_bound {c p r : ℕ} {S : Finset ℕ} (hc : 0 < c)
    (hS : ∀ q ∈ S, q.Prime) (hp : p.Prime) (hr : r.Prime)
    (hdiv : p * r ∣ c * ∏ q ∈ S, q)
    (hnot : ¬ (p ∈ S ∧ r ∈ S ∧ p ≠ r)) : min p r ≤ c := by
  by_contra! hmin
  have hpc : c < p := lt_of_lt_of_le hmin (min_le_left _ _)
  have hrc : c < r := lt_of_lt_of_le hmin (min_le_right _ _)
  have hpcop : p.Coprime c := hp.coprime_iff_not_dvd.mpr fun hd =>
    hpc.not_ge (Nat.le_of_dvd hc hd)
  have hrcop : r.Coprime c := hr.coprime_iff_not_dvd.mpr fun hd =>
    hrc.not_ge (Nat.le_of_dvd hc hd)
  have hpS := prime_mem_of_dvd_product hS hp
    (hpcop.dvd_of_dvd_mul_left ((dvd_mul_right p r).trans hdiv))
  have hrS := prime_mem_of_dvd_product hS hr
    (hrcop.dvd_of_dvd_mul_left ((dvd_mul_left r p).trans hdiv))
  have he : p = r := by
    by_contra hne
    exact hnot ⟨hpS, hrS, hne⟩
  subst r
  have hd2 : p ^ 2 ∣ c * ∏ q ∈ S, q := by simpa only [pow_two] using hdiv
  have hsquare : Squarefree (∏ q ∈ S, q) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun q hq t ht hne => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hS q hq) (hS t ht)).mpr hne))
      (fun q hq => (hS q hq).squarefree)
  exact (Nat.squarefree_iff_prime_squarefree.mp hsquare p hp)
    (by simpa only [pow_two] using (hpcop.pow_left 2).dvd_of_dvd_mul_left hd2)

end U3PairBound

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1.H2 := by
  intro c hc _ a S b u ha _ _ hS hbal p r hp hr hdiv hnot
  apply U3PairBound.pair_bound hc.pos (fun q hq => (hS q hq).1) hp hr ?_ hnot
  have hseed := OMA.R_Erdos1052_erdos_1052_R2_H2_R2.seed_divisibility (a := a) (c := c) (by omega) hc S hbal
  exact hdiv.trans ((dvd_mul_right _ _).trans hseed)
