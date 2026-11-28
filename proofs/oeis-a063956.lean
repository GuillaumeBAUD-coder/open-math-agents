import OMAStatements.S_oeis_a063956

-- Proof of oeis-a063956
-- Credit: @lettucrisp

namespace OeisA063956

open OMA.S_oeis_a063956

private lemma a_eq_sum_over {d k : ℕ} (hd : d ∣ k) (hk : k ≠ 0) :
    a d = ∑ p ∈ k.primeFactors, if d.factorization p = 1 then p else 0 := by
  unfold a
  refine Finset.sum_subset (Nat.primeFactors_mono hd hk) ?_
  intro p _ hp_not
  have h0 : d.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
  simp [h0]

private lemma term_eq (x y p : ℕ) :
    ((if x + y = 1 then p else 0) +
      (if min (2 * y) x = 1 then p else 0) +
      (if min y (2 * x) = 1 then p else 0)) =
    (if y = 1 then p else 0) + (if x = 1 then p else 0) := by
  split_ifs <;> omega

private lemma main_proof :
    ∀ m n : ℕ, 0 < m → 0 < n →
      a (m * n) + a ((n ^ 2).gcd m) + a (n.gcd (m ^ 2)) = a n + a m := by
  intro m n hm hn
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
  have hn20 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  rw [a_eq_sum_over (dvd_refl (m * n)) hmn0,
      a_eq_sum_over (dvd_trans (Nat.gcd_dvd_right (n ^ 2) m) (dvd_mul_right m n)) hmn0,
      a_eq_sum_over (dvd_trans (Nat.gcd_dvd_left n (m ^ 2)) (dvd_mul_left n m)) hmn0,
      a_eq_sum_over (dvd_mul_left n m) hmn0,
      a_eq_sum_over (dvd_mul_right m n) hmn0]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul hm0 hn0,
      Nat.factorization_gcd hn20 hm0,
      Nat.factorization_gcd hn0 hm20,
      Nat.factorization_pow, Nat.factorization_pow]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    Finsupp.inf_apply]
  exact term_eq (m.factorization p) (n.factorization p) p

end OeisA063956

theorem OMA.solution : type_of% @OMA.S_oeis_a063956.main :=
  OeisA063956.main_proof
