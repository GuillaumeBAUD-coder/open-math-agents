import OMAReductions.R_Erdos384_erdos_384_R1_H2_R1

open Finset

namespace OMAEckTwo

lemma bern (k m : ℕ) : k ^ m * (k + m) ≤ (k + 1) ^ m * k := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc k ^ (m + 1) * (k + (m + 1)) ≤ k ^ m * (k + m) * (k + 1) := by
          have h1 : k ^ (m + 1) * (k + (m + 1)) = k ^ m * (k * k + k * m + k) := by ring
          have h2 : k ^ m * (k + m) * (k + 1) = k ^ m * (k * k + k * m + k + m) := by ring
          rw [h1, h2]
          exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ (k + 1) ^ m * k * (k + 1) := Nat.mul_le_mul_right _ ih
      _ = (k + 1) ^ (m + 1) * k := by ring

lemma two_pow_le (k : ℕ) (hk : 0 < k) : 2 * k ^ k ≤ (k + 1) ^ k := by
  have h := bern k k
  have h2 : k ^ k * (k + k) = (2 * k ^ k) * k := by ring
  rw [h2] at h
  exact Nat.le_of_mul_le_mul_right h hk

lemma fact_bound2 (k : ℕ) (hk : 60 ≤ k) : 4 ^ k * k.factorial * (k * k) ≤ 3 ^ k * k ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hb := two_pow_le k (by omega)
    have h6 : 4 * ((k + 1) * (k + 1)) ≤ 6 * (k * k) := by nlinarith
    have hkk : 0 < k * k := Nat.mul_pos (by omega) (by omega)
    apply Nat.le_of_mul_le_mul_right _ hkk
    calc 4 ^ (k + 1) * (k + 1).factorial * ((k + 1) * (k + 1)) * (k * k)
        = 4 * (k + 1) * ((k + 1) * (k + 1)) * (4 ^ k * k.factorial * (k * k)) := by
          rw [Nat.factorial_succ]; ring
      _ ≤ 4 * (k + 1) * ((k + 1) * (k + 1)) * (3 ^ k * k ^ k) := Nat.mul_le_mul_left _ ih
      _ = (k + 1) * 3 ^ k * k ^ k * (4 * ((k + 1) * (k + 1))) := by ring
      _ ≤ (k + 1) * 3 ^ k * k ^ k * (6 * (k * k)) := Nat.mul_le_mul_left _ h6
      _ = 3 * (k + 1) * 3 ^ k * (k * k) * (2 * k ^ k) := by ring
      _ ≤ 3 * (k + 1) * 3 ^ k * (k * k) * ((k + 1) ^ k) := Nat.mul_le_mul_left _ hb
      _ = 3 ^ (k + 1) * (k + 1) ^ (k + 1) * (k * k) := by ring

lemma window_count (n k : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, n - k < m ∧ m ≤ n ∧ (m % 6 = 1 ∨ m % 6 = 5)) :
    S.card ≤ (k + 4) / 3 := by
  have hinj : Set.InjOn (fun m : ℕ => m / 3) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hS a (Finset.mem_coe.1 ha)
    have h2 := hS b (Finset.mem_coe.1 hb)
    simp only at hab
    omega
  have hsub : S.image (fun m : ℕ => m / 3) ⊆ Finset.Icc ((n - k + 1) / 3) (n / 3) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
    have h1 := hS m hm
    rw [Finset.mem_Icc]
    omega
  calc S.card = (S.image (fun m : ℕ => m / 3)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc ((n - k + 1) / 3) (n / 3)).card := Finset.card_le_card hsub
    _ = n / 3 + 1 - (n - k + 1) / 3 := Nat.card_Icc _ _
    _ ≤ (k + 4) / 3 := by omega

end OMAEckTwo

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1_H2_R1.H2 := by
  intro n k hk hcube hnk
  by_contra hcon
  push_neg at hcon
  have h4kn : 4 * k ≤ n := by
    by_contra hlt
    push_neg at hlt
    have h1 : n * n ≤ (4 * k) * (4 * k) := Nat.mul_le_mul hlt.le hlt.le
    have h2 : 16 * (k * k) ≤ k * (k * k) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hkn' : k ≤ n := by omega
  have h240 : 240 ≤ n := by omega
  obtain ⟨C, hCdef⟩ : ∃ C, C = n.choose k := ⟨_, rfl⟩
  rw [← hCdef] at hcon
  have hCpos : 0 < C := by rw [hCdef]; exact Nat.choose_pos hkn'
  have hfact : C * k.factorial * (n - k).factorial = n.factorial := by
    rw [hCdef]; exact Nat.choose_mul_factorial_mul_factorial hkn'
  have hpf : ∀ p ∈ C.primeFactors, n - k < p ∧ p ≤ n ∧ (p % 6 = 1 ∨ p % 6 = 5) ∧
      C.factorization p = 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hlarge := hcon p hpp hpd
    have hp2 := hpp.two_le
    have hpn : p ≤ n := by
      have : p ∣ n.factorial := by
        rw [← hfact]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpd _) _
      exact (Nat.Prime.dvd_factorial hpp).1 this
    have hpos : 0 < C.factorization p := hpp.factorization_pos_of_dvd hCpos.ne' hpd
    have hnpp : n < p ^ 2 := by nlinarith
    have hle1 : C.factorization p ≤ 1 := by
      rw [hCdef]; exact Nat.factorization_choose_le_one hnpp
    have hlogn : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) hnpp
    have hgt : n - k < p := by
      by_contra hle
      push_neg at hle
      have hlognk : Nat.log p (n - k) < 2 :=
        Nat.log_lt_of_lt_pow' (by decide) (lt_of_le_of_lt (Nat.sub_le n k) hnpp)
      have h1 : n.factorial.factorization p = 1 := by
        rw [Nat.factorization_factorial hpp hlogn]
        simp only [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, pow_one]
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have h2 : (n - k).factorial.factorization p = 1 := by
        rw [Nat.factorization_factorial hpp hlognk]
        simp only [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, pow_one]
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have h3 : (C * k.factorial * (n - k).factorial).factorization p =
          n.factorial.factorization p := by rw [hfact]
      rw [Nat.factorization_mul (mul_ne_zero hCpos.ne' (Nat.factorial_ne_zero k))
        (Nat.factorial_ne_zero _),
        Nat.factorization_mul hCpos.ne' (Nat.factorial_ne_zero k)] at h3
      simp only [Finsupp.coe_add, Pi.add_apply] at h3
      omega
    have h2 : ¬ 2 ∣ p := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 h
      omega
    have h3 : ¬ 3 ∣ p := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1 h
      omega
    refine ⟨hgt, hpn, by omega, by omega⟩
  have hsqf : Squarefree C := by
    apply Nat.squarefree_of_factorization_le_one hCpos.ne'
    intro p
    by_cases hp : p ∈ C.primeFactors
    · exact (hpf p hp).2.2.2.le
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rw [hp]
      exact Nat.zero_le _
  have hprod : ∏ p ∈ C.primeFactors, p = C := Nat.prod_primeFactors_of_squarefree hsqf
  have hcard := OMAEckTwo.window_count n k C.primeFactors
    (fun p hp => ⟨(hpf p hp).1, (hpf p hp).2.1, (hpf p hp).2.2.1⟩)
  have hn1 : 1 ≤ n := by omega
  have hCle : C ≤ n ^ ((k + 4) / 3) := by
    calc C = ∏ p ∈ C.primeFactors, p := hprod.symm
      _ ≤ ∏ _p ∈ C.primeFactors, n :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hpf p hp).2.1)
      _ = n ^ C.primeFactors.card := Finset.prod_const _
      _ ≤ n ^ ((k + 4) / 3) := Nat.pow_le_pow_right hn1 hcard
  have hdesc : (n + 1 - k) ^ k ≤ C * k.factorial := by
    rw [hCdef, mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.pow_sub_le_descFactorial n k
  obtain ⟨t, ht⟩ : ∃ t, t = (k + 4) / 3 := ⟨_, rfl⟩
  rw [← ht] at hCle
  have htk : t ≤ k := by omega
  have h3n : 3 * n ≤ 4 * (n + 1 - k) := by omega
  have hnt : 0 < n ^ t := Nat.pow_pos (by omega)
  have key : 3 ^ k * n ^ (k - t) ≤ 4 ^ k * k.factorial := by
    have h1 : (3 * n) ^ k ≤ (4 * (n + 1 - k)) ^ k := Nat.pow_le_pow_left h3n k
    have h2 : (4 * (n + 1 - k)) ^ k ≤ 4 ^ k * (n ^ t * k.factorial) := by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (hdesc.trans (Nat.mul_le_mul_right _ hCle))
    have h3 : (3 * n) ^ k = 3 ^ k * n ^ (k - t) * n ^ t := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel htk]
    have h4 : 4 ^ k * (n ^ t * k.factorial) = 4 ^ k * k.factorial * n ^ t := by ring
    rw [h3] at h1
    rw [h4] at h2
    exact Nat.le_of_mul_le_mul_right (h1.trans h2) hnt
  have hfb := OMAEckTwo.fact_bound2 k hk
  have hE2 : 2 * k - 4 ≤ 3 * (k - t) := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = n ^ (k - t) := ⟨_, rfl⟩
  rw [← ha] at key
  have h9 : a * (k * k) ≤ k ^ k := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.pow_pos (show 0 < 3 by norm_num) (n := k))
    calc 3 ^ k * (a * (k * k)) = 3 ^ k * a * (k * k) := by ring
      _ ≤ 4 ^ k * k.factorial * (k * k) := Nat.mul_le_mul_right _ key
      _ ≤ 3 ^ k * k ^ k := hfb
  have h8 : k ^ (2 * k - 4) < a * a := by
    have h1 : (k * k * k) ^ (k - t) < (n * n) ^ (k - t) := Nat.pow_lt_pow_left hcube (by omega)
    have h2 : (k * k * k) ^ (k - t) = k ^ (3 * (k - t)) := by
      rw [show k * k * k = k ^ 3 by ring, ← pow_mul]
    have h3 : (n * n) ^ (k - t) = a * a := by
      rw [ha, mul_pow]
    have h4 : k ^ (2 * k - 4) ≤ k ^ (3 * (k - t)) := Nat.pow_le_pow_right (by omega) hE2
    omega
  have h10 := Nat.mul_le_mul h9 h9
  have h11 : k ^ k * k ^ k = k ^ (2 * k - 4) * (k * k * (k * k)) := by
    rw [← pow_add, show k * k * (k * k) = k ^ 4 by ring, ← pow_add]
    congr 1
    omega
  have h12 : k ^ (2 * k - 4) * (k * k * (k * k)) < a * a * (k * k * (k * k)) :=
    Nat.mul_lt_mul_of_pos_right h8 (by positivity)
  have h13 : a * (k * k) * (a * (k * k)) = a * a * (k * k * (k * k)) := by ring
  omega
