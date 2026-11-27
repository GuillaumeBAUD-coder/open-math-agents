import OMAReductions.R_Erdos384_erdos_384_R1

-- Step Erdos384.erdos_384.R1.H1: hypothesis H1 of reduction Erdos384.erdos_384.R1
-- Credit: @koolkao
-- Original proof of Ecklund's first case. If no prime p with 2p ≤ n divides C(n,k), every prime factor
-- of C(n,k) lies in (n-k, n] and occurs once, so C(n,k) ≤ n^s with s the number of primes in (n-k, n].
-- Parity (and, for odd k, a multiple of 3 among three consecutive odd numbers) gives 2s ≤ k, while
-- n^k ≤ k^k C(n,k); together n ≤ k², a contradiction.

namespace OMA384H1

open Finset

lemma prime_odd_of_three_le {p : ℕ} (hp : p.Prime) (h : 3 ≤ p) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | h2
  · omega
  · exact h2

lemma prime_mod_three {p : ℕ} (hp : p.Prime) (h : 5 ≤ p) : p % 3 ≠ 0 := by
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h3)
  omega

lemma prime_mod_six {p : ℕ} (hp : p.Prime) (h : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 := prime_odd_of_three_le hp (by omega)
  have h3 := prime_mod_three hp h
  omega

lemma window_two (b : ℕ) (hb : 2 ≤ b) : ((Ioc b (b + 2)).filter Nat.Prime).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hx hy
  have h1 := prime_odd_of_three_le hx.2 (by omega)
  have h2 := prime_odd_of_three_le hy.2 (by omega)
  omega

lemma window_five (b : ℕ) (hb : 3 ≤ b) : ((Ioc b (b + 5)).filter Nat.Prime).card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hlt
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hx hy hz
  have hx5 : 5 ≤ x := by
    by_contra h; have : x = 4 := by omega
    subst this; exact absurd hx.2 (by decide)
  have hy5 : 5 ≤ y := by
    by_contra h; have : y = 4 := by omega
    subst this; exact absurd hy.2 (by decide)
  have hz5 : 5 ≤ z := by
    by_contra h; have : z = 4 := by omega
    subst this; exact absurd hz.2 (by decide)
  have h1 := prime_mod_six hx.2 hx5
  have h2 := prime_mod_six hy.2 hy5
  have h3 := prime_mod_six hz.2 hz5
  omega

lemma Ioc_split (a j l : ℕ) :
    Ioc a (a + (j + l)) = Ioc a (a + j) ∪ Ioc (a + j) (a + j + l) := by
  rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
  congr 1; ring

lemma card_split (a j l : ℕ) :
    ((Ioc a (a + (j + l))).filter Nat.Prime).card ≤
      ((Ioc a (a + j)).filter Nat.Prime).card + ((Ioc (a + j) (a + j + l)).filter Nat.Prime).card := by
  rw [Ioc_split, Finset.filter_union]
  exact Finset.card_union_le _ _

/-- At most `k / 2` primes in an interval of length `k` above `3` (for `k ≠ 1, 3`). -/
lemma prime_count (a : ℕ) (ha : 3 ≤ a) : ∀ k : ℕ, k ≠ 1 → k ≠ 3 →
    2 * ((Ioc a (a + k)).filter Nat.Prime).card ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hk3
    rcases Nat.lt_or_ge k 6 with hlt | hge
    · interval_cases k
      · simp
      · exact absurd rfl hk1
      · have := window_two a (by omega); omega
      · exact absurd rfl hk3
      · have h := card_split a 2 2
        simp only [Nat.reduceAdd] at h
        have h1 := window_two a (by omega)
        have h2 := window_two (a + 2) (by omega)
        omega
      · have := window_five a ha; omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hj := ih j (by omega) (by omega) (by omega)
      have h := card_split a j 2
      have h2 := window_two (a + j) (by omega)
      omega

lemma descFactorial_bound (n k : ℕ) (hkn : k ≤ n) :
    n ^ k * k.factorial ≤ k ^ k * n.descFactorial k := by
  rw [Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range,
    show n ^ k = ∏ _i ∈ range k, n by simp, show k ^ k = ∏ _i ∈ range k, k by simp,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod' 
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : i ≤ k := hi.le
  have h2 : i ≤ n := by omega
  zify [h1, h2]
  nlinarith

lemma choose_lower (n k : ℕ) (hkn : k ≤ n) : n ^ k ≤ k ^ k * n.choose k := by
  have h := descFactorial_bound n k hkn
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hf : 0 < k.factorial := Nat.factorial_pos k
  have : n ^ k * k.factorial ≤ (k ^ k * n.choose k) * k.factorial := by
    calc n ^ k * k.factorial ≤ k ^ k * (k.factorial * n.choose k) := h
      _ = (k ^ k * n.choose k) * k.factorial := by ring
  exact Nat.le_of_mul_le_mul_right this hf

theorem h1 : ∀ n k : ℕ, 4 ≤ k → k * k < n → ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  intro n k hk hkn
  by_contra hcon
  push Not at hcon
  have hkn' : k ≤ n := by nlinarith
  set C := n.choose k with hC
  have hC0 : C ≠ 0 := (Nat.choose_pos hkn').ne'
  -- every prime factor of `C` is a prime in `(n - k, n]`
  have hbig : ∀ p, p.Prime → p ∣ C → n < 2 * p := fun p hp hd => hcon p hp hd
  have hsq : ∀ p, p.Prime → p ∣ C → n < p ^ 2 := by
    intro p hp hd
    have := hbig p hp hd
    nlinarith
  have hle : ∀ p, p.Prime → p ∣ C → p ≤ n := by
    intro p hp hd
    by_contra h
    push Not at h
    have : C.factorization p = 0 := Nat.factorization_choose_eq_zero_of_lt h
    have hpos : 0 < C.factorization p := hp.factorization_pos_of_dvd hC0 hd
    omega
  have hlow : ∀ p, p.Prime → p ∣ C → n - k < p := by
    intro p hp hd
    by_contra h
    push Not at h
    have hp2 : p ^ 2 ∣ n.factorial := by
      have hmul := Nat.choose_mul_factorial_mul_factorial hkn'
      have h1 : p ∣ (n - k).factorial := hp.dvd_factorial.mpr (by
        have := hbig p hp hd; omega)
      have : p * p ∣ C * k.factorial * (n - k).factorial :=
        Nat.mul_dvd_mul (Dvd.dvd.mul_right hd _) h1
      rw [hmul] at this
      simpa [sq] using this
    have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow (by omega) (hsq p hp hd)
    rw [hp.pow_dvd_factorial_iff hlog] at hp2
    simp only [show Finset.Ico 1 2 = {1} by rfl, Finset.sum_singleton, pow_one] at hp2
    have : n / p < 2 := by
      have := hbig p hp hd
      exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
    omega
  -- `C` is squarefree
  have hsqf : Squarefree C := by
    rw [Nat.squarefree_iff_factorization_le_one hC0]
    intro p
    by_cases hp : p.Prime
    · by_cases hd : p ∣ C
      · exact Nat.factorization_choose_le_one (hsq p hp hd)
      · rw [Nat.factorization_eq_zero_of_not_dvd hd]; omega
    · rw [Nat.factorization_eq_zero_of_not_prime C hp]; omega
  set S := (Ioc (n - k) n).filter Nat.Prime with hS
  have hsub : C.primeFactors ⊆ S := by
    intro p hpC
    rw [Nat.mem_primeFactors] at hpC
    rw [hS, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlow p hpC.1 hpC.2.1, hle p hpC.1 hpC.2.1⟩, hpC.1⟩
  have hCle : C ≤ n ^ S.card := by
    calc C = ∏ p ∈ C.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsqf).symm
      _ ≤ ∏ p ∈ S, p := by
          apply Finset.prod_le_prod_of_subset_of_one_le' hsub
          intro p hp _
          exact (Finset.mem_filter.mp hp).2.one_lt.le
      _ ≤ n ^ S.card := by
          apply Finset.prod_le_pow_card
          intro p hp
          exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have hcount : 2 * S.card ≤ k := by
    have h4k : 4 * k ≤ k * k := Nat.mul_le_mul_right k hk
    have := prime_count (n - k) (by omega) k (by omega) (by omega)
    rwa [show n - k + k = n by omega] at this
  have hlower := choose_lower n k hkn'
  -- combine
  have hn1 : 1 ≤ n := by omega
  have key : n ^ k ≤ k ^ k * n ^ S.card := hlower.trans (Nat.mul_le_mul_left _ hCle)
  have hsplit : n ^ k = n ^ (k - S.card) * n ^ S.card := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at key
  have hpos : 0 < n ^ S.card := by positivity
  have h2 : n ^ (k - S.card) ≤ k ^ k := Nat.le_of_mul_le_mul_right key hpos
  have h3 : n ^ (2 * (k - S.card)) ≤ (k * k) ^ k := by
    rw [pow_mul', show (k * k) ^ k = (k ^ k) ^ 2 by ring]
    exact Nat.pow_le_pow_left h2 2
  have h4 : n ^ k ≤ n ^ (2 * (k - S.card)) := Nat.pow_le_pow_right hn1 (by omega)
  have h5 : n ^ k ≤ (k * k) ^ k := h4.trans h3
  have h6 : n ≤ k * k := (Nat.pow_le_pow_iff_left (by omega)).mp h5
  omega

end OMA384H1

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H1 := OMA384H1.h1
