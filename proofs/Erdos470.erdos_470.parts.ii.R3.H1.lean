import OMAReductions.R_Erdos470_erdos_470_parts_ii_R3

-- Step Erdos470.erdos_470.parts.ii.R3.H1: hypothesis H1 of reduction Erdos470.erdos_470.parts.ii.R3
-- Credit: @subramanya1997
-- H1 := ∀ k p q : ℕ, p.Prime → q.Prime → 2 ^ (k + 1) < p → 2 ^ (k + 1) < q → p ≠ q →     2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) →     (∀ b c : ℕ, b < 2 ^ (k + 1) → c < 2 ^ (k + 1) →       ¬ (b * p + c * q ≤ (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q ∧         (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q < b * p + c * q + 2 ^ (k + 1))) →     Erdos470.PrimitiveWeird (2 ^ k * p * q)
--
-- Proof sketch.  Put n = 2^k p q, M = 2^(k+1), e = sigma(n) - 2n.
--  * sigma(n) = (M-1)(p+1)(q+1), so n is abundant.
--  * If s is a set of proper divisors summing to n, its complement t sums to e < p q, so no
--    element of t is divisible by p q.  Splitting t by divisibility by p and q, each part sums
--    to r * (a sum of distinct divisors of 2^k) with r = p, q, 1, hence e = a + b p + c q with
--    a, b, c < M, which the hypothesis excludes.
--  * A proper divisor of n divides n/2, n/p or n/q, each with sigma <= twice itself, and
--    sigma(d)/d is monotone along divisibility, so no proper divisor is abundant.

namespace OMA.Aux470

lemma sig2 (k : ℕ) : ∑ d ∈ (2 ^ k).divisors, d + 1 = 2 ^ (k + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (n + 1)]
    linarith

lemma sig2p (k p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    ∑ d ∈ (2 ^ k * p).divisors, d + (p + 1) = 2 ^ (k + 1) * (p + 1) := by
  have hc : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  rw [hc.sum_divisors_mul, hp.sum_divisors, ← sig2 k]
  ring

lemma sig2pq (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (h2q : 2 < q)
    (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ k * p * q).divisors, d + (p + 1) * (q + 1)
      = 2 ^ (k + 1) * (p + 1) * (q + 1) := by
  have hc : Nat.Coprime (2 ^ k * p) q :=
    Nat.Coprime.mul_left
      (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)))
      ((Nat.coprime_primes hp hq).mpr hpq)
  rw [hc.sum_divisors_mul, hq.sum_divisors, ← sig2p k p hp h2p]
  ring

lemma sig_dvd {d m : ℕ} (hm : 0 < m) (h : d ∣ m) :
    (∑ x ∈ d.divisors, x) * m ≤ (∑ x ∈ m.divisors, x) * d := by
  obtain ⟨c, rfl⟩ := h
  have hc : 0 < c := Nat.pos_of_mul_pos_left hm
  have key : (∑ x ∈ d.divisors, x) * c ≤ ∑ x ∈ (d * c).divisors, x := by
    rw [Finset.sum_mul]
    have hinj : Set.InjOn (fun x : ℕ => x * c) (d.divisors : Set ℕ) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right hc hab
    rw [← Finset.sum_image (f := fun x : ℕ => x) hinj]
    apply Finset.sum_le_sum_of_subset
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors hx) c, hm.ne'⟩
  calc (∑ x ∈ d.divisors, x) * (d * c) = (∑ x ∈ d.divisors, x) * c * d := by ring
    _ ≤ (∑ x ∈ (d * c).divisors, x) * d := Nat.mul_le_mul_right _ key

lemma not_abundant_of_dvd {d m : ℕ} (hm : 0 < m) (h : d ∣ m)
    (hs : ∑ x ∈ m.divisors, x ≤ 2 * m) : ¬ d.Abundant := by
  intro ha
  have h1 := sig_dvd hm h
  have h2 : ∑ x ∈ d.divisors, x = ∑ x ∈ d.properDivisors, x + d :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  unfold Nat.Abundant at ha
  have h3 : 2 * d < ∑ x ∈ d.divisors, x := by omega
  have h4 : 2 * d * m < (∑ x ∈ d.divisors, x) * m := Nat.mul_lt_mul_of_pos_right h3 hm
  have h5 : (∑ x ∈ m.divisors, x) * d ≤ 2 * m * d := Nat.mul_le_mul_right _ hs
  have h6 : 2 * d * m = 2 * m * d := by ring
  omega

lemma block_sum (k r : ℕ) (hr : 0 < r) (t : Finset ℕ)
    (ht : ∀ d ∈ t, ∃ x, x ∣ 2 ^ k ∧ d = r * x) :
    ∃ b, b < 2 ^ (k + 1) ∧ ∑ d ∈ t, d = b * r := by
  refine ⟨∑ d ∈ t, d / r, ?_, ?_⟩
  · have hinj : Set.InjOn (fun d : ℕ => d / r) (t : Set ℕ) := by
      intro a ha b hb hab
      obtain ⟨x, -, rfl⟩ := ht a ha
      obtain ⟨y, -, rfl⟩ := ht b hb
      have hab' : r * x / r = r * y / r := hab
      rw [Nat.mul_div_cancel_left _ hr, Nat.mul_div_cancel_left _ hr] at hab'
      rw [hab']
    have h1 : ∑ d ∈ t, d / r = ∑ x ∈ t.image (fun d : ℕ => d / r), x :=
      (Finset.sum_image (f := fun x : ℕ => x) hinj).symm
    have hsub : t.image (fun d : ℕ => d / r) ⊆ (2 ^ k).divisors := by
      intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨x, hx, rfl⟩ := ht d hd
      have : r * x / r = x := Nat.mul_div_cancel_left _ hr
      rw [this]
      exact Nat.mem_divisors.mpr ⟨hx, by positivity⟩
    have h2 : ∑ x ∈ t.image (fun d : ℕ => d / r), x ≤ ∑ x ∈ (2 ^ k).divisors, x :=
      Finset.sum_le_sum_of_subset hsub
    have h3 := sig2 k
    omega
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨x, -, rfl⟩ := ht d hd
    rw [Nat.mul_div_cancel_left _ hr, mul_comm]

lemma strip {x m q : ℕ} (hq : q.Prime) (h : x ∣ m * q) (hx : ¬ q ∣ x) : x ∣ m :=
  (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hx)).dvd_of_dvd_mul_right h

lemma e_lt (u p q e : ℕ) (hp : u + 2 ≤ p) (hq : u + 2 ≤ q)
    (hE : (u + 1) * p * q + e = u * (p + 1) * (q + 1)) : e < p * q := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hq
  nlinarith [Nat.zero_le (u * x), Nat.zero_le (u * y), Nat.zero_le (x * y), Nat.zero_le u,
    Nat.zero_le x, Nat.zero_le y]

lemma half_ineq (N p q : ℕ) (hN : 1 ≤ N) (hp : 2 * N < p) (hq : 2 * N < q) :
    N * (p + 1) * (q + 1) ≤ (p + 1) * (q + 1) + N * p * q := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_lt hp
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_lt hq
  nlinarith [Nat.zero_le (m * x), Nat.zero_le (m * y), Nat.zero_le (x * y), Nat.zero_le m,
    Nat.zero_le x, Nat.zero_le y, Nat.zero_le (m * m)]

end OMA.Aux470

open OMA.Aux470 in
theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R3.H1 := by
  intro k p q hp hq hMp hMq hpq hab hrep
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have hσ := sig2pq k p q hp hq (by omega) (by omega) hpq
  have hσp := sig2p k p hp (by omega)
  have hσq := sig2p k q hq (by omega)
  obtain ⟨u, hu⟩ : ∃ u, 2 ^ (k + 1) = u + 1 := ⟨2 ^ (k + 1) - 1, by omega⟩
  rw [hu] at hab hrep hMp hMq hσ hσp hσq
  simp only [Nat.add_sub_cancel] at hab hrep
  obtain ⟨e, hE⟩ := Nat.exists_eq_add_of_lt hab
  have hE' : (u + 1) * p * q + (e + 1) = u * (p + 1) * (q + 1) := by omega
  have he : u * (p + 1) * (q + 1) - (u + 1) * p * q = e + 1 := by omega
  rw [he] at hrep
  have h2n : 2 * (2 ^ k * p * q) = (u + 1) * p * q := by rw [← hu, hpow]; ring
  have hnpos : 0 < 2 ^ k * p * q := Nat.mul_pos (Nat.mul_pos (by omega) hp.pos) hq.pos
  have hprop : ∑ d ∈ (2 ^ k * p * q).divisors, d
      = ∑ d ∈ (2 ^ k * p * q).properDivisors, d + 2 ^ k * p * q :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hring : (u + 1) * (p + 1) * (q + 1) = u * (p + 1) * (q + 1) + (p + 1) * (q + 1) := by
    ring
  -- sum of proper divisors = n + (e + 1)
  have hpd : ∑ d ∈ (2 ^ k * p * q).properDivisors, d = 2 ^ k * p * q + (e + 1) := by omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show 2 ^ k * p * q < ∑ d ∈ (2 ^ k * p * q).properDivisors, d
    omega
  · rintro ⟨-, s, hs, hsum⟩
    have hsd := Finset.sum_sdiff (f := fun d : ℕ => d) hs
    have ht_sum : ∑ d ∈ (2 ^ k * p * q).properDivisors \ s, d = e + 1 := by
      omega
    have hepq : e + 1 < p * q := e_lt u p q (e + 1) (by omega) (by omega) hE'
    have hmem : ∀ d ∈ (2 ^ k * p * q).properDivisors \ s,
        d ∣ 2 ^ k * p * q ∧ d ≤ e + 1 ∧ 0 < d := by
      intro d hd
      have hd' := (Finset.mem_sdiff.mp hd).1
      refine ⟨(Nat.mem_properDivisors.mp hd').1, ?_, Nat.pos_of_mem_properDivisors hd'⟩
      rw [← ht_sum]
      exact Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _) hd
    have hnotboth : ∀ d ∈ (2 ^ k * p * q).properDivisors \ s, p ∣ d → ¬ q ∣ d := by
      intro d hd h1 h2
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
      have h3 : p * q ∣ d := hcop.mul_dvd_of_dvd_of_dvd h1 h2
      have h4 := Nat.le_of_dvd (hmem d hd).2.2 h3
      have h5 := (hmem d hd).2.1
      omega
    have hsplit1 := Finset.sum_filter_add_sum_filter_not
      ((2 ^ k * p * q).properDivisors \ s) (fun d => p ∣ d) (fun d : ℕ => d)
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (((2 ^ k * p * q).properDivisors \ s).filter (fun d => ¬ p ∣ d)) (fun d => q ∣ d)
      (fun d : ℕ => d)
    have hP : ∀ d ∈ ((2 ^ k * p * q).properDivisors \ s).filter (fun d => p ∣ d),
        ∃ x, x ∣ 2 ^ k ∧ d = p * x := by
      intro d hd
      obtain ⟨hdt, hpd'⟩ := Finset.mem_filter.mp hd
      have hq' := hnotboth d hdt hpd'
      obtain ⟨x, rfl⟩ := hpd'
      refine ⟨x, ?_, rfl⟩
      have h1 : p * x ∣ p * (2 ^ k * q) := by
        have := (hmem _ hdt).1
        rwa [show 2 ^ k * p * q = p * (2 ^ k * q) by ring] at this
      have h2 : x ∣ 2 ^ k * q := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
      exact strip hq h2 (fun h => hq' (Dvd.dvd.mul_left h p))
    have hQ : ∀ d ∈ (((2 ^ k * p * q).properDivisors \ s).filter (fun d => ¬ p ∣ d)).filter
        (fun d => q ∣ d), ∃ x, x ∣ 2 ^ k ∧ d = q * x := by
      intro d hd
      obtain ⟨hd1, hqd⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdt, hpd'⟩ := Finset.mem_filter.mp hd1
      obtain ⟨x, rfl⟩ := hqd
      refine ⟨x, ?_, rfl⟩
      have h1 : q * x ∣ q * (2 ^ k * p) := by
        have := (hmem _ hdt).1
        rwa [show 2 ^ k * p * q = q * (2 ^ k * p) by ring] at this
      have h2 : x ∣ 2 ^ k * p := Nat.dvd_of_mul_dvd_mul_left hq.pos h1
      exact strip hp h2 (fun h => hpd' (Dvd.dvd.mul_left h q))
    have hO : ∀ d ∈ (((2 ^ k * p * q).properDivisors \ s).filter (fun d => ¬ p ∣ d)).filter
        (fun d => ¬ q ∣ d), ∃ x, x ∣ 2 ^ k ∧ d = 1 * x := by
      intro d hd
      obtain ⟨hd1, hqd⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdt, hpd'⟩ := Finset.mem_filter.mp hd1
      refine ⟨d, ?_, (one_mul d).symm⟩
      exact strip hp (strip hq (hmem _ hdt).1 hqd) hpd'
    obtain ⟨b, hb, hbs⟩ := block_sum k p hp.pos _ hP
    obtain ⟨c, hc, hcs⟩ := block_sum k q hq.pos _ hQ
    obtain ⟨a, ha, has⟩ := block_sum k 1 one_pos _ hO
    apply hrep b c (by omega) (by omega)
    constructor <;> omega
  · intro d hd hw
    obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.mp hd
    obtain ⟨c, hc⟩ := hdn
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [mul_one] at hc
      omega
    obtain ⟨l, hl, hlc⟩ := Nat.exists_prime_and_dvd hc1
    have hdl : d * l ∣ 2 ^ k * p * q := by
      rw [hc]
      exact Nat.mul_dvd_mul_left d hlc
    have hln : l ∣ 2 ^ k * p * q := dvd_trans (Dvd.intro_left d rfl) hdl
    apply not_abundant_of_dvd (m := (2 ^ k * p * q) / l) ?_ ?_ ?_ hw.1
    · exact Nat.div_pos (Nat.le_of_dvd hnpos hln) hl.pos
    · apply Nat.dvd_of_mul_dvd_mul_right hl.pos
      rwa [Nat.div_mul_cancel hln]
    · rcases (Nat.Prime.dvd_mul hl).mp hln with h | h
      · rcases (Nat.Prime.dvd_mul hl).mp h with h | h
        · have h2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h)
          subst h2
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
            cases k with
            | zero => simp at h
            | succ j => exact ⟨j, rfl⟩
          have hdiv : 2 ^ (j + 1) * p * q / 2 = 2 ^ j * p * q := by
            rw [show 2 ^ (j + 1) * p * q = 2 * (2 ^ j * p * q) by ring]
            exact Nat.mul_div_cancel_left _ two_pos
          rw [hdiv]
          have hs := sig2pq j p q hp hq (by omega) (by omega) hpq
          have hj1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
          have hh := half_ineq (2 ^ (j + 1)) p q hj1 (by omega) (by omega)
          have h2' : 2 * (2 ^ j * p * q) = 2 ^ (j + 1) * p * q := by ring
          omega
        · have h2 : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).mp h
          subst h2
          have hdiv : 2 ^ k * l * q / l = 2 ^ k * q := by
            rw [show 2 ^ k * l * q = l * (2 ^ k * q) by ring]
            exact Nat.mul_div_cancel_left _ hl.pos
          rw [hdiv]
          have h2' : 2 * (2 ^ k * q) = (u + 1) * q := by rw [← hu, hpow]; ring
          have h3 : (u + 1) * (q + 1) = (u + 1) * q + u + 1 := by ring
          omega
      · have h2 : l = q := (Nat.prime_dvd_prime_iff_eq hl hq).mp h
        subst h2
        have hdiv : 2 ^ k * p * l / l = 2 ^ k * p := Nat.mul_div_cancel _ hl.pos
        rw [hdiv]
        have h2' : 2 * (2 ^ k * p) = (u + 1) * p := by rw [← hu, hpow]; ring
        have h3 : (u + 1) * (p + 1) = (u + 1) * p + u + 1 := by ring
        omega
