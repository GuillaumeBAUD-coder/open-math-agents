import FormalConjectures.OEIS.«46969»

-- Problem: Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$
-- Upstream: formal-conjectures FormalConjectures/OEIS/46969.lean:125 (declaration OeisA46969.conjecture1)
-- Credit: @jagong-cmu (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof: von Staudt-Clausen gives B_{2p} = N/6 with N = 6Z - 5. Faulhaber plus a doubling
-- congruence give p | N and (2p-1) not dividing N, so a p = 12 (2p - 1).

open Finset

namespace OMA46969

abbrev RI (r : ℕ) [Fact r.Prime] : Subring ℚ := (Rat.padicValuation r).integer

lemma mem_RI {r : ℕ} [Fact r.Prime] {x : ℚ} : x ∈ RI r ↔ ¬ r ∣ x.den := by
  rw [Valuation.mem_integer_iff]
  exact Rat.padicValuation_le_one_iff

lemma inv_mem_RI {r : ℕ} [Fact r.Prime] {s : ℕ} (hs : 0 < s) (h : ¬ r ∣ s) :
    (1 / (s : ℚ)) ∈ RI r := by
  rw [mem_RI, one_div, Rat.inv_natCast_den_of_pos hs]
  exact h

lemma dvd_of_eq_mul {r : ℕ} [Fact r.Prime] (k : ℕ) (M : ℤ) (W : ℚ) (hW : W ∈ RI r)
    (h : (M : ℚ) = (r : ℚ) ^ k * W) : ((r : ℤ) ^ k) ∣ M := by
  rw [mem_RI] at hW
  have hcop : IsCoprime ((r : ℤ) ^ k) (W.den : ℤ) := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).2 hW
    exact_mod_cast this
  have h2 : M * W.den = (r : ℤ) ^ k * W.num := by
    have hd : (W.den : ℚ) ≠ 0 := by positivity
    have : (M : ℚ) * W.den = (r : ℚ) ^ k * W.num := by
      rw [h]
      nth_rewrite 1 [← Rat.num_div_den W]
      field_simp
    exact_mod_cast this
  exact hcop.dvd_of_dvd_mul_right ⟨_, h2⟩

lemma r_mul_inv_prime_mem {r s : ℕ} [Fact r.Prime] (hs : s.Prime) :
    (r : ℚ) * (1 / (s : ℚ)) ∈ RI r := by
  by_cases h : s = r
  · subst h
    rw [mul_one_div_cancel (by exact_mod_cast hs.ne_zero)]
    exact (RI s).one_mem
  · apply Subring.mul_mem _ (natCast_mem _ _)
    apply inv_mem_RI hs.pos
    intro hd
    exact h ((Nat.prime_dvd_prime_iff_eq Fact.out hs).1 hd).symm

lemma r_mul_bernoulli_mem {r : ℕ} [Fact r.Prime] (i : ℕ) : (r : ℚ) * bernoulli i ∈ RI r := by
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | hodd
  · obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have hB : bernoulli (k + k) = z - ∑ s ∈ range (2 * k + 2) with s.Prime ∧ (s - 1) ∣ 2 * k,
        (1 : ℚ) / s := by
      rw [← two_mul]; linarith
    rw [hB, mul_sub, mul_sum]
    apply Subring.sub_mem _ (Subring.mul_mem _ (natCast_mem _ _) (intCast_mem _ _))
    apply Subring.sum_mem
    intro s hs
    exact r_mul_inv_prime_mem (mem_filter.1 hs).2.1
  · by_cases h1 : i = 1
    · subst h1
      rw [bernoulli_one]
      have := r_mul_inv_prime_mem (r := r) Nat.prime_two
      have e : (r : ℚ) * (-1 / 2) = -((r : ℚ) * (1 / ((2 : ℕ) : ℚ))) := by push_cast; ring
      rw [e]
      exact Subring.neg_mem _ this
    · rw [bernoulli_eq_zero_of_odd hodd (by obtain ⟨t, ht⟩ := hodd; omega), mul_zero]
      exact Subring.zero_mem _

lemma faulhaber_mod {r : ℕ} [Fact r.Prime] (m : ℕ) (hm : 4 ≤ m) (hodd : Odd (m - 1))
    (hr : ¬ r ∣ m + 1) :
    ∃ Y ∈ RI r, (∑ k ∈ range r, (k : ℚ) ^ m) = r * bernoulli m + (r : ℚ) ^ 2 * Y := by
  rw [sum_range_pow]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  rw [sum_range_succ, sum_range_succ]
  refine ⟨∑ i ∈ range (j + 1), ((r : ℚ) * bernoulli i) * ((j + 2 + 1).choose i : ℚ) *
    (r : ℚ) ^ (j - i) * (1 / ((j + 2 + 1 : ℕ) : ℚ)), ?_, ?_⟩
  · apply Subring.sum_mem
    intro i _
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (r_mul_bernoulli_mem i)
      (natCast_mem _ _)) (Subring.pow_mem _ (natCast_mem _ _) _)) ?_
    exact inv_mem_RI (by omega) hr
  · have hB : bernoulli (j + 1) = 0 :=
      bernoulli_eq_zero_of_odd (by simpa using hodd) (by omega)
    rw [hB, mul_sum]
    have hr0 : ((j : ℚ) + 2 + 1) ≠ 0 := by positivity
    have e1 : ∀ i ∈ range (j + 1), bernoulli i * ((j + 2 + 1).choose i : ℚ) *
        (r : ℚ) ^ (j + 2 + 1 - i) / ((j + 2 : ℕ) + 1 : ℚ) =
        (r : ℚ) ^ 2 * (((r : ℚ) * bernoulli i) * ((j + 2 + 1).choose i : ℚ) *
          (r : ℚ) ^ (j - i) * (1 / ((j + 2 + 1 : ℕ) : ℚ))) := by
      intro i hi
      have hi' := mem_range.1 hi
      rw [show j + 2 + 1 - i = (j - i) + 3 by omega, pow_add]
      push_cast
      field_simp
    rw [sum_congr rfl e1]
    simp only [Nat.choose_succ_self_right, show j + 2 + 1 - (j + 2) = 1 by omega]
    push_cast
    field_simp
    ring


lemma sum_range_odd (f : ℕ → ℤ) (h : ℕ) : ∑ k ∈ range (2 * h + 1), f k =
    ∑ j ∈ range (h + 1), f (2 * j) + ∑ j ∈ range h, f (2 * j + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) + 1 = 2 * h + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun j => f (2 * j)) (h + 1), sum_range_succ (fun j => f (2 * j + 1)) h,
      show 2 * (h + 1) = 2 * h + 1 + 1 by ring]
    ring

lemma sum_range_double (f : ℕ → ℤ) (h : ℕ) : ∑ k ∈ range (2 * h + 1), f (2 * k) =
    ∑ j ∈ range (h + 1), f (2 * j) + ∑ j ∈ range h, f (2 * (j + h + 1)) := by
  rw [show 2 * h + 1 = (h + 1) + h by ring, sum_range_add]
  congr 1
  apply sum_congr rfl
  intro j _
  ring_nf

lemma doubling (h n : ℕ) :
    ((2 * h + 1 : ℕ) : ℤ) ^ 2 ∣ (2 ^ n - 1) * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ n
      - ((2 * h + 1 : ℕ) : ℤ) * n * ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ (n - 1) := by
  have hS := sum_range_odd (fun k => (k : ℤ) ^ n) h
  have hD := sum_range_double (fun k => (k : ℤ) ^ n) h
  beta_reduce at hS hD
  have h2 : (2 : ℤ) ^ n * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ n =
      ∑ k ∈ range (2 * h + 1), ((2 * k : ℕ) : ℤ) ^ n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    push_cast
    ring
  have h3 : ∑ j ∈ range h, ((2 * (j + h + 1) : ℕ) : ℤ) ^ n =
      ∑ j ∈ range h, (((2 * j + 1 : ℕ) : ℤ) + ((2 * h + 1 : ℕ) : ℤ)) ^ n := by
    apply sum_congr rfl
    intro j _
    push_cast
    ring
  have key : (2 ^ n - 1) * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ n
      - ((2 * h + 1 : ℕ) : ℤ) * n * ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ (n - 1) =
      ∑ j ∈ range h, ((((2 * j + 1 : ℕ) : ℤ) + ((2 * h + 1 : ℕ) : ℤ)) ^ n
        - ((2 * j + 1 : ℕ) : ℤ) ^ (n - 1) * ((2 * h + 1 : ℕ) : ℤ) * n
        - ((2 * j + 1 : ℕ) : ℤ) ^ n) := by
    rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul, ← h3]
    linear_combination h2 + hD - hS
  rw [key]
  exact dvd_sum fun j _ => sq_dvd_add_pow_sub_sub _ _ n

lemma p_sq_dvd (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    ((p : ℤ)) ^ 2 ∣ ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
  obtain ⟨g, hg⟩ := hp.odd_of_ne_two (by omega)
  have hd := doubling g (2 * p)
  rw [← hg] at hd
  have h1 : ((p : ℤ)) ^ 2 ∣ (2 ^ (2 * p) - 1) * ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
    have : ((p : ℤ)) ^ 2 ∣ (p : ℤ) * ((2 * p : ℕ) : ℤ) *
        ∑ j ∈ range g, ((2 * j + 1 : ℕ) : ℤ) ^ (2 * p - 1) :=
      ⟨2 * ∑ j ∈ range g, ((2 * j + 1 : ℕ) : ℤ) ^ (2 * p - 1), by push_cast; ring⟩
    have := dvd_add hd this
    rwa [sub_add_cancel] at this
  have hcop : IsCoprime ((p : ℤ) ^ 2) (2 ^ (2 * p) - 1) := by
    apply IsCoprime.pow_left
    rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)]
    intro hdvd
    haveI := Fact.mk hp
    have h0 : ((2 ^ (2 * p) - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    push_cast at h0
    rw [pow_mul, ZMod.pow_card] at h0
    have h3' : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h0
    rw [ZMod.natCast_eq_zero_iff] at h3'
    have := Nat.le_of_dvd (by norm_num) h3'
    omega
  exact hcop.dvd_of_dvd_mul_left h1

lemma sum_odd_nat (h : ℕ) : ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) = (h : ℤ) ^ 2 := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_range_succ, ih]; push_cast; ring

lemma q_not_sq_dvd (p q : ℕ) (hq : q + 1 = 2 * p) (hp' : q.Prime) (h3 : 3 < p) :
    ¬ ((q : ℕ) : ℤ) ^ 2 ∣ ∑ k ∈ range q, (k : ℤ) ^ (2 * p) := by
  intro hT
  obtain ⟨h, rfl⟩ : ∃ h, p = h + 1 := ⟨p - 1, by omega⟩
  obtain rfl : q = 2 * h + 1 := by omega
  have hd := doubling h (2 * (h + 1))
  rw [show 2 * (h + 1) - 1 = 2 * h + 1 by omega] at hd
  have hF : ((2 * h + 1 : ℕ) : ℤ) ∣ ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ (2 * h + 1)
      - (h : ℤ) ^ 2 := by
    haveI := Fact.mk hp'
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have e := congrArg (fun x : ℤ => (x : ZMod (2 * h + 1))) (sum_odd_nat h)
    simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast] at e
    simp only [Int.cast_sub, Int.cast_sum, Int.cast_pow, Int.cast_natCast]
    simp_rw [ZMod.pow_card]
    rw [e, sub_self]
  have key : ((2 * h + 1 : ℕ) : ℤ) ^ 2 ∣
      4 * (2 ^ (2 * (h + 1)) - 1) * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ (2 * (h + 1))
      - 4 * ((2 ^ (2 * (h + 1)) - 1) * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ (2 * (h + 1))
        - ((2 * h + 1 : ℕ) : ℤ) * ((2 * (h + 1) : ℕ) : ℤ) *
          ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ (2 * h + 1))
      - 4 * ((2 * (h + 1) : ℕ) : ℤ) * (((2 * h + 1 : ℕ) : ℤ) *
          (∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ (2 * h + 1) - (h : ℤ) ^ 2))
      - ((2 * h + 1 : ℕ) : ℤ) ^ 2 * (4 * (h : ℤ) ^ 2 + 2 * h - 1) := by
    refine dvd_sub (dvd_sub (dvd_sub (dvd_mul_of_dvd_right hT _) (dvd_mul_of_dvd_right hd _))
      (dvd_mul_of_dvd_right ?_ _)) (dvd_mul_right _ _)
    rw [sq]
    exact mul_dvd_mul_left _ hF
  have hq2 : ((2 * h + 1 : ℕ) : ℤ) ^ 2 ∣ ((2 * h + 1 : ℕ) : ℤ) := by
    convert key using 1
    push_cast
    ring
  have := Int.le_of_dvd (by positivity) hq2
  push_cast at this
  nlinarith

lemma vs_primes (p s : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p)
    (hs : s.Prime) (hdvd : (s - 1) ∣ 2 * p) : s = 2 ∨ s = 3 := by
  have hs2 := hs.two_le
  obtain ⟨q, hq⟩ : ∃ q, q = 2 * p - 1 := ⟨_, rfl⟩
  rw [← hq] at hp'
  by_cases hps : p ∣ s - 1
  · obtain ⟨t, ht⟩ := hps
    have ht2 : t ∣ 2 := by
      rw [ht, mul_comm 2 p] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
    have : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht2
    have hst : s = p * t + 1 := by omega
    interval_cases t
    · omega
    · exfalso
      obtain ⟨g, hg⟩ := hp.odd_of_ne_two (by omega)
      have h2 : 2 ∣ s := ⟨g + 1, by omega⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hs).1 h2
      omega
    · exfalso
      have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      have : 3 ∣ s ∨ 3 ∣ q ∨ 3 ∣ p := by
        rcases hmod with h | h | h
        · right; right; omega
        · left; omega
        · right; left; omega
      rcases this with h | h | h
      · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).1 h; omega
      · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp').1 h; omega
      · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h; omega
  · have hcop : Nat.Coprime (s - 1) p := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hps
    have : (s - 1) ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by norm_num) this
    omega


theorem main (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (OeisA46969.a p / 12).Prime := by
  have hfilt : (range (2 * p + 2)).filter (fun s => s.Prime ∧ (s - 1) ∣ 2 * p) = {2, 3} := by
    ext s
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨_, hsp, hdvd⟩
      exact vs_primes p s hp hp' h3 hsp hdvd
    · rintro (rfl | rfl)
      · exact ⟨by omega, Nat.prime_two, by simp⟩
      · exact ⟨by omega, Nat.prime_three, ⟨p, by omega⟩⟩
  obtain ⟨Z, hZ⟩ := Bernoulli.vonStaudt_clausen p
  rw [hfilt, sum_pair (by norm_num)] at hZ
  have hB : bernoulli (2 * p) = ((6 * Z - 5 : ℤ) : ℚ) / 6 := by
    push_cast at hZ ⊢
    linarith
  obtain ⟨q, hq⟩ : ∃ q, 2 * p - 1 = q := ⟨_, rfl⟩
  rw [hq] at hp'
  have hq1 : q + 1 = 2 * p := by omega
  have hq7 : 7 ≤ q := by omega
  -- H1 : p divides the numerator
  have H1 : (p : ℤ) ∣ 6 * Z - 5 := by
    haveI := Fact.mk hp
    have hr : ¬ p ∣ 2 * p + 1 := by
      intro h
      have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p 2)).1 h
      have := Nat.le_of_dvd (by norm_num) this
      omega
    obtain ⟨Y, hY, hF⟩ := faulhaber_mod (r := p) (2 * p) (by omega) ⟨p - 1, by omega⟩ hr
    obtain ⟨t, ht⟩ := p_sq_dvd p hp h3
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have htq : (∑ k ∈ range p, (k : ℚ) ^ (2 * p)) = (p : ℚ) ^ 2 * t := by
      have := congrArg (fun x : ℤ => (x : ℚ)) ht
      push_cast at this
      exact this
    have hBp : bernoulli (2 * p) = p * (t - Y) := by
      have h0 : (p : ℚ) * (bernoulli (2 * p) - p * (t - Y)) = 0 := by
        linear_combination htq.symm.trans hF |>.symm
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hp0
      · linarith
    rw [← pow_one (p : ℤ)]
    apply dvd_of_eq_mul (r := p) 1 _ (((6 : ℤ) : ℚ) * ((t : ℚ) - Y))
      (Subring.mul_mem _ (intCast_mem _ _) (Subring.sub_mem _ (intCast_mem _ _) hY))
    have := hB.symm.trans hBp
    push_cast at this ⊢
    linear_combination 6 * this
  -- H2 : q does not divide the numerator
  have H2 : ¬ (q : ℤ) ∣ 6 * Z - 5 := by
    rintro ⟨N2, hN2⟩
    haveI := Fact.mk hp'
    have hr : ¬ q ∣ 2 * p + 1 := by
      intro h
      rw [show 2 * p + 1 = q + 2 by omega] at h
      have : q ∣ 2 := (Nat.dvd_add_right (dvd_refl q)).1 h
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have h6 : ¬ q ∣ 6 := by
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    obtain ⟨Y, hY, hF⟩ := faulhaber_mod (r := q) (2 * p) (by omega) ⟨p - 1, by omega⟩ hr
    apply q_not_sq_dvd p q hq1 hp' h3
    apply dvd_of_eq_mul (r := q) 2 _ ((N2 : ℚ) * (1 / ((6 : ℕ) : ℚ)) + Y)
      (Subring.add_mem _ (Subring.mul_mem _ (intCast_mem _ _) (inv_mem_RI (by norm_num) h6)) hY)
    push_cast
    rw [hF, hB]
    have : ((6 * Z - 5 : ℤ) : ℚ) = (q : ℚ) * N2 := by exact_mod_cast hN2
    rw [this]
    ring
  obtain ⟨N1, hN1⟩ := H1
  have hcop : Nat.Coprime N1.natAbs (((12 * q : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast]
    apply Nat.coprime_of_dvd
    intro k hk hk1 hk2
    have hkN : (k : ℤ) ∣ 6 * Z - 5 := by
      rw [hN1]
      exact Dvd.dvd.mul_left (Int.ofNat_dvd_left.2 hk1) _
    rcases (Nat.Prime.dvd_mul hk).1 hk2 with h12 | hkq
    · have : k ≤ 12 := Nat.le_of_dvd (by norm_num) h12
      interval_cases k <;> first | omega | (exfalso; norm_num at hk)
    · have := (Nat.prime_dvd_prime_iff_eq hk hp').1 hkq
      subst this
      exact H2 hkN
  have ha : OeisA46969.a p = 12 * q := by
    unfold OeisA46969.a
    rw [if_neg (by omega)]
    show (bernoulli (2 * p) / ((2 * p * (2 * p - 1) : ℕ) : ℚ)).den = 12 * q
    have hx : bernoulli (2 * p) / ((2 * p * (2 * p - 1) : ℕ) : ℚ) =
        ((N1 : ℤ) : ℚ) / (((12 * q : ℕ) : ℤ) : ℚ) := by
      rw [hB, hN1, hq]
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
      push_cast
      field_simp
      ring
    rw [hx]
    have := Rat.den_div_eq_of_coprime (a := N1) (b := ((12 * q : ℕ) : ℤ)) (by positivity) hcop
    exact_mod_cast this
  rw [ha, Nat.mul_div_cancel_left q (by norm_num)]
  exact hp'

end OMA46969

theorem OMA.solution : type_of% @OeisA46969.conjecture1 := by
  exact fun p hp hp' h3 => OMA46969.main p hp hp' h3
