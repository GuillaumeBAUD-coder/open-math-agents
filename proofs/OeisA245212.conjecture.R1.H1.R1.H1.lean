import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1

-- Credit: @jatin6
-- For any odd, non-prime-power n with sigma(n) at most 2n,
-- the gap between A245212(n) and sigma(n) is at least n/3.
namespace OMA.A245212DivisorBound

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private lemma totient_dilate (m d : ℕ) : (m * d).totient ≤ m * d.totient := by
  induction m using Nat.recOnMul generalizing d with
  | zero => simp
  | one => simp
  | prime p hp =>
    by_cases h : p ∣ d
    · rw [Nat.totient_mul_of_prime_of_dvd hp h]
    · rw [Nat.totient_mul_of_prime_of_not_dvd hp h]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  | mul a b ha hb =>
    calc
      ((a * b) * d).totient = (a * (b * d)).totient := by rw [Nat.mul_assoc]
      _ ≤ a * (b * d).totient := ha _
      _ ≤ a * (b * d.totient) := Nat.mul_le_mul_left _ (hb _)
      _ = (a * b) * d.totient := (Nat.mul_assoc ..).symm

private lemma totient_ratio {d n : ℕ} (h : d ∣ n) : d * n.totient ≤ n * d.totient := by
  obtain ⟨m, rfl⟩ := h
  have hd := Nat.mul_le_mul_left d (totient_dilate m d)
  simpa only [Nat.mul_comm m d, Nat.mul_assoc] using hd

private lemma sigma_at_most_twice {n : ℕ} (hn : 0 < n) (h : n ≤ 2 * n.totient) :
    σ 1 n ≤ 2 * n := by
  have prod_bound : (σ 1 n) * n.totient ≤ n * n := calc
    _ = ∑ d ∈ n.divisors, d * n.totient := by rw [sigma_one_apply, sum_mul]
    _ ≤ ∑ d ∈ n.divisors, n * d.totient :=
      sum_le_sum fun _ hd => totient_ratio (Nat.dvd_of_mem_divisors hd)
    _ = n * n := by rw [← mul_sum, Nat.sum_totient]
  by_contra! hh
  have ht := Nat.mul_lt_mul_of_pos_right hh (Nat.totient_pos.mpr hn)
  nlinarith only [prod_bound, ht, Nat.mul_le_mul_left n h]

private lemma rearrange (n : ℕ) :
    (∑ d ∈ n.divisors, d * d.divisors.card) =
      ∑ d ∈ n.divisors, (n / d) * (σ 1 d) := by
  let I := ArithmeticFunction.id
  have hII (m : ℕ) : (I * I) m = m * m.divisors.card := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => I x * I y)]
    calc
      _ = ∑ _d ∈ m.divisors, m := by
        apply sum_congr rfl
        intro d hd
        change d * (m / d) = m
        simpa [Nat.mul_comm] using Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
      _ = _ := by simp [Nat.mul_comm]
  have hIz : ArithmeticFunction.zeta * I = σ 1 := by
    ext m
    simp [zeta_mul_apply, sigma_one_apply, I]
  have hassoc : (I * I) * ArithmeticFunction.zeta = (ArithmeticFunction.zeta * I) * I := by
    ac_rfl
  calc
    _ = ((I * I) * ArithmeticFunction.zeta) n := by rw [mul_zeta_apply]; simp_rw [hII]
    _ = ((σ 1) * I) n := by rw [hassoc, hIz]
    _ = _ := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => σ 1 x * I y)]
      simp [I, Nat.mul_comm]

private lemma scale_sigma {n d : ℕ} (hd : d ∈ n.divisors) :
    (n / d) * σ 1 d ≤ σ 1 n := by
  obtain ⟨hdiv, hn⟩ := Nat.mem_divisors.mp hd
  have hnd := Nat.div_mul_cancel hdiv
  have hpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv)
    (Nat.pos_of_mem_divisors hd)
  let e : ℕ ↪ ℕ := ⟨fun a => (n / d) * a, fun _ _ h => Nat.eq_of_mul_eq_mul_left hpos h⟩
  have hsub : d.divisors.map e ⊆ n.divisors := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn⟩
    change (n / d) * x ∣ n
    simpa only [hnd] using Nat.mul_dvd_mul_left (n / d) (Nat.dvd_of_mem_divisors hx)
  rw [sigma_one_apply, sigma_one_apply, mul_sum]
  calc
    _ = ∑ v ∈ d.divisors.map e, v := by simp [e]
    _ ≤ ∑ v ∈ n.divisors, v := sum_le_sum_of_subset hsub

private lemma small_prime_term {n p : ℕ} (hp : p.Prime) (hd : p ∣ n) (h3 : 3 ≤ p) :
    3 * ((n / p) * σ 1 p) ≤ 4 * n := by
  have hs : σ 1 p = p + 1 := by
    rw [sigma_one_apply, hp.divisors]
    simp [Ne.symm hp.ne_one, Nat.add_comm]
  rw [hs]
  have he := Nat.div_mul_cancel hd
  nlinarith only [he, Nat.mul_le_mul_left (n / p) h3]

private lemma moment_bound {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hnp : ¬ IsPrimePow n) (hs : σ 1 n ≤ 2 * n) :
    3 * (∑ d ∈ n.divisors, d * d.divisors.card) + 7 * n ≤ 6 * (n * n.divisors.card) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hnp
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hqP := Nat.prime_of_mem_primeFactors hq
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have three (r : ℕ) (hr : r.Prime) (hd : r ∣ n) : 3 ≤ r := by
    have h2 := hr.two_le
    have hne : r ≠ 2 := fun h => ho.not_two_dvd_nat (h ▸ hd)
    omega
  have h1m : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩
  have hpm : p ∈ n.divisors := Nat.mem_divisors.mpr ⟨hpd, by omega⟩
  have hqm : q ∈ n.divisors := Nat.mem_divisors.mpr ⟨hqd, by omega⟩
  let term (d : ℕ) := (n / d) * σ 1 d
  have hpoint (d : ℕ) (hd : d ∈ n.divisors) :
      3 * term d + (if d = 1 then 3 * n else 0) +
        (if d = p then 2 * n else 0) + (if d = q then 2 * n else 0) ≤ 6 * n := by
    by_cases h1 : d = 1
    · subst d
      simp [term, Ne.symm hpP.ne_one, Ne.symm hqP.ne_one] <;> omega
    by_cases hep : d = p
    · subst d
      have h := small_prime_term hpP hpd (three p hpP hpd)
      simp [term, hpP.ne_one, hpq] <;> omega
    by_cases heq : d = q
    · subst d
      have h := small_prime_term hqP hqd (three q hqP hqd)
      simp [term, hqP.ne_one, Ne.symm hpq] <;> omega
    · have h := (scale_sigma hd).trans hs
      simp [term, h1, hep, heq] <;> omega
  have hsum := sum_le_sum hpoint
  rw [rearrange]
  simp [sum_add_distrib, ← mul_sum, h1m, hpm, hqm, term, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] at hsum ⊢
  omega

theorem gap {n : ℕ} (hn : 1 < n) (ho : Odd n) (hnp : ¬ IsPrimePow n)
    (hs : σ 1 n ≤ 2 * n) : (n : ℤ) ≤ 3 * (OeisA245212.a n - (σ 1 n : ℤ)) := by
  have hm := moment_bound hn ho hnp hs
  have he : (∑ d ∈ n.divisors, d * d.divisors.card) =
      n * n.divisors.card + ∑ d ∈ n.properDivisors, d * d.divisors.card := by
    calc
      _ = ∑ d ∈ insert n n.properDivisors, d * d.divisors.card := by
        rw [Nat.insert_self_properDivisors (by omega : n ≠ 0)]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [he] at hm
  have hz : (3 : ℤ) * ((n : ℤ) * n.divisors.card +
      ∑ d ∈ n.properDivisors, (d : ℤ) * d.divisors.card) + 7 * n ≤
      6 * ((n : ℤ) * n.divisors.card) := by exact_mod_cast hm
  have hs' : (σ 1 n : ℤ) ≤ 2 * n := by exact_mod_cast hs
  unfold OeisA245212.a
  linarith

end OMA.A245212DivisorBound

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1.H1 := by
  intro n hn ho hnp hr _hshape heq
  have h := OMA.A245212DivisorBound.gap hn ho hnp
    (OMA.A245212DivisorBound.sigma_at_most_twice (by omega) hr)
  rw [heq, sub_self, mul_zero] at h
  omega
