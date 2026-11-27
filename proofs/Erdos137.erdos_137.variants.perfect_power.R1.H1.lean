import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

/-!
The product of two consecutive positive integers is never a perfect power.
-/

open Finset

/- Two consecutive positive integers are coprime, so if their product is an `l`-th power then each
factor is. Equal pure powers differ by at least `2` once the exponent is at least `2`. -/

lemma pow_add_two_le_succ_pow (a l : ℕ) (ha : 1 ≤ a) (hl : 2 ≤ l) :
    a ^ l + 2 ≤ (a + 1) ^ l := by
  induction l, hl using Nat.le_induction with
  | base =>
    have h2 : 2 ≤ 2 * a + 1 := by omega
    calc
      a ^ 2 + 2 ≤ a ^ 2 + (2 * a + 1) := Nat.add_le_add_left h2 _
      _ = (a + 1) ^ 2 := by ring
  | succ k hk ih =>
    have hmul : (a + 1) * (a ^ k + 2) ≤ (a + 1) * (a + 1) ^ k :=
      Nat.mul_le_mul_left _ ih
    have hexpand : (a + 1) * (a ^ k + 2) = a ^ (k + 1) + a ^ k + 2 * a + 2 := by ring
    calc
      a ^ (k + 1) + 2 ≤ a ^ (k + 1) + a ^ k + 2 * a + 2 := by omega
      _ = (a + 1) * (a ^ k + 2) := hexpand.symm
      _ ≤ (a + 1) * (a + 1) ^ k := hmul
      _ = (a + 1) ^ (k + 1) := by rw [pow_succ, mul_comm]

lemma eq_pow_of_coprime_mul_pow {a b c l : ℕ} (hl : 0 < l) (hcp : a.Coprime b)
    (h : a * b = c ^ l) : ∃ d, a = d ^ l := by
  by_cases ha0 : a = 0
  · exact ⟨0, by simp [ha0, Nat.zero_pow hl]⟩
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := (Nat.coprime_zero_right a).mp (hb0 ▸ hcp)
    exact ⟨1, by simp [ha1]⟩
  let factors := a.factorization.mapRange (· / l) (Nat.zero_div l)
  set d := factors.prod (· ^ ·) with hd
  refine ⟨d, ?_⟩
  apply Nat.eq_of_factorization_eq ha0 (by simp [d, factors])
  intro p
  have hprime : ∀ q ∈ factors.support, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hq)
  rw [Nat.factorization_pow, hd, Nat.prod_pow_factorization_eq_self hprime]
  suffices hdiv : l ∣ a.factorization p by
    simp [factors, Nat.mul_div_cancel' hdiv]
  have hsplit : a.factorization p + b.factorization p = l * c.factorization p := by
    have hmul := congrArg (fun n : ℕ => n.factorization p) h
    simpa [Nat.factorization_mul ha0 hb0, Nat.factorization_pow, Finsupp.add_apply,
      Finsupp.smul_apply] using hmul
  by_cases hpa : a.factorization p = 0
  · simp [hpa]
  · have hp : p.Prime := by
      contrapose! hpa
      exact Nat.factorization_eq_zero_of_not_prime a hpa
    have hpb : b.factorization p = 0 := by
      by_contra hbpos
      have hda : p ∣ a := Nat.dvd_of_factorization_pos hpa
      have hdb : p ∣ b := Nat.dvd_of_factorization_pos hbpos
      have hgcd : Nat.gcd a b = 1 := by simpa [Nat.Coprime] using hcp
      have hdg : p ∣ Nat.gcd a b := Nat.dvd_gcd hda hdb
      rw [hgcd] at hdg
      exact hp.not_dvd_one hdg
    rw [hpb, add_zero] at hsplit
    exact ⟨c.factorization p, hsplit⟩

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  intro n x l hl hprod
  have hset : Ioc n (n + 2) = ({n + 1, n + 2} : Finset ℕ) := by
    ext m
    simp only [mem_Ioc, mem_insert, mem_singleton]
    omega
  rw [hset, prod_pair (by omega : n + 1 ≠ n + 2)] at hprod
  have hcp : Nat.Coprime (n + 1) (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.coprime_self_add_right]
    exact (Nat.coprime_one_right_iff _).mpr trivial
  obtain ⟨d, hd⟩ := eq_pow_of_coprime_mul_pow (by omega) hcp hprod
  have hcp2 : Nat.Coprime (n + 2) (n + 1) := hcp.symm
  rw [mul_comm] at hprod
  obtain ⟨e, he⟩ := eq_pow_of_coprime_mul_pow (by omega) hcp2 hprod
  have hdiff : d ^ l + 1 = e ^ l := by
    rw [← hd, ← he]
  have hd1 : 1 ≤ d := by
    by_contra hlt
    have hd0 : d = 0 := by omega
    rw [hd0, Nat.zero_pow (by omega)] at hd
    omega
  have hlt : d < e := by
    by_contra hle
    have hle' : e ≤ d := Nat.le_of_not_lt hle
    have hpow : e ^ l ≤ d ^ l := pow_le_pow_left' hle' l
    have : e ^ l < e ^ l := by
      calc
        e ^ l ≤ d ^ l := hpow
        _ < d ^ l + 1 := Nat.lt_succ_self _
        _ = e ^ l := hdiff
    exact lt_irrefl _ this
  have hgap : d ^ l + 2 ≤ (d + 1) ^ l := pow_add_two_le_succ_pow d l hd1 hl
  have hmono : (d + 1) ^ l ≤ e ^ l := pow_le_pow_left' hlt l
  have : d ^ l + 2 ≤ d ^ l + 1 := by
    calc
      d ^ l + 2 ≤ (d + 1) ^ l := hgap
      _ ≤ e ^ l := hmono
      _ = d ^ l + 1 := hdiff.symm
  omega
