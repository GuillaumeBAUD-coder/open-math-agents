import OMAReductions.R_AgohGiuga_agoh_giuga_R1
import Mathlib.NumberTheory.Bernoulli
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Proof of AgohGiuga.agoh_giuga.R1.H1

Equivalence between Agoh's congruence for Bernoulli numbers and Giuga's power-sum
divisibility condition for all n >= 2.
-/

namespace OMA.AgohGiugaH1

open Finset Nat

def GiugaCond (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1) ∧ p ∣ (n / p - 1)

lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime) {s : Finset ℕ}
    (h : p ∣ ∏ q ∈ s, q) : ∃ q ∈ s, p ∣ q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at h
    exact absurd (Nat.le_of_dvd (by omega) h) (by have := hp.two_le; omega)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨q, hqs, hpq⟩ := ih h2
      exact ⟨q, Finset.mem_insert_of_mem hqs, hpq⟩

lemma prod_primes_dvd_nat {s : Finset ℕ} {b : ℕ}
    (hprime : ∀ p ∈ s, p.Prime) (hdvd : ∀ p ∈ s, p ∣ b) :
    (∏ p ∈ s, p) ∣ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_prime : a.Prime := hprime a (Finset.mem_insert_self a s)
    have ha_dvd : a ∣ b := hdvd a (Finset.mem_insert_self a s)
    have hs_dvd : (∏ p ∈ s, p) ∣ b :=
      ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
         (fun p hp => hdvd p (Finset.mem_insert_of_mem hp))
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      rw [ha_prime.coprime_iff_not_dvd]
      intro h
      obtain ⟨q, hqs, haq⟩ := prime_dvd_finset_prod ha_prime h
      have hq_prime : q.Prime := hprime q (Finset.mem_insert_of_mem hqs)
      have heq : a = q := (Nat.prime_dvd_prime_iff_eq ha_prime hq_prime).mp haq
      exact ha (heq ▸ hqs)
    exact hcop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

lemma prod_primes_dvd_int {s : Finset ℕ} {b : ℤ}
    (hprime : ∀ p ∈ s, p.Prime) (hdvd : ∀ p ∈ s, (p : ℤ) ∣ b) :
    ((∏ p ∈ s, p : ℕ) : ℤ) ∣ b := by
  have habs : ∀ p ∈ s, p ∣ b.natAbs := fun p hp => Int.natCast_dvd.mp (hdvd p hp)
  exact Int.natCast_dvd.mpr (prod_primes_dvd_nat hprime habs)

lemma not_dvd_power_sum_of_even {n : ℕ} (hn : 4 ≤ n) (heven : Even n) :
    ¬ n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := heven
  have hm : 2 ≤ m := by omega
  intro hdvd
  have hmdvd : m ∣ 1 + ∑ i ∈ Finset.Ioo 0 (m + m), i ^ (m + m - 1) :=
    dvd_trans ⟨2, by ring⟩ hdvd
  have hrev : (∑ i ∈ Finset.Ioo 0 (m + m), (i : ZMod (m + m)) ^ (m + m - 1)) =
      ∑ i ∈ Finset.Ioo 0 (m + m), ((m + m - i : ℕ) : ZMod (m + m)) ^ (m + m - 1) := by
    refine Finset.sum_bij (fun i _ => m + m - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Ioo] at hi ⊢
      omega
    · intro i₁ hi₁ i₂ hi₂ h
      simp only [Finset.mem_Ioo] at hi₁ hi₂
      omega
    · intro j hj
      simp only [Finset.mem_Ioo] at hj
      exact ⟨m + m - j, by simp only [Finset.mem_Ioo]; omega, by omega⟩
    · intro i _
      rfl
  have hodd : Odd (m + m - 1) := ⟨m - 1, by omega⟩
  have hneg : ∀ i ∈ Finset.Ioo 0 (m + m),
      ((m + m - i : ℕ) : ZMod (m + m)) ^ (m + m - 1) =
        -((i : ZMod (m + m)) ^ (m + m - 1)) := by
    intro i hi
    simp only [Finset.mem_Ioo] at hi
    have hsub : ((m + m - i : ℕ) : ZMod (m + m)) = -(i : ZMod (m + m)) := by
      have hle : i ≤ m + m := by omega
      rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
    rw [hsub, hodd.neg_pow]
  have hsum_neg : (∑ i ∈ Finset.Ioo 0 (m + m), (i : ZMod (m + m)) ^ (m + m - 1)) =
      -(∑ i ∈ Finset.Ioo 0 (m + m), (i : ZMod (m + m)) ^ (m + m - 1)) := by
    rw [hrev, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hneg
  have h2sum : ((2 * ∑ i ∈ Finset.Ioo 0 (m + m), i ^ (m + m - 1) : ℕ) : ZMod (m + m)) = 0 := by
    push_cast
    rw [two_mul]
    conv_rhs => rw [← add_neg_cancel (∑ i ∈ Finset.Ioo 0 (m + m), (i : ZMod (m + m)) ^ (m + m - 1))]
    rw [← hsum_neg]
  have h2dvd : (m + m) ∣ 2 * ∑ i ∈ Finset.Ioo 0 (m + m), i ^ (m + m - 1) :=
    (ZMod.natCast_eq_zero_iff _ _).mp h2sum
  have hsum_dvd : m ∣ ∑ i ∈ Finset.Ioo 0 (m + m), i ^ (m + m - 1) := by
    rw [← two_mul] at h2dvd
    exact (mul_dvd_mul_iff_left (by omega : (2 : ℕ) ≠ 0)).mp h2dvd
  have h1 : m ∣ 1 := (Nat.dvd_add_left hsum_dvd).mp hmdvd
  have : m ≤ 1 := Nat.le_of_dvd (by omega) h1
  omega

lemma not_bernoulli_cond_of_even {n : ℕ} (hn : 4 ≤ n) (heven : Even n) :
    ¬ ∃ k : ℤ, let B := bernoulli' (n - 1); (n : ℤ) * B.num + B.den = k * (n : ℤ) ^ 2 := by
  have hodd : Odd (n - 1) := by
    obtain ⟨m, rfl⟩ := heven
    exact ⟨m - 1, by omega⟩
  have hgt : 1 < n - 1 := by omega
  have hB : bernoulli' (n - 1) = 0 := bernoulli'_eq_zero_of_odd hodd hgt
  rintro ⟨k, hk⟩
  simp only [hB, Rat.num_zero, mul_zero, Rat.den_zero, zero_add] at hk
  have hdvd : (n : ℤ) ^ 2 ∣ 1 := ⟨k, by linarith⟩
  have hle : ((n : ℤ) ^ 2).natAbs ≤ 1 := Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num)
  have : n ^ 2 ≤ 1 := by
    have : ((n : ℤ) ^ 2).natAbs = n ^ 2 := by
      rw [← Int.natCast_pow, Int.natAbs_natCast]
    omega
  nlinarith

lemma sum_pow_mod_prime {p e : ℕ} [Fact p.Prime] (he : 0 < e) :
    ((∑ r ∈ Finset.range p, (r : ZMod p) ^ e) = if (p - 1) ∣ e then (-1 : ZMod p) else 0) := by
  have hp : p.Prime := Fact.out
  split_ifs with hdvd
  · have hsum : ∑ r ∈ Finset.range p, (r : ZMod p) ^ e =
        ∑ r ∈ Finset.Ioo 0 p, (r : ZMod p) ^ e := by
      have hrange : Finset.range p = insert 0 (Finset.Ioo 0 p) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
        have := hp.pos
        omega
      rw [hrange, Finset.sum_insert (by simp), Nat.cast_zero, zero_pow (by omega), zero_add]
    rw [hsum]
    have hones : ∀ r ∈ Finset.Ioo 0 p, (r : ZMod p) ^ e = 1 := by
      intro r hr
      simp only [Finset.mem_Ioo] at hr
      have hr0 : (r : ZMod p) ≠ 0 := by
        intro h
        rw [ZMod.natCast_eq_zero_iff] at h
        have := Nat.le_of_dvd hr.1 h
        omega
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one hr0, one_pow]
    rw [Finset.sum_congr rfl hones, Finset.sum_const, Nat.card_Ioo]
    simp only [nsmul_eq_mul, mul_one, Nat.sub_zero]
    have hp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
      have hcast : ((p - 1 : ℕ) : ZMod p) + 1 = (p : ZMod p) := by
        norm_cast
        have := hp.pos
        omega
      rw [ZMod.natCast_self] at hcast
      exact eq_neg_of_add_eq_zero_left hcast
    exact hp1
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hge : (g : ZMod p) ^ e ≠ 1 := by
      intro h1
      have hord : orderOf g = p - 1 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg, ZMod.card_units_eq_totient,
          Nat.totient_prime hp]
      have hg1 : g ^ e = 1 := Units.ext (by simpa using h1)
      exact hdvd (hord ▸ orderOf_dvd_of_pow_eq_one hg1)
    have hmul : (g : ZMod p) ^ e * ∑ r ∈ Finset.range p, (r : ZMod p) ^ e =
        ∑ r ∈ Finset.range p, (r : ZMod p) ^ e := by
      rw [Finset.mul_sum]
      have hcast : ∀ r ∈ Finset.range p, (g : ZMod p) ^ e * (r : ZMod p) ^ e =
          ((g : ZMod p) * (r : ZMod p)) ^ e := fun r _ => (mul_pow _ _ _).symm
      rw [Finset.sum_congr rfl hcast]
      have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ e = ∑ x : ZMod p, x ^ e :=
        Fintype.sum_equiv (Equiv.mulLeft₀ (g : ZMod p) (Units.ne_zero g)) _ _ (fun _ => rfl)
      have hrange : ∀ f : ZMod p → ZMod p,
          ∑ r ∈ Finset.range p, f (r : ZMod p) = ∑ x : ZMod p, f x := by
        intro f
        rw [← Finset.sum_image (f := f) (g := (Nat.cast : ℕ → ZMod p))]
        · congr 1
          ext x
          simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
          exact ⟨x.val, x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a ha b hb hab
          simp only [Finset.mem_range] at ha hb
          have := congrArg ZMod.val hab
          simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using this
      rw [hrange (fun x => ((g : ZMod p) * x) ^ e), hrange (fun x => x ^ e), hbij]
    have hsub : ((g : ZMod p) ^ e - 1) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ e = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hge)

lemma power_sum_zmod {n p : ℕ} [Fact p.Prime] (hn : 2 ≤ n) (hpn : p ∣ n) :
    ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) =
      1 + (n / p : ℕ) * (if (p - 1) ∣ (n - 1) then (-1 : ZMod p) else 0) := by
  have hp : p.Prime := Fact.out
  have hrange : ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) = ∑ i ∈ Finset.range n, i ^ (n - 1) := by
    have hr : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
      omega
    rw [hr, Finset.sum_insert (by simp), zero_pow (by omega), zero_add]
  rw [Nat.cast_add, Nat.cast_one, hrange, Nat.cast_sum]
  have hblocks : ∑ i ∈ Finset.range n, ((i ^ (n - 1) : ℕ) : ZMod p) =
      (n / p : ℕ) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (n - 1) := by
    obtain ⟨q, hq⟩ := hpn
    have hdiv : n / p = q := by
      rw [hq, Nat.mul_div_cancel_left q hp.pos]
    rw [hdiv, hq]
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_add_one, Finset.sum_range_add, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      push_cast
      have : ((p * q : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact dvd_mul_right p q
      simp [this]
  rw [hblocks, sum_pow_mod_prime (by omega)]

lemma power_sum_iff_giuga {n : ℕ} (hn : 2 ≤ n) :
    n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) ↔ GiugaCond n := by
  constructor
  · intro hdvd
    have hprime : ∀ p : ℕ, p.Prime → p ∣ n →
        ¬ p * p ∣ n ∧ (p - 1) ∣ (n - 1) ∧ p ∣ (n / p - 1) := by
      intro p hp hpn
      haveI : Fact p.Prime := ⟨hp⟩
      have h0 : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact dvd_trans hpn hdvd
      rw [power_sum_zmod hn hpn] at h0
      by_cases hpm : (p - 1) ∣ (n - 1)
      · rw [if_pos hpm] at h0
        have hq : ((n / p : ℕ) : ZMod p) = 1 := by
          linear_combination -h0
        have hnot2 : ¬ p * p ∣ n := by
          intro h2
          have hpd : p ∣ n / p := by
            obtain ⟨c, hc⟩ := h2
            refine ⟨c, ?_⟩
            rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
          have hq0 : ((n / p : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
          rw [hq0] at hq
          exact zero_ne_one hq
        have hqpos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
        have hsub : ((n / p - 1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_sub hqpos, hq, Nat.cast_one, sub_self]
        exact ⟨hnot2, hpm, (ZMod.natCast_eq_zero_iff _ _).mp hsub⟩
      · rw [if_neg hpm, mul_zero, add_zero] at h0
        exact absurd h0 one_ne_zero
    refine ⟨?_, fun p hp hpn => (hprime p hp hpn).2⟩
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp h2
    exact (hprime p hp (dvd_trans (dvd_mul_left p p) h2)).1 h2
  · rintro ⟨hsq, hcond⟩
    have hall : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) := by
      intro p hp hpn
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨hpm, hq⟩ := hcond p hp hpn
      rw [← ZMod.natCast_eq_zero_iff, power_sum_zmod hn hpn, if_pos hpm]
      have hqpos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
      have hq1 : ((n / p : ℕ) : ZMod p) = 1 := by
        have h0 : ((n / p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hq
        rw [Nat.cast_sub hqpos, Nat.cast_one] at h0
        exact sub_eq_zero.mp h0
      rw [hq1]
      ring
    have hprod : ∏ p ∈ n.primeFactors, p = n :=
      Nat.prod_primeFactors_of_squarefree hsq
    rw [← hprod]
    exact prod_primes_dvd_nat
      (fun p hp => (Nat.mem_primeFactors.mp hp).1)
      (fun p hp => hall p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1)

lemma bernoulli_cond_iff_giuga_of_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    (∃ k : ℤ, let B := bernoulli' (n - 1); (n : ℤ) * B.num + B.den = k * (n : ℤ) ^ 2) ↔
      GiugaCond n := by
  obtain ⟨m, rfl⟩ := hodd
  have hm : 0 < m := by omega
  have hsub : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hsub, ← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
  set B := bernoulli (2 * m)
  set S : Finset ℕ := (Finset.range (2 * m + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * m)
  set D : ℕ := ∏ p ∈ S, p
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hS_dvd : ∀ p ∈ S, (p - 1) ∣ 2 * m := fun p hp => (Finset.mem_filter.mp hp).2.2
  have hD_sqf : Squarefree D := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp h2
    have hmem : p ∈ S := by
      have hpD : p ∣ D := dvd_trans (dvd_mul_left p p) h2
      obtain ⟨q, hqS, hpq⟩ := prime_dvd_finset_prod hp hpD
      have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS_prime q hqS)).mp hpq
      rwa [hqp]
    have hsplit : D = p * ∏ q ∈ S.erase p, q := (Finset.mul_prod_erase S id hmem).symm
    rw [hsplit] at h2
    have hpd : p ∣ ∏ q ∈ S.erase p, q := (mul_dvd_mul_iff_left hp.ne_zero).mp h2
    obtain ⟨q, hq, hpq⟩ := prime_dvd_finset_prod hp hpd
    have hne : q ≠ p := (Finset.mem_erase.mp hq).1
    have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS_prime q (Finset.mem_erase.mp hq).2)).mp hpq
    exact hne hqp.symm
  obtain ⟨M, hM⟩ := Bernoulli.vonStaudt_clausen (k := m)
  have hB_eq : B = (M : ℚ) - ∑ p ∈ S, (1 : ℚ) / p := by
    have : (M : ℚ) = B + ∑ p ∈ S, (1 : ℚ) / p := hM
    linarith
  have hB_den : B.den = D := by
    have hmul_int : (D : ℚ) * B = ((D : ℤ) * M - ∑ p ∈ S, ((D / p : ℕ) : ℤ) : ℤ) := by
      rw [hB_eq, mul_sub, Finset.mul_sum]
      push_cast
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      have hpD : p ∣ D := Finset.dvd_prod_of_mem id hp
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hS_prime p hp).ne_zero
      rw [mul_one_div, eq_div_iff hp0]
      exact_mod_cast (Nat.div_mul_cancel hpD).symm
    have hden_dvd : B.den ∣ D := by
      have h1 : ((B.den : ℤ) : ℚ) * ((D : ℚ) * B) = (D : ℚ) * (B.num : ℚ) := by
        rw [← mul_assoc, mul_comm ((B.den : ℤ) : ℚ) (D : ℚ), mul_assoc]
        simp only [Int.cast_natCast, Rat.den_mul_eq_num]
      rw [hmul_int] at h1
      have h2 : (B.den : ℤ) * ((D : ℤ) * M - ∑ p ∈ S, ((D / p : ℕ) : ℤ)) = (D : ℤ) * B.num := by
        exact_mod_cast h1
      have h3 : B.den ∣ D * B.num.natAbs := by
        have h4 : (B.den : ℤ) ∣ (D : ℤ) * B.num := ⟨_, h2.symm⟩
        exact_mod_cast Int.natAbs_dvd_natAbs.mpr h4
      exact B.reduced.symm.dvd_of_dvd_mul_right h3
    have hD_dvd : D ∣ B.den := by
      refine prod_primes_dvd_nat hS_prime ?_
      intro p hp
      haveI : Fact p.Prime := ⟨hS_prime p hp⟩
      exact Bernoulli.dvd_den_bernoulli hm (hS_dvd p hp)
    exact Nat.dvd_antisymm hden_dvd hD_dvd
  have hB_num : B.num = (D : ℤ) * M - ∑ p ∈ S, ((D / p : ℕ) : ℤ) := by
    have h1 : (D : ℚ) * B = ((D : ℤ) * M - ∑ p ∈ S, ((D / p : ℕ) : ℤ) : ℤ) := by
      rw [hB_eq, mul_sub, Finset.mul_sum]
      push_cast
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      have hpD : p ∣ D := Finset.dvd_prod_of_mem id hp
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hS_prime p hp).ne_zero
      rw [mul_one_div, eq_div_iff hp0]
      exact_mod_cast (Nat.div_mul_cancel hpD).symm
    have h2 : (D : ℚ) * B = (B.num : ℚ) := by
      rw [← hB_den, Rat.den_mul_eq_num]
    rw [h2] at h1
    exact_mod_cast h1
  set N := 2 * m + 1
  constructor
  · rintro ⟨k, hk⟩
    have hND : N ∣ D := by
      have h1 : (N : ℤ) ∣ (D : ℤ) := by
        refine ⟨k * (N : ℤ) - B.num, ?_⟩
        rw [hB_den] at hk
        linarith
      exact_mod_cast h1
    have hN_sqf : Squarefree N := hD_sqf.squarefree_of_dvd hND
    refine ⟨hN_sqf, ?_⟩
    intro p hp hpN
    have hpD : p ∣ D := dvd_trans hpN hND
    have hpS : p ∈ S := by
      obtain ⟨q, hqS, hpq⟩ := prime_dvd_finset_prod hp hpD
      have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS_prime q hqS)).mp hpq
      rwa [hqp]
    refine ⟨hS_dvd p hpS, ?_⟩
    obtain ⟨E, hDE⟩ := hND
    have hpE_nd : ¬ p ∣ E := by
      intro hpE
      have h2 : p * p ∣ D := by
        obtain ⟨c, hc⟩ := hpN
        obtain ⟨d, hd⟩ := hpE
        exact ⟨c * d, by rw [hDE, hc, hd]; ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hD_sqf) p hp h2
    have hN_dvd_expr : (N : ℤ) ∣ B.num + (E : ℤ) := by
      refine ⟨k, ?_⟩
      have hcast : (D : ℤ) = (N : ℤ) * (E : ℤ) := by exact_mod_cast hDE
      rw [hB_den, hcast] at hk
      have hN0 : (N : ℤ) ≠ 0 := by positivity
      apply mul_left_cancel₀ hN0
      linarith
    have hp_dvd_expr : (p : ℤ) ∣ B.num + (E : ℤ) :=
      dvd_trans (Int.ofNat_dvd.mpr hpN) hN_dvd_expr
    rw [hB_num] at hp_dvd_expr
    have hp_dvd_DM : (p : ℤ) ∣ (D : ℤ) * M := dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hpD) M
    have hp_dvd_rest : (p : ℤ) ∣ ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ) := by
      apply Finset.dvd_sum
      intro q hq
      have hne : q ≠ p := (Finset.mem_erase.mp hq).1
      have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
      have hqD : q ∣ D := Finset.dvd_prod_of_mem id hqS
      have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr fun h =>
        hne ((Nat.prime_dvd_prime_iff_eq hp (hS_prime q hqS)).mp h).symm
      have hpDq : p ∣ D / q := by
        have h1 : p ∣ q * (D / q) := by rwa [Nat.mul_div_cancel' hqD]
        exact hcop.dvd_of_dvd_mul_left h1
      exact Int.ofNat_dvd.mpr hpDq
    have hsplit_sum : ∑ q ∈ S, ((D / q : ℕ) : ℤ) =
        ((D / p : ℕ) : ℤ) + ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ) :=
      (Finset.add_sum_erase S _ hpS).symm
    rw [hsplit_sum] at hp_dvd_expr
    have hp_dvd_diff : (p : ℤ) ∣ ((D / p : ℕ) : ℤ) - (E : ℤ) := by
      have h1 : ((D / p : ℕ) : ℤ) - (E : ℤ) =
          (D : ℤ) * M - ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ) -
          ((D : ℤ) * M - (((D / p : ℕ) : ℤ) + ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ)) + (E : ℤ)) := by
        ring
      rw [h1]
      exact dvd_sub (dvd_sub hp_dvd_DM hp_dvd_rest) hp_dvd_expr
    have hDp : D / p = (N / p) * E := by
      apply Nat.div_eq_of_eq_mul_left hp.pos
      rw [hDE, mul_assoc, mul_comm E p, ← mul_assoc, Nat.div_mul_cancel hpN]
    have hNdiv_pos : 1 ≤ N / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpN) hp.pos
    have hfact : ((D / p : ℕ) : ℤ) - (E : ℤ) = ((N / p - 1 : ℕ) : ℤ) * (E : ℤ) := by
      rw [hDp, Nat.cast_mul, Nat.cast_sub hNdiv_pos, Nat.cast_one]
      ring
    rw [hfact] at hp_dvd_diff
    have hp_prime_Z : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hp_prime_Z.dvd_or_dvd hp_dvd_diff with h1 | h2
    · exact Int.ofNat_dvd.mp h1
    · exact absurd (Int.ofNat_dvd.mp h2) hpE_nd
  · rintro ⟨hN_sqf, hcond⟩
    have hND : N ∣ D := by
      have hprod : ∏ p ∈ N.primeFactors, p = N :=
        Nat.prod_primeFactors_of_squarefree hN_sqf
      rw [← hprod]
      refine prod_primes_dvd_nat (fun p hp => (Nat.mem_primeFactors.mp hp).1) ?_
      intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have hpN := (Nat.mem_primeFactors.mp hp).2.1
      have hpm := (hcond p hp_prime hpN).1
      have hpS : p ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        have hle : p ≤ N := Nat.le_of_dvd (by omega) hpN
        exact ⟨by omega, hp_prime, hpm⟩
      exact Finset.dvd_prod_of_mem id hpS
    obtain ⟨E, hDE⟩ := hND
    have hall : ∀ p : ℕ, p.Prime → p ∣ N → (p : ℤ) ∣ B.num + (E : ℤ) := by
      intro p hp hpN
      have hpD : p ∣ D := dvd_trans hpN hND
      have hpS : p ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        have hle : p ≤ N := Nat.le_of_dvd (by omega) hpN
        exact ⟨by omega, hp, (hcond p hp hpN).1⟩
      rw [hB_num]
      have hp_dvd_DM : (p : ℤ) ∣ (D : ℤ) * M := dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hpD) M
      have hp_dvd_rest : (p : ℤ) ∣ ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ) := by
        apply Finset.dvd_sum
        intro q hq
        have hne : q ≠ p := (Finset.mem_erase.mp hq).1
        have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
        have hqD : q ∣ D := Finset.dvd_prod_of_mem id hqS
        have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr fun h =>
          hne ((Nat.prime_dvd_prime_iff_eq hp (hS_prime q hqS)).mp h).symm
        have hpDq : p ∣ D / q := by
          have h1 : p ∣ q * (D / q) := by rwa [Nat.mul_div_cancel' hqD]
          exact hcop.dvd_of_dvd_mul_left h1
        exact Int.ofNat_dvd.mpr hpDq
      have hsplit_sum : ∑ q ∈ S, ((D / q : ℕ) : ℤ) =
          ((D / p : ℕ) : ℤ) + ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ) :=
        (Finset.add_sum_erase S _ hpS).symm
      rw [hsplit_sum]
      have hDp : D / p = (N / p) * E := by
        apply Nat.div_eq_of_eq_mul_left hp.pos
        rw [hDE, mul_assoc, mul_comm E p, ← mul_assoc, Nat.div_mul_cancel hpN]
      have hNdiv_pos : 1 ≤ N / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpN) hp.pos
      have hfact : ((D / p : ℕ) : ℤ) - (E : ℤ) = ((N / p - 1 : ℕ) : ℤ) * (E : ℤ) := by
        rw [hDp, Nat.cast_mul, Nat.cast_sub hNdiv_pos, Nat.cast_one]
        ring
      have hp_dvd_diff : (p : ℤ) ∣ ((D / p : ℕ) : ℤ) - (E : ℤ) := by
        rw [hfact]
        exact dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr (hcond p hp hpN).2) (E : ℤ)
      have hrew : (D : ℤ) * M - (((D / p : ℕ) : ℤ) + ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ)) + (E : ℤ) =
          (D : ℤ) * M - ∑ q ∈ S.erase p, ((D / q : ℕ) : ℤ) - (((D / p : ℕ) : ℤ) - (E : ℤ)) := by
        ring
      rw [hrew]
      exact dvd_sub (dvd_sub hp_dvd_DM hp_dvd_rest) hp_dvd_diff
    have hN_dvd : (N : ℤ) ∣ B.num + (E : ℤ) := by
      have hprod : ∏ p ∈ N.primeFactors, p = N :=
        Nat.prod_primeFactors_of_squarefree hN_sqf
      rw [← hprod]
      exact prod_primes_dvd_int
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
        (fun p hp => hall p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1)
    obtain ⟨k, hk⟩ := hN_dvd
    refine ⟨k, ?_⟩
    have hcast : (D : ℤ) = (N : ℤ) * (E : ℤ) := by exact_mod_cast hDE
    rw [hB_den, hcast]
    nlinarith

end OMA.AgohGiugaH1

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_R1.H1 := by
  intro n hn
  by_cases h2 : n = 2
  · subst h2
    constructor
    · intro _
      decide
    · intro _
      refine ⟨1, ?_⟩
      simp only [Nat.reduceSub, bernoulli'_one]
      decide
  · rcases Nat.even_or_odd n with heven | hodd
    · have h4 : 4 ≤ n := by
        obtain ⟨m, rfl⟩ := heven
        omega
      exact iff_of_false
        (OMA.AgohGiugaH1.not_bernoulli_cond_of_even h4 heven)
        (OMA.AgohGiugaH1.not_dvd_power_sum_of_even h4 heven)
    · have h3 : 3 ≤ n := by omega
      exact (OMA.AgohGiugaH1.bernoulli_cond_iff_giuga_of_odd h3 hodd).trans
        (OMA.AgohGiugaH1.power_sum_iff_giuga hn).symm
