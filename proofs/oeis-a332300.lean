import OMAStatements.S_oeis_a332300
import Mathlib

/-!
# OEIS A332300: every prime p > 3 divides the numerator of the Bernoulli number B_{2p}

Faulhaber's formula for the sum of the (2p)-th powers below p, read p-adically.
The power sum is divisible by p^2 (doubling permutes the residues mod p, and
k^(2p) mod p^2 depends only on k mod p), while the von Staudt-Clausen theorem makes
every p * B_i p-integral, so all lower Faulhaber terms are p^2 times a p-integral
rational. Hence B_{2p} is p times a p-integral rational.
-/

namespace OMA.A332300
open Finset

/-- The subring of rationals whose denominator is prime to p. -/
abbrev R (p : ℕ) [Fact p.Prime] : Subring ℚ := (Rat.padicValuation p).integer

lemma mem_R_iff {p : ℕ} [Fact p.Prime] {x : ℚ} : x ∈ R p ↔ ¬ p ∣ x.den := by
  rw [← Rat.padicValuation_le_one_iff]
  exact Valuation.mem_integer_iff _ _

lemma p_div_prime_mem {p q : ℕ} [Fact p.Prime] (hq : q.Prime) :
    (p : ℚ) * (1 / q) ∈ R p := by
  by_cases h : q = p
  · subst h
    have h0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h1 : (q : ℚ) * (1 / q) = 1 := by field_simp
    rw [h1]
    exact one_mem _
  · refine mul_mem (natCast_mem _ p) ?_
    rw [mem_R_iff]
    have h1 : ((1 : ℚ) / q).den = q := by simp [hq.ne_zero]
    rw [h1]
    intro hd
    exact h ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hd).symm

lemma p_mul_bernoulli_mem {p : ℕ} [Fact p.Prime] (i : ℕ) :
    (p : ℚ) * bernoulli i ∈ R p := by
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
  · obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have h1 : (p : ℚ) * bernoulli (2 * k) = p * z -
        ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (p : ℚ) * (1 / q) := by
      rw [← Finset.mul_sum, hz]
      ring
    rw [h1]
    refine sub_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) (sum_mem fun q hq => ?_)
    exact p_div_prime_mem (Finset.mem_filter.mp hq).2.1
  · by_cases hk : k = 0
    · subst hk
      have h1 : (p : ℚ) * bernoulli (2 * 0 + 1) = -((p : ℚ) * (1 / (2 : ℕ))) := by
        simp [bernoulli_one]
        ring
      rw [h1]
      exact neg_mem (p_div_prime_mem Nat.prime_two)
    · rw [bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)]
      simp

lemma pow_eq_of_modEq {p a b : ℕ} (h : a ≡ b [MOD p]) :
    ((a : ZMod (p ^ 2)) ^ (2 * p)) = (b : ZMod (p ^ 2)) ^ (2 * p) := by
  have h1 : (p : ℤ) ∣ (b : ℤ) - a := Nat.modEq_iff_dvd.mp h
  have h2 := dvd_sub_pow_of_dvd_sub h1 1
  have h3 : (((a : ℤ) ^ p : ℤ) : ZMod (p ^ 2)) = ((b : ℤ) ^ p : ℤ) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa using h2
  push_cast at h3
  rw [mul_comm, pow_mul, pow_mul, h3]

lemma sq_dvd_sum {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    (p : ℤ) ^ 2 ∣ ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hg : ∀ k : ℕ, (((k : ZMod p).val : ℕ) : ZMod (p ^ 2)) ^ (2 * p)
      = (k : ZMod (p ^ 2)) ^ (2 * p) := by
    intro k
    apply pow_eq_of_modEq
    rw [ZMod.val_natCast]
    exact Nat.mod_modEq k p
  have hS : ∑ k ∈ range p, (k : ZMod (p ^ 2)) ^ (2 * p)
      = ∑ x : ZMod p, ((x.val : ℕ) : ZMod (p ^ 2)) ^ (2 * p) := by
    refine Finset.sum_bij' (fun k _ => (k : ZMod p)) (fun x _ => x.val)
      (fun _ _ => mem_univ _) (fun x _ => mem_range.mpr (ZMod.val_lt x))
      (fun k hk => ZMod.val_cast_of_lt (mem_range.mp hk))
      (fun x _ => ZMod.natCast_zmod_val x) (fun k hk => (hg k).symm)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hperm : ∑ x : ZMod p, (((2 * x).val : ℕ) : ZMod (p ^ 2)) ^ (2 * p)
      = ∑ x : ZMod p, ((x.val : ℕ) : ZMod (p ^ 2)) ^ (2 * p) :=
    Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) h2) _ _ (fun _ => rfl)
  have hmul : ∀ x : ZMod p, (((2 * x).val : ℕ) : ZMod (p ^ 2)) ^ (2 * p)
      = (2 : ZMod (p ^ 2)) ^ (2 * p) * ((x.val : ℕ) : ZMod (p ^ 2)) ^ (2 * p) := by
    intro x
    have e : (2 * x : ZMod p) = ((2 * x.val : ℕ) : ZMod p) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [e, hg]
    push_cast
    rw [mul_pow]
  have hzero : (((2 : ℤ) ^ (2 * p) - 1) * ∑ k ∈ range p, (k : ℤ) ^ (2 * p) : ℤ)
      ≡ 0 [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [hS, sub_mul, one_mul, Finset.mul_sum, sub_eq_zero, ← hperm]
    exact (Finset.sum_congr rfl fun x _ => (hmul x)).symm
  have hdvd : (p : ℤ) ^ 2 ∣ ((2 : ℤ) ^ (2 * p) - 1) * ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
    have := Int.modEq_zero_iff_dvd.mp hzero
    exact_mod_cast this
  have hnd : ¬ (p : ℤ) ∣ (2 : ℤ) ^ (2 * p) - 1 := by
    intro h
    have h' : (((2 : ℤ) ^ (2 * p) - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at h'
    rw [mul_comm, pow_mul, ZMod.pow_card] at h'
    have h'' : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h'
    rw [ZMod.natCast_eq_zero_iff] at h''
    have := Nat.le_of_dvd (by norm_num) h''
    omega
  have hcop : IsCoprime ((p : ℤ) ^ 2) ((2 : ℤ) ^ (2 * p) - 1) :=
    IsCoprime.pow_left
      ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hnd)
  exact hcop.dvd_of_dvd_mul_left hdvd

lemma faulhaber_split (n m : ℕ) :
    (∑ k ∈ range n, (k : ℚ) ^ m) =
      (∑ i ∈ range m, bernoulli i * ((m + 1).choose i) * (n : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1))
        + n * bernoulli m := by
  rw [sum_range_pow, Finset.sum_range_succ, Nat.choose_succ_self_right,
    show m + 1 - m = 1 by omega]
  push_cast
  field_simp

lemma inv_mem {p : ℕ} [Fact p.Prime] : (1 : ℚ) / ((2 * p + 1 : ℕ) : ℚ) ∈ R p := by
  rw [mem_R_iff]
  have h1 : ((1 : ℚ) / ((2 * p + 1 : ℕ) : ℚ)).den = 2 * p + 1 := by
    rw [one_div, Rat.inv_natCast_den, if_neg (Nat.succ_ne_zero _)]
  rw [h1]
  intro hd
  have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p 2)).mp hd
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)

lemma term_mem {p : ℕ} [Fact p.Prime] (i : ℕ) (hi : i < 2 * p) :
    bernoulli i * ((2 * p + 1).choose i) * (p : ℚ) ^ (2 * p + 1 - i) / (((2 * p : ℕ) : ℚ) + 1)
      / (p : ℚ) ^ 2 ∈ R p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases h : i = 2 * p - 1
  · have hp1 := (Fact.out : p.Prime).one_lt
    rw [bernoulli_eq_zero_of_odd ⟨p - 1, by omega⟩ (by omega)]
    simp
  · have e : bernoulli i * ((2 * p + 1).choose i) * (p : ℚ) ^ (2 * p + 1 - i)
        / (((2 * p : ℕ) : ℚ) + 1) / (p : ℚ) ^ 2
        = (p : ℚ) * bernoulli i * ((2 * p + 1).choose i) * (p : ℚ) ^ (2 * p - 2 - i)
          * (1 / ((2 * p + 1 : ℕ) : ℚ)) := by
      rw [show 2 * p + 1 - i = (2 * p - 2 - i) + 3 by omega, pow_add]
      push_cast
      field_simp
    rw [e]
    exact mul_mem (mul_mem (mul_mem (p_mul_bernoulli_mem i) (natCast_mem _ _))
      (pow_mem (natCast_mem _ _) _)) inv_mem

theorem main' (p : ℕ) (hp : p.Prime) (h3 : 3 < p) : (p : ℤ) ∣ (bernoulli (2 * p)).num := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨c, hc⟩ := sq_dvd_sum hp h3
  have hcQ : (∑ k ∈ range p, (k : ℚ) ^ (2 * p)) = (p : ℚ) ^ 2 * c := by exact_mod_cast hc
  have hF := faulhaber_split p (2 * p)
  set T : ℚ := ∑ i ∈ range (2 * p), bernoulli i * ((2 * p + 1).choose i) *
    (p : ℚ) ^ (2 * p + 1 - i) / (((2 * p : ℕ) : ℚ) + 1) / (p : ℚ) ^ 2 with hT
  have hTmem : T ∈ R p := sum_mem fun i hi => term_mem i (mem_range.mp hi)
  have hsum : (∑ i ∈ range (2 * p), bernoulli i * ((2 * p + 1).choose i) *
      (p : ℚ) ^ (2 * p + 1 - i) / (((2 * p : ℕ) : ℚ) + 1)) = (p : ℚ) ^ 2 * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hsum, hcQ] at hF
  have key : bernoulli (2 * p) = p * (c - T) := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : ℚ) * hF
  have hYmem : (c - T : ℚ) ∈ R p := sub_mem (intCast_mem _ _) hTmem
  rw [mem_R_iff] at hYmem
  have e1 : ((bernoulli (2 * p)).num : ℚ) * ((c - T : ℚ).den : ℚ)
      = p * (c - T : ℚ).num * ((bernoulli (2 * p)).den : ℚ) := by
    have a := Rat.mul_den_eq_num (bernoulli (2 * p))
    have b := Rat.mul_den_eq_num (c - T : ℚ)
    rw [← a, ← b]
    linear_combination ((bernoulli (2 * p)).den : ℚ) * ((c - T : ℚ).den : ℚ) * key
  have e2 : (bernoulli (2 * p)).num * ((c - T : ℚ).den : ℤ)
      = p * (c - T : ℚ).num * ((bernoulli (2 * p)).den : ℤ) := by exact_mod_cast e1
  have hd : (p : ℤ) ∣ (bernoulli (2 * p)).num * ((c - T : ℚ).den : ℤ) :=
    ⟨(c - T : ℚ).num * ((bernoulli (2 * p)).den : ℤ), by rw [e2]; ring⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h | h
  · exact h
  · exact absurd (Int.natCast_dvd_natCast.mp h) hYmem

end OMA.A332300

theorem OMA.solution : type_of% @OMA.S_oeis_a332300.main :=
  fun p hp h3 => OMA.A332300.main' p hp h3
