import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1_H2_R1
import Mathlib

-- Step PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1.H2.R1
-- Credit: @brainchain-agent
-- Every prime factor of such an n is at least 5, hence coprime to 6. The six smallest integers
-- at least 5 that are coprime to 6 are 5, 7, 11, 13, 17, 19, so
-- sigma(n)/n < prod p/(p-1) <= (5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2.
-- The abundancy lemmas follow the merged proof of step R1.H2.R1.H1 (@ivillar).

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace B7OPNSix

/-- The `i`-th integer (from `0`) that is at least `5` and coprime to `6`: 5, 7, 11, 13, ... -/
def u (i : ℕ) : ℕ := 3 * i + 5 - i % 2

/-- `c r = ∏_{i<r} u i / (u i - 1)`. -/
def c (r : ℕ) : ℚ := ∏ i ∈ Finset.range r, ((u i : ℚ) / ((u i : ℚ) - 1))

lemma c_succ (r : ℕ) : c (r + 1) = c r * ((u r : ℚ) / ((u r : ℚ) - 1)) := by
  simp only [c, Finset.prod_range_succ]

lemma u_ge (i : ℕ) : 5 ≤ u i := by
  unfold u
  omega

lemma c_nonneg (r : ℕ) : 0 ≤ c r := by
  unfold c
  apply Finset.prod_nonneg
  intro i _
  have h5 : (5 : ℚ) ≤ u i := by exact_mod_cast u_ge i
  apply div_nonneg <;> linarith

/-- The product of `x/(x-1)` over a set of integers `≥ 5` coprime to `6` is at most `c` of
its size. -/
lemma prod_le_c (S : Finset ℕ) (hS : ∀ x ∈ S, (x % 6 = 1 ∨ x % 6 = 5) ∧ 5 ≤ x) :
    ∏ x ∈ S, ((x : ℚ) / ((x : ℚ) - 1)) ≤ c S.card := by
  induction S using Finset.induction_on_max with
  | empty => simp [c]
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, c_succ]
    have hs : ∀ x ∈ s, (x % 6 = 1 ∨ x % 6 = 5) ∧ 5 ≤ x :=
      fun x hx => hS x (Finset.mem_insert_of_mem hx)
    have ih' := ih hs
    obtain ⟨ham, ha5⟩ := hS a (Finset.mem_insert_self a s)
    have hcard : (insert a s).card ≤ a / 3 := by
      have : (insert a s).card ≤ (Finset.range (a / 3)).card := by
        apply Finset.card_le_card_of_injOn (fun x => x / 3 - 1)
        · intro x hx
          have hxo := hS x hx
          have hxa : x ≤ a := by
            rcases Finset.mem_insert.mp hx with rfl | h
            · exact le_rfl
            · exact (hlt x h).le
          simp only [Finset.coe_range, Set.mem_Iio]
          omega
        · intro x hx y hy hxy
          have hxo := hS x hx
          have hyo := hS y hy
          simp only at hxy
          omega
      simpa using this
    rw [Finset.card_insert_of_notMem ha] at hcard
    have hua : u s.card ≤ a := by
      unfold u
      omega
    have hu5 : 5 ≤ u s.card := u_ge s.card
    have hU : (5 : ℚ) ≤ (u s.card : ℚ) := by exact_mod_cast hu5
    have hUA : (u s.card : ℚ) ≤ (a : ℚ) := by exact_mod_cast hua
    have hA : (5 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha5
    have hA1 : (0 : ℚ) < (a : ℚ) - 1 := by linarith
    have hU1 : (0 : ℚ) < (u s.card : ℚ) - 1 := by linarith
    have hfac : (a : ℚ) / ((a : ℚ) - 1) ≤ (u s.card : ℚ) / ((u s.card : ℚ) - 1) := by
      rw [div_le_div_iff₀ hA1 hU1]
      nlinarith
    have hprod_nonneg : 0 ≤ ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1)) := by
      apply Finset.prod_nonneg
      intro x hx
      have h5 : (5 : ℚ) ≤ x := by exact_mod_cast (hs x hx).2
      apply div_nonneg <;> linarith
    have hfac_nonneg : 0 ≤ (u s.card : ℚ) / ((u s.card : ℚ) - 1) := by
      apply div_nonneg <;> linarith
    calc (a : ℚ) / ((a : ℚ) - 1) * ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1))
        ≤ (u s.card : ℚ) / ((u s.card : ℚ) - 1) * c s.card := by
          exact mul_le_mul hfac ih' hprod_nonneg hfac_nonneg
      _ = c s.card * ((u s.card : ℚ) / ((u s.card : ℚ) - 1)) := by ring

/-- `σ(p^e) / p^e < p / (p - 1)` for a prime `p`. -/
lemma sigma_pp_lt {p e : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ e) : ℕ) : ℚ) / ((p ^ e : ℕ) : ℚ) < (p : ℚ) / ((p : ℚ) - 1) := by
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  rw [sigma_one_apply_prime_pow hp]
  set S := ∑ i ∈ Finset.range (e + 1), p ^ i with hSdef
  have hgeo : S * (p - 1) + 1 = p ^ (e + 1) := by
    have := geom_sum_mul_add (p - 1) (e + 1)
    rwa [Nat.sub_add_cancel hp.one_le] at this
  have hq : (S : ℚ) * ((p : ℚ) - 1) + 1 = (p : ℚ) ^ e * p := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hgeo
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_pow, Nat.cast_one,
      pow_succ] at h
    exact h
  have hpe : (0 : ℚ) < (p : ℚ) ^ e := by positivity
  rw [Nat.cast_pow, div_lt_div_iff₀ hpe (by linarith)]
  nlinarith

/-- `σ(n)/n < ∏ p/(p-1)` over the prime factors, for `n > 1`. -/
lemma abundancy_lt (n : ℕ) (hn : 1 < n) :
    ((σ 1 n : ℕ) : ℚ) / (n : ℚ) < ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hn0 : n ≠ 0 := by omega
  have hs := isMultiplicative_sigma.multiplicative_factorization (σ 1) hn0
  have hn' := Nat.prod_factorization_pow_eq_self hn0
  have key : ((σ 1 n : ℕ) : ℚ) / (n : ℚ) =
      ∏ p ∈ n.primeFactors,
        (((σ 1 (p ^ n.factorization p) : ℕ) : ℚ) / ((p ^ n.factorization p : ℕ) : ℚ)) := by
    rw [Finset.prod_div_distrib]
    congr 1
    · rw [hs, Nat.cast_finsuppProd]
      rfl
    · conv_lhs => rw [← hn']
      rw [Nat.cast_finsuppProd]
      rfl
  rw [key]
  apply Finset.prod_lt_prod_of_nonempty
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : 0 < σ 1 (p ^ n.factorization p) := by
      rw [sigma_one_apply_prime_pow hpp]
      exact Finset.sum_pos (fun i _ => pow_pos hpp.pos i) ⟨0, by simp⟩
    have h2 : 0 < p ^ n.factorization p := pow_pos hpp.pos _
    exact div_pos (by exact_mod_cast h1) (by exact_mod_cast h2)
  · intro p hp
    exact sigma_pp_lt (Nat.prime_of_mem_primeFactors hp)
  · exact Nat.nonempty_primeFactors.mpr hn

lemma c_six_lt : c 6 < 2 := by
  first
  | (simp only [c, u, Finset.prod_range_succ, Finset.prod_range_zero]; norm_num)
  | norm_num [c, u, Finset.prod_range_succ]

theorem opn_six_factors : ∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card = 6 →
    Nat.minFac n ∉ ({5, 7, 11, 13, 17} : Set ℕ) := by
  intro n hperf hodd hcard hmin
  have hn0 : n ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmin
  have h5 : 5 ≤ n.minFac := by omega
  have hn1 : 1 < n := by
    by_contra h
    have : n = 1 := by omega
    rw [this, Nat.minFac_one] at h5
    omega
  have hσ : σ 1 n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero hn0)).mp hperf
  have hb := abundancy_lt n hn1
  have hprod := prod_le_c n.primeFactors (by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hle : n.minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpd
    have h2 : ¬ 2 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h
      omega
    have h3 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h
      omega
    exact ⟨by omega, by omega⟩)
  rw [hcard] at hprod
  have hlt := c_six_lt
  rw [hσ] at hb
  have hn0' : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  push_cast at hb
  rw [mul_div_assoc, div_self hn0'.ne', mul_one] at hb
  linarith

end B7OPNSix

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1_H2_R1.H1 :=
  B7OPNSix.opn_six_factors
