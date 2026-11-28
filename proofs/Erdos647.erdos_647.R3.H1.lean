import OMAReductions.R_Erdos647_erdos_647_R3
import Mathlib

-- Step Erdos647.erdos_647.R3.H1: hypothesis H1 of reduction Erdos647.erdos_647.R3
-- Credit: @Raimo33

open ArithmeticFunction.sigma ArithmeticFunction

namespace RaimoDiv

def N : ℕ → ℕ
  | 2 => 2075942 | 3 => 192902 | 5 => 32768 | 7 => 14878 | 11 => 6025 | 13 => 4924
  | 17 => 3765 | 19 => 3369 | 23 => 2783 | 29 => 2207 | 31 => 2065 | 37 => 1730
  | 41 => 1561 | 43 => 1489 | 47 => 1362 | 53 => 1208 | 59 => 1085 | 61 => 1050
  | _ => 1000

lemma N_ge (p : ℕ) : 1000 ≤ N p := by
  unfold N; split <;> norm_num

lemma N_large (p : ℕ) (hp : 64 ≤ p) : N p = 1000 := by
  unfold N; split <;> omega

lemma grow (D M p : ℕ) (hp : 2 ≤ p) (base : ∀ k ≤ 9, (k+1)^6*D ≤ M*p^k) :
    ∀ k, (k+1)^6*D ≤ M*p^k := by
  have step : ∀ j, (j+10)^6*D ≤ M*p^(j+9) := by
    intro j
    induction j with
    | zero => exact base 9 le_rfl
    | succ j ih =>
      have hpoly : (j+1+10)^6 ≤ 2*(j+10)^6 := by ring_nf; nlinarith [Nat.zero_le j, Nat.zero_le (j^2), Nat.zero_le (j^3), Nat.zero_le (j^4), Nat.zero_le (j^5), Nat.zero_le (j^6)]
      calc (j+1+10)^6*D ≤ 2*(j+10)^6*D := Nat.mul_le_mul_right _ hpoly
        _ = 2*((j+10)^6*D) := by ring
        _ ≤ 2*(M*p^(j+9)) := Nat.mul_le_mul_left _ ih
        _ ≤ p*(M*p^(j+9)) := Nat.mul_le_mul_right _ hp
        _ = M*p^(j+1+9) := by ring
  intro k
  by_cases hk : k ≤ 9
  · exact base k hk
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have := step j
    have e : j + 9 + 1 = j + 10 := by ring
    rw [e]; exact this

lemma localN (p k : ℕ) (hp : p.Prime) : (k+1)^6 * 1000 ≤ N p * p^k := by
  by_cases h64 : 64 ≤ p
  · rw [N_large p h64, mul_comm]
    apply Nat.mul_le_mul_left
    have h1 : k + 1 ≤ 2^k := Nat.lt_two_pow_self
    calc (k+1)^6 ≤ (2^k)^6 := Nat.pow_le_pow_left h1 6
      _ = 64^k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ p^k := Nat.pow_le_pow_left h64 k
  · rw [not_le] at h64
    have h2 := hp.two_le
    interval_cases p <;> first
      | (exfalso; norm_num at hp; done)
      | exact grow _ _ _ (by norm_num) (by intro k hk; interval_cases k <;> norm_num [N]) k

lemma main_bound (m : ℕ) (hm : m ≠ 0) :
    ((σ 0 m : ℕ) : ℝ)^6 ≤ (∏ p ∈ m.primeFactors, (N p : ℝ)/1000) * m := by
  rw [sigma_zero_apply, Nat.card_divisors hm]
  push_cast
  rw [← Finset.prod_pow]
  have e : ((m : ℕ) : ℝ) = ∏ p ∈ m.primeFactors, ((p:ℝ))^(m.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [e, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p _; positivity
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := localN p (m.factorization p) hpp
    have h' : (((m.factorization p + 1)^6 * 1000 : ℕ) : ℝ) ≤ ((N p * p^(m.factorization p) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    exact h'

def Big : Finset ℕ := {7,11,13,17,19,23,29,31,37,41,43,47,53,59,61}

lemma prod_le (m : ℕ) (hm : m ≠ 0) : ∏ p ∈ m.primeFactors, (N p:ℝ)/1000 ≤
    (∏ p ∈ ({2,3,5}:Finset ℕ).filter (· ∣ m), (N p:ℝ)/1000) * ∏ p ∈ Big, (N p:ℝ)/1000 := by
  have r1 : ∀ p, (1:ℝ) ≤ (N p:ℝ)/1000 := by
    intro p
    have := N_ge p
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : 1 * 1000 ≤ N p)
  rw [← Finset.prod_filter_mul_prod_filter_not m.primeFactors (· < 64)]
  have h2 : ∏ p ∈ m.primeFactors.filter (fun p => ¬ p < 64), (N p:ℝ)/1000 = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [N_large p (by omega)]; norm_num
  rw [h2, mul_one]
  have hdisj : Disjoint (({2,3,5}:Finset ℕ).filter (· ∣ m)) Big := by
    rw [Finset.disjoint_left]
    intro p hp
    rw [Finset.mem_filter] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp.1 with rfl | rfl | rfl <;> decide
  rw [← Finset.prod_union hdisj]
  have hsub : m.primeFactors.filter (· < 64) ⊆ (({2,3,5}:Finset ℕ).filter (· ∣ m)) ∪ Big := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hdvd, _⟩, hlt⟩ := hp
    have h2 := hpp.two_le
    rw [Finset.mem_union, Finset.mem_filter]
    interval_cases p <;> first
      | (exfalso; norm_num at hpp; done)
      | (left; exact ⟨by decide, hdvd⟩)
      | (right; decide)
  rw [← Finset.inter_eq_right.mpr hsub, ← Finset.filter_mem_eq_inter, Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro p _; split_ifs <;> positivity
  · intro p _; split_ifs
    · exact le_rfl
    · exact r1 p

lemma realprod (S : Finset ℕ) :
    ∏ p ∈ S, (N p:ℝ)/1000 = ((∏ p ∈ S, N p : ℕ):ℝ) / 1000^S.card := by
  rw [Finset.prod_div_distrib, Finset.prod_const]; push_cast; rfl

lemma bigval : ∏ p ∈ Big, N p = 535214683802088897618863010541691845239442200000000 := by decide +kernel

theorem H1 : ∀ m : ℕ,
    (σ 0 m) ^ 6 ≤
      (if 2 ∣ m then
        (if 3 ∣ m then (if 5 ∣ m then 139 else 78)
         else (if 5 ∣ m then 58 else 33))
       else
        (if 3 ∣ m then (if 5 ∣ m then 39 else 22)
         else (if 5 ∣ m then 17 else 10))) ^ 6 * m := by
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hc : (∏ p ∈ ({2,3,5}:Finset ℕ).filter (· ∣ m), (N p:ℝ)/1000) * ∏ p ∈ Big, (N p:ℝ)/1000 ≤
      (((if 2 ∣ m then
        (if 3 ∣ m then (if 5 ∣ m then 139 else 78)
         else (if 5 ∣ m then 58 else 33))
       else
        (if 3 ∣ m then (if 5 ∣ m then 39 else 22)
         else (if 5 ∣ m then 17 else 10)) : ℕ) : ℝ)) ^ 6 := by
    rw [realprod, realprod, bigval, div_mul_div_comm, div_le_iff₀ (by positivity)]
    have hB : Big.card = 15 := by decide +kernel
    rw [hB]
    by_cases h2 : 2 ∣ m <;> by_cases h3 : 3 ∣ m <;> by_cases h5 : 5 ∣ m <;>
      simp only [Finset.filter_insert, Finset.filter_singleton, h2, h3, h5, if_true, if_false] <;>
      norm_cast <;> decide +kernel
  have key : ((σ 0 m : ℕ) : ℝ)^6 ≤ (((if 2 ∣ m then
        (if 3 ∣ m then (if 5 ∣ m then 139 else 78)
         else (if 5 ∣ m then 58 else 33))
       else
        (if 3 ∣ m then (if 5 ∣ m then 39 else 22)
         else (if 5 ∣ m then 17 else 10)) : ℕ) : ℝ)) ^ 6 * m :=
    (main_bound m hm).trans ((mul_le_mul_of_nonneg_right (prod_le m hm) hm0).trans
      (mul_le_mul_of_nonneg_right hc hm0))
  exact_mod_cast key

end RaimoDiv

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R3.H1 := RaimoDiv.H1
