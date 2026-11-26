import FormalConjectures.ErdosProblems.«400»

-- Problem: Erdős Problem 400 — upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/400.lean:68 (declaration Erdos400.erdos_400.variants.upper_bound)
-- Credit: @jonas-klesen (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea. Compare powers of two. By Legendre's formula `m = v₂(m!) + s₂(m)`, where `s₂(m)` is
-- the binary digit sum, and `s₂(m) ≤ log₂ m + 1`. If `a₁! ⋯ a_k! ∣ n!` with `n ≥ 1` then every
-- `a_i ≤ n` and `∑ v₂(a_i!) ≤ v₂(n!) ≤ n`, hence `∑ a_i ≤ n + k (log₂ n + 1)`.
-- So `g_k(n) ≤ k (log₂ n + 1) ≤ k (1 / log 2 + 1) log n` for `n ≥ 3`.

open Nat Finset

namespace OMAErdos400

lemma digit_sum_le_log (m n : ℕ) (hmn : m ≤ n) : (Nat.digits 2 m).sum ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length • 1 :=
      List.sum_le_card_nsmul _ _ (fun d hd => by
        have := Nat.digits_lt_base (by norm_num : 1 < 2) hd
        omega)
    rw [Nat.digits_len 2 m (by norm_num) (by omega), smul_eq_mul, mul_one] at h1
    have h2 : Nat.log 2 m ≤ Nat.log 2 n := Nat.log_mono_right hmn
    omega

lemma legendre_two (m : ℕ) : m = padicValNat 2 (m !) + (Nat.digits 2 m).sum := by
  have h : 1 * padicValNat 2 (m !) = m - (Nat.digits 2 m).sum :=
    sub_one_mul_padicValNat_factorial (p := 2) m
  have h2 := Nat.digit_sum_le 2 m
  omega

lemma le_of_factorial_dvd (a n : ℕ) (hn : 0 < n) (h : a ! ∣ n !) : a ≤ n := by
  by_contra hlt
  have h1 : n ! < a ! := (Nat.factorial_lt hn).2 (by omega)
  have h2 : a ! ≤ n ! := Nat.le_of_dvd (Nat.factorial_pos n) h
  omega

lemma key (k n : ℕ) (hn : 0 < n) (a : Fin k → ℕ) (h : (∏ i, (a i)!) ∣ n !) :
    (∑ i, a i) - n ≤ k * (Nat.log 2 n + 1) := by
  have hle : ∀ i, a i ≤ n := fun i =>
    le_of_factorial_dvd _ _ hn
      ((Finset.dvd_prod_of_mem (fun i => (a i)!) (Finset.mem_univ i)).trans h)
  have hpow : 2 ^ (∑ i, padicValNat 2 ((a i)!)) ∣ n ! := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_padicValNat_dvd)).trans h
  have hv : ∑ i, padicValNat 2 ((a i)!) ≤ padicValNat 2 (n !) :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).1 hpow
  have hn' := legendre_two n
  have hsum : ∑ i, a i ≤ ∑ i, (padicValNat 2 ((a i)!) + (Nat.log 2 n + 1)) := by
    apply Finset.sum_le_sum
    intro i _
    have h1 := legendre_two (a i)
    have h2 := digit_sum_le_log (a i) n (hle i)
    omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  omega

end OMAErdos400

open OMAErdos400 in
theorem OMA.solution : type_of% @Erdos400.erdos_400.variants.upper_bound := by
  intro k hk
  apply Asymptotics.IsBigO.of_bound ((k : ℝ) * (1 / Real.log 2 + 1))
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hg : Erdos400.g k n ≤ k * (Nat.log 2 n + 1) := by
    unfold Erdos400.g
    apply csSup_le'
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact key k n (by omega) a ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 1 ≤ Real.log n := by
    have he : Real.exp 1 ≤ (n : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) he
  have hL : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ)) ^ Nat.log 2 n ≤ n := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at h3
  have hL' : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact hL
  have hg' : ((Erdos400.g k n : ℕ) : ℝ) ≤ (k : ℝ) * ((Nat.log 2 n : ℝ) + 1) := by
    exact_mod_cast hg
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by linarith)]
  calc ((Erdos400.g k n : ℕ) : ℝ) ≤ (k : ℝ) * ((Nat.log 2 n : ℝ) + 1) := hg'
    _ ≤ (k : ℝ) * (Real.log n / Real.log 2 + Real.log n) := by gcongr
    _ = (k : ℝ) * (1 / Real.log 2 + 1) * Real.log n := by ring
