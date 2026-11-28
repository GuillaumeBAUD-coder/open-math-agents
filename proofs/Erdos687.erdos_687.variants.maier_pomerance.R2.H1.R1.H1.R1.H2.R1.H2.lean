import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1
import Mathlib

-- Step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1
-- Credit: @carterleffen

/-!
# Uniform Count-Error Remainder Bound on the Admissible Prime Tree

We prove `OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H2`:
there exist explicit `k >= 3`, `ε > 0`, and `δ > 0` such that for all sufficiently large `z`,
any residue assignment `a : ℕ → ℕ`, and any subfamily `E ⊆ T` of the admissible prime tree
whose bad compact subset `A = {d ∈ E | g(d) ≤ k ∧ ε < |Z(d, Q) / (μ / D(d)) - 1|}` satisfies
`B^2 * ∑_{d ∈ A} (D d)⁻¹ ≤ δ`, the total progression count error obeys
`∑_{d ∈ E} |Z(d, Q) - μ / D(d)| ≤ μ / (100 * B^2)`.

The proof is completely self-contained in four sections:
1. **Mertens and discrete Abel summation (`Erdos687H2.Mertens`)**: proves Mertens first theorem
   via Legendre factorial valuation and `Chebyshev.theta_le_log4_mul_x`, together with discrete
   Abel summation bounds for prime reciprocal sums and Euler product ratios.
2. **Elementary `r^2 / y` tree-mass barrier (`Erdos687H2.TreeMass`)**: bounds the reciprocal
   weight of admissible histories `d ∈ T` in each slab `g(d) ∈ (a, a + Δ]` (`Δ = 1 / log w`)
   by `(C_m / B^2) * ((a + Δ)^3 - a^3) / (3 * e(p))`, yielding both the compact reciprocal-mass
   bound `B^2 * ∑_{d ∈ T, g d ≤ k} (D d)⁻¹ ≤ C_small(k)` and the exponential tail bound
   `B^2 * ∑_{d ∈ T, k < g d} (D d)⁻¹ * exp (-c * g d) ≤ O(exp (-c*k/2)) + o(1)`.
3. **Unified two-sided exponential Brun sieve (`Erdos687H2.BrunSieve`)**: merges lower and upper
   Brun combinatorial sieves into one parameterized proof yielding the two-sided exponential
   Fundamental Lemma, transferred to progressions `Z(d, Q)` via CRT for both long progressions
   (`g(d) ≥ sBrun + 4`) and all admitted progressions (`g(d) ≥ 2`, via a reduced sifting cutoff
   and the Mertens Euler-product ratio bound).
4. **Three-piece remainder assembly (`Erdos687H2.Main`)**: partitions `E ⊆ E_long ∪ E_good ∪ A`,
   charging at most `μ / (300 * B^2)` to each piece for a combined bound of `μ / (100 * B^2)`.
-/


namespace Erdos687H2.Mertens
open Finset Real

/-
# Mertens first theorem and elementary Abel summation corollaries

Adapted from `OMALib.Mertens` (Mertens first theorem via Legendre factorial valuation and
`Chebyshev.theta_le_log4_mul_x`), followed by discrete Abel summation bounds for
`∑ 1 / (p * log p)`, `∑ 1 / p`, `∑ log p / p`, and Euler product ratios.
-/

lemma log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

lemma real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

lemma log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

lemma log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith

lemma summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

lemma sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

lemma sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

lemma sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

lemma primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

noncomputable def CM : ℝ := Real.log 4 + 1 + primePowerConst

lemma CM_pos : 0 < CM := by
  have h1 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 := primePowerConst_nonneg
  unfold CM
  linarith

lemma abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ CM := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold CM; constructor <;> linarith

lemma primesLE_eq_range_filter (N : ℕ) :
    Nat.primesLE N = (Finset.range (N + 1)).filter Nat.Prime := by
  ext p
  simp [Nat.mem_primesLE]

lemma sum_Ioc_sub_prev (g : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ioc A B, (g n - g (n - 1)) = g B - g A := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hIoc : Finset.Ioc A (k + 1) = insert (k + 1) (Finset.Ioc A k) := by
      ext x; simp only [mem_Ioc, mem_insert]; omega
    rw [hIoc, Finset.sum_insert (by simp), ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma sum_log_div_p_Ioc_ge {A B : ℕ} (hAB : A ≤ B) :
    Real.log B - Real.log A - 2 * CM ≤
      ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log p / p := by
  have hsplit : Nat.primesLE B = Nat.primesLE A ∪ (Finset.Ioc A B).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, mem_union, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hpB, hpp⟩
      by_cases hpA : p ≤ A
      · exact Or.inl ⟨hpA, hpp⟩
      · exact Or.inr ⟨⟨by omega, hpB⟩, hpp⟩
    · rintro (⟨hpA, hpp⟩ | ⟨⟨_, hpB⟩, hpp⟩)
      · exact ⟨hpA.trans hAB, hpp⟩
      · exact ⟨hpB, hpp⟩
  have hdisj : Disjoint (Nat.primesLE A) ((Finset.Ioc A B).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hA hI
    have := (Nat.mem_primesLE.mp hA).1
    have := (mem_Ioc.mp (mem_filter.mp hI).1).1
    omega
  have hsum : ∑ p ∈ Nat.primesLE B, Real.log p / p =
      (∑ p ∈ Nat.primesLE A, Real.log p / p) +
        ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log p / p := by
    rw [hsplit, Finset.sum_union hdisj]
  have hA := (abs_le.mp (abs_sum_log_div_sub_log_le_nat A)).2
  have hB := (abs_le.mp (abs_sum_log_div_sub_log_le_nat B)).1
  linarith

/-- Discrete Abel summation bound for bounded error sequences weighted by a nonneg antitone `f`. -/
lemma abel_error_sum_le {E f : ℕ → ℝ} {C : ℝ} {A B : ℕ} (hAB : A ≤ B)
    (hE : ∀ n, A ≤ n → n ≤ B → |E n| ≤ C)
    (hf_nn : ∀ n, A ≤ n → n ≤ B → 0 ≤ f n)
    (hf_anti : ∀ n, A ≤ n → n < B → f (n + 1) ≤ f n) :
    ∑ n ∈ Finset.Ioc A B, (E n - E (n - 1)) * f n ≤ 2 * C * f A := by
  have htel : ∀ m, A ≤ m →
      ∑ n ∈ Finset.Ioc A m, (E n - E (n - 1)) * f n =
        E m * f m - E A * f A + ∑ n ∈ Finset.Ico A m, E n * (f n - f (n + 1)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ j hj ihj =>
      have hIoc : Finset.Ioc A (j + 1) = insert (j + 1) (Finset.Ioc A j) := by
        ext x; simp only [mem_Ioc, mem_insert]; omega
      have hIco : Finset.Ico A (j + 1) = insert j (Finset.Ico A j) := by
        ext x; simp only [mem_Ico, mem_insert]; omega
      rw [hIoc, Finset.sum_insert (by simp), hIco, Finset.sum_insert (by simp), ihj]
      simp only [Nat.add_sub_cancel]
      ring
  rw [htel B hAB]
  have hsum_le : ∑ n ∈ Finset.Ico A B, E n * (f n - f (n + 1)) ≤
      ∑ n ∈ Finset.Ico A B, C * (f n - f (n + 1)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' := mem_Ico.mp hn
    have hdiff : 0 ≤ f n - f (n + 1) := sub_nonneg.mpr (hf_anti n hn'.1 hn'.2)
    have hEn : E n ≤ C := (abs_le.mp (hE n hn'.1 hn'.2.le)).2
    exact mul_le_mul_of_nonneg_right hEn hdiff
  have htelesc : ∑ n ∈ Finset.Ico A B, C * (f n - f (n + 1)) = C * (f A - f B) := by
    rw [← Finset.mul_sum]
    congr 1
    have hsub : ∀ m, A ≤ m → ∑ n ∈ Finset.Ico A m, (f n - f (n + 1)) = f A - f m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ j hj ihj =>
        have hIco : Finset.Ico A (j + 1) = insert j (Finset.Ico A j) := by
          ext x; simp only [mem_Ico, mem_insert]; omega
        rw [hIco, Finset.sum_insert (by simp), ihj]
        ring
    exact hsub B hAB
  have h1 : E B * f B ≤ C * f B :=
    mul_le_mul_of_nonneg_right (abs_le.mp (hE B hAB le_rfl)).2 (hf_nn B hAB le_rfl)
  have h2 : -E A * f A ≤ C * f A := by
    have := (abs_le.mp (hE A le_rfl hAB)).1
    have := hf_nn A le_rfl hAB
    nlinarith
  linarith

lemma sum_primes_Ioc_weighted_eq {f : ℕ → ℝ} {A B : ℕ} :
    ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (Real.log p / p) * f p =
      ∑ n ∈ Finset.Ioc A B,
        ((∑ p ∈ Nat.primesLE n, Real.log p / p) -
         (∑ p ∈ Nat.primesLE (n - 1), Real.log p / p)) * f n := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  have hstep : Nat.primesLE n =
      if n.Prime then insert n (Nat.primesLE (n - 1)) else Nat.primesLE (n - 1) := by
    ext p
    split_ifs with hp
    · simp only [Nat.mem_primesLE, mem_insert]
      constructor
      · rintro ⟨hpn, hpp⟩
        rcases eq_or_lt_of_le hpn with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨by omega, hpp⟩
      · rintro (rfl | ⟨hpn, hpp⟩)
        · exact ⟨le_rfl, hp⟩
        · exact ⟨by omega, hpp⟩
    · simp only [Nat.mem_primesLE]
      constructor
      · rintro ⟨hpn, hpp⟩
        refine ⟨?_, hpp⟩
        rcases eq_or_lt_of_le hpn with rfl | hlt
        · exact absurd hpp hp
        · omega
      · rintro ⟨hpn, hpp⟩
        exact ⟨by omega, hpp⟩
  rw [hstep]
  split_ifs with hp
  · have hnot : n ∉ Nat.primesLE (n - 1) := by
      rw [Nat.mem_primesLE]; omega
    rw [Finset.sum_insert hnot, add_sub_cancel_right]
  · simp

lemma sum_inv_p_mul_log_Ioc_le {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * Real.log p) ≤
      1 / Real.log A - 1 / Real.log B + 2 * CM / (Real.log A) ^ 2 := by
  let f : ℕ → ℝ := fun n => 1 / (Real.log n) ^ 2
  let E : ℕ → ℝ := fun n => (∑ p ∈ Nat.primesLE n, Real.log p / p) - Real.log n
  have hrewrite : ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * Real.log p) =
      ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (Real.log p / p) * f p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
    dsimp [f]
    field_simp
  rw [hrewrite, sum_primes_Ioc_weighted_eq]
  have hsplit : ∑ n ∈ Finset.Ioc A B,
      ((∑ p ∈ Nat.primesLE n, Real.log p / p) -
        (∑ p ∈ Nat.primesLE (n - 1), Real.log p / p)) * f n =
      (∑ n ∈ Finset.Ioc A B, (Real.log n - Real.log (n - 1 : ℕ)) * f n) +
      (∑ n ∈ Finset.Ioc A B, (E n - E (n - 1)) * f n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [E]
    ring
  rw [hsplit]
  have hmain : ∑ n ∈ Finset.Ioc A B, (Real.log n - Real.log (n - 1 : ℕ)) * f n ≤
      1 / Real.log A - 1 / Real.log B := by
    have hle : ∑ n ∈ Finset.Ioc A B, (Real.log n - Real.log (n - 1 : ℕ)) * f n ≤
        ∑ n ∈ Finset.Ioc A B, (-(1 / Real.log n) - -(1 / Real.log (n - 1 : ℕ))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnA : A < n := (mem_Ioc.mp hn).1
      have hnm1 : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 by omega)
      have hle_n : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
      have hl1 : 0 < Real.log (n - 1 : ℕ) := Real.log_pos (by linarith)
      have hl2 : 0 < Real.log n := Real.log_pos (by linarith)
      have hmono : Real.log (n - 1 : ℕ) ≤ Real.log n := Real.log_le_log (by linarith) hle_n
      dsimp [f]
      have hrhs : -(1 / Real.log n) - -(1 / Real.log (n - 1 : ℕ)) =
          (Real.log n - Real.log (n - 1 : ℕ)) / (Real.log (n - 1 : ℕ) * Real.log n) := by
        field_simp; ring
      rw [hrhs, mul_one_div]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hmono) (mul_pos hl1 hl2) (by nlinarith)
    have htel := sum_Ioc_sub_prev (fun n => -(1 / Real.log (n : ℝ))) hAB
    linarith
  have herr : ∑ n ∈ Finset.Ioc A B, (E n - E (n - 1)) * f n ≤ 2 * CM / (Real.log A) ^ 2 := by
    have h1 := abel_error_sum_le (E := E) (f := f) (C := CM) hAB
      (fun n _ _ => abs_sum_log_div_sub_log_le_nat n)
      (fun n _ _ => by dsimp [f]; positivity)
      (fun n hn _ => by
        dsimp [f]
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (hA.trans hn)
        have hl1 : 0 < Real.log n := Real.log_pos (by linarith)
        have hle : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
          Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_succ n)
        exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hl1) (by nlinarith))
    have heq : 2 * CM * f A = 2 * CM / (Real.log A) ^ 2 := by dsimp [f]; ring
    linarith
  linarith

lemma sum_inv_p_Ioc_le {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      Real.log (Real.log B / Real.log A) + 2 * CM / Real.log A := by
  let f : ℕ → ℝ := fun n => 1 / Real.log n
  let E : ℕ → ℝ := fun n => (∑ p ∈ Nat.primesLE n, Real.log p / p) - Real.log n
  have hrewrite : ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℝ)⁻¹ =
      ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (Real.log p / p) * f p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
    dsimp [f]
    field_simp
  rw [hrewrite, sum_primes_Ioc_weighted_eq]
  have hsplit : ∑ n ∈ Finset.Ioc A B,
      ((∑ p ∈ Nat.primesLE n, Real.log p / p) -
        (∑ p ∈ Nat.primesLE (n - 1), Real.log p / p)) * f n =
      (∑ n ∈ Finset.Ioc A B, (Real.log n - Real.log (n - 1 : ℕ)) * f n) +
      (∑ n ∈ Finset.Ioc A B, (E n - E (n - 1)) * f n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [E]
    ring
  rw [hsplit]
  have hmain : ∑ n ∈ Finset.Ioc A B, (Real.log n - Real.log (n - 1 : ℕ)) * f n ≤
      Real.log (Real.log B / Real.log A) := by
    have hle : ∑ n ∈ Finset.Ioc A B, (Real.log n - Real.log (n - 1 : ℕ)) * f n ≤
        ∑ n ∈ Finset.Ioc A B, (Real.log (Real.log n) - Real.log (Real.log (n - 1 : ℕ))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnA : A < n := (mem_Ioc.mp hn).1
      have hnm1 : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 by omega)
      have hl1 : 0 < Real.log (n - 1 : ℕ) := Real.log_pos (by linarith)
      have hl2 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hrat_pos : 0 < Real.log n / Real.log (n - 1 : ℕ) := div_pos hl2 hl1
      have h1 : 1 - (Real.log n / Real.log (n - 1 : ℕ))⁻¹ ≤
          Real.log (Real.log n / Real.log (n - 1 : ℕ)) := by
        have h := Real.add_one_le_exp (-Real.log (Real.log n / Real.log (n - 1 : ℕ)))
        rw [Real.exp_neg, Real.exp_log hrat_pos] at h
        linarith
      rw [Real.log_div hl2.ne' hl1.ne'] at h1
      dsimp [f]
      have heq : (Real.log n - Real.log (n - 1 : ℕ)) * (1 / Real.log n) =
          1 - (Real.log n / Real.log (n - 1 : ℕ))⁻¹ := by
        field_simp
      rwa [heq]
    have htel := sum_Ioc_sub_prev (fun n => Real.log (Real.log (n : ℝ))) hAB
    have hlA : 0 < Real.log A := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
    have hlB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    rw [Real.log_div hlB.ne' hlA.ne']
    exact hle.trans_eq htel
  have herr : ∑ n ∈ Finset.Ioc A B, (E n - E (n - 1)) * f n ≤ 2 * CM / Real.log A := by
    have h1 := abel_error_sum_le (E := E) (f := f) (C := CM) hAB
      (fun n _ _ => abs_sum_log_div_sub_log_le_nat n)
      (fun n hn _ => by
        dsimp [f]
        have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        positivity)
      (fun n hn _ => by
        dsimp [f]
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (hA.trans hn)
        have hl1 : 0 < Real.log n := Real.log_pos (by linarith)
        have hle : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
          Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_succ n)
        exact div_le_div_of_nonneg_left zero_le_one hl1 hle)
    have heq : 2 * CM * f A = 2 * CM / Real.log A := by dsimp [f]; ring
    linarith
  linarith

lemma log_floor_rpow_ge {w u : ℝ} (hw : 4 ≤ w) (hu : 1 ≤ u) :
    u * Real.log w - 2 / w ^ u ≤ Real.log ((⌊w ^ u⌋₊ : ℕ) : ℝ) := by
  have hwpos : 0 < w := by linarith
  have hwu : 4 ≤ w ^ u := by
    calc (4 : ℝ) = 4 ^ (1 : ℝ) := (Real.rpow_one 4).symm
      _ ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hw (by norm_num)
      _ ≤ w ^ u := Real.rpow_le_rpow_of_exponent_le (by linarith) hu
  have hwu_pos : 0 < w ^ u := by linarith
  have hpos : 0 < 1 - (w ^ u)⁻¹ := by
    have : (w ^ u)⁻¹ ≤ 1 / 4 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hwu
    linarith
  have hA_gt : w ^ u - 1 < (⌊w ^ u⌋₊ : ℝ) := Nat.sub_one_lt_floor (w ^ u)
  have hA_ge_mul : w ^ u * (1 - (w ^ u)⁻¹) ≤ (⌊w ^ u⌋₊ : ℝ) := by
    have : w ^ u * (1 - (w ^ u)⁻¹) = w ^ u - 1 := by field_simp
    linarith
  have hlog_mul : Real.log (w ^ u) + Real.log (1 - (w ^ u)⁻¹) ≤ Real.log (⌊w ^ u⌋₊ : ℝ) := by
    rw [← Real.log_mul hwu_pos.ne' hpos.ne']
    exact Real.log_le_log (mul_pos hwu_pos hpos) hA_ge_mul
  have hlog_rpow : Real.log (w ^ u) = u * Real.log w := Real.log_rpow hwpos u
  have hlog_sub : -(2 / w ^ u) ≤ Real.log (1 - (w ^ u)⁻¹) := by
    have h2 := Real.add_one_le_exp (-Real.log (1 - (w ^ u)⁻¹))
    rw [Real.exp_neg, Real.exp_log hpos] at h2
    have h3 : (1 - (w ^ u)⁻¹)⁻¹ ≤ 1 + 2 / w ^ u := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      have h4 : (1 + 2 / w ^ u) * (1 - (w ^ u)⁻¹) = 1 + (w ^ u - 2) / (w ^ u) ^ 2 := by
        field_simp; ring
      rw [h4]
      have : 0 ≤ (w ^ u - 2) / (w ^ u) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
      linarith
    linarith
  linarith

/-- Real-exponent wrapper: `∑_{u₁ < e(p) ≤ u₂} 1 / (p * e(p)) ≤ (1/u₁ - 1/u₂) + C / (u₁² log w)`. -/
lemma sum_inv_p_mul_e_le {w u₁ u₂ : ℝ} (hw : 4 ≤ w) (hu₁ : 1 ≤ u₁) (hu12 : u₁ < u₂)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ u₁ < Real.log p / Real.log w ∧ Real.log p / Real.log w ≤ u₂) :
    ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * (Real.log p / Real.log w)) ≤
      (1 / u₁ - 1 / u₂) + (8 * CM + 4) / (u₁ ^ 2 * Real.log w) := by
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlw1 : 1 ≤ Real.log w := by
    have h1 : Real.exp 1 ≤ w := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h1
  have hwpos : 0 < w := by linarith
  have hwu1 : 4 ≤ w ^ u₁ := by
    calc (4 : ℝ) = 4 ^ (1 : ℝ) := (Real.rpow_one 4).symm
      _ ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hw (by norm_num)
      _ ≤ w ^ u₁ := Real.rpow_le_rpow_of_exponent_le (by linarith) hu₁
  let A : ℕ := ⌊w ^ u₁⌋₊
  let B : ℕ := ⌊w ^ u₂⌋₊
  have hA3 : 3 ≤ A := by have : 4 ≤ A := Nat.le_floor hwu1; omega
  have hAB : A ≤ B := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) hu12.le)
  have hsub : S ⊆ (Finset.Ioc A B).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ := hS p hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hgt : w ^ u₁ < (p : ℝ) := by
      rw [← Real.exp_log hppos, Real.rpow_def_of_pos hwpos]
      apply Real.exp_lt_exp.mpr
      have := (lt_div_iff₀ hlw).mp hlo
      linarith
    have hle : (p : ℝ) ≤ w ^ u₂ := by
      rw [← Real.exp_log hppos, Real.rpow_def_of_pos hwpos]
      apply Real.exp_le_exp.mpr
      have := (div_le_iff₀ hlw).mp hhi
      linarith
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity)).mpr hgt, Nat.le_floor hle⟩, hpp⟩
  have hsum_le : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * (Real.log p / Real.log w)) ≤
      Real.log w * ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * Real.log p) := by
    rw [Finset.mul_sum]
    have hsub_le := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log w * ((1 : ℝ) / ((p : ℝ) * Real.log (p : ℝ)))) hsub (fun p hp _ => by
      have hpp := (mem_filter.mp hp).2
      have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpp.one_lt)
      positivity)
    have hcongr : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * (Real.log p / Real.log w)) =
        ∑ p ∈ S, Real.log w * ((1 : ℝ) / ((p : ℝ) * Real.log p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpp := (hS p hp).1
      have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
      field_simp
    rw [hcongr]
    exact hsub_le
  have hm := sum_inv_p_mul_log_Ioc_le (by omega : 2 ≤ A) hAB
  have h1 := mul_le_mul_of_nonneg_left hm hlw.le
  have hlogA_ge : u₁ * Real.log w - 2 / w ^ u₁ ≤ Real.log (A : ℝ) := log_floor_rpow_ge hw hu₁
  have hlogA_pos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogA_half : u₁ * Real.log w / 2 ≤ Real.log (A : ℝ) := by
    have : 2 / w ^ u₁ ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith
  have hlogB_le : Real.log (B : ℝ) ≤ u₂ * Real.log w := by
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hBle : (B : ℝ) ≤ w ^ u₂ := Nat.floor_le (by positivity)
    calc Real.log (B : ℝ) ≤ Real.log (w ^ u₂) := Real.log_le_log hBpos hBle
      _ = u₂ * Real.log w := Real.log_rpow hwpos u₂
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hu1lw_pos : 0 < u₁ * Real.log w := mul_pos (by linarith) hlw
  have htermA : Real.log w / Real.log (A : ℝ) ≤ 1 / u₁ + 4 / (u₁ ^ 2 * Real.log w) := by
    have hdiff : Real.log w / Real.log (A : ℝ) - 1 / u₁ =
        Real.log w * (u₁ * Real.log w - Real.log (A : ℝ)) / (Real.log (A : ℝ) * (u₁ * Real.log w)) := by
      have : u₁ ≠ 0 := by linarith
      field_simp
    have hnum : u₁ * Real.log w - Real.log (A : ℝ) ≤ 2 / w ^ u₁ := by linarith
    have hden : (u₁ * Real.log w) ^ 2 / 2 ≤ Real.log (A : ℝ) * (u₁ * Real.log w) := by
      have h := mul_le_mul_of_nonneg_right hlogA_half hu1lw_pos.le
      linarith [show u₁ * Real.log w / 2 * (u₁ * Real.log w) = (u₁ * Real.log w) ^ 2 / 2 by ring]
    have hsub_le : Real.log w / Real.log (A : ℝ) - 1 / u₁ ≤
        Real.log w * (2 / w ^ u₁) / ((u₁ * Real.log w) ^ 2 / 2) := by
      rw [hdiff]
      by_cases hnn : 0 ≤ u₁ * Real.log w - Real.log (A : ℝ)
      · calc Real.log w * (u₁ * Real.log w - Real.log (A : ℝ)) / (Real.log (A : ℝ) * (u₁ * Real.log w))
            ≤ Real.log w * (2 / w ^ u₁) / (Real.log (A : ℝ) * (u₁ * Real.log w)) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hlw.le) (by positivity)
          _ ≤ Real.log w * (2 / w ^ u₁) / ((u₁ * Real.log w) ^ 2 / 2) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      · have hle0 : Real.log w * (u₁ * Real.log w - Real.log (A : ℝ)) / (Real.log (A : ℝ) * (u₁ * Real.log w)) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hlw.le (le_of_not_ge hnn)) (by positivity)
        exact hle0.trans (by positivity)
    have hsimp : Real.log w * (2 / w ^ u₁) / ((u₁ * Real.log w) ^ 2 / 2) =
        4 / (u₁ ^ 2 * w ^ u₁ * Real.log w) := by
      have : u₁ ≠ 0 := by linarith
      field_simp
      ring
    have hdropw : 4 / (u₁ ^ 2 * w ^ u₁ * Real.log w) ≤ 4 / (u₁ ^ 2 * Real.log w) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    linarith
  have htermB : 1 / u₂ ≤ Real.log w / Real.log (B : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) hlogB_pos, one_mul, mul_comm]
    exact hlogB_le
  have htermErr : Real.log w * (2 * CM / (Real.log (A : ℝ)) ^ 2) ≤ 8 * CM / (u₁ ^ 2 * Real.log w) := by
    have hsq : (u₁ * Real.log w) ^ 2 / 4 ≤ (Real.log (A : ℝ)) ^ 2 := by
      have h := mul_le_mul hlogA_half hlogA_half (by positivity) hlogA_pos.le
      linarith [show u₁ * Real.log w / 2 * (u₁ * Real.log w / 2) = (u₁ * Real.log w) ^ 2 / 4 by ring,
                show Real.log (A : ℝ) * Real.log (A : ℝ) = (Real.log (A : ℝ)) ^ 2 by ring]
    have hpos_cm : 0 ≤ CM := CM_pos.le
    calc Real.log w * (2 * CM / (Real.log (A : ℝ)) ^ 2)
        = (2 * CM * Real.log w) / (Real.log (A : ℝ)) ^ 2 := by ring
      _ ≤ (2 * CM * Real.log w) / ((u₁ * Real.log w) ^ 2 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = 8 * CM / (u₁ ^ 2 * Real.log w) := by
          have : u₁ ≠ 0 := by linarith
          field_simp
          ring
  have hdist : Real.log w * (1 / Real.log (A : ℝ) - 1 / Real.log (B : ℝ) + 2 * CM / (Real.log (A : ℝ)) ^ 2) =
      Real.log w / Real.log (A : ℝ) - Real.log w / Real.log (B : ℝ) +
        Real.log w * (2 * CM / (Real.log (A : ℝ)) ^ 2) := by
    ring
  have hadd : (8 * CM + 4) / (u₁ ^ 2 * Real.log w) =
      4 / (u₁ ^ 2 * Real.log w) + 8 * CM / (u₁ ^ 2 * Real.log w) := by ring
  linarith

/-- Real-exponent wrapper: `∑_{u₁ < e(p) ≤ u₂} 1 / p ≤ (u₂ - u₁) / u₁ + (4*CM + 2) / (u₁ * log w)`. -/
lemma sum_inv_p_e_le {w u₁ u₂ : ℝ} (hw : 4 ≤ w) (hu₁ : 1 ≤ u₁) (hu12 : u₁ ≤ u₂)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ u₁ < Real.log p / Real.log w ∧ Real.log p / Real.log w ≤ u₂) :
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤
      (u₂ - u₁) / u₁ + (4 * CM + 2) / (u₁ * Real.log w) := by
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlw1 : 1 ≤ Real.log w := by
    have h1 : Real.exp 1 ≤ w := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h1
  have hwpos : 0 < w := by linarith
  have hwu1 : 4 ≤ w ^ u₁ := by
    calc (4 : ℝ) = 4 ^ (1 : ℝ) := (Real.rpow_one 4).symm
      _ ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hw (by norm_num)
      _ ≤ w ^ u₁ := Real.rpow_le_rpow_of_exponent_le (by linarith) hu₁
  let A : ℕ := ⌊w ^ u₁⌋₊
  let B : ℕ := ⌊w ^ u₂⌋₊
  have hA3 : 3 ≤ A := by have : 4 ≤ A := Nat.le_floor hwu1; omega
  have hAB : A ≤ B := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) hu12)
  have hsub : S ⊆ (Finset.Ioc A B).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ := hS p hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hgt : w ^ u₁ < (p : ℝ) := by
      rw [← Real.exp_log hppos, Real.rpow_def_of_pos hwpos]
      apply Real.exp_lt_exp.mpr
      have := (lt_div_iff₀ hlw).mp hlo
      linarith
    have hle : (p : ℝ) ≤ w ^ u₂ := by
      rw [← Real.exp_log hppos, Real.rpow_def_of_pos hwpos]
      apply Real.exp_le_exp.mpr
      have := (div_le_iff₀ hlw).mp hhi
      linarith
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity)).mpr hgt, Nat.le_floor hle⟩, hpp⟩
  have hsum_le : ∑ p ∈ S, (p : ℝ)⁻¹ ≤ ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hm := sum_inv_p_Ioc_le (by omega : 2 ≤ A) hAB
  have hlogA_ge : u₁ * Real.log w - 2 / w ^ u₁ ≤ Real.log (A : ℝ) := log_floor_rpow_ge hw hu₁
  have hlogA_pos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogA_half : u₁ * Real.log w / 2 ≤ Real.log (A : ℝ) := by
    have : 2 / w ^ u₁ ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith
  have hlogB_le : Real.log (B : ℝ) ≤ u₂ * Real.log w := by
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hBle : (B : ℝ) ≤ w ^ u₂ := Nat.floor_le (by positivity)
    calc Real.log (B : ℝ) ≤ Real.log (w ^ u₂) := Real.log_le_log hBpos hBle
      _ = u₂ * Real.log w := Real.log_rpow hwpos u₂
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hu2_pos : 0 < u₂ := by linarith
  have hlog_term : Real.log (Real.log (B : ℝ) / Real.log (A : ℝ)) ≤
      (u₂ - u₁) / u₁ + 2 / (u₁ * Real.log w) := by
    have hrat_pos : 0 < Real.log (B : ℝ) / Real.log (A : ℝ) := div_pos hlogB_pos hlogA_pos
    have hle1 : Real.log (Real.log (B : ℝ) / Real.log (A : ℝ)) ≤
        Real.log (u₂ / u₁) + Real.log (u₁ * Real.log w / Real.log (A : ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      apply Real.log_le_log hrat_pos
      have heq : u₂ / u₁ * (u₁ * Real.log w / Real.log (A : ℝ)) = u₂ * Real.log w / Real.log (A : ℝ) := by
        have : u₁ ≠ 0 := by linarith
        field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right hlogB_le hlogA_pos.le
    have hlog_u : Real.log (u₂ / u₁) ≤ (u₂ - u₁) / u₁ := by
      have h := Real.log_le_sub_one_of_pos (show 0 < u₂ / u₁ by positivity)
      have heq : u₂ / u₁ - 1 = (u₂ - u₁) / u₁ := by
        have : u₁ ≠ 0 := by linarith
        field_simp
      linarith
    have hlog_err : Real.log (u₁ * Real.log w / Real.log (A : ℝ)) ≤ 2 / (u₁ * Real.log w) := by
      have h := Real.log_le_sub_one_of_pos (show 0 < u₁ * Real.log w / Real.log (A : ℝ) by positivity)
      have heq : u₁ * Real.log w / Real.log (A : ℝ) - 1 =
          (u₁ * Real.log w - Real.log (A : ℝ)) / Real.log (A : ℝ) := by
        field_simp
      rw [heq] at h
      have hbd : (u₁ * Real.log w - Real.log (A : ℝ)) / Real.log (A : ℝ) ≤ 2 / (u₁ * Real.log w) := by
        by_cases hnn : 0 ≤ u₁ * Real.log w - Real.log (A : ℝ)
        · calc (u₁ * Real.log w - Real.log (A : ℝ)) / Real.log (A : ℝ)
              ≤ (2 / w ^ u₁) / Real.log (A : ℝ) := div_le_div_of_nonneg_right (by linarith) hlogA_pos.le
            _ ≤ (2 / w ^ u₁) / (u₁ * Real.log w / 2) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hlogA_half
            _ = 4 / (w ^ u₁ * (u₁ * Real.log w)) := by field_simp; ring
            _ ≤ 4 / (4 * (u₁ * Real.log w)) :=
                div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
            _ = 1 / (u₁ * Real.log w) := by ring
            _ ≤ 2 / (u₁ * Real.log w) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
        · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hnn) hlogA_pos.le).trans (by positivity)
      linarith
    linarith
  have herr_term : 2 * CM / Real.log (A : ℝ) ≤ 4 * CM / (u₁ * Real.log w) := by
    have hpos_cm : 0 ≤ CM := CM_pos.le
    calc 2 * CM / Real.log (A : ℝ)
        ≤ 2 * CM / (u₁ * Real.log w / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlogA_half
      _ = 4 * CM / (u₁ * Real.log w) := by ring
  have hadd : (4 * CM + 2) / (u₁ * Real.log w) =
      2 / (u₁ * Real.log w) + 4 * CM / (u₁ * Real.log w) := by ring
  linarith

/-- Real-exponent lower bound on `∑_{p ∈ P, u₁ < e(p) < u₂} e(p) / p` using Mertens first theorem. -/
lemma sum_e_div_p_ge {w z u₁ u₂ : ℝ} (hw : 4 ≤ w) (hu₁ : 1 ≤ u₁) (hu12 : u₁ < u₂)
    (hz : w ^ u₂ ≤ z) :
    (u₂ - u₁) - (2 * CM + 1) / Real.log w ≤
      ∑ p ∈ ((Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime).filter
        (fun p : ℕ => u₁ < Real.log (p : ℝ) / Real.log w ∧ Real.log (p : ℝ) / Real.log w < u₂),
        (Real.log (p : ℝ) / Real.log w) / (p : ℝ) := by
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hwpos : 0 < w := by linarith
  have hwu1 : 4 ≤ w ^ u₁ := by
    calc (4 : ℝ) = 4 ^ (1 : ℝ) := (Real.rpow_one 4).symm
      _ ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hw (by norm_num)
      _ ≤ w ^ u₁ := Real.rpow_le_rpow_of_exponent_le (by linarith) hu₁
  have hwu2 : 4 < w ^ u₂ := hwu1.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by linarith) hu12)
  let A : ℕ := ⌊w ^ u₁⌋₊
  let B : ℕ := ⌈w ^ u₂⌉₊ - 1
  have hceil_pos : 4 ≤ ⌈w ^ u₂⌉₊ := by
    have : (4 : ℝ) < (⌈w ^ u₂⌉₊ : ℝ) := hwu2.trans_le (Nat.le_ceil _)
    exact_mod_cast this.le
  have hBr_ge : w ^ u₂ - 1 ≤ (B : ℝ) := by
    have h1 : ((B : ℕ) : ℝ) = (⌈w ^ u₂⌉₊ : ℝ) - 1 := by
      dsimp [B]; rw [Nat.cast_sub (by omega)]; simp
    rw [h1]
    linarith [Nat.le_ceil (w ^ u₂)]
  have hBr_lt : (B : ℝ) < w ^ u₂ := by
    have h1 : ((B : ℕ) : ℝ) = (⌈w ^ u₂⌉₊ : ℝ) - 1 := by
      dsimp [B]; rw [Nat.cast_sub (by omega)]; simp
    rw [h1]
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ w ^ u₂ by positivity)
    linarith
  by_cases hAB : A ≤ B
  · have hsub : (Finset.Ioc A B).filter Nat.Prime ⊆
        ((Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime).filter
          (fun p : ℕ => u₁ < Real.log (p : ℝ) / Real.log w ∧ Real.log (p : ℝ) / Real.log w < u₂) := by
      intro p hp
      obtain ⟨hIoc, hpp⟩ := mem_filter.mp hp
      obtain ⟨hAp, hpB⟩ := mem_Ioc.mp hIoc
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hgt : w ^ u₁ < (p : ℝ) := (Nat.floor_lt (by positivity)).mp hAp
      have hlt : (p : ℝ) < w ^ u₂ := lt_of_le_of_lt (by exact_mod_cast hpB) hBr_lt
      have hw_lt_p : w < (p : ℝ) := by
        have : w ≤ w ^ u₁ := by
          calc w = w ^ (1 : ℝ) := (Real.rpow_one w).symm
            _ ≤ w ^ u₁ := Real.rpow_le_rpow_of_exponent_le (by linarith) hu₁
        linarith
      have hp_lo : ⌊w⌋₊ + 1 ≤ p := Nat.succ_le_of_lt ((Nat.floor_lt hwpos.le).mpr hw_lt_p)
      have hp_hi : p ≤ ⌊z⌋₊ := Nat.le_floor (hlt.le.trans hz)
      have he_lo : u₁ < Real.log (p : ℝ) / Real.log w := by
        rw [lt_div_iff₀ hlw]
        have := Real.log_lt_log (by positivity) hgt
        rwa [Real.log_rpow hwpos] at this
      have he_hi : Real.log (p : ℝ) / Real.log w < u₂ := by
        rw [div_lt_iff₀ hlw]
        have := Real.log_lt_log hppos hlt
        rwa [Real.log_rpow hwpos] at this
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp_lo, hp_hi⟩, hpp⟩, he_lo, he_hi⟩
    have hsum_ge :
        (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) / Real.log w ≤
          ∑ p ∈ ((Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime).filter
            (fun p : ℕ => u₁ < Real.log (p : ℝ) / Real.log w ∧ Real.log (p : ℝ) / Real.log w < u₂),
            (Real.log (p : ℝ) / Real.log w) / (p : ℝ) := by
      rw [Finset.sum_div]
      have hsub_le := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (Real.log (p : ℝ) / Real.log w) / (p : ℝ)) hsub (fun p hp _ => by
        have hpp := (mem_filter.mp (mem_filter.mp hp).1).2
        have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
        positivity)
      have hcongr : ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (Real.log (p : ℝ) / (p : ℝ)) / Real.log w =
          ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (Real.log (p : ℝ) / Real.log w) / (p : ℝ) := by
        apply Finset.sum_congr rfl
        intro p _
        ring
      rw [hcongr]
      exact hsub_le
    have hm := sum_log_div_p_Ioc_ge hAB
    have hApos : (0 : ℝ) < A := by
      have : 4 ≤ A := Nat.le_floor hwu1
      exact_mod_cast (show 0 < A by omega)
    have hlogA_le : Real.log (A : ℝ) ≤ u₁ * Real.log w := by
      calc Real.log (A : ℝ) ≤ Real.log (w ^ u₁) := Real.log_le_log hApos (Nat.floor_le (by positivity))
        _ = u₁ * Real.log w := Real.log_rpow hwpos u₁
    have hlogB_ge : u₂ * Real.log w - 1 ≤ Real.log (B : ℝ) := by
      have hpos : 0 < 1 - (w ^ u₂)⁻¹ := by
        have : (w ^ u₂)⁻¹ ≤ 1 / 4 := by
          rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hwu2.le
        linarith
      have hB_ge_mul : w ^ u₂ * (1 - (w ^ u₂)⁻¹) ≤ (B : ℝ) := by
        have : w ^ u₂ * (1 - (w ^ u₂)⁻¹) = w ^ u₂ - 1 := by
          have : w ^ u₂ ≠ 0 := by positivity
          field_simp
        linarith
      have h1 : Real.log (w ^ u₂) + Real.log (1 - (w ^ u₂)⁻¹) ≤ Real.log (B : ℝ) := by
        rw [← Real.log_mul (by positivity) hpos.ne']
        exact Real.log_le_log (by positivity) hB_ge_mul
      have h2 : -1 ≤ Real.log (1 - (w ^ u₂)⁻¹) := by
        have h3 := Real.add_one_le_exp (-Real.log (1 - (w ^ u₂)⁻¹))
        rw [Real.exp_neg, Real.exp_log hpos] at h3
        have h4 : (1 - (w ^ u₂)⁻¹)⁻¹ ≤ 2 := by
          rw [inv_le_iff_one_le_mul₀ hpos]
          have : (w ^ u₂)⁻¹ ≤ 1 / 4 := by
            rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hwu2.le
          linarith
        linarith
      rw [Real.log_rpow hwpos] at h1
      linarith
    have hnum : (u₂ - u₁) * Real.log w - (2 * CM + 1) ≤
        ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
      linarith
    have hdiv := div_le_div_of_nonneg_right hnum hlw.le
    have hlhs : ((u₂ - u₁) * Real.log w - (2 * CM + 1)) / Real.log w =
        (u₂ - u₁) - (2 * CM + 1) / Real.log w := by
      field_simp
    linarith
  · have hBA : (B : ℝ) < (A : ℝ) := by exact_mod_cast (show B < A by omega)
    have hAle : (A : ℝ) ≤ w ^ u₁ := Nat.floor_le (by positivity)
    have hdiff_w : w ^ u₂ - w ^ u₁ < 1 := by linarith
    have hdiff_u : u₂ - u₁ ≤ 1 / Real.log w := by
      have h1 : w ^ u₁ * (1 + (u₂ - u₁) * Real.log w) ≤ w ^ u₂ := by
        have heq : w ^ u₂ = w ^ u₁ * Real.exp ((u₂ - u₁) * Real.log w) := by
          rw [Real.rpow_def_of_pos hwpos, Real.rpow_def_of_pos hwpos, ← Real.exp_add]
          congr 1; ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp ((u₂ - u₁) * Real.log w)])
          (by positivity)
      have h2 : 4 * ((u₂ - u₁) * Real.log w) ≤ w ^ u₁ * ((u₂ - u₁) * Real.log w) :=
        mul_le_mul_of_nonneg_right hwu1 (mul_nonneg (sub_nonneg.mpr hu12.le) hlw.le)
      have h3 : (u₂ - u₁) * Real.log w ≤ 1 := by nlinarith
      exact (le_div_iff₀ hlw).mpr h3
    have hsum_nn : 0 ≤ ∑ p ∈ ((Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime).filter
        (fun p : ℕ => u₁ < Real.log (p : ℝ) / Real.log w ∧ Real.log (p : ℝ) / Real.log w < u₂),
        (Real.log (p : ℝ) / Real.log w) / (p : ℝ) := by
      apply Finset.sum_nonneg
      intro p hp
      have hpp := (mem_filter.mp (mem_filter.mp hp).1).2
      have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      positivity
    have hcm_nn : 0 ≤ 2 * CM / Real.log w := div_nonneg (by linarith [CM_pos]) hlw.le
    have hsplit : (2 * CM + 1) / Real.log w = 2 * CM / Real.log w + 1 / Real.log w := by ring
    linarith

lemma one_sub_inv_inv_le_exp_two {p : ℕ} (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * (p : ℝ)⁻¹) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hinv_le : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  have h1sub_pos : 0 < 1 - (p : ℝ)⁻¹ := by linarith
  have h1 : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 1 + 2 * (p : ℝ)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ h1sub_pos]
    have hsq : (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ * (p : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hinv_le (by positivity)
    nlinarith
  exact h1.trans (by linarith [Real.add_one_le_exp (2 * (p : ℝ)⁻¹)])

lemma eulerProd_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
  have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  linarith

/-- Euler product ratio bound for `2 ≤ A ≤ B`: `V(A) ≤ exp(2 * (log(log B / log A) + 2*CM / log A)) * V(B)`. -/
lemma eulerProd_ratio_le {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ∏ p ∈ (Finset.range (A + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) ≤
      Real.exp (2 * (Real.log (Real.log B / Real.log A) + 2 * CM / Real.log A)) *
        ∏ p ∈ (Finset.range (B + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  let QA := (Finset.range (A + 1)).filter Nat.Prime
  let QB := (Finset.range (B + 1)).filter Nat.Prime
  let Qdiff := (Finset.Ioc A B).filter Nat.Prime
  have hunion : QB = QA ∪ Qdiff := by
    ext p
    simp only [QB, QA, Qdiff, mem_union, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hpB, hpp⟩
      by_cases hpA : p ≤ A
      · exact Or.inl ⟨by omega, hpp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hpp⟩
    · rintro (⟨hpA, hpp⟩ | ⟨⟨_, hpB⟩, hpp⟩)
      · exact ⟨by omega, hpp⟩
      · exact ⟨by omega, hpp⟩
  have hdisj : Disjoint QA Qdiff := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have := mem_range.mp (mem_filter.mp h1).1
    have := (mem_Ioc.mp (mem_filter.mp h2).1).1
    omega
  have hprod : ∏ p ∈ QB, (1 - (p : ℝ)⁻¹) =
      (∏ p ∈ QA, (1 - (p : ℝ)⁻¹)) * ∏ p ∈ Qdiff, (1 - (p : ℝ)⁻¹) := by
    rw [hunion, Finset.prod_union hdisj]
  have hQA_pos : 0 < ∏ p ∈ QA, (1 - (p : ℝ)⁻¹) :=
    eulerProd_pos QA (fun _ hp => (mem_filter.mp hp).2)
  have hQdiff_pos : 0 < ∏ p ∈ Qdiff, (1 - (p : ℝ)⁻¹) :=
    eulerProd_pos Qdiff (fun _ hp => (mem_filter.mp hp).2)
  have hinv_le : (∏ p ∈ Qdiff, (1 - (p : ℝ)⁻¹))⁻¹ ≤
      Real.exp (2 * ∑ p ∈ Qdiff, (p : ℝ)⁻¹) := by
    rw [← Finset.prod_inv_distrib, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
      have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · intro p hp
      exact one_sub_inv_inv_le_exp_two (mem_filter.mp hp).2.two_le
  have hm := sum_inv_p_Ioc_le hA hAB
  have hexp_le : Real.exp (2 * ∑ p ∈ Qdiff, (p : ℝ)⁻¹) ≤
      Real.exp (2 * (Real.log (Real.log B / Real.log A) + 2 * CM / Real.log A)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hle := hinv_le.trans hexp_le
  calc ∏ p ∈ QA, (1 - (p : ℝ)⁻¹)
      = (∏ p ∈ Qdiff, (1 - (p : ℝ)⁻¹))⁻¹ * ((∏ p ∈ QA, (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ Qdiff, (1 - (p : ℝ)⁻¹)) := by
        rw [mul_left_comm, inv_mul_cancel₀ hQdiff_pos.ne', mul_one]
    _ = (∏ p ∈ Qdiff, (1 - (p : ℝ)⁻¹))⁻¹ * ∏ p ∈ QB, (1 - (p : ℝ)⁻¹) := by rw [← hprod]
    _ ≤ Real.exp (2 * (Real.log (Real.log B / Real.log A) + 2 * CM / Real.log A)) *
          ∏ p ∈ QB, (1 - (p : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hle (mul_pos hQA_pos hQdiff_pos |> fun h => by rw [← hprod] at h; exact h.le)

end Erdos687H2.Mertens

namespace Erdos687H2.TreeMass
open Finset Real Erdos687H2.Mertens
open scoped Classical

/-
# Elementary `r²/y` barrier for admissible prime-tree reciprocal sums

For the tree `T` of subsets `d ⊆ P` (primes in `(w, z]`) satisfying the even-prefix
admission rule `max (2 e(p)) (e(p) + 2) ≤ g(d.filter (p ≤ ·))`, we prove:
1. Every `d ∈ T` satisfies `2 ≤ g(d)`.
2. The depth tail `∑_{|d| ≥ K} (D d)⁻¹` decays super-polynomially in `B = log z / log w`.
3. By pure algebraic induction on depth `2m ≤ 20 log B`, the reciprocal weight of `d ∈ T`
   with `min(d) = p` and `g(d) ∈ (a, a + Δ]` (`Δ = 1 / log w`) is bounded by
   `(C_m / B^2) * ((a + Δ)^3 - a^3) / (3 * e(p))` with `C_m = C₁ * (1 + C₃ / log w)^m`.
4. Summing over `p ∈ P` and slabs `(a_i, a_i + Δ]` yields both the compact mass bound
   `B^2 * ∑_{d ∈ T, g d ≤ k} (D d)⁻¹ ≤ C_small(k)` and the uniform exponential tail bound
   `B^2 * ∑_{d ∈ T, k < g d} (D d)⁻¹ * exp (-c * g d) ≤ η` for large `k`.
-/

noncomputable def pExp (w : ℝ) (p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log w

noncomputable def prodR (d : Finset ℕ) : ℝ := ∏ p ∈ d, (p : ℝ)

noncomputable def gapOf (w G : ℝ) (d : Finset ℕ) : ℝ := G - ∑ p ∈ d, pExp w p

noncomputable def primeSet (w z : ℝ) : Finset ℕ :=
  (Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime

noncomputable def admTree (w z G : ℝ) : Finset (Finset ℕ) :=
  (primeSet w z).powerset.filter fun d => ∀ p ∈ d,
    let A := d.filter (p ≤ ·)
    Even A.card → max (2 * pExp w p) (pExp w p + 2) ≤ gapOf w G A

noncomputable def cubicQ (a Δ : ℝ) : ℝ := ((a + Δ) ^ 3 - a ^ 3) / 3

lemma cubicQ_eq (a Δ : ℝ) : cubicQ a Δ = Δ * (a ^ 2 + a * Δ + Δ ^ 2 / 3) := by
  unfold cubicQ; ring

lemma cubicQ_nonneg {a Δ : ℝ} (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) : 0 ≤ cubicQ a Δ := by
  rw [cubicQ_eq]; positivity

lemma cubicQ_ge_mul_sq {a Δ : ℝ} (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) : Δ * a ^ 2 ≤ cubicQ a Δ := by
  rw [cubicQ_eq]; nlinarith [sq_nonneg Δ]

lemma cubicQ_le_mul_sq {a Δ : ℝ} (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) : cubicQ a Δ ≤ Δ * (a + Δ) ^ 2 := by
  rw [cubicQ_eq]; nlinarith [sq_nonneg Δ]

lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s₁ s₂ : Finset α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ (∑ x ∈ s₁, f x) + ∑ x ∈ s₂, f x := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have hnn : 0 ≤ ∑ x ∈ s₁ ∩ s₂, f x := Finset.sum_nonneg (fun x _ => hf x)
  linarith

lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β] {s : Finset α} {t : α → Finset β} {f : β → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (sum_union_le_of_nonneg hf).trans (add_le_add le_rfl ih)

lemma mem_primeSet_spec {w z : ℝ} (hw : 1 < w) {p : ℕ} (hp : p ∈ primeSet w z) :
    p.Prime ∧ w < (p : ℝ) ∧ (p : ℝ) ≤ z ∧ 1 < pExp w p ∧ pExp w p ≤ Real.log z / Real.log w := by
  obtain ⟨hIcc, hpp⟩ := mem_filter.mp hp
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hIcc
  have hw0 : 0 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw
  have hwp : w < (p : ℝ) := by
    have : ⌊w⌋₊ < p := by omega
    exact (Nat.floor_lt hw0.le).mp this
  have hpz : (p : ℝ) ≤ z := by
    have hz0 : 0 ≤ z := by
      have : (⌊w⌋₊ + 1 : ℕ) ≤ ⌊z⌋₊ := hlo.trans hhi
      by_contra hlt
      push Not at hlt
      have : ⌊z⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.le_floor_iff hz0).mp hhi
  have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have he1 : 1 < pExp w p := by
    unfold pExp
    rw [one_lt_div hlw]
    exact Real.log_lt_log hw0 hwp
  have heB : pExp w p ≤ Real.log z / Real.log w := by
    unfold pExp
    exact div_le_div_of_nonneg_right (Real.log_le_log hppos hpz) hlw.le
  exact ⟨hpp, hwp, hpz, he1, heB⟩

lemma prodR_pos {w z : ℝ} (hw : 1 < w) {d : Finset ℕ} (hd : d ⊆ primeSet w z) :
    0 < prodR d := by
  unfold prodR
  apply Finset.prod_pos
  intro p hp
  exact_mod_cast (mem_primeSet_spec hw (hd hp)).1.pos

lemma gapOf_erase {w G : ℝ} {d : Finset ℕ} {p : ℕ} (hp : p ∈ d) :
    gapOf w G d = gapOf w G (d.erase p) - pExp w p := by
  unfold gapOf
  rw [← Finset.add_sum_erase _ _ hp]
  ring

lemma admTree_erase_min {w z G : ℝ} {d : Finset ℕ} (hd : d ∈ admTree w z G) (hne : d.Nonempty) :
    d.erase (d.min' hne) ∈ admTree w z G := by
  obtain ⟨hsub, hadm⟩ := mem_filter.mp hd
  have hsub' : d.erase (d.min' hne) ∈ (primeSet w z).powerset :=
    mem_powerset.mpr ((Finset.erase_subset _ _).trans (mem_powerset.mp hsub))
  refine mem_filter.mpr ⟨hsub', fun q hq => ?_⟩
  have hqd : q ∈ d := Finset.mem_of_mem_erase hq
  have hmin_lt : d.min' hne < q :=
    lt_of_le_of_ne (Finset.min'_le d q hqd) (Ne.symm (Finset.ne_of_mem_erase hq))
  have hfilt : (d.erase (d.min' hne)).filter (q ≤ ·) = d.filter (q ≤ ·) := by
    ext x
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hx⟩, hqx⟩; exact ⟨hx, hqx⟩
    · rintro ⟨hx, hqx⟩; exact ⟨⟨by omega, hx⟩, hqx⟩
  rw [hfilt]
  exact hadm q hqd

lemma admTree_gap_ge_two {w z G : ℝ} (hw : 1 < w) (hB : 20 ≤ Real.log z / Real.log w)
    (hG : (19 : ℝ) / 10 * (Real.log z / Real.log w) ≤ G)
    {d : Finset ℕ} (hd : d ∈ admTree w z G) :
    2 ≤ gapOf w G d := by
  obtain ⟨hpow, hadm⟩ := mem_filter.mp hd
  have hsub : d ⊆ primeSet w z := mem_powerset.mp hpow
  rcases d.eq_empty_or_nonempty with rfl | hne
  · simp only [gapOf, Finset.sum_empty, sub_zero]
    linarith
  · by_cases heven : Even d.card
    · let p := d.min' hne
      have hp : p ∈ d := Finset.min'_mem d hne
      have hfilt : d.filter (p ≤ ·) = d := by
        ext x; simp only [mem_filter, and_iff_left_iff_imp]
        intro hx; exact Finset.min'_le d x hx
      have h1 := hadm p hp
      rw [hfilt] at h1
      have h2 := h1 heven
      have hep : 1 < pExp w p := (mem_primeSet_spec hw (hsub hp)).2.2.2.1
      linarith [le_max_right (2 * pExp w p) (pExp w p + 2)]
    · let p := d.min' hne
      have hp : p ∈ d := Finset.min'_mem d hne
      let d' := d.erase p
      rcases d'.eq_empty_or_nonempty with hd'e | hd'ne
      · have hdeq : d = {p} := by
          ext x
          simp only [mem_singleton]
          constructor
          · intro hx
            by_contra hne_xp
            have : x ∈ d' := mem_erase.mpr ⟨hne_xp, hx⟩
            rw [hd'e] at this; exact Finset.notMem_empty x this
          · rintro rfl; exact hp
        rw [hdeq]
        unfold gapOf
        rw [Finset.sum_singleton]
        have hep : pExp w p ≤ Real.log z / Real.log w := (mem_primeSet_spec hw (hsub hp)).2.2.2.2
        linarith
      · let q := d'.min' hd'ne
        have hqd' : q ∈ d' := Finset.min'_mem d' hd'ne
        have hqd : q ∈ d := Finset.mem_of_mem_erase hqd'
        have hpq : p < q := lt_of_le_of_ne (Finset.min'_le d q hqd) (Ne.symm (Finset.ne_of_mem_erase hqd'))
        have hfilt : d.filter (q ≤ ·) = d' := by
          ext x
          simp only [d', mem_filter, mem_erase]
          constructor
          · rintro ⟨hx, hqx⟩; exact ⟨by omega, hx⟩
          · rintro ⟨hxp, hx⟩
            have hxd' : x ∈ d' := mem_erase.mpr ⟨hxp, hx⟩
            exact ⟨hx, Finset.min'_le d' x hxd'⟩
        have heven' : Even d'.card := by
          have hc : d'.card + 1 = d.card := Finset.card_erase_add_one hp
          rw [Nat.even_iff] at heven ⊢
          omega
        have h1 := hadm q hqd
        rw [hfilt] at h1
        have h2 := h1 heven'
        have h3 : pExp w q + 2 ≤ gapOf w G d' := (le_max_right _ _).trans h2
        have hlw : 0 < Real.log w := Real.log_pos hw
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast (mem_primeSet_spec hw (hsub hp)).1.pos
        have hep_lt : pExp w p < pExp w q := by
          unfold pExp
          exact div_lt_div_of_pos_right (Real.log_lt_log hp_pos (by exact_mod_cast hpq)) hlw
        rw [gapOf_erase hp]
        linarith

/-- Factorial upper bound on fixed-cardinality reciprocal sums. -/
lemma sum_powersetCard_inv_prod_le (S : Finset ℕ) (k : ℕ) :
    ∑ d ∈ S.powersetCard k, (prodR d)⁻¹ ≤
      (∑ p ∈ S, (p : ℝ)⁻¹) ^ k / (k.factorial : ℝ) := by
  induction k with
  | zero =>
    simp [prodR]
  | succ k ih =>
    have hmul : ((k + 1 : ℕ) : ℝ) * ∑ d ∈ S.powersetCard (k + 1), (prodR d)⁻¹ ≤
        (∑ p ∈ S, (p : ℝ)⁻¹) * ((∑ p ∈ S, (p : ℝ)⁻¹) ^ k / (k.factorial : ℝ)) := by
      have hcard_eq : ((k + 1 : ℕ) : ℝ) * ∑ d ∈ S.powersetCard (k + 1), (prodR d)⁻¹ =
          ∑ d ∈ S.powersetCard (k + 1), ∑ p ∈ d, (p : ℝ)⁻¹ * (prodR (d.erase p))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hcard : d.card = k + 1 := (mem_powersetCard.mp hd).2
        have hterm : ∀ p ∈ d, (p : ℝ)⁻¹ * (prodR (d.erase p))⁻¹ = (prodR d)⁻¹ := by
          intro p hp
          unfold prodR
          rw [← mul_inv, Finset.mul_prod_erase d (fun q => (q : ℝ)) hp]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcard]
      rw [hcard_eq]
      have hswap : ∑ d ∈ S.powersetCard (k + 1), ∑ p ∈ d, (p : ℝ)⁻¹ * (prodR (d.erase p))⁻¹ =
          ∑ p ∈ S, (p : ℝ)⁻¹ * ∑ d' ∈ (S.erase p).powersetCard k, (prodR d')⁻¹ := by
        rw [Finset.sum_sigma']
        have hrhs : ∑ p ∈ S, (p : ℝ)⁻¹ * ∑ d' ∈ (S.erase p).powersetCard k, (prodR d')⁻¹ =
            ∑ x ∈ S.sigma (fun p => (S.erase p).powersetCard k), (x.1 : ℝ)⁻¹ * (prodR x.2)⁻¹ := by
          have h1 : ∑ p ∈ S, (p : ℝ)⁻¹ * ∑ d' ∈ (S.erase p).powersetCard k, (prodR d')⁻¹ =
              ∑ p ∈ S, ∑ d' ∈ (S.erase p).powersetCard k, (p : ℝ)⁻¹ * (prodR d')⁻¹ := by
            apply Finset.sum_congr rfl; intro p _; rw [Finset.mul_sum]
          rw [h1, Finset.sum_sigma']
        rw [hrhs]
        refine Finset.sum_bij (fun x _ => ⟨x.2, x.1.erase x.2⟩) ?_ ?_ ?_ ?_
        · rintro ⟨d, p⟩ hx
          obtain ⟨hd, hp⟩ := Finset.mem_sigma.mp hx
          obtain ⟨hdS, hcard⟩ := mem_powersetCard.mp hd
          refine Finset.mem_sigma.mpr ⟨hdS hp, mem_powersetCard.mpr ⟨?_, ?_⟩⟩
          · intro q hq
            exact mem_erase.mpr ⟨Finset.ne_of_mem_erase hq, hdS (Finset.mem_of_mem_erase hq)⟩
          · rw [Finset.card_erase_of_mem hp, hcard]; simp
        · rintro ⟨d₁, p₁⟩ h₁ ⟨d₂, p₂⟩ h₂ heq
          obtain ⟨_, hp₁⟩ := Finset.mem_sigma.mp h₁
          obtain ⟨_, hp₂⟩ := Finset.mem_sigma.mp h₂
          dsimp only at hp₁ hp₂ heq
          have hp_eq : p₁ = p₂ := congrArg Sigma.fst heq
          subst hp_eq
          have hd_eq : d₁.erase p₁ = d₂.erase p₁ := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
          have : d₁ = d₂ := by
            rw [← Finset.insert_erase hp₁, ← Finset.insert_erase hp₂, hd_eq]
          subst this
          rfl
        · rintro ⟨p, d'⟩ hy
          obtain ⟨hpS, hd'⟩ := Finset.mem_sigma.mp hy
          obtain ⟨hd'sub, hcard'⟩ := mem_powersetCard.mp hd'
          have hpnot : p ∉ d' := fun h => (mem_erase.mp (hd'sub h)).1 rfl
          refine ⟨⟨insert p d', p⟩, Finset.mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, mem_insert_self p d'⟩, ?_⟩
          · exact Finset.insert_subset hpS (hd'sub.trans (Finset.erase_subset p S))
          · rw [Finset.card_insert_of_notMem hpnot, hcard']
          · simp [Finset.erase_insert hpnot]
        · rintro ⟨d, p⟩ _
          rfl
      rw [hswap, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hsub : (S.erase p).powersetCard k ⊆ S.powersetCard k :=
        Finset.powersetCard_mono (Finset.erase_subset p S)
      exact (Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (prodR d)⁻¹) hsub (fun d _ _ => by
        unfold prodR; positivity)).trans ih
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((k + 1).factorial : ℝ))]
    have hfac : ((k + 1).factorial : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have h1 := mul_le_mul_of_nonneg_right hmul hkf.le
    have hlhs : ((k + 1 : ℕ) : ℝ) * (∑ d ∈ S.powersetCard (k + 1), (prodR d)⁻¹) * (k.factorial : ℝ) =
        (∑ d ∈ S.powersetCard (k + 1), (prodR d)⁻¹) * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) := by ring
    have hrhs : (∑ p ∈ S, (p : ℝ)⁻¹) * ((∑ p ∈ S, (p : ℝ)⁻¹) ^ k / (k.factorial : ℝ)) * (k.factorial : ℝ) =
        (∑ p ∈ S, (p : ℝ)⁻¹) ^ (k + 1) := by
      rw [pow_succ']
      field_simp
    linarith

lemma sum_primeSet_inv_le {w z : ℝ} (hw : 4 ≤ w) (hz : 4 ≤ z) (hB : 20 ≤ Real.log z / Real.log w)
    (hlw_cm : 4 * CM + 2 ≤ Real.log w) :
    ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ ≤ 2 * Real.log (Real.log z / Real.log w) := by
  have hw1 : 1 < w := by linarith
  have hw0 : 0 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hBpos : 0 < Real.log z / Real.log w := by linarith
  have hle_wz : w ≤ z := by
    have h1 : Real.log w < Real.log z := by
      have := (le_div_iff₀ hlw).mp hB; linarith
    by_contra hlt
    push Not at hlt
    have : Real.log z ≤ Real.log w := Real.log_le_log (by linarith) hlt.le
    linarith
  let A : ℕ := ⌊w⌋₊
  let B_nat : ℕ := ⌊z⌋₊
  have hA4 : 4 ≤ A := Nat.le_floor hw
  have hAB : A ≤ B_nat := Nat.floor_mono hle_wz
  have hsub : primeSet w z ⊆ (Finset.Ioc A B_nat).filter Nat.Prime := by
    intro p hp
    obtain ⟨hIcc, hpp⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hIcc
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hhi⟩, hpp⟩
  have h1 : ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ ≤ ∑ p ∈ (Finset.Ioc A B_nat).filter Nat.Prime, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (p : ℝ)⁻¹) hsub (fun _ _ _ => by positivity)
  have hm := sum_inv_p_Ioc_le (by omega : 2 ≤ A) hAB
  have hlogA_ge : Real.log w - 2 / w ≤ Real.log (A : ℝ) := by
    have h := log_floor_rpow_ge hw (le_refl (1 : ℝ))
    simpa [Real.rpow_one] using h
  have hlogA_pos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogA_half : Real.log w / 2 ≤ Real.log (A : ℝ) := by
    have hlw1 : 1 ≤ Real.log w := by
      have : Real.exp 1 ≤ w := by linarith [Real.exp_one_lt_d9]
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
    have : 2 / w ≤ 1 / 2 := by rw [div_le_div_iff₀ hw0 (by norm_num)]; linarith
    linarith
  have hlogB_le : Real.log (B_nat : ℝ) ≤ Real.log z := by
    have hBpos' : (0 : ℝ) < B_nat := by exact_mod_cast (show 0 < B_nat by omega)
    exact Real.log_le_log hBpos' (Nat.floor_le (by linarith))
  have hlogB_pos : 0 < Real.log (B_nat : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B_nat by omega))
  have hrat : Real.log (Real.log (B_nat : ℝ) / Real.log (A : ℝ)) ≤
      Real.log (Real.log z / Real.log w) + Real.log 2 := by
    rw [← Real.log_mul hBpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    apply Real.log_le_log (div_pos hlogB_pos hlogA_pos)
    calc Real.log (B_nat : ℝ) / Real.log (A : ℝ)
        ≤ Real.log z / Real.log (A : ℝ) := div_le_div_of_nonneg_right hlogB_le hlogA_pos.le
      _ ≤ Real.log z / (Real.log w / 2) := div_le_div_of_nonneg_left (by nlinarith) (by positivity) hlogA_half
      _ = Real.log z / Real.log w * 2 := by ring
  have herr : 2 * CM / Real.log (A : ℝ) ≤ 1 := by
    have hcm0 : 0 ≤ CM := CM_pos.le
    calc 2 * CM / Real.log (A : ℝ)
        ≤ 2 * CM / (Real.log w / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hlogA_half
      _ = 4 * CM / Real.log w := by ring
      _ ≤ 1 := (div_le_one hlw).mpr (by linarith)
  have hlog20 : 2 ≤ Real.log (Real.log z / Real.log w) := by
    have he2 : Real.exp 2 ≤ 20 := by
      have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have := Real.log_le_log (Real.exp_pos 2) (he2.trans hB)
    rwa [Real.log_exp] at this
  have hlog2_lt : Real.log 2 < 1 := by
    have : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have := Real.log_lt_log (by norm_num) this
    rwa [Real.log_exp] at this
  linarith

/-- Depth cutoff: subsets of `primeSet w z` with cardinality `≥ 2 * M` (for `M = ⌈10 * log B⌉₊`)
have total reciprocal weight at most `2 / B^3`. -/
lemma sum_large_card_le {w z : ℝ} (hw : 4 ≤ w) (hz : 4 ≤ z) (hB : 20 ≤ Real.log z / Real.log w)
    (hlw_cm : 4 * CM + 2 ≤ Real.log w) :
    let B := Real.log z / Real.log w
    let M := ⌈10 * Real.log B⌉₊
    ∑ d ∈ (primeSet w z).powerset.filter (fun d => 2 * M ≤ d.card), (prodR d)⁻¹ ≤ 2 / B ^ 3 := by
  intro B M
  let K := 2 * M
  have hBpos : 0 < B := by linarith
  have hlogB_ge2 : 2 ≤ Real.log B := by
    have he2 : Real.exp 2 ≤ 20 := by
      have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have := Real.log_le_log (Real.exp_pos 2) (he2.trans hB)
    rwa [Real.log_exp] at this
  have hS : ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ ≤ 2 * Real.log B := sum_primeSet_inv_le hw hz hB hlw_cm
  have hS_nn : 0 ≤ ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hK_ge : 20 * Real.log B ≤ (K : ℝ) := by
    have hM : 10 * Real.log B ≤ (M : ℝ) := Nat.le_ceil _
    dsimp [K]; push_cast; linarith
  let N := (primeSet w z).card
  have hpart : (primeSet w z).powerset.filter (fun d => K ≤ d.card) =
      (Finset.Icc K N).biUnion (fun k => (primeSet w z).powersetCard k) := by
    ext d
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_Icc, mem_powersetCard]
    constructor
    · rintro ⟨hd, hK⟩
      exact ⟨d.card, ⟨hK, Finset.card_le_card hd⟩, hd, rfl⟩
    · rintro ⟨k, ⟨hK, _⟩, hd, rfl⟩
      exact ⟨hd, hK⟩
  have hpw : (Finset.Icc K N : Set ℕ).PairwiseDisjoint (fun k => (primeSet w z).powersetCard k) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro d hi hj
    exact hij ((mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2)
  rw [hpart, Finset.sum_biUnion hpw]
  have hterm : ∀ k ∈ Finset.Icc K N,
      ∑ d ∈ (primeSet w z).powersetCard k, (prodR d)⁻¹ ≤ (1 / 3 : ℝ) ^ k := by
    intro k hk
    have hkK : K ≤ k := (mem_Icc.mp hk).1
    have hk_ge : 20 * Real.log B ≤ (k : ℝ) := hK_ge.trans (by exact_mod_cast hkK)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
    have h1 := sum_powersetCard_inv_prod_le (primeSet w z) k
    have hpow_le : (∑ p ∈ primeSet w z, (p : ℝ)⁻¹) ^ k ≤ (2 * Real.log B) ^ k :=
      pow_le_pow_left₀ hS_nn hS k
    have hfac_ge : ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
      have hlog := log_factorial_ge k
      have hpos_f : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
      have h2 := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log hpos_f] at h2
      have h3 : Real.exp ((k : ℝ) * Real.log (k : ℝ) - (k : ℝ)) = ((k : ℝ) / Real.exp 1) ^ k := by
        rw [div_pow, ← Real.exp_nat_mul, mul_one, Real.exp_sub, Real.exp_nat_mul, Real.exp_log hk_pos]
      rw [← h3]; exact h2
    have hdiv : (2 * Real.log B) ^ k / (k.factorial : ℝ) ≤ (1 / 3 : ℝ) ^ k := by
      calc (2 * Real.log B) ^ k / (k.factorial : ℝ)
          ≤ (2 * Real.log B) ^ k / ((k : ℝ) / Real.exp 1) ^ k :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hfac_ge
        _ = (2 * Real.log B * Real.exp 1 / (k : ℝ)) ^ k := by
            rw [← div_pow]; congr 1; field_simp
        _ ≤ (1 / 3 : ℝ) ^ k := by
            apply pow_le_pow_left₀ (by positivity)
            rw [div_le_div_iff₀ hk_pos (by norm_num)]
            have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
            nlinarith
    exact h1.trans ((div_le_div_of_nonneg_right hpow_le (by positivity)).trans hdiv)
  calc ∑ k ∈ Finset.Icc K N, ∑ d ∈ (primeSet w z).powersetCard k, (prodR d)⁻¹
      ≤ ∑ k ∈ Finset.Icc K N, (1 / 3 : ℝ) ^ k := Finset.sum_le_sum hterm
    _ ≤ (3 / 2 : ℝ) * (1 / 3 : ℝ) ^ K := by
        by_cases hKN : K ≤ N
        · have hgeom : ∑ k ∈ Finset.Icc K N, (1 / 3 : ℝ) ^ k =
              (1 / 3 : ℝ) ^ K * ∑ j ∈ Finset.range (N - K + 1), (1 / 3 : ℝ) ^ j := by
            rw [Finset.mul_sum]
            refine Finset.sum_bij (fun k _ => k - K) ?_ ?_ ?_ ?_
            · intro k hk; rw [mem_range]; have := mem_Icc.mp hk; omega
            · intro k₁ h₁ k₂ h₂ heq
              have := (mem_Icc.mp h₁).1; have := (mem_Icc.mp h₂).1; omega
            · intro j hj
              refine ⟨K + j, mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩, by omega⟩
            · intro k hk
              have hkK : K ≤ k := (mem_Icc.mp hk).1
              rw [← pow_add, Nat.add_sub_cancel' hkK]
          rw [hgeom, geom_sum_eq (by norm_num : (1 / 3 : ℝ) ≠ 1)]
          have hnn : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ (N - K + 1) := by positivity
          have h1 : ((1 / 3 : ℝ) ^ (N - K + 1) - 1) / ((1 / 3 : ℝ) - 1) ≤ 3 / 2 := by
            have heq : ((1 / 3 : ℝ) ^ (N - K + 1) - 1) / ((1 / 3 : ℝ) - 1) =
                3 / 2 * (1 - (1 / 3 : ℝ) ^ (N - K + 1)) := by ring
            rw [heq]; linarith
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) K]
        · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
          positivity
    _ ≤ 2 / B ^ 3 := by
        have h3_ge : Real.exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
        have hpow3 : Real.exp (K : ℝ) ≤ (3 : ℝ) ^ K := by
          have : Real.exp (K : ℝ) = (Real.exp 1) ^ K := by rw [← Real.exp_nat_mul, mul_one]
          rw [this]
          exact pow_le_pow_left₀ (Real.exp_pos 1).le h3_ge K
        have hinv3 : (1 / 3 : ℝ) ^ K ≤ Real.exp (-(K : ℝ)) := by
          rw [one_div, inv_pow, Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) hpow3
        have hB3 : B ^ 3 ≤ Real.exp (K : ℝ) := by
          have h1 : B ^ 3 = Real.exp (3 * Real.log B) := by
            rw [mul_comm, Real.exp_mul, Real.exp_log hBpos]; norm_cast
          rw [h1]
          exact Real.exp_le_exp.mpr (by linarith)
        have h1 : (1 / 3 : ℝ) ^ K ≤ 1 / B ^ 3 := by
          refine hinv3.trans ?_
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ (by positivity) hB3
        have h2 : (0 : ℝ) ≤ 1 / B ^ 3 := by positivity
        linarith [show (2 : ℝ) / B ^ 3 = 2 * (1 / B ^ 3) by ring]

/-
## Exact depth-bounded barrier induction on `evenMass` and `oddMass`
-/

noncomputable def evenMass (w z G : ℝ) (m : ℕ) (a Δ : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) * ∑ d ∈ (admTree w z G).filter (fun d =>
    Even d.card ∧ 2 ≤ d.card ∧ d.card ≤ 2 * m ∧
    (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ), (prodR d)⁻¹

noncomputable def oddMass (w z G : ℝ) (m : ℕ) (a Δ : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) * ∑ d ∈ (admTree w z G).filter (fun d =>
    ¬ Even d.card ∧ 3 ≤ d.card ∧ d.card ≤ 2 * m + 1 ∧
    (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ), (prodR d)⁻¹

noncomputable def evenMassTwo (w z G : ℝ) (a Δ : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) * ∑ d ∈ (admTree w z G).filter (fun d =>
    d.card = 2 ∧
    (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ), (prodR d)⁻¹

lemma evenMass_zero_of_out {w z G : ℝ} (hw : 1 < w) (m : ℕ) (a Δ : ℝ) {p : ℕ}
    (hp : p ∈ primeSet w z) (h : G - 2 * pExp w p ≤ a ∨ a + Δ < 2 * pExp w p) :
    evenMass w z G m a Δ p = 0 := by
  unfold evenMass
  have hEmpty : (admTree w z G).filter (fun d =>
      Even d.card ∧ 2 ≤ d.card ∧ d.card ≤ 2 * m ∧
      (∃ hne : d.Nonempty, d.min' hne = p) ∧
      a < gapOf w G d ∧ gapOf w G d ≤ a + Δ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd hcond
    rcases hcond with ⟨heven, hcard2, _, ⟨hne, hmin⟩, hga, hgb⟩
    obtain ⟨hpow, hadm⟩ := mem_filter.mp hd
    have hsub : d ⊆ primeSet w z := mem_powerset.mp hpow
    have hpd : p ∈ d := hmin ▸ Finset.min'_mem d hne
    rcases h with h1 | h2
    · have hex : ∃ q ∈ d, p < q := by
        have hne' : (d.erase p).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hpd]; omega
        obtain ⟨q, hq⟩ := hne'
        have hqd : q ∈ d := Finset.mem_of_mem_erase hq
        have hne_qp : q ≠ p := Finset.ne_of_mem_erase hq
        have hle : p ≤ q := hmin ▸ Finset.min'_le d q hqd
        exact ⟨q, hqd, lt_of_le_of_ne hle hne_qp.symm⟩
      obtain ⟨q, hqd, hpq⟩ := hex
      have hlw : 0 < Real.log w := Real.log_pos hw
      have hppos : (0 : ℝ) < p := by exact_mod_cast (mem_primeSet_spec hw hp).1.pos
      have hep_lt : pExp w p < pExp w q := by
        unfold pExp
        exact div_lt_div_of_pos_right (Real.log_lt_log hppos (by exact_mod_cast hpq)) hlw
      have hsub2 : ({p, q} : Finset ℕ) ⊆ d := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
      have hsum_ge : pExp w p + pExp w q ≤ ∑ x ∈ d, pExp w x := by
        have hnn : ∀ x ∈ d, 0 ≤ pExp w x := fun x hx => by
          have := (mem_primeSet_spec hw (hsub hx)).2.2.2.1; linarith
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := pExp w) hsub2 (fun x hx _ => hnn x hx)
        rwa [Finset.sum_pair (by omega : p ≠ q)] at this
      unfold gapOf at hga
      linarith
    · have hfilt : d.filter (p ≤ ·) = d := by
        ext x; simp only [mem_filter, and_iff_left_iff_imp]
        intro hx; exact hmin ▸ Finset.min'_le d x hx
      have h3 := hadm p hpd
      rw [hfilt] at h3
      have h4 : 2 * pExp w p ≤ gapOf w G d := (le_max_left _ _).trans (h3 heven)
      linarith
  rw [hEmpty, Finset.sum_empty, mul_zero]

lemma oddMass_zero_of_out {w z G : ℝ} (hw : 1 < w) (m : ℕ) (a Δ : ℝ) {p : ℕ}
    (hp : p ∈ primeSet w z) (h : G - 3 * pExp w p ≤ a ∨ a + Δ ≤ pExp w p) :
    oddMass w z G m a Δ p = 0 := by
  unfold oddMass
  have hEmpty : (admTree w z G).filter (fun d =>
      ¬ Even d.card ∧ 3 ≤ d.card ∧ d.card ≤ 2 * m + 1 ∧
      (∃ hne : d.Nonempty, d.min' hne = p) ∧
      a < gapOf w G d ∧ gapOf w G d ≤ a + Δ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd hcond
    rcases hcond with ⟨hodd, hcard3, _, ⟨hne, hmin⟩, hga, hgb⟩
    obtain ⟨hpow, hadm⟩ := mem_filter.mp hd
    have hsub : d ⊆ primeSet w z := mem_powerset.mp hpow
    have hpd : p ∈ d := hmin ▸ Finset.min'_mem d hne
    have hlw : 0 < Real.log w := Real.log_pos hw
    have hppos : (0 : ℝ) < p := by exact_mod_cast (mem_primeSet_spec hw hp).1.pos
    rcases h with h1 | h2
    · have hsum_gt : 3 * pExp w p < ∑ x ∈ d, pExp w x := by
        have hcard_er : 2 ≤ (d.erase p).card := by
          rw [Finset.card_erase_of_mem hpd]; omega
        have hne1 : (d.erase p).Nonempty := Finset.card_pos.mp (by omega)
        let q₁ := (d.erase p).min' hne1
        have hq₁_er : q₁ ∈ d.erase p := Finset.min'_mem _ hne1
        have hq₁ : q₁ ∈ d := Finset.mem_of_mem_erase hq₁_er
        have hne2 : ((d.erase p).erase q₁).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hq₁_er]; omega
        obtain ⟨q₂, hq₂_er2⟩ := hne2
        have hq₂_er : q₂ ∈ d.erase p := Finset.mem_of_mem_erase hq₂_er2
        have hq₂ : q₂ ∈ d := Finset.mem_of_mem_erase hq₂_er
        have hpq₁ : p < q₁ := lt_of_le_of_ne (hmin ▸ Finset.min'_le d q₁ hq₁)
          (Ne.symm (Finset.ne_of_mem_erase hq₁_er))
        have hpq₂ : p < q₂ := lt_of_le_of_ne (hmin ▸ Finset.min'_le d q₂ hq₂)
          (Ne.symm (Finset.ne_of_mem_erase hq₂_er))
        have hq₁q₂ : q₁ ≠ q₂ := Ne.symm (Finset.ne_of_mem_erase hq₂_er2)
        have he1 : pExp w p < pExp w q₁ := by
          unfold pExp; exact div_lt_div_of_pos_right (Real.log_lt_log hppos (by exact_mod_cast hpq₁)) hlw
        have he2 : pExp w p < pExp w q₂ := by
          unfold pExp; exact div_lt_div_of_pos_right (Real.log_lt_log hppos (by exact_mod_cast hpq₂)) hlw
        have hsub3 : ({p, q₁, q₂} : Finset ℕ) ⊆ d := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have hsum3 : ∑ x ∈ ({p, q₁, q₂} : Finset ℕ), pExp w x = pExp w p + pExp w q₁ + pExp w q₂ := by
          rw [Finset.sum_insert (by simp; omega), Finset.sum_pair hq₁q₂]; ring
        have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := pExp w) hsub3 (fun x hx _ => by
          have := (mem_primeSet_spec hw (hsub hx)).2.2.2.1; linarith)
        linarith
      unfold gapOf at hga
      linarith
    · let d' := d.erase p
      have hd'ne : d'.Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hpd]; omega
      let q := d'.min' hd'ne
      have hqd' : q ∈ d' := Finset.min'_mem d' hd'ne
      have hqd : q ∈ d := Finset.mem_of_mem_erase hqd'
      have hpq : p < q := lt_of_le_of_ne (hmin ▸ Finset.min'_le d q hqd)
        (Ne.symm (Finset.ne_of_mem_erase hqd'))
      have hfilt : d.filter (q ≤ ·) = d' := by
        ext x; simp only [d', mem_filter, mem_erase]
        constructor
        · rintro ⟨hx, hqx⟩; exact ⟨by omega, hx⟩
        · rintro ⟨hxp, hx⟩; exact ⟨hx, Finset.min'_le d' x (mem_erase.mpr ⟨hxp, hx⟩)⟩
      have heven' : Even d'.card := by
        have hc : d'.card + 1 = d.card := Finset.card_erase_add_one hpd
        rw [Nat.even_iff] at hodd ⊢; omega
      have h3 := hadm q hqd
      rw [hfilt] at h3
      have h4 : 2 * pExp w q ≤ gapOf w G d' := (le_max_left _ _).trans (h3 heven')
      have he_lt : pExp w p < pExp w q := by
        unfold pExp; exact div_lt_div_of_pos_right (Real.log_lt_log hppos (by exact_mod_cast hpq)) hlw
      rw [gapOf_erase hpd] at hgb
      linarith
  rw [hEmpty, Finset.sum_empty, mul_zero]

/-- Exact parent expansion for odd depth `3 ≤ d.card ≤ 2m + 1`. -/
lemma oddMass_le_sum_evenMass {w z G : ℝ} (hw : 1 < w) (m : ℕ) (a Δ : ℝ) {p : ℕ}
    (hp : p ∈ primeSet w z) :
    oddMass w z G m a Δ p ≤
      ∑ q ∈ (primeSet w z).filter (p < ·),
        (q : ℝ)⁻¹ * evenMass w z G m (a + pExp w p) Δ q := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw hp).1.pos
  let S_odd := (admTree w z G).filter (fun d =>
    ¬ Even d.card ∧ 3 ≤ d.card ∧ d.card ≤ 2 * m + 1 ∧
    (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)
  let S_even : ℕ → Finset (Finset ℕ) := fun q => (admTree w z G).filter (fun d' =>
    Even d'.card ∧ 2 ≤ d'.card ∧ d'.card ≤ 2 * m ∧
    (∃ hne : d'.Nonempty, d'.min' hne = q) ∧
    a + pExp w p < gapOf w G d' ∧ gapOf w G d' ≤ a + pExp w p + Δ)
  unfold oddMass evenMass
  have hpw : (((primeSet w z).filter (p < ·) : Finset ℕ) : Set ℕ).PairwiseDisjoint S_even := by
    intro q₁ _ q₂ _ hne_q
    rw [Function.onFun, Finset.disjoint_left]
    intro d' h1 h2
    obtain ⟨_, _, _, _, ⟨hne₁, hm₁⟩, _, _⟩ := mem_filter.mp h1
    obtain ⟨_, _, _, _, ⟨hne₂, hm₂⟩, _, _⟩ := mem_filter.mp h2
    exact hne_q (hm₁.symm.trans hm₂)
  have hrhs : ∑ q ∈ (primeSet w z).filter (p < ·),
      (q : ℝ)⁻¹ * ((q : ℝ) * ∑ d' ∈ S_even q, (prodR d')⁻¹) =
      ∑ d' ∈ ((primeSet w z).filter (p < ·)).biUnion S_even, (prodR d')⁻¹ := by
    rw [Finset.sum_biUnion hpw]
    apply Finset.sum_congr rfl
    intro q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (mem_primeSet_spec hw (mem_filter.mp hq).1).1.pos
    rw [← mul_assoc, inv_mul_cancel₀ hq_pos.ne', one_mul]
  rw [hrhs, Finset.mul_sum]
  have hinj_map : ∀ d ∈ S_odd, d.erase p ∈ ((primeSet w z).filter (p < ·)).biUnion S_even ∧
      (p : ℝ) * (prodR d)⁻¹ = (prodR (d.erase p))⁻¹ := by
    intro d hd
    obtain ⟨hdT, hodd, hcard3, hcardhi, ⟨hne, hmin⟩, hga, hgb⟩ := mem_filter.mp hd
    have hsub : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
    have hpd : p ∈ d := hmin ▸ Finset.min'_mem d hne
    have hd'T : d.erase p ∈ admTree w z G := by
      rw [← hmin]; exact admTree_erase_min hdT hne
    have hd'card : (d.erase p).card + 1 = d.card := Finset.card_erase_add_one hpd
    have hd'ne : (d.erase p).Nonempty := Finset.card_pos.mp (by omega)
    let q := (d.erase p).min' hd'ne
    have hqd' : q ∈ d.erase p := Finset.min'_mem (d.erase p) hd'ne
    have hqd : q ∈ d := Finset.mem_of_mem_erase hqd'
    have hpq : p < q := lt_of_le_of_ne (hmin ▸ Finset.min'_le d q hqd)
      (Ne.symm (Finset.ne_of_mem_erase hqd'))
    refine ⟨mem_biUnion.mpr ⟨q, mem_filter.mpr ⟨hsub hqd, hpq⟩,
      mem_filter.mpr ⟨hd'T, ?_, by omega, by omega, ⟨hd'ne, rfl⟩, ?_, ?_⟩⟩, ?_⟩
    · rw [Nat.even_iff] at hodd ⊢; omega
    · rw [gapOf_erase hpd] at hga; linarith
    · rw [gapOf_erase hpd] at hgb; linarith
    · unfold prodR
      rw [← Finset.mul_prod_erase d (fun x => (x : ℝ)) hpd, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ hp_pos.ne', one_mul]
  have hsum_eq' : ∑ d ∈ S_odd, (p : ℝ) * (prodR d)⁻¹ = ∑ d ∈ S_odd, (prodR (d.erase p))⁻¹ :=
    Finset.sum_congr rfl (fun d hd => (hinj_map d hd).2)
  rw [hsum_eq']
  have hsum_img : ∑ d ∈ S_odd, (prodR (d.erase p))⁻¹ =
      ∑ d' ∈ S_odd.image (fun d => d.erase p), (prodR d')⁻¹ := by
    symm
    refine Finset.sum_image ?_
    intro d₁ h₁ d₂ h₂ heq
    obtain ⟨hne₁, hmin₁⟩ := (mem_filter.mp h₁).2.2.2.2.1
    obtain ⟨hne₂, hmin₂⟩ := (mem_filter.mp h₂).2.2.2.2.1
    have hp₁ : p ∈ d₁ := hmin₁ ▸ Finset.min'_mem d₁ hne₁
    have hp₂ : p ∈ d₂ := hmin₂ ▸ Finset.min'_mem d₂ hne₂
    dsimp only at heq
    rw [← Finset.insert_erase hp₁, ← Finset.insert_erase hp₂, heq]
  have himg_sub : S_odd.image (fun d => d.erase p) ⊆ ((primeSet w z).filter (p < ·)).biUnion S_even := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hd'
    exact (hinj_map d hd).1
  rw [hsum_img]
  exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun d' => (prodR d')⁻¹)
    himg_sub (fun d' _ _ => by unfold prodR; positivity)

/-- Exact parent decomposition for even depth `2 ≤ d.card ≤ 2(m + 1)`. -/
lemma evenMass_succ_le {w z G : ℝ} (hw : 1 < w) (m : ℕ) (a Δ : ℝ) {p : ℕ}
    (hp : p ∈ primeSet w z) :
    evenMass w z G (m + 1) a Δ p ≤
      evenMassTwo w z G a Δ p +
      ∑ q ∈ (primeSet w z).filter (p < ·),
        (q : ℝ)⁻¹ * oddMass w z G m (a + pExp w p) Δ q := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw hp).1.pos
  let S_all := (admTree w z G).filter (fun d =>
    Even d.card ∧ 2 ≤ d.card ∧ d.card ≤ 2 * (m + 1) ∧
    (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)
  let S_two := (admTree w z G).filter (fun d =>
    d.card = 2 ∧
    (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)
  let S_ge4 := (admTree w z G).filter (fun d =>
    Even d.card ∧ 4 ≤ d.card ∧ d.card ≤ 2 * (m + 1) ∧
    (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)
  have hsplit : S_all = S_two ∪ S_ge4 := by
    ext d
    simp only [S_all, S_two, S_ge4, mem_union, mem_filter]
    constructor
    · rintro ⟨hd, hev, h2, hhi, hmin, hga, hgb⟩
      rcases eq_or_lt_of_le h2 with hc2 | hcgt
      · exact Or.inl ⟨hd, hc2.symm, hmin, hga, hgb⟩
      · have h4 : 4 ≤ d.card := by rw [Nat.even_iff] at hev; omega
        exact Or.inr ⟨hd, hev, h4, hhi, hmin, hga, hgb⟩
    · rintro (⟨hd, hc2, hmin, hga, hgb⟩ | ⟨hd, hev, h4, hhi, hmin, hga, hgb⟩)
      · exact ⟨hd, by rw [hc2]; exact even_two, by omega, by omega, hmin, hga, hgb⟩
      · exact ⟨hd, hev, by omega, hhi, hmin, hga, hgb⟩
  have hdisj : Disjoint S_two S_ge4 := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    have := (mem_filter.mp h1).2.1
    have := (mem_filter.mp h2).2.2.1
    omega
  unfold evenMass evenMassTwo oddMass
  change (p : ℝ) * ∑ d ∈ S_all, (prodR d)⁻¹ ≤
    (p : ℝ) * ∑ d ∈ S_two, (prodR d)⁻¹ + _
  rw [hsplit, Finset.sum_union hdisj, mul_add]
  refine add_le_add le_rfl ?_
  let S_odd : ℕ → Finset (Finset ℕ) := fun q => (admTree w z G).filter (fun d' =>
    ¬ Even d'.card ∧ 3 ≤ d'.card ∧ d'.card ≤ 2 * m + 1 ∧
    (∃ hne : d'.Nonempty, d'.min' hne = q) ∧
    a + pExp w p < gapOf w G d' ∧ gapOf w G d' ≤ a + pExp w p + Δ)
  have hpw : (((primeSet w z).filter (p < ·) : Finset ℕ) : Set ℕ).PairwiseDisjoint S_odd := by
    intro q₁ _ q₂ _ hne_q
    rw [Function.onFun, Finset.disjoint_left]
    intro d' h1 h2
    obtain ⟨_, _, _, _, ⟨hne₁, hm₁⟩, _, _⟩ := mem_filter.mp h1
    obtain ⟨_, _, _, _, ⟨hne₂, hm₂⟩, _, _⟩ := mem_filter.mp h2
    exact hne_q (hm₁.symm.trans hm₂)
  have hrhs : ∑ q ∈ (primeSet w z).filter (p < ·),
      (q : ℝ)⁻¹ * ((q : ℝ) * ∑ d' ∈ S_odd q, (prodR d')⁻¹) =
      ∑ d' ∈ ((primeSet w z).filter (p < ·)).biUnion S_odd, (prodR d')⁻¹ := by
    rw [Finset.sum_biUnion hpw]
    apply Finset.sum_congr rfl
    intro q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (mem_primeSet_spec hw (mem_filter.mp hq).1).1.pos
    rw [← mul_assoc, inv_mul_cancel₀ hq_pos.ne', one_mul]
  rw [hrhs, Finset.mul_sum]
  have hinj_map : ∀ d ∈ S_ge4, d.erase p ∈ ((primeSet w z).filter (p < ·)).biUnion S_odd ∧
      (p : ℝ) * (prodR d)⁻¹ = (prodR (d.erase p))⁻¹ := by
    intro d hd
    obtain ⟨hdT, heven, hcard4, hcardhi, ⟨hne, hmin⟩, hga, hgb⟩ := mem_filter.mp hd
    have hsub : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
    have hpd : p ∈ d := hmin ▸ Finset.min'_mem d hne
    have hd'T : d.erase p ∈ admTree w z G := by
      rw [← hmin]; exact admTree_erase_min hdT hne
    have hd'card : (d.erase p).card + 1 = d.card := Finset.card_erase_add_one hpd
    have hd'ne : (d.erase p).Nonempty := Finset.card_pos.mp (by omega)
    let q := (d.erase p).min' hd'ne
    have hqd' : q ∈ d.erase p := Finset.min'_mem (d.erase p) hd'ne
    have hqd : q ∈ d := Finset.mem_of_mem_erase hqd'
    have hpq : p < q := lt_of_le_of_ne (hmin ▸ Finset.min'_le d q hqd)
      (Ne.symm (Finset.ne_of_mem_erase hqd'))
    refine ⟨mem_biUnion.mpr ⟨q, mem_filter.mpr ⟨hsub hqd, hpq⟩,
      mem_filter.mpr ⟨hd'T, ?_, by omega, by omega, ⟨hd'ne, rfl⟩, ?_, ?_⟩⟩, ?_⟩
    · rw [Nat.even_iff] at heven ⊢; omega
    · rw [gapOf_erase hpd] at hga; linarith
    · rw [gapOf_erase hpd] at hgb; linarith
    · unfold prodR
      rw [← Finset.mul_prod_erase d (fun x => (x : ℝ)) hpd, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ hp_pos.ne', one_mul]
  have hsum_eq' : ∑ d ∈ S_ge4, (p : ℝ) * (prodR d)⁻¹ = ∑ d ∈ S_ge4, (prodR (d.erase p))⁻¹ :=
    Finset.sum_congr rfl (fun d hd => (hinj_map d hd).2)
  rw [hsum_eq']
  have hsum_img : ∑ d ∈ S_ge4, (prodR (d.erase p))⁻¹ =
      ∑ d' ∈ S_ge4.image (fun d => d.erase p), (prodR d')⁻¹ := by
    symm
    refine Finset.sum_image ?_
    intro d₁ h₁ d₂ h₂ heq
    obtain ⟨hne₁, hmin₁⟩ := (mem_filter.mp h₁).2.2.2.2.1
    obtain ⟨hne₂, hmin₂⟩ := (mem_filter.mp h₂).2.2.2.2.1
    have hp₁ : p ∈ d₁ := hmin₁ ▸ Finset.min'_mem d₁ hne₁
    have hp₂ : p ∈ d₂ := hmin₂ ▸ Finset.min'_mem d₂ hne₂
    dsimp only at heq
    rw [← Finset.insert_erase hp₁, ← Finset.insert_erase hp₂, heq]
  have himg_sub : S_ge4.image (fun d => d.erase p) ⊆ ((primeSet w z).filter (p < ·)).biUnion S_odd := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hd'
    exact (hinj_map d hd).1
  rw [hsum_img]
  exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun d' => (prodR d')⁻¹)
    himg_sub (fun d' _ _ => by unfold prodR; positivity)

/-- Depth-2 bound: `E_2(a, Δ; p) = 0` when `a + Δ + y < G - B`, and otherwise
`E_2(a, Δ; p) ≤ (4*CM + 4) * Δ / max(y, G - a - Δ - y)`. -/
lemma evenMassTwo_eq_zero_of_lt {w z G : ℝ} (hw : 1 < w) (a Δ : ℝ) {p : ℕ}
    (h : a + Δ + pExp w p < G - Real.log z / Real.log w) :
    evenMassTwo w z G a Δ p = 0 := by
  unfold evenMassTwo
  have hEmpty : (admTree w z G).filter (fun d =>
      d.card = 2 ∧ (∃ hne : d.Nonempty, d.min' hne = p) ∧
      a < gapOf w G d ∧ gapOf w G d ≤ a + Δ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd hcond
    rcases hcond with ⟨hcard2, ⟨hne, hmin⟩, _, hgb⟩
    have hsub : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hd).1
    have hpd : p ∈ d := hmin ▸ Finset.min'_mem d hne
    have hcard_er : (d.erase p).card = 1 := by rw [Finset.card_erase_of_mem hpd, hcard2]
    obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hcard_er
    have hq_er : q ∈ d.erase p := by rw [hq_eq]; exact mem_singleton_self q
    have hqd : q ∈ d := Finset.mem_of_mem_erase hq_er
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq_er
    have hdeq : d = {p, q} := by rw [← Finset.insert_erase hpd, hq_eq]
    have hgap : gapOf w G d = G - (pExp w p + pExp w q) := by
      unfold gapOf; rw [hdeq, Finset.sum_pair hqp.symm]
    have heq_le : pExp w q ≤ Real.log z / Real.log w := (mem_primeSet_spec hw (hsub hqd)).2.2.2.2
    linarith
  rw [hEmpty, Finset.sum_empty, mul_zero]

lemma evenMassTwo_le {w z : ℝ} (G : ℝ) (hw : 4 ≤ w) (a : ℝ) {p : ℕ} (hp : p ∈ primeSet w z) :
    let Δ := 1 / Real.log w
    evenMassTwo w z G a Δ p ≤
      (4 * CM + 4) * Δ / max (pExp w p) (G - a - Δ - pExp w p) := by
  intro Δ
  have hw1 : 1 < w := by linarith
  have hw0 : 0 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hp_spec := mem_primeSet_spec hw1 hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_spec.1.pos
  have hy1 : 1 < pExp w p := hp_spec.2.2.2.1
  let y := pExp w p
  let u₁ := max y (G - a - Δ - y)
  let u₂ := G - a - y
  have hu₁_ge1 : 1 ≤ u₁ := le_trans hy1.le (le_max_left _ _)
  have hu₁_pos : 0 < u₁ := by linarith
  let S_two := (admTree w z G).filter (fun d =>
    d.card = 2 ∧ (∃ hne : d.Nonempty, d.min' hne = p) ∧
    a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)
  let Q_all := (primeSet w z).filter (fun q => u₁ ≤ pExp w q ∧ pExp w q ≤ u₂)
  let Q_gt := Q_all.filter (fun q => u₁ < pExp w q)
  let Q_eq := Q_all.filter (fun q => pExp w q = u₁)
  by_cases h12 : u₁ ≤ u₂
  · have hsum_le : evenMassTwo w z G a Δ p ≤ ∑ q ∈ Q_all, (q : ℝ)⁻¹ := by
      unfold evenMassTwo
      change (p : ℝ) * ∑ d ∈ S_two, (prodR d)⁻¹ ≤ ∑ q ∈ Q_all, (q : ℝ)⁻¹
      rw [Finset.mul_sum]
      have hmap : ∀ d ∈ S_two, ∃ q ∈ Q_all, d = {p, q} ∧ p < q ∧ (p : ℝ) * (prodR d)⁻¹ = (q : ℝ)⁻¹ := by
        intro d hd
        obtain ⟨hdT, hcard2, ⟨hne, hmin⟩, hga, hgb⟩ := mem_filter.mp hd
        have hsub : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
        have hpd : p ∈ d := hmin ▸ Finset.min'_mem d hne
        have hcard_er : (d.erase p).card = 1 := by rw [Finset.card_erase_of_mem hpd, hcard2]
        obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hcard_er
        have hq_er : q ∈ d.erase p := by rw [hq_eq]; exact mem_singleton_self q
        have hqd : q ∈ d := Finset.mem_of_mem_erase hq_er
        have hpq : p < q := lt_of_le_of_ne (hmin ▸ Finset.min'_le d q hqd)
          (Ne.symm (Finset.ne_of_mem_erase hq_er))
        have hdeq : d = {p, q} := by rw [← Finset.insert_erase hpd, hq_eq]
        have hgap : gapOf w G d = G - (y + pExp w q) := by
          unfold gapOf; rw [hdeq, Finset.sum_pair (by omega : p ≠ q)]
        have hy_lt_q : y < pExp w q := by
          unfold y pExp
          exact div_lt_div_of_pos_right (Real.log_lt_log hp_pos (by exact_mod_cast hpq)) hlw
        have hu1_le : u₁ ≤ pExp w q := max_le hy_lt_q.le (by linarith)
        have hle_u2 : pExp w q ≤ u₂ := by linarith
        refine ⟨q, mem_filter.mpr ⟨hsub hqd, hu1_le, hle_u2⟩, hdeq, hpq, ?_⟩
        unfold prodR
        rw [hdeq, Finset.prod_pair (by omega : p ≠ q), mul_inv, ← mul_assoc,
          mul_inv_cancel₀ hp_pos.ne', one_mul]
      let f_q : Finset ℕ → ℕ := fun d => if h : (d.erase p).Nonempty then (d.erase p).min' h else 0
      have himg_sub : S_two.image f_q ⊆ Q_all := by
        intro q hq
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hq
        obtain ⟨q', hq'Q, hdeq, hpq', _⟩ := hmap d hd
        have her : d.erase p = {q'} := by rw [hdeq, Finset.erase_insert (by simp; omega)]
        have hf : f_q d = q' := by dsimp [f_q]; rw [her]; simp
        rwa [hf]
      have hcongr : ∑ d ∈ S_two, (p : ℝ) * (prodR d)⁻¹ = ∑ d ∈ S_two, (f_q d : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨q', _, hdeq, hpq', hval⟩ := hmap d hd
        have her : d.erase p = {q'} := by rw [hdeq, Finset.erase_insert (by simp; omega)]
        have hf : f_q d = q' := by dsimp [f_q]; rw [her]; simp
        rw [hf, hval]
      rw [hcongr]
      have hbij : ∑ d ∈ S_two, (f_q d : ℝ)⁻¹ = ∑ q ∈ S_two.image f_q, (q : ℝ)⁻¹ := by
        symm
        refine Finset.sum_image ?_
        intro d₁ h₁ d₂ h₂ heq
        obtain ⟨q₁, _, hd₁, hpq₁, _⟩ := hmap d₁ h₁
        obtain ⟨q₂, _, hd₂, hpq₂, _⟩ := hmap d₂ h₂
        have hf1 : f_q d₁ = q₁ := by dsimp [f_q]; rw [hd₁, Finset.erase_insert (by simp; omega)]; simp
        have hf2 : f_q d₂ = q₂ := by dsimp [f_q]; rw [hd₂, Finset.erase_insert (by simp; omega)]; simp
        rw [hf1, hf2] at heq
        rw [hd₁, hd₂, heq]
      rw [hbij]
      exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (q : ℝ)⁻¹)
        himg_sub (fun _ _ _ => by positivity)
    -- Split `Q_all` into `Q_gt` and `Q_eq`
    have hQ_sub : Q_all ⊆ Q_gt ∪ Q_eq := by
      intro q hq
      have hlo := (mem_filter.mp hq).2.1
      rcases eq_or_lt_of_le hlo with heq | hlt
      · exact mem_union_right _ (mem_filter.mpr ⟨hq, heq.symm⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hq, hlt⟩)
    have hQ_split : ∑ q ∈ Q_all, (q : ℝ)⁻¹ ≤ (∑ q ∈ Q_gt, (q : ℝ)⁻¹) + ∑ q ∈ Q_eq, (q : ℝ)⁻¹ :=
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (q : ℝ)⁻¹) hQ_sub
        (fun _ _ _ => by positivity)).trans (sum_union_le_of_nonneg (f := fun q : ℕ => (q : ℝ)⁻¹) (fun _ => by positivity))
    -- `Q_eq` has at most 1 element, whose reciprocal is ≤ Δ / u₁
    have hQ_eq_le : ∑ q ∈ Q_eq, (q : ℝ)⁻¹ ≤ Δ / u₁ := by
      have hcard_le1 : Q_eq.card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro q₁ h₁ q₂ h₂
        have he1 := (mem_filter.mp h₁).2
        have he2 := (mem_filter.mp h₂).2
        have hp1 : (0 : ℝ) < (q₁ : ℝ) := by
          exact_mod_cast (mem_primeSet_spec hw1 (mem_filter.mp (mem_filter.mp h₁).1).1).1.pos
        have hp2 : (0 : ℝ) < (q₂ : ℝ) := by
          exact_mod_cast (mem_primeSet_spec hw1 (mem_filter.mp (mem_filter.mp h₂).1).1).1.pos
        have hlog_eq : Real.log (q₁ : ℝ) = Real.log (q₂ : ℝ) := by
          unfold pExp at he1 he2
          have := he1.trans he2.symm
          exact (div_left_inj' hlw.ne').mp this
        exact_mod_cast (Real.log_injOn_pos hp1 hp2 hlog_eq)
      rcases Q_eq.eq_empty_or_nonempty with hEmp | ⟨q, hq⟩
      · rw [hEmp, Finset.sum_empty]; positivity
      · have hsing : Q_eq = {q} := Finset.card_le_one.mp hcard_le1 |> fun h =>
          Finset.ext fun x => ⟨fun hx => mem_singleton.mpr (h x hx q hq), fun hx => (mem_singleton.mp hx) ▸ hq⟩
        rw [hsing, Finset.sum_singleton]
        have heq : pExp w q = u₁ := (mem_filter.mp hq).2
        have hqpos : (0 : ℝ) < (q : ℝ) := by
          exact_mod_cast (mem_primeSet_spec hw1 (mem_filter.mp (mem_filter.mp hq).1).1).1.pos
        have hq_ge : Real.log w * u₁ ≤ (q : ℝ) := by
          have h1 : Real.log (q : ℝ) = u₁ * Real.log w := by
            unfold pExp at heq; exact (div_eq_iff hlw.ne').mp heq
          have h2 := Real.add_one_le_exp (Real.log (q : ℝ))
          rw [Real.exp_log hqpos, h1] at h2
          linarith
        dsimp [Δ]
        rw [div_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (mul_pos hlw hu₁_pos) hq_ge
    -- `Q_gt` bounded by `sum_inv_p_e_le`
    have hm := sum_inv_p_e_le hw hu₁_ge1 h12 Q_gt (fun q hq => by
      obtain ⟨hq_all, hgt⟩ := mem_filter.mp hq
      obtain ⟨hqP, _, hhi⟩ := mem_filter.mp hq_all
      exact ⟨(mem_primeSet_spec hw1 hqP).1, hgt, hhi⟩)
    have hdiff : u₂ - u₁ ≤ Δ := by
      have : G - a - Δ - y ≤ u₁ := le_max_right _ _
      dsimp [u₂]; linarith
    have h1 : (u₂ - u₁) / u₁ ≤ Δ / u₁ := div_le_div_of_nonneg_right hdiff hu₁_pos.le
    have h2 : (4 * CM + 2) / (u₁ * Real.log w) = (4 * CM + 2) * Δ / u₁ := by
      dsimp [Δ]; field_simp
    have h3 : Δ / u₁ + (4 * CM + 2) * Δ / u₁ + Δ / u₁ = (4 * CM + 4) * Δ / u₁ := by ring
    linarith
  · have hEmpty : S_two = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd hcond
      rcases hcond with ⟨hcard2, ⟨hne, hmin⟩, hga, hgb⟩
      have hsub : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hd).1
      have hpd : p ∈ d := hmin ▸ Finset.min'_mem d hne
      have hcard_er : (d.erase p).card = 1 := by rw [Finset.card_erase_of_mem hpd, hcard2]
      obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hcard_er
      have hq_er : q ∈ d.erase p := by rw [hq_eq]; exact mem_singleton_self q
      have hqd : q ∈ d := Finset.mem_of_mem_erase hq_er
      have hpq : p < q := lt_of_le_of_ne (hmin ▸ Finset.min'_le d q hqd)
        (Ne.symm (Finset.ne_of_mem_erase hq_er))
      have hdeq : d = {p, q} := by rw [← Finset.insert_erase hpd, hq_eq]
      have hgap : gapOf w G d = G - (y + pExp w q) := by
        unfold gapOf; rw [hdeq, Finset.sum_pair (by omega : p ≠ q)]
      have hy_lt_q : y < pExp w q := by
        unfold y pExp
        exact div_lt_div_of_pos_right (Real.log_lt_log hp_pos (by exact_mod_cast hpq)) hlw
      have hu1_le : u₁ ≤ pExp w q := max_le hy_lt_q.le (by linarith)
      linarith
    unfold evenMassTwo
    change (p : ℝ) * ∑ d ∈ S_two, (prodR d)⁻¹ ≤ _
    rw [hEmpty, Finset.sum_empty, mul_zero]
    have hcm0 : 0 ≤ CM := CM_pos.le
    positivity

/-- Constants for the barrier induction. -/
noncomputable def cA : ℝ := 8 * CM + 4
noncomputable def cDelta : ℝ := 1 + 9 * cA
noncomputable def cStep : ℝ := 4 * cA + (2 * CM + 1) + 8 * cDelta
noncomputable def cInit : ℝ := 8 * (4 * CM + 4)

lemma cInit_pos : 0 < cInit := by unfold cInit; linarith [CM_pos]
lemma cStep_pos : 0 < cStep := by unfold cStep cDelta cA; linarith [CM_pos]

set_option maxHeartbeats 600000 in
/-- Step A of the barrier induction: even depth `2k` implies odd depth `2k + 1`. -/
private lemma oddMass_step_of_even {w z G Ck : ℝ} (hw : 4 ≤ w)
    (hlw_ge : max 4 (cA + 1) ≤ Real.log w)
    (hB : 20 ≤ Real.log z / Real.log w)
    (hCk_pos : 0 < Ck) (k : ℕ)
    (hEven : let B := Real.log z / Real.log w
      let Δ := 1 / Real.log w
      ∀ (a : ℝ), 2 - Δ ≤ a → ∀ p ∈ primeSet w z,
        evenMass w z G k a Δ p ≤
          Ck / B ^ 2 *
            (if 2 * pExp w p ≤ a + Δ ∧ a < G - 2 * pExp w p then cubicQ a Δ / pExp w p else 0)) :
    let B := Real.log z / Real.log w
    let Δ := 1 / Real.log w
    ∀ (a' : ℝ), 2 - Δ ≤ a' → ∀ q ∈ primeSet w z,
      oddMass w z G k a' Δ q ≤
        Ck / B ^ 2 *
          (if pExp w q < a' + Δ ∧ a' < G - 3 * pExp w q then
            max 0 (cubicQ a' Δ / pExp w q - Δ * pExp w q) +
              (cDelta / Real.log w) * (cubicQ a' Δ / pExp w q)
          else 0) := by
  intro B Δ a' ha' q hq
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 4 := by
    dsimp [Δ]; rw [one_div, inv_le_comm₀ hlw (by norm_num)]; norm_num; exact hlw4
  let x := pExp w q
  have hx1 : 1 < x := (mem_primeSet_spec hw1 hq).2.2.2.1
  by_cases hact : x < a' + Δ ∧ a' < G - 3 * x
  · rw [if_pos hact]
    have hstep := oddMass_le_sum_evenMass (G := G) hw1 k a' Δ hq
    let U := (a' + x + Δ) / 2
    have hxU : x < U := by dsimp [U]; linarith
    let S_r := (primeSet w z).filter (fun r => q < r ∧ 2 * pExp w r ≤ a' + x + Δ)
    have hsum_le : ∑ r ∈ (primeSet w z).filter (q < ·),
        (r : ℝ)⁻¹ * evenMass w z G k (a' + x) Δ r ≤
        Ck / B ^ 2 * cubicQ (a' + x) Δ *
          ∑ r ∈ S_r, (1 : ℝ) / ((r : ℝ) * pExp w r) := by
      rw [Finset.mul_sum]
      have h1 : ∑ r ∈ (primeSet w z).filter (q < ·),
          (r : ℝ)⁻¹ * evenMass w z G k (a' + x) Δ r ≤
          ∑ r ∈ (primeSet w z).filter (q < ·),
            (if 2 * pExp w r ≤ a' + x + Δ then
              Ck / B ^ 2 * cubicQ (a' + x) Δ * ((1 : ℝ) / ((r : ℝ) * pExp w r))
            else 0) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrP : r ∈ primeSet w z := (mem_filter.mp hr).1
        have hih := hEven (a' + x) (by linarith) r hrP
        have hmul := mul_le_mul_of_nonneg_left hih (by positivity : (0 : ℝ) ≤ (r : ℝ)⁻¹)
        refine hmul.trans ?_
        split_ifs with h1' h2' h2'
        · apply le_of_eq; ring
        · exfalso; exact h2' h1'.1
        · have ha'x : 0 ≤ a' + x := by linarith
          have hr_pos : 0 < pExp w r := by linarith [(mem_primeSet_spec hw1 hrP).2.2.2.1]
          have hq_nn : 0 ≤ cubicQ (a' + x) Δ := cubicQ_nonneg ha'x hΔ_pos.le
          simp only [mul_zero]; positivity
        · simp
      have h2 : ∑ r ∈ (primeSet w z).filter (q < ·),
          (if 2 * pExp w r ≤ a' + x + Δ then
            Ck / B ^ 2 * cubicQ (a' + x) Δ * ((1 : ℝ) / ((r : ℝ) * pExp w r))
          else 0) =
          ∑ r ∈ S_r, Ck / B ^ 2 * cubicQ (a' + x) Δ * ((1 : ℝ) / ((r : ℝ) * pExp w r)) := by
        rw [← Finset.sum_filter]; congr 1; ext r; simp only [S_r, mem_filter]; tauto
      exact h1.trans_eq h2
    have hS_r_spec : ∀ r ∈ S_r, r.Prime ∧ x < Real.log (r : ℝ) / Real.log w ∧
        Real.log (r : ℝ) / Real.log w ≤ U := by
      intro r hr
      obtain ⟨hrP, hqr, hle⟩ := mem_filter.mp hr
      have hr_spec := mem_primeSet_spec hw1 hrP
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hq).1.pos
      have hx_lt_r : x < Real.log (r : ℝ) / Real.log w := by
        unfold x pExp
        exact div_lt_div_of_pos_right (Real.log_lt_log hq_pos (by exact_mod_cast hqr)) hlw
      exact ⟨hr_spec.1, hx_lt_r, by dsimp [U]; unfold pExp at hle; linarith⟩
    have hm := sum_inv_p_mul_e_le hw hx1.le hxU S_r hS_r_spec
    have hm' : ∑ r ∈ S_r, (1 : ℝ) / ((r : ℝ) * pExp w r) ≤
        (1 / x - 2 / (a' + x + Δ)) + cA / (x ^ 2 * Real.log w) := by
      have heq : 1 / U = 2 / (a' + x + Δ) := by
        dsimp [U]; have : a' + x + Δ ≠ 0 := by linarith
        field_simp
      unfold pExp cA; linarith
    have hq_ax_nn : 0 ≤ cubicQ (a' + x) Δ := cubicQ_nonneg (by linarith) hΔ_pos.le
    have hprod1 : cubicQ (a' + x) Δ * (1 / x - 2 / (a' + x + Δ)) ≤
        max 0 (cubicQ a' Δ / x - Δ * x) + Δ ^ 2 := by
      have hs_pos : 0 < a' + x + Δ := by linarith
      have hdiv_ge : Δ * (a' + x) ≤ cubicQ (a' + x) Δ / (a' + x + Δ) := by
        rw [le_div_iff₀ hs_pos, cubicQ_eq]
        have : Δ ^ 3 / 3 ≥ 0 := by positivity
        nlinarith
      have hstep1 : cubicQ (a' + x) Δ * (1 / x - 2 / (a' + x + Δ)) =
          cubicQ (a' + x) Δ / x - 2 * (cubicQ (a' + x) Δ / (a' + x + Δ)) := by ring
      have hstep2 : cubicQ (a' + x) Δ / x - 2 * (Δ * (a' + x)) =
          (cubicQ a' Δ / x - Δ * x) + Δ ^ 2 := by
        rw [cubicQ_eq, cubicQ_eq]
        have hx0 : x ≠ 0 := by linarith
        field_simp; ring
      have hmax := le_max_right (0 : ℝ) (cubicQ a' Δ / x - Δ * x)
      linarith
    have ha'74 : (7 : ℝ) / 4 ≤ a' := by linarith
    have hx_le : x ≤ a' + 1 / 4 := by linarith
    have hΔ2_le : Δ ^ 2 ≤ Δ * (cubicQ a' Δ / x) := by
      have hq_ge := cubicQ_ge_mul_sq (by linarith : 0 ≤ a') hΔ_pos.le
      have h1 : 1 ≤ a' ^ 2 / x := by rw [le_div_iff₀ (by linarith : 0 < x)]; nlinarith
      have h2 : Δ ≤ cubicQ a' Δ / x := by
        calc Δ = Δ * 1 := by ring
          _ ≤ Δ * (a' ^ 2 / x) := mul_le_mul_of_nonneg_left h1 hΔ_pos.le
          _ = (Δ * a' ^ 2) / x := by ring
          _ ≤ cubicQ a' Δ / x := div_le_div_of_nonneg_right hq_ge (by linarith)
      nlinarith
    have hq9 : cubicQ (a' + x) Δ ≤ 9 * cubicQ a' Δ := by
      rw [cubicQ_eq, cubicQ_eq]
      have hax : a' + x ≤ 3 * a' := by linarith
      have h1 : (a' + x) ^ 2 + (a' + x) * Δ + Δ ^ 2 / 3 ≤
          9 * (a' ^ 2 + a' * Δ + Δ ^ 2 / 3) := by nlinarith
      nlinarith
    have herr_le : cubicQ (a' + x) Δ * (cA / (x ^ 2 * Real.log w)) ≤
        (9 * cA / Real.log w) * (cubicQ a' Δ / x) := by
      have hcA_nn : 0 ≤ cA := by unfold cA; linarith [CM_pos]
      have hx2 : x ≤ x ^ 2 := by nlinarith
      have h1 : cA / (x ^ 2 * Real.log w) ≤ cA / (x * Real.log w) :=
        div_le_div_of_nonneg_left hcA_nn (by positivity) (by nlinarith)
      calc cubicQ (a' + x) Δ * (cA / (x ^ 2 * Real.log w))
          ≤ (9 * cubicQ a' Δ) * (cA / (x * Real.log w)) :=
            mul_le_mul hq9 h1 (by positivity)
              (mul_nonneg (by norm_num) (cubicQ_nonneg (by linarith) hΔ_pos.le))
        _ = (9 * cA / Real.log w) * (cubicQ a' Δ / x) := by ring
    have hΔ_eq : Δ * (cubicQ a' Δ / x) = (1 / Real.log w) * (cubicQ a' Δ / x) := by dsimp [Δ]
    have hcDelta_eq : (1 / Real.log w) * (cubicQ a' Δ / x) + (9 * cA / Real.log w) * (cubicQ a' Δ / x) =
        (cDelta / Real.log w) * (cubicQ a' Δ / x) := by unfold cDelta; ring
    have hcomb : cubicQ (a' + x) Δ * ((1 / x - 2 / (a' + x + Δ)) + cA / (x ^ 2 * Real.log w)) ≤
        max 0 (cubicQ a' Δ / x - Δ * x) + (cDelta / Real.log w) * (cubicQ a' Δ / x) := by
      rw [mul_add]; linarith
    have hfinal := (hstep.trans hsum_le).trans
      (mul_le_mul_of_nonneg_left hm'
        (mul_nonneg (div_nonneg hCk_pos.le (sq_nonneg B)) hq_ax_nn))
    have hassoc : Ck / B ^ 2 * cubicQ (a' + x) Δ * ((1 / x - 2 / (a' + x + Δ)) + cA / (x ^ 2 * Real.log w)) =
        Ck / B ^ 2 * (cubicQ (a' + x) Δ * ((1 / x - 2 / (a' + x + Δ)) + cA / (x ^ 2 * Real.log w))) := by ring
    rw [hassoc] at hfinal
    exact hfinal.trans (mul_le_mul_of_nonneg_left hcomb (div_nonneg hCk_pos.le (sq_nonneg B)))
  · rw [if_neg hact, mul_zero]
    have hout : G - 3 * x ≤ a' ∨ a' + Δ ≤ x := by
      by_contra h; push Not at h; exact hact ⟨h.2, h.1⟩
    rw [oddMass_zero_of_out hw1 k a' Δ hq hout]

set_option maxHeartbeats 600000 in
/-- Step B of the barrier induction: odd depth `2k + 1` implies even depth `2(k + 1)`. -/
private lemma evenMass_step_of_odd {w z G Ck : ℝ} (hw : 4 ≤ w) (hz : 0 < z)
    (hlw_ge : max 4 (cA + 1) ≤ Real.log w)
    (hB : 20 ≤ Real.log z / Real.log w)
    (hG_lo : (19 : ℝ) / 10 * (Real.log z / Real.log w) ≤ G)
    (hG_hi : G ≤ 2 * (Real.log z / Real.log w))
    (hCk_ge : cInit ≤ Ck) (k : ℕ)
    (hOdd : let B := Real.log z / Real.log w
      let Δ := 1 / Real.log w
      ∀ (a' : ℝ), 2 - Δ ≤ a' → ∀ q ∈ primeSet w z,
        oddMass w z G k a' Δ q ≤
          Ck / B ^ 2 *
            (if pExp w q < a' + Δ ∧ a' < G - 3 * pExp w q then
              max 0 (cubicQ a' Δ / pExp w q - Δ * pExp w q) +
                (cDelta / Real.log w) * (cubicQ a' Δ / pExp w q)
            else 0)) :
    let B := Real.log z / Real.log w
    let Δ := 1 / Real.log w
    ∀ (a : ℝ), 2 - Δ ≤ a → ∀ p ∈ primeSet w z,
      evenMass w z G (k + 1) a Δ p ≤
        Ck * (1 + cStep / Real.log w) / B ^ 2 *
          (if 2 * pExp w p ≤ a + Δ ∧ a < G - 2 * pExp w p then cubicQ a Δ / pExp w p else 0) := by
  intro B Δ a ha p hp
  have hw1 : 1 < w := by linarith
  have hw0 : 0 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hlw_cA : cA + 1 ≤ Real.log w := (le_max_right _ _).trans hlw_ge
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 4 := by
    dsimp [Δ]; rw [one_div, inv_le_comm₀ hlw (by norm_num)]; norm_num; exact hlw4
  have hBpos : 0 < B := by linarith
  have hCk_pos : 0 < Ck := cInit_pos.trans_le hCk_ge
  have hB_pow_eq_z : w ^ B = z := by
    rw [Real.rpow_def_of_pos hw0]
    have : Real.log w * B = Real.log z := by dsimp [B]; field_simp
    rw [this, Real.exp_log hz]
  let y := pExp w p
  have hy1 : 1 < y := (mem_primeSet_spec hw1 hp).2.2.2.1
  by_cases hact : 2 * y ≤ a + Δ ∧ a < G - 2 * y
  · rw [if_pos hact]
    have hdecomp := evenMass_succ_le (G := G) hw1 k a Δ hp
    have ha74 : (7 : ℝ) / 4 ≤ a := by linarith
    have hy_le_a : y ≤ a := by linarith
    have hQa_nn : 0 ≤ cubicQ a Δ := cubicQ_nonneg (by linarith) hΔ_pos.le
    let V : ℝ := min (a + y + Δ) ((G - a - y) / 3)
    have hV_le_B : V ≤ B := by
      by_cases hcase : a + Δ + y < G - B
      · exact (min_le_left _ _).trans (by linarith)
      · push Not at hcase
        exact (min_le_right _ _).trans (by linarith)
    by_cases hyV : y < V
    · have hV_pos : 0 < V := by linarith
      let R0 : ℝ := Real.sqrt (cubicQ (a + y) Δ / Δ)
      have hQay_div : cubicQ (a + y) Δ / Δ = (a + y) ^ 2 + (a + y) * Δ + Δ ^ 2 / 3 := by
        rw [cubicQ_eq]; field_simp
      have hR0_sq : R0 ^ 2 = (a + y) ^ 2 + (a + y) * Δ + Δ ^ 2 / 3 := by
        dsimp [R0]; rw [Real.sq_sqrt (by rw [hQay_div]; positivity), hQay_div]
      have hR0_gt : a + y + Δ / 2 < R0 := by
        have h1 : (a + y + Δ / 2) ^ 2 < R0 ^ 2 := by
          rw [hR0_sq]; nlinarith [sq_pos_of_pos hΔ_pos]
        have h2 : 0 ≤ a + y + Δ / 2 := by linarith
        nlinarith [Real.sqrt_nonneg (cubicQ (a + y) Δ / Δ)]
      have hR0_pos : 0 < R0 := by linarith
      let W : ℝ := min V R0
      have hyW : y < W := lt_min hyV (by linarith)
      have hW_le_B : W ≤ B := (min_le_left _ _).trans hV_le_B
      have hW_pow_z : w ^ W ≤ z := by
        calc w ^ W ≤ w ^ B := Real.rpow_le_rpow_of_exponent_le hw1.le hW_le_B
          _ = z := hB_pow_eq_z
      let SV := (primeSet w z).filter (fun q => y < pExp w q ∧ pExp w q < V)
      let SW := (primeSet w z).filter (fun q => y < pExp w q ∧ pExp w q < W)
      have hOdd_sum : ∑ q ∈ (primeSet w z).filter (p < ·),
          (q : ℝ)⁻¹ * oddMass w z G k (a + y) Δ q ≤
          Ck / B ^ 2 * (
            (Δ * R0 ^ 2 * (∑ q ∈ SW, (1 : ℝ) / ((q : ℝ) * pExp w q)) -
             Δ * (∑ q ∈ SW, pExp w q / (q : ℝ))) +
            (cDelta / Real.log w) * cubicQ (a + y) Δ *
              (∑ q ∈ SV, (1 : ℝ) / ((q : ℝ) * pExp w q))) := by
        have hq_step : ∀ q ∈ (primeSet w z).filter (p < ·),
            (q : ℝ)⁻¹ * oddMass w z G k (a + y) Δ q ≤
            Ck / B ^ 2 * (
              (if y < pExp w q ∧ pExp w q < W then
                Δ * R0 ^ 2 * ((1 : ℝ) / ((q : ℝ) * pExp w q)) - Δ * (pExp w q / (q : ℝ))
              else 0) +
              (if y < pExp w q ∧ pExp w q < V then
                (cDelta / Real.log w) * cubicQ (a + y) Δ * ((1 : ℝ) / ((q : ℝ) * pExp w q))
              else 0)) := by
          intro q hq
          have hqP : q ∈ primeSet w z := (mem_filter.mp hq).1
          have hpq : p < q := (mem_filter.mp hq).2
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hp).1.pos
          have hy_lt_q : y < pExp w q := by
            unfold y pExp
            exact div_lt_div_of_pos_right (Real.log_lt_log hp_pos (by exact_mod_cast hpq)) hlw
          have hq1 : 1 < pExp w q := (mem_primeSet_spec hw1 hqP).2.2.2.1
          have ho := hOdd (a + y) (by linarith) q hqP
          have hmul := mul_le_mul_of_nonneg_left ho (by positivity : (0 : ℝ) ≤ (q : ℝ)⁻¹)
          refine hmul.trans ?_
          have hiffV : (pExp w q < a + y + Δ ∧ a + y < G - 3 * pExp w q) ↔
              (y < pExp w q ∧ pExp w q < V) := by
            dsimp [V]; rw [lt_min_iff]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨hy_lt_q, h1, by linarith⟩
            · rintro ⟨_, h1, h2⟩; exact ⟨h1, by linarith⟩
          by_cases hV : y < pExp w q ∧ pExp w q < V
          · rw [if_pos (hiffV.mpr hV), if_pos hV]
            have hrearr : (q : ℝ)⁻¹ * (Ck / B ^ 2 * (max 0 (cubicQ (a + y) Δ / pExp w q - Δ * pExp w q) +
                cDelta / Real.log w * (cubicQ (a + y) Δ / pExp w q))) =
                Ck / B ^ 2 * ((q : ℝ)⁻¹ * max 0 (cubicQ (a + y) Δ / pExp w q - Δ * pExp w q) +
                  cDelta / Real.log w * cubicQ (a + y) Δ * ((1 : ℝ) / ((q : ℝ) * pExp w q))) := by ring
            rw [hrearr]
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hCk_pos.le (sq_nonneg B))
            refine add_le_add ?_ le_rfl
            have hQay_eq : cubicQ (a + y) Δ = Δ * R0 ^ 2 := by rw [hR0_sq, cubicQ_eq]
            by_cases hW : y < pExp w q ∧ pExp w q < W
            · rw [if_pos hW]
              have hltR : pExp w q < R0 := hW.2.trans_le (min_le_right _ _)
              have hpos_diff : 0 ≤ cubicQ (a + y) Δ / pExp w q - Δ * pExp w q := by
                rw [hQay_eq, sub_nonneg, le_div_iff₀ (by linarith only [hq1])]
                have hsq : (pExp w q) ^ 2 ≤ R0 ^ 2 := by nlinarith only [hq1, hltR]
                have hmul := mul_le_mul_of_nonneg_left hsq hΔ_pos.le
                linarith only [hmul, show Δ * pExp w q * pExp w q = Δ * (pExp w q) ^ 2 by ring]
              rw [max_eq_right hpos_diff, hQay_eq]
              apply le_of_eq; ring
            · rw [if_neg hW]
              have hgeR : R0 ≤ pExp w q := by
                by_contra hlt; push Not at hlt
                exact hW ⟨hy_lt_q, lt_min hV.2 hlt⟩
              have hle0 : cubicQ (a + y) Δ / pExp w q - Δ * pExp w q ≤ 0 := by
                rw [hQay_eq, sub_nonpos, div_le_iff₀ (by linarith only [hq1])]
                have hsq : R0 ^ 2 ≤ (pExp w q) ^ 2 := by nlinarith only [hR0_pos, hgeR]
                have hmul := mul_le_mul_of_nonneg_left hsq hΔ_pos.le
                linarith only [hmul, show Δ * pExp w q * pExp w q = Δ * (pExp w q) ^ 2 by ring]
              rw [max_eq_left hle0, mul_zero]
          · rw [if_neg (mt hiffV.mp hV), if_neg hV]
            have hnW : ¬ (y < pExp w q ∧ pExp w q < W) := fun h => hV ⟨h.1, h.2.trans_le (min_le_left _ _)⟩
            rw [if_neg hnW]; simp
        have hsum1 := Finset.sum_le_sum hq_step
        rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum1
        have hSW_eq : ∑ q ∈ (primeSet w z).filter (p < ·),
            (if y < pExp w q ∧ pExp w q < W then
              Δ * R0 ^ 2 * ((1 : ℝ) / ((q : ℝ) * pExp w q)) - Δ * (pExp w q / (q : ℝ))
            else 0) =
            Δ * R0 ^ 2 * (∑ q ∈ SW, (1 : ℝ) / ((q : ℝ) * pExp w q)) -
              Δ * (∑ q ∈ SW, pExp w q / (q : ℝ)) := by
          rw [← Finset.sum_filter, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          have hset : ((primeSet w z).filter (p < ·)).filter (fun q => y < pExp w q ∧ pExp w q < W) = SW := by
            ext q; simp only [SW, mem_filter]
            constructor
            · rintro ⟨⟨hqP, _⟩, hyq, hqW⟩; exact ⟨hqP, hyq, hqW⟩
            · rintro ⟨hqP, hyq, hqW⟩
              have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hp).1.pos
              have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hqP).1.pos
              have hpq : p < q := by
                unfold y pExp at hyq
                exact_mod_cast (Real.log_lt_log_iff hp_pos hq_pos).mp ((div_lt_div_iff_of_pos_right hlw).mp hyq)
              exact ⟨⟨hqP, hpq⟩, hyq, hqW⟩
          rw [hset]
        have hSV_eq : ∑ q ∈ (primeSet w z).filter (p < ·),
            (if y < pExp w q ∧ pExp w q < V then
              (cDelta / Real.log w) * cubicQ (a + y) Δ * ((1 : ℝ) / ((q : ℝ) * pExp w q))
            else 0) =
            (cDelta / Real.log w) * cubicQ (a + y) Δ *
              (∑ q ∈ SV, (1 : ℝ) / ((q : ℝ) * pExp w q)) := by
          rw [← Finset.sum_filter, ← Finset.mul_sum]
          have hset : ((primeSet w z).filter (p < ·)).filter (fun q => y < pExp w q ∧ pExp w q < V) = SV := by
            ext q; simp only [SV, mem_filter]
            constructor
            · rintro ⟨⟨hqP, _⟩, hyq, hqV⟩; exact ⟨hqP, hyq, hqV⟩
            · rintro ⟨hqP, hyq, hqV⟩
              have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hp).1.pos
              have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hqP).1.pos
              have hpq : p < q := by
                unfold y pExp at hyq
                exact_mod_cast (Real.log_lt_log_iff hp_pos hq_pos).mp ((div_lt_div_iff_of_pos_right hlw).mp hyq)
              exact ⟨⟨hqP, hpq⟩, hyq, hqV⟩
          rw [hset]
        rw [hSW_eq, hSV_eq] at hsum1
        exact hsum1
      have hm1 : ∑ q ∈ SW, (1 : ℝ) / ((q : ℝ) * pExp w q) ≤
          (1 / y - 1 / W) + cA / (y ^ 2 * Real.log w) := by
        unfold pExp cA
        exact sum_inv_p_mul_e_le hw hy1.le hyW SW (fun q hq => by
          obtain ⟨hqP, hlo, hhi⟩ := mem_filter.mp hq
          exact ⟨(mem_primeSet_spec hw1 hqP).1, hlo, hhi.le⟩)
      have hm2 : (W - y) - (2 * CM + 1) / Real.log w ≤ ∑ q ∈ SW, pExp w q / (q : ℝ) := by
        exact sum_e_div_p_ge hw hy1.le hyW hW_pow_z
      have hm3 : ∑ q ∈ SV, (1 : ℝ) / ((q : ℝ) * pExp w q) ≤ 2 / y := by
        have h1 : ∑ q ∈ SV, (1 : ℝ) / ((q : ℝ) * pExp w q) ≤
            (1 / y - 1 / V) + cA / (y ^ 2 * Real.log w) := by
          unfold pExp cA
          exact sum_inv_p_mul_e_le hw hy1.le hyV SV (fun q hq => by
            obtain ⟨hqP, hlo, hhi⟩ := mem_filter.mp hq
            exact ⟨(mem_primeSet_spec hw1 hqP).1, hlo, hhi.le⟩)
        have h2 : cA / (y ^ 2 * Real.log w) ≤ 1 / y := by
          have hcA_nn : 0 ≤ cA := by unfold cA; linarith only [CM_pos]
          rw [div_le_div_iff₀ (by positivity) (by linarith only [hy1])]
          have hy2 : y ≤ y ^ 2 := by nlinarith only [hy1]
          nlinarith only [hlw_cA, hy2, hy1, hlw, hcA_nn]
        have h3 : 0 ≤ 1 / V := by positivity
        linarith only [h1, h2, h3, show (1 : ℝ) / y + 1 / y = 2 / y by ring]
      have hQ4 : cubicQ (a + y) Δ ≤ 4 * cubicQ a Δ := by
        rw [cubicQ_eq, cubicQ_eq]
        have h1 : (a + y) ^ 2 + (a + y) * Δ + Δ ^ 2 / 3 ≤
            4 * (a ^ 2 + a * Δ + Δ ^ 2 / 3) := by nlinarith only [hy_le_a, hy1, hΔ_pos]
        have h2 := mul_le_mul_of_nonneg_left h1 hΔ_pos.le
        linarith only [h2]
      have hΔ_le_Q : Δ ≤ cubicQ a Δ / y := by
        have hq_ge := cubicQ_ge_mul_sq (by linarith only [ha74] : 0 ≤ a) hΔ_pos.le
        have h1 : 1 ≤ a ^ 2 / y := by
          rw [le_div_iff₀ (by linarith only [hy1] : 0 < y)]; nlinarith only [hy_le_a, hy1, ha74]
        calc Δ = Δ * 1 := by ring
          _ ≤ Δ * (a ^ 2 / y) := mul_le_mul_of_nonneg_left h1 hΔ_pos.le
          _ = (Δ * a ^ 2) / y := by ring
          _ ≤ cubicQ a Δ / y := div_le_div_of_nonneg_right hq_ge (by linarith only [hy1])
      have hR0y : Δ * (R0 - y) ^ 2 ≤ cubicQ a Δ := by
        have h1 : Δ * (R0 - y) ^ 2 = Δ * R0 ^ 2 - 2 * Δ * y * R0 + Δ * y ^ 2 := by ring
        have h2 : Δ * R0 ^ 2 - 2 * Δ * y * (a + y + Δ / 2) + Δ * y ^ 2 = cubicQ a Δ := by
          rw [hR0_sq, cubicQ_eq]; ring
        have hmul := mul_le_mul_of_nonneg_left hR0_gt.le (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hΔ_pos.le) (by linarith only [hy1] : 0 ≤ y))
        linarith only [h1, h2, hmul]
      have hmain_id : Δ * R0 ^ 2 * (1 / y - 1 / W) - Δ * (W - y) =
          Δ * (R0 - y) ^ 2 / y - Δ * (R0 - W) ^ 2 / W := by
        have hy0 : y ≠ 0 := by linarith only [hy1]
        have hW0 : W ≠ 0 := by linarith only [hy1, hyW]
        field_simp; ring
      have hQay_eq : cubicQ (a + y) Δ = Δ * R0 ^ 2 := by rw [hR0_sq, cubicQ_eq]
      have herr1 : Δ * R0 ^ 2 * (cA / (y ^ 2 * Real.log w)) ≤
          (4 * cA / Real.log w) * (cubicQ a Δ / y) := by
        have hcA_nn : 0 ≤ cA := by unfold cA; linarith only [CM_pos]
        rw [← hQay_eq]
        have hy2 : y ≤ y ^ 2 := by nlinarith only [hy1]
        have h1 : cA / (y ^ 2 * Real.log w) ≤ cA / (y * Real.log w) :=
          div_le_div_of_nonneg_left hcA_nn (by positivity) (mul_le_mul_of_nonneg_right hy2 hlw.le)
        calc cubicQ (a + y) Δ * (cA / (y ^ 2 * Real.log w))
            ≤ (4 * cubicQ a Δ) * (cA / (y * Real.log w)) :=
              mul_le_mul hQ4 h1 (by positivity) (mul_nonneg (by norm_num) hQa_nn)
          _ = (4 * cA / Real.log w) * (cubicQ a Δ / y) := by ring
      have herr2 : Δ * ((2 * CM + 1) / Real.log w) ≤
          ((2 * CM + 1) / Real.log w) * (cubicQ a Δ / y) := by
        have hcm_nn : 0 ≤ (2 * CM + 1) / Real.log w := div_nonneg (by linarith only [CM_pos]) hlw.le
        have hmul := mul_le_mul_of_nonneg_left hΔ_le_Q hcm_nn
        linarith only [hmul]
      have herr3 : (cDelta / Real.log w) * cubicQ (a + y) Δ * (∑ q ∈ SV, (1 : ℝ) / ((q : ℝ) * pExp w q)) ≤
          (8 * cDelta / Real.log w) * (cubicQ a Δ / y) := by
        have hcD_nn : 0 ≤ cDelta / Real.log w := div_nonneg (by unfold cDelta cA; linarith only [CM_pos]) hlw.le
        calc (cDelta / Real.log w) * cubicQ (a + y) Δ * (∑ q ∈ SV, (1 : ℝ) / ((q : ℝ) * pExp w q))
            ≤ (cDelta / Real.log w) * (4 * cubicQ a Δ) * (2 / y) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hQ4 hcD_nn) hm3
                (Finset.sum_nonneg (fun q hq => by
                  have := (mem_primeSet_spec hw1 (mem_filter.mp hq).1).2.2.2.1; positivity))
                (mul_nonneg hcD_nn (mul_nonneg (by norm_num) hQa_nn))
          _ = (8 * cDelta / Real.log w) * (cubicQ a Δ / y) := by ring
      have hpart1_le : Δ * R0 ^ 2 * (∑ q ∈ SW, (1 : ℝ) / ((q : ℝ) * pExp w q)) -
          Δ * (∑ q ∈ SW, pExp w q / (q : ℝ)) ≤
          cubicQ a Δ / y - Δ * (R0 - W) ^ 2 / W +
            (4 * cA / Real.log w) * (cubicQ a Δ / y) +
            ((2 * CM + 1) / Real.log w) * (cubicQ a Δ / y) := by
        have h1 := mul_le_mul_of_nonneg_left hm1 (by positivity : 0 ≤ Δ * R0 ^ 2)
        have h2 := mul_le_mul_of_nonneg_left hm2 hΔ_pos.le
        have h3 : Δ * (R0 - y) ^ 2 / y ≤ cubicQ a Δ / y :=
          div_le_div_of_nonneg_right hR0y (by linarith only [hy1])
        rw [mul_add] at h1
        linarith only [h1, h2, h3, hmain_id, herr1, herr2]
      have hstep_sum : (4 * cA / Real.log w) * (cubicQ a Δ / y) +
          ((2 * CM + 1) / Real.log w) * (cubicQ a Δ / y) +
          (8 * cDelta / Real.log w) * (cubicQ a Δ / y) =
          (cStep / Real.log w) * (cubicQ a Δ / y) := by
        unfold cStep; ring
      have hK2_bound : ∑ q ∈ (primeSet w z).filter (p < ·),
          (q : ℝ)⁻¹ * oddMass w z G k (a + y) Δ q ≤
          Ck * (1 + cStep / Real.log w) / B ^ 2 * (cubicQ a Δ / y) -
            Ck / B ^ 2 * (Δ * (R0 - W) ^ 2 / W) := by
        have h1 : (Δ * R0 ^ 2 * (∑ q ∈ SW, (1 : ℝ) / ((q : ℝ) * pExp w q)) -
            Δ * (∑ q ∈ SW, pExp w q / (q : ℝ))) +
            (cDelta / Real.log w) * cubicQ (a + y) Δ * (∑ q ∈ SV, (1 : ℝ) / ((q : ℝ) * pExp w q)) ≤
            (1 + cStep / Real.log w) * (cubicQ a Δ / y) - Δ * (R0 - W) ^ 2 / W := by
          linarith only [hpart1_le, herr3, hstep_sum,
            show (1 + cStep / Real.log w) * (cubicQ a Δ / y) = cubicQ a Δ / y + (cStep / Real.log w) * (cubicQ a Δ / y) by ring]
        have h2 := hOdd_sum.trans (mul_le_mul_of_nonneg_left h1 (div_nonneg hCk_pos.le (sq_nonneg B)))
        linarith only [h2, show Ck / B ^ 2 * ((1 + cStep / Real.log w) * (cubicQ a Δ / y) - Δ * (R0 - W) ^ 2 / W) =
          Ck * (1 + cStep / Real.log w) / B ^ 2 * (cubicQ a Δ / y) - Ck / B ^ 2 * (Δ * (R0 - W) ^ 2 / W) by ring]
      by_cases hlt : a + Δ + y < G - B
      · have he2_zero := evenMassTwo_eq_zero_of_lt hw1 a Δ hlt
        have hW_pos : 0 < W := by linarith only [hy1, hyW]
        have hdef_nn : 0 ≤ Ck / B ^ 2 * (Δ * (R0 - W) ^ 2 / W) := by positivity
        linarith only [hdecomp, he2_zero, hK2_bound, hdef_nn]
      · push Not at hlt
        have hay_ge : (71 : ℝ) / 80 * B ≤ a + y := by linarith only [hlt, hG_lo, hΔ_le, hB]
        have hhi_le : (G - a - y) / 3 ≤ (89 : ℝ) / 240 * B := by linarith only [hay_ge, hG_hi]
        have hW_eq : W = (G - a - y) / 3 := by
          dsimp [W, V]
          have h1 : (G - a - y) / 3 ≤ a + y + Δ := by linarith only [hay_ge, hhi_le, hΔ_pos, hB]
          have h2 : (G - a - y) / 3 ≤ R0 := by linarith only [hR0_gt, hay_ge, hhi_le, hΔ_pos, hB]
          rw [min_eq_right h1, min_eq_left h2]
        have hR0W : B / 2 ≤ R0 - W := by linarith only [hR0_gt, hay_ge, hW_eq, hhi_le, hΔ_pos, hB]
        have hW_pos : 0 < W := by linarith only [hy1, hyW]
        have hdef_ge : (Ck / 4) * Δ / W ≤ Ck / B ^ 2 * (Δ * (R0 - W) ^ 2 / W) := by
          have hsq : B ^ 2 / 4 ≤ (R0 - W) ^ 2 := by nlinarith only [hR0W, hBpos]
          have h1 : (Ck / 4) * Δ / W = Ck / B ^ 2 * (Δ * (B ^ 2 / 4) / W) := by field_simp
          rw [h1]
          apply mul_le_mul_of_nonneg_left _ (div_nonneg hCk_pos.le (sq_nonneg B))
          apply div_le_div_of_nonneg_right _ hW_pos.le
          exact mul_le_mul_of_nonneg_left hsq hΔ_pos.le
        have hmax_ge : 2 * W ≤ max y (G - a - Δ - y) := by
          have h1 : 3 * W = G - a - y := by rw [hW_eq]; ring
          have hW1 : 1 < W := hy1.trans hyW
          have h2 : 2 * W ≤ G - a - Δ - y := by linarith only [h1, hW1, hΔ_le]
          exact h2.trans (le_max_right _ _)
        have he2 := evenMassTwo_le G hw a hp
        have hcm0 : 0 ≤ CM := CM_pos.le
        have he2_le : evenMassTwo w z G a Δ p ≤ (4 * CM + 4) * Δ / (2 * W) :=
          he2.trans (div_le_div_of_nonneg_left (by positivity) (by linarith only [hW_pos]) hmax_ge)
        have hdom : (4 * CM + 4) * Δ / (2 * W) ≤ (Ck / 4) * Δ / W := by
          have h1 : (4 * CM + 4) * Δ / (2 * W) = ((4 * CM + 4) / 2) * (Δ / W) := by ring
          have h2 : (Ck / 4) * Δ / W = (Ck / 4) * (Δ / W) := by ring
          rw [h1, h2]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          unfold cInit at hCk_ge; linarith only [hCk_ge, CM_pos]
        linarith only [hdecomp, hK2_bound, hdef_ge, he2_le, hdom]
    · push Not at hyV
      have hsum_zero : ∑ q ∈ (primeSet w z).filter (p < ·),
          (q : ℝ)⁻¹ * oddMass w z G k (a + y) Δ q = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        have hqP : q ∈ primeSet w z := (mem_filter.mp hq).1
        have hpq : p < q := (mem_filter.mp hq).2
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hp).1.pos
        have hy_lt_q : y < pExp w q := by
          unfold y pExp
          exact div_lt_div_of_pos_right (Real.log_lt_log hp_pos (by exact_mod_cast hpq)) hlw
        have hV_le_q : V < pExp w q := hyV.trans_lt hy_lt_q
        have hout : G - 3 * pExp w q ≤ a + y ∨ a + y + Δ ≤ pExp w q := by
          dsimp [V] at hV_le_q
          rcases min_cases (a + y + Δ) ((G - a - y) / 3) with ⟨hmin, _⟩ | ⟨hmin, _⟩
          · rw [hmin] at hV_le_q; exact Or.inr hV_le_q.le
          · rw [hmin] at hV_le_q; exact Or.inl (by linarith)
        rw [oddMass_zero_of_out hw1 k (a + y) Δ hqP hout, mul_zero]
      rw [hsum_zero, add_zero] at hdecomp
      by_cases hlt : a + Δ + y < G - B
      · rw [evenMassTwo_eq_zero_of_lt hw1 a Δ hlt] at hdecomp
        have hstep_pos : 0 < 1 + cStep / Real.log w := by have := cStep_pos; positivity
        exact hdecomp.trans (by positivity)
      · push Not at hlt
        have ha_ge_half : B / 2 ≤ a := by linarith
        have hq_ge : Δ * (B ^ 2 / 4) ≤ cubicQ a Δ := by
          have h1 := cubicQ_ge_mul_sq (by linarith : 0 ≤ a) hΔ_pos.le
          have h2 : B ^ 2 / 4 ≤ a ^ 2 := by nlinarith
          nlinarith
        have he2 := evenMassTwo_le G hw a hp
        have hcm0 : 0 ≤ CM := CM_pos.le
        have he2' : evenMassTwo w z G a Δ p ≤ (4 * CM + 4) * Δ / y :=
          he2.trans (div_le_div_of_nonneg_left (by positivity) (by linarith) (le_max_left _ _))
        have hstep_ge1 : 1 ≤ 1 + cStep / Real.log w := by
          have := cStep_pos; linarith [div_nonneg this.le hlw.le]
        have hCk_succ : cInit ≤ Ck * (1 + cStep / Real.log w) := by nlinarith
        have hrhs : (cInit / 4) * Δ / y ≤ Ck * (1 + cStep / Real.log w) / B ^ 2 * (cubicQ a Δ / y) := by
          have h1 : (cInit / 4) * Δ / y = cInit / B ^ 2 * (Δ * (B ^ 2 / 4) / y) := by field_simp
          rw [h1]
          apply mul_le_mul (div_le_div_of_nonneg_right hCk_succ (sq_nonneg B))
            (div_le_div_of_nonneg_right hq_ge (by linarith)) (by positivity)
            (div_nonneg (mul_nonneg hCk_pos.le (by linarith)) (sq_nonneg B))
        have hcinit_eq : (cInit / 4) * Δ / y = 2 * ((4 * CM + 4) * Δ / y) := by unfold cInit; ring
        have hnn : 0 ≤ (4 * CM + 4) * Δ / y := by positivity
        linarith
  · rw [if_neg hact, mul_zero]
    have hout : G - 2 * y ≤ a ∨ a + Δ < 2 * y := by
      by_contra h; push Not at h; exact hact ⟨h.2, h.1⟩
    rw [evenMass_zero_of_out hw1 (k + 1) a Δ hp hout]

/-- Main inductive barrier bound on `evenMass w z G m a Δ p` for `m ≥ 1` and `2 - Δ ≤ a`. -/
lemma evenMass_barrier_le {w z G : ℝ} (hw : 4 ≤ w) (hz : 0 < z)
    (hlw_ge : max 4 (cA + 1) ≤ Real.log w)
    (hB : 20 ≤ Real.log z / Real.log w)
    (hG_lo : (19 : ℝ) / 10 * (Real.log z / Real.log w) ≤ G)
    (hG_hi : G ≤ 2 * (Real.log z / Real.log w))
    (m : ℕ) (hm : 1 ≤ m) :
    let B := Real.log z / Real.log w
    let Δ := 1 / Real.log w
    ∀ (a : ℝ), 2 - Δ ≤ a → ∀ p ∈ primeSet w z,
      evenMass w z G m a Δ p ≤
        cInit * (1 + cStep / Real.log w) ^ (m - 1) / B ^ 2 *
          (if 2 * pExp w p ≤ a + Δ ∧ a < G - 2 * pExp w p then cubicQ a Δ / pExp w p else 0) := by
  intro B Δ
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 4 := by
    dsimp [Δ]; rw [one_div, inv_le_comm₀ hlw (by norm_num)]; norm_num; exact hlw4
  have hBpos : 0 < B := by linarith
  have hstep_ge1 : 1 ≤ 1 + cStep / Real.log w := by
    have : 0 ≤ cStep / Real.log w := div_nonneg cStep_pos.le hlw.le
    linarith
  induction m, hm using Nat.le_induction with
  | base =>
    intro a ha p hp
    simp only [Nat.sub_self, pow_zero, mul_one]
    have heq_two : evenMass w z G 1 a Δ p = evenMassTwo w z G a Δ p := by
      unfold evenMass evenMassTwo
      congr 1
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext d; simp only [mem_filter]
      constructor
      · rintro ⟨hd, _, h2, hle, hrest⟩; exact ⟨hd, by omega, hrest⟩
      · rintro ⟨hd, hc2, hrest⟩; exact ⟨hd, by rw [hc2]; exact even_two, by omega, by omega, hrest⟩
    by_cases hact : 2 * pExp w p ≤ a + Δ ∧ a < G - 2 * pExp w p
    · rw [if_pos hact, heq_two]
      let y := pExp w p
      have hy1 : 1 < y := (mem_primeSet_spec hw1 hp).2.2.2.1
      have ha_nn : 0 ≤ a := by linarith
      by_cases hlt : a + Δ + y < G - B
      · rw [evenMassTwo_eq_zero_of_lt hw1 a Δ hlt]
        have hq : 0 ≤ cubicQ a Δ := cubicQ_nonneg ha_nn hΔ_pos.le
        have := cInit_pos
        positivity
      · push Not at hlt
        have ha_ge_half : B / 2 ≤ a := by linarith
        have hq_ge : Δ * (B ^ 2 / 4) ≤ cubicQ a Δ := by
          have h1 := cubicQ_ge_mul_sq ha_nn hΔ_pos.le
          have h2 : B ^ 2 / 4 ≤ a ^ 2 := by nlinarith
          nlinarith
        have he2 := evenMassTwo_le G hw a hp
        have hmax_ge : y ≤ max y (G - a - Δ - y) := le_max_left _ _
        have hcm0 : 0 ≤ CM := CM_pos.le
        have he2' : evenMassTwo w z G a Δ p ≤ (4 * CM + 4) * Δ / y :=
          he2.trans (div_le_div_of_nonneg_left (by positivity) (by linarith) hmax_ge)
        have hrhs : (cInit / 4) * Δ / y ≤ cInit / B ^ 2 * (cubicQ a Δ / y) := by
          have h1 : (cInit / 4) * Δ / y = cInit / B ^ 2 * (Δ * (B ^ 2 / 4) / y) := by field_simp
          rw [h1]
          apply mul_le_mul_of_nonneg_left _ (div_nonneg cInit_pos.le (sq_nonneg B))
          exact div_le_div_of_nonneg_right hq_ge (by linarith)
        have hcinit_eq : (cInit / 4) * Δ / y = 2 * ((4 * CM + 4) * Δ / y) := by unfold cInit; ring
        have hnn : 0 ≤ (4 * CM + 4) * Δ / y := by positivity
        linarith
    · rw [if_neg hact, mul_zero]
      have hout : G - 2 * pExp w p ≤ a ∨ a + Δ < 2 * pExp w p := by
        by_contra h; push Not at h; exact hact ⟨h.2, h.1⟩
      rw [evenMass_zero_of_out hw1 1 a Δ hp hout]
  | succ k hk ih =>
    let Ck : ℝ := cInit * (1 + cStep / Real.log w) ^ (k - 1)
    have hCk_ge : cInit ≤ Ck := by
      dsimp [Ck]
      have hpow : 1 ≤ (1 + cStep / Real.log w) ^ (k - 1) := one_le_pow₀ hstep_ge1
      nlinarith [cInit_pos]
    have hCk_pos : 0 < Ck := cInit_pos.trans_le hCk_ge
    have hOdd := oddMass_step_of_even hw hlw_ge hB hCk_pos k ih
    have hEven := evenMass_step_of_odd hw hz hlw_ge hB hG_lo hG_hi hCk_ge k hOdd
    intro a ha p hp
    have hpow_eq : cInit * (1 + cStep / Real.log w) ^ (k + 1 - 1) =
        Ck * (1 + cStep / Real.log w) := by
      dsimp [Ck]; rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
    rw [hpow_eq]
    exact hEven a ha p hp

/-- Slab total reciprocal mass bound for all `d ∈ admTree` of depth `2 ≤ d.card ≤ 2M`
with `g(d) ∈ (a, a + Δ]`. -/
noncomputable def cSlab : ℝ := 4 * (1 + cDelta) * cInit * Real.exp (22 * cStep)

lemma cSlab_pos : 0 < cSlab := by
  unfold cSlab cDelta cA
  have := cInit_pos
  have := Real.exp_pos (22 * cStep)
  have := CM_pos
  positivity

set_option maxHeartbeats 600000 in
/-- Standalone odd-depth pointwise barrier derived from `evenMass_barrier_le` at depth `M`. -/
lemma oddMass_le_of_even_barrier {w z G : ℝ} (hw : 4 ≤ w) (hz : 0 < z)
    (hlw_ge : max 4 (cA + 1) ≤ Real.log w)
    (hB : 20 ≤ Real.log z / Real.log w)
    (hG_lo : (19 : ℝ) / 10 * (Real.log z / Real.log w) ≤ G)
    (hG_hi : G ≤ 2 * (Real.log z / Real.log w))
    (M : ℕ) (hM1 : 1 ≤ M) :
    let B := Real.log z / Real.log w
    let Δ := 1 / Real.log w
    let CM_val := cInit * (1 + cStep / Real.log w) ^ (M - 1)
    ∀ a : ℝ, 2 - Δ ≤ a → ∀ p ∈ primeSet w z,
      oddMass w z G M a Δ p ≤ (1 + cDelta) * CM_val / B ^ 2 * (cubicQ a Δ / pExp w p) := by
  intro B Δ CM_val a ha p hp
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 4 := by
    dsimp [Δ]; rw [one_div, inv_le_comm₀ hlw (by norm_num)]; norm_num; exact hlw4
  have hBpos : 0 < B := by linarith
  have hCM_pos : 0 < CM_val := by
    dsimp [CM_val]; have := cInit_pos; have := cStep_pos; positivity
  have hQ_nn : 0 ≤ cubicQ a Δ := cubicQ_nonneg (by linarith) hΔ_pos.le
  have hbar := evenMass_barrier_le hw hz hlw_ge hB hG_lo hG_hi M hM1
  let x := pExp w p
  have hx1 : 1 < x := (mem_primeSet_spec hw1 hp).2.2.2.1
  by_cases hact : x < a + Δ
  · have hstep := oddMass_le_sum_evenMass (G := G) hw1 M a Δ hp
    let U := (a + x + Δ) / 2
    have hxU : x < U := by dsimp [U]; linarith
    let S_r := (primeSet w z).filter (fun r => p < r ∧ 2 * pExp w r ≤ a + x + Δ)
    have hsum_le : ∑ r ∈ (primeSet w z).filter (p < ·),
        (r : ℝ)⁻¹ * evenMass w z G M (a + x) Δ r ≤
        CM_val / B ^ 2 * cubicQ (a + x) Δ *
          ∑ r ∈ S_r, (1 : ℝ) / ((r : ℝ) * pExp w r) := by
      rw [Finset.mul_sum]
      have h1 : ∑ r ∈ (primeSet w z).filter (p < ·),
          (r : ℝ)⁻¹ * evenMass w z G M (a + x) Δ r ≤
          ∑ r ∈ (primeSet w z).filter (p < ·),
            (if 2 * pExp w r ≤ a + x + Δ then
              CM_val / B ^ 2 * cubicQ (a + x) Δ * ((1 : ℝ) / ((r : ℝ) * pExp w r))
            else 0) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrP := (mem_filter.mp hr).1
        have hih := hbar (a + x) (by linarith) r hrP
        have hmul := mul_le_mul_of_nonneg_left hih (by positivity : (0 : ℝ) ≤ (r : ℝ)⁻¹)
        refine hmul.trans ?_
        split_ifs with h1' h2' h2'
        · apply le_of_eq; dsimp [CM_val]; ring
        · exfalso; exact h2' h1'.1
        · have hr1 := (mem_primeSet_spec hw1 hrP).2.2.2.1
          have hq_nn := cubicQ_nonneg (by linarith : 0 ≤ a + x) hΔ_pos.le
          simp only [mul_zero]; positivity
        · simp
      have h2 : ∑ r ∈ (primeSet w z).filter (p < ·),
          (if 2 * pExp w r ≤ a + x + Δ then
            CM_val / B ^ 2 * cubicQ (a + x) Δ * ((1 : ℝ) / ((r : ℝ) * pExp w r))
          else 0) =
          ∑ r ∈ S_r, CM_val / B ^ 2 * cubicQ (a + x) Δ * ((1 : ℝ) / ((r : ℝ) * pExp w r)) := by
        rw [← Finset.sum_filter]
        congr 1; ext r; simp only [S_r, mem_filter]; tauto
      exact h1.trans_eq h2
    have hm := sum_inv_p_mul_e_le hw hx1.le hxU S_r (fun r hr => by
      obtain ⟨hrP, hpr, hle⟩ := mem_filter.mp hr
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hp).1.pos
      have hx_lt_r : x < Real.log (r : ℝ) / Real.log w := by
        unfold x pExp; exact div_lt_div_of_pos_right (Real.log_lt_log hp_pos (by exact_mod_cast hpr)) hlw
      exact ⟨(mem_primeSet_spec hw1 hrP).1, hx_lt_r, by dsimp [U]; unfold pExp at hle; linarith⟩)
    have hq_ax_nn : 0 ≤ cubicQ (a + x) Δ := cubicQ_nonneg (by linarith) hΔ_pos.le
    have hm' : ∑ r ∈ S_r, (1 : ℝ) / ((r : ℝ) * pExp w r) ≤
        (1 / x - 2 / (a + x + Δ)) + cA / (x ^ 2 * Real.log w) := by
      have heq : 1 / U = 2 / (a + x + Δ) := by
        dsimp [U]; have : a + x + Δ ≠ 0 := by linarith
        field_simp
      unfold pExp cA; linarith
    have hprod1 : cubicQ (a + x) Δ * (1 / x - 2 / (a + x + Δ)) ≤ cubicQ a Δ / x + Δ ^ 2 := by
      have hs_pos : 0 < a + x + Δ := by linarith
      have hdiv_ge : Δ * (a + x) ≤ cubicQ (a + x) Δ / (a + x + Δ) := by
        rw [le_div_iff₀ hs_pos, cubicQ_eq]; nlinarith [pow_nonneg hΔ_pos.le 3]
      have hstep1 : cubicQ (a + x) Δ * (1 / x - 2 / (a + x + Δ)) =
          cubicQ (a + x) Δ / x - 2 * (cubicQ (a + x) Δ / (a + x + Δ)) := by ring
      have hstep2 : cubicQ (a + x) Δ / x - 2 * (Δ * (a + x)) =
          (cubicQ a Δ / x - Δ * x) + Δ ^ 2 := by
        rw [cubicQ_eq, cubicQ_eq]
        have : x ≠ 0 := by linarith
        field_simp; ring
      have hxΔ : 0 ≤ Δ * x := by positivity
      linarith
    have hΔ2_le : Δ ^ 2 ≤ (1 / Real.log w) * (cubicQ a Δ / x) := by
      have hq_ge := cubicQ_ge_mul_sq (by linarith : 0 ≤ a) hΔ_pos.le
      have h1 : 1 ≤ a ^ 2 / x := by rw [le_div_iff₀ (by linarith : 0 < x)]; nlinarith
      have h2 : Δ ≤ cubicQ a Δ / x := by
        calc Δ = Δ * 1 := by ring
          _ ≤ Δ * (a ^ 2 / x) := mul_le_mul_of_nonneg_left h1 hΔ_pos.le
          _ = (Δ * a ^ 2) / x := by ring
          _ ≤ cubicQ a Δ / x := div_le_div_of_nonneg_right hq_ge (by linarith)
      have hΔ_eq : Δ = 1 / Real.log w := rfl
      nlinarith
    have hq9 : cubicQ (a + x) Δ ≤ 9 * cubicQ a Δ := by
      rw [cubicQ_eq, cubicQ_eq]
      have : (a + x) ^ 2 + (a + x) * Δ + Δ ^ 2 / 3 ≤ 9 * (a ^ 2 + a * Δ + Δ ^ 2 / 3) := by nlinarith
      nlinarith
    have herr_le : cubicQ (a + x) Δ * (cA / (x ^ 2 * Real.log w)) ≤
        (9 * cA / Real.log w) * (cubicQ a Δ / x) := by
      have hcA_nn : 0 ≤ cA := by unfold cA; linarith [CM_pos]
      have hx2 : x ≤ x ^ 2 := by nlinarith
      have h1 : cA / (x ^ 2 * Real.log w) ≤ cA / (x * Real.log w) :=
        div_le_div_of_nonneg_left hcA_nn (by positivity) (by nlinarith)
      calc cubicQ (a + x) Δ * (cA / (x ^ 2 * Real.log w))
          ≤ (9 * cubicQ a Δ) * (cA / (x * Real.log w)) :=
            mul_le_mul hq9 h1 (by positivity) (mul_nonneg (by norm_num) hQ_nn)
        _ = (9 * cA / Real.log w) * (cubicQ a Δ / x) := by ring
    have hcomb : cubicQ (a + x) Δ * ((1 / x - 2 / (a + x + Δ)) + cA / (x ^ 2 * Real.log w)) ≤
        (1 + cDelta) * (cubicQ a Δ / x) := by
      rw [mul_add]
      have h1 : (1 / Real.log w) * (cubicQ a Δ / x) + (9 * cA / Real.log w) * (cubicQ a Δ / x) =
          (cDelta / Real.log w) * (cubicQ a Δ / x) := by unfold cDelta; ring
      have h2 : cDelta / Real.log w ≤ cDelta := by
        rw [div_le_iff₀ hlw]; have : 0 ≤ cDelta := by unfold cDelta cA; linarith [CM_pos]
        nlinarith
      have h3 : 0 ≤ cubicQ a Δ / x := div_nonneg hQ_nn (by linarith)
      nlinarith
    have hfin := (hstep.trans hsum_le).trans
      (mul_le_mul_of_nonneg_left hm'
        (mul_nonneg (div_nonneg hCM_pos.le (sq_nonneg B)) hq_ax_nn))
    have hassoc : CM_val / B ^ 2 * cubicQ (a + x) Δ * ((1 / x - 2 / (a + x + Δ)) + cA / (x ^ 2 * Real.log w)) =
        CM_val / B ^ 2 * (cubicQ (a + x) Δ * ((1 / x - 2 / (a + x + Δ)) + cA / (x ^ 2 * Real.log w))) := by ring
    rw [hassoc] at hfin
    have h4 := hfin.trans (mul_le_mul_of_nonneg_left hcomb (div_nonneg hCM_pos.le (sq_nonneg B)))
    linarith [show CM_val / B ^ 2 * ((1 + cDelta) * (cubicQ a Δ / x)) =
      (1 + cDelta) * CM_val / B ^ 2 * (cubicQ a Δ / x) by ring]
  · push Not at hact
    rw [oddMass_zero_of_out hw1 M a Δ hp (Or.inr hact)]
    have : 0 ≤ cDelta := by unfold cDelta cA; linarith [CM_pos]
    positivity

set_option maxHeartbeats 600000 in
lemma slab_total_mass_le {w z G : ℝ} (hw : 4 ≤ w) (hz : 4 ≤ z)
    (hlw_ge : max 4 (cA + 1) ≤ Real.log w)
    (hB : 20 ≤ Real.log z / Real.log w)
    (hlogB : Real.log (Real.log z / Real.log w) ≤ 2 * Real.log w)
    (hG_lo : (19 : ℝ) / 10 * (Real.log z / Real.log w) ≤ G)
    (hG_hi : G ≤ 2 * (Real.log z / Real.log w)) :
    let B := Real.log z / Real.log w
    let Δ := 1 / Real.log w
    let M := ⌈10 * Real.log B⌉₊
    ∀ a : ℝ, 2 - Δ ≤ a →
      ∑ d ∈ (admTree w z G).filter (fun d =>
        2 ≤ d.card ∧ d.card ≤ 2 * M ∧ a < gapOf w G d ∧ gapOf w G d ≤ a + Δ), (prodR d)⁻¹ ≤
        cSlab / B ^ 2 * cubicQ a Δ := by
  intro B Δ M a ha
  have hw1 : 1 < w := by linarith
  have hz0 : 0 < z := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hlw_cA : cA + 1 ≤ Real.log w := (le_max_right _ _).trans hlw_ge
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 4 := by
    dsimp [Δ]; rw [one_div, inv_le_comm₀ hlw (by norm_num)]; norm_num; exact hlw4
  have hBpos : 0 < B := by linarith
  have hlogB_ge2 : 2 ≤ Real.log B := by
    have he2 : Real.exp 2 ≤ 20 := by
      have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have := Real.log_le_log (Real.exp_pos 2) (he2.trans hB)
    rwa [Real.log_exp] at this
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < (M : ℝ) := by linarith [Nat.le_ceil (10 * Real.log B)]
    exact_mod_cast this.le
  have hM_le : (M : ℝ) - 1 ≤ 22 * Real.log w := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ 10 * Real.log B by linarith)
    linarith
  let CM_val := cInit * (1 + cStep / Real.log w) ^ (M - 1)
  have hCM_le : CM_val ≤ cInit * Real.exp (22 * cStep) := by
    dsimp [CM_val]
    apply mul_le_mul_of_nonneg_left _ cInit_pos.le
    have h1 : (1 + cStep / Real.log w) ^ (M - 1) ≤ Real.exp (((M - 1 : ℕ) : ℝ) * (cStep / Real.log w)) := by
      rw [Real.exp_nat_mul]
      have hcS := cStep_pos.le
      exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (cStep / Real.log w)]) (M - 1)
    have h2 : ((M - 1 : ℕ) : ℝ) * (cStep / Real.log w) ≤ 22 * cStep := by
      rw [Nat.cast_sub hM1, Nat.cast_one]
      have : ((M : ℝ) - 1) * (cStep / Real.log w) ≤ (22 * Real.log w) * (cStep / Real.log w) :=
        mul_le_mul_of_nonneg_right hM_le (div_nonneg cStep_pos.le hlw.le)
      have heq : (22 * Real.log w) * (cStep / Real.log w) = 22 * cStep := by field_simp
      linarith
    exact h1.trans (Real.exp_le_exp.mpr h2)
  have hCM_pos : 0 < CM_val := by
    dsimp [CM_val]
    have := cInit_pos; have := cStep_pos; positivity
  let S_all := (admTree w z G).filter (fun d =>
    2 ≤ d.card ∧ d.card ≤ 2 * M ∧ a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)
  let S_ev := S_all.filter (fun d => Even d.card)
  let S_od := S_all.filter (fun d => ¬ Even d.card)
  have hsplit : ∑ d ∈ S_all, (prodR d)⁻¹ = (∑ d ∈ S_ev, (prodR d)⁻¹) + ∑ d ∈ S_od, (prodR d)⁻¹ := by
    exact (Finset.sum_filter_add_sum_filter_not S_all (fun d => Even d.card) (fun d => (prodR d)⁻¹)).symm
  change ∑ d ∈ S_all, (prodR d)⁻¹ ≤ _
  rw [hsplit]
  have hev_le : ∑ d ∈ S_ev, (prodR d)⁻¹ ≤
      ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * evenMass w z G M a Δ p := by
    have hrhs : ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * evenMass w z G M a Δ p =
        ∑ p ∈ primeSet w z, ∑ d ∈ (admTree w z G).filter (fun d =>
          Even d.card ∧ 2 ≤ d.card ∧ d.card ≤ 2 * M ∧
          (∃ hne : d.Nonempty, d.min' hne = p) ∧
          a < gapOf w G d ∧ gapOf w G d ≤ a + Δ), (prodR d)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold evenMass
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hp).1.pos
      rw [← mul_assoc, inv_mul_cancel₀ hp_pos.ne', one_mul]
    rw [hrhs]
    have hbi : S_ev = (primeSet w z).biUnion (fun p => (admTree w z G).filter (fun d =>
        Even d.card ∧ 2 ≤ d.card ∧ d.card ≤ 2 * M ∧
        (∃ hne : d.Nonempty, d.min' hne = p) ∧
        a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)) := by
      ext d
      simp only [S_ev, S_all, mem_filter, mem_biUnion]
      constructor
      · rintro ⟨⟨hdT, h2, hhi, hga, hgb⟩, hev⟩
        have hne : d.Nonempty := Finset.card_pos.mp (by omega)
        have hsub : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
        exact ⟨d.min' hne, hsub (Finset.min'_mem d hne), hdT, hev, h2, hhi, ⟨hne, rfl⟩, hga, hgb⟩
      · rintro ⟨p, _, hdT, hev, h2, hhi, _, hga, hgb⟩
        exact ⟨⟨hdT, h2, hhi, hga, hgb⟩, hev⟩
    have hpw : (primeSet w z : Set ℕ).PairwiseDisjoint (fun p => (admTree w z G).filter (fun d =>
        Even d.card ∧ 2 ≤ d.card ∧ d.card ≤ 2 * M ∧
        (∃ hne : d.Nonempty, d.min' hne = p) ∧
        a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)) := by
      intro p₁ _ p₂ _ hne_p
      rw [Function.onFun, Finset.disjoint_left]
      intro d h1 h2
      obtain ⟨hne₁, hm₁⟩ := (mem_filter.mp h1).2.2.2.2.1
      obtain ⟨hne₂, hm₂⟩ := (mem_filter.mp h2).2.2.2.2.1
      exact hne_p (hm₁.symm.trans hm₂)
    rw [hbi, Finset.sum_biUnion hpw]
  have hod_le : ∑ d ∈ S_od, (prodR d)⁻¹ ≤
      ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * oddMass w z G M a Δ p := by
    have hrhs : ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * oddMass w z G M a Δ p =
        ∑ p ∈ primeSet w z, ∑ d ∈ (admTree w z G).filter (fun d =>
          ¬ Even d.card ∧ 3 ≤ d.card ∧ d.card ≤ 2 * M + 1 ∧
          (∃ hne : d.Nonempty, d.min' hne = p) ∧
          a < gapOf w G d ∧ gapOf w G d ≤ a + Δ), (prodR d)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold oddMass
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primeSet_spec hw1 hp).1.pos
      rw [← mul_assoc, inv_mul_cancel₀ hp_pos.ne', one_mul]
    rw [hrhs]
    have hsub : S_od ⊆ (primeSet w z).biUnion (fun p => (admTree w z G).filter (fun d =>
        ¬ Even d.card ∧ 3 ≤ d.card ∧ d.card ≤ 2 * M + 1 ∧
        (∃ hne : d.Nonempty, d.min' hne = p) ∧
        a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)) := by
      intro d hd
      obtain ⟨hdSall, hodd⟩ := mem_filter.mp hd
      obtain ⟨hdT, h2, hhi, hga, hgb⟩ := mem_filter.mp hdSall
      have h3 : 3 ≤ d.card := by rw [Nat.even_iff] at hodd; omega
      have hne : d.Nonempty := Finset.card_pos.mp (by omega)
      have hsub' : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
      exact mem_biUnion.mpr ⟨d.min' hne, hsub' (Finset.min'_mem d hne),
        mem_filter.mpr ⟨hdT, hodd, h3, by omega, ⟨hne, rfl⟩, hga, hgb⟩⟩
    have hpw : (primeSet w z : Set ℕ).PairwiseDisjoint (fun p => (admTree w z G).filter (fun d =>
        ¬ Even d.card ∧ 3 ≤ d.card ∧ d.card ≤ 2 * M + 1 ∧
        (∃ hne : d.Nonempty, d.min' hne = p) ∧
        a < gapOf w G d ∧ gapOf w G d ≤ a + Δ)) := by
      intro p₁ _ p₂ _ hne_p
      rw [Function.onFun, Finset.disjoint_left]
      intro d h1 h2
      obtain ⟨hne₁, hm₁⟩ := (mem_filter.mp h1).2.2.2.2.1
      obtain ⟨hne₂, hm₂⟩ := (mem_filter.mp h2).2.2.2.2.1
      exact hne_p (hm₁.symm.trans hm₂)
    rw [← Finset.sum_biUnion hpw]
    exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (prodR d)⁻¹) hsub
      (fun d _ _ => by unfold prodR; positivity)
  have hsum_pe_le2 : ∑ p ∈ primeSet w z, (1 : ℝ) / ((p : ℝ) * pExp w p) ≤ 2 := by
    have h1 := sum_inv_p_mul_e_le hw (le_refl (1 : ℝ)) (by linarith : (1 : ℝ) < B) (primeSet w z)
      (fun p hp => by
        have hs := mem_primeSet_spec hw1 hp
        exact ⟨hs.1, hs.2.2.2.1, hs.2.2.2.2⟩)
    unfold pExp
    have h2 : (8 * CM + 4) / (1 ^ 2 * Real.log w) ≤ 1 := by
      rw [one_pow, one_mul, div_le_one hlw]
      unfold cA at hlw_cA; linarith
    have h3 : 0 ≤ 1 / B := by positivity
    linarith
  have hbar := evenMass_barrier_le hw hz0 hlw_ge hB hG_lo hG_hi M hM1
  have hOdd_pt := oddMass_le_of_even_barrier hw hz0 hlw_ge hB hG_lo hG_hi M hM1 a ha
  have hQ_nn : 0 ≤ cubicQ a Δ := cubicQ_nonneg (by linarith) hΔ_pos.le
  have hev_final : ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * evenMass w z G M a Δ p ≤
      2 * CM_val / B ^ 2 * cubicQ a Δ := by
    calc ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * evenMass w z G M a Δ p
        ≤ ∑ p ∈ primeSet w z, CM_val / B ^ 2 * cubicQ a Δ * ((1 : ℝ) / ((p : ℝ) * pExp w p)) := by
          apply Finset.sum_le_sum
          intro p hp
          have h1 := mul_le_mul_of_nonneg_left (hbar a ha p hp) (by positivity : (0 : ℝ) ≤ (p : ℝ)⁻¹)
          refine h1.trans ?_
          split_ifs
          · apply le_of_eq; dsimp [CM_val]; ring
          · rw [mul_zero, mul_zero]
            have := (mem_primeSet_spec hw1 hp).2.2.2.1
            positivity
      _ = CM_val / B ^ 2 * cubicQ a Δ * ∑ p ∈ primeSet w z, (1 : ℝ) / ((p : ℝ) * pExp w p) := by
          rw [← Finset.mul_sum]
      _ ≤ CM_val / B ^ 2 * cubicQ a Δ * 2 :=
          mul_le_mul_of_nonneg_left hsum_pe_le2 (by positivity)
      _ = 2 * CM_val / B ^ 2 * cubicQ a Δ := by ring
  have hod_final : ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * oddMass w z G M a Δ p ≤
      2 * (1 + cDelta) * CM_val / B ^ 2 * cubicQ a Δ := by
    calc ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ * oddMass w z G M a Δ p
        ≤ ∑ p ∈ primeSet w z, (1 + cDelta) * CM_val / B ^ 2 * cubicQ a Δ *
            ((1 : ℝ) / ((p : ℝ) * pExp w p)) := by
          apply Finset.sum_le_sum
          intro p hp
          have h1 := mul_le_mul_of_nonneg_left (hOdd_pt p hp) (by positivity : (0 : ℝ) ≤ (p : ℝ)⁻¹)
          refine h1.trans_eq ?_; ring
      _ = (1 + cDelta) * CM_val / B ^ 2 * cubicQ a Δ *
            ∑ p ∈ primeSet w z, (1 : ℝ) / ((p : ℝ) * pExp w p) := by rw [← Finset.mul_sum]
      _ ≤ (1 + cDelta) * CM_val / B ^ 2 * cubicQ a Δ * 2 :=
          mul_le_mul_of_nonneg_left hsum_pe_le2 (by
            have : 0 ≤ cDelta := by unfold cDelta cA; linarith [CM_pos]
            positivity)
      _ = 2 * (1 + cDelta) * CM_val / B ^ 2 * cubicQ a Δ := by ring
  have htot : (2 * CM_val / B ^ 2 * cubicQ a Δ) + (2 * (1 + cDelta) * CM_val / B ^ 2 * cubicQ a Δ) ≤
      cSlab / B ^ 2 * cubicQ a Δ := by
    have h1 : 2 * CM_val + 2 * (1 + cDelta) * CM_val ≤ 4 * (1 + cDelta) * (cInit * Real.exp (22 * cStep)) := by
      have hcD : 0 ≤ cDelta := by unfold cDelta cA; linarith [CM_pos]
      nlinarith
    have h2 : (2 * CM_val / B ^ 2 * cubicQ a Δ) + (2 * (1 + cDelta) * CM_val / B ^ 2 * cubicQ a Δ) =
        (2 * CM_val + 2 * (1 + cDelta) * CM_val) * (cubicQ a Δ / B ^ 2) := by ring
    have h3 : cSlab / B ^ 2 * cubicQ a Δ = (4 * (1 + cDelta) * (cInit * Real.exp (22 * cStep))) * (cubicQ a Δ / B ^ 2) := by
      unfold cSlab; ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_right h1 (div_nonneg hQ_nn (sq_nonneg B))
  linarith only [hev_le, hod_le, hev_final, hod_final, htot]

/-
## Compact mass bound and exponential tail bound on `admTree`
-/

lemma sum_cubicQ_range (a₀ Δ : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, cubicQ (a₀ + (i : ℝ) * Δ) Δ =
      ((a₀ + (N : ℝ) * Δ) ^ 3 - a₀ ^ 3) / 3 := by
  induction N with
  | zero => simp [cubicQ]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold cubicQ
    push_cast
    ring

set_option maxHeartbeats 600000 in
/-- Compact reciprocal mass bound: for any `k ≥ 3`,
`B^2 * ∑_{d ∈ admTree, g d ≤ k} (prodR d)⁻¹ ≤ 1 + cSlab * (k + 1)^3 / 3`. -/
lemma tree_compact_mass_le {w z G k : ℝ} (hw : 4 ≤ w) (hz : 4 ≤ z)
    (hlw_ge : max 4 (cA + 1) ≤ Real.log w)
    (hB : max 20 (2 * k) ≤ Real.log z / Real.log w)
    (hlogB : Real.log (Real.log z / Real.log w) ≤ 2 * Real.log w)
    (hG_lo : (19 : ℝ) / 10 * (Real.log z / Real.log w) ≤ G)
    (hG_hi : G ≤ 2 * (Real.log z / Real.log w))
    (hk : 3 ≤ k) :
    let B := Real.log z / Real.log w
    B ^ 2 * ∑ d ∈ (admTree w z G).filter (fun d => gapOf w G d ≤ k), (prodR d)⁻¹ ≤
      1 + cSlab * (k + 1) ^ 3 / 3 := by
  intro B
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hlw_cA : cA + 1 ≤ Real.log w := (le_max_right _ _).trans hlw_ge
  have hlw_cm : 4 * CM + 2 ≤ Real.log w := by unfold cA at hlw_cA; linarith [CM_pos]
  have hB20 : 20 ≤ B := (le_max_left _ _).trans hB
  have hB2k : 2 * k ≤ B := (le_max_right _ _).trans hB
  let Δ := 1 / Real.log w
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 4 := by
    dsimp [Δ]; rw [one_div, inv_le_comm₀ hlw (by norm_num)]; norm_num; exact hlw4
  let M := ⌈10 * Real.log B⌉₊
  let Sk := (admTree w z G).filter (fun d => gapOf w G d ≤ k)
  let Sk_mid := Sk.filter (fun d => 2 ≤ d.card ∧ d.card ≤ 2 * M)
  let Sk_hi := Sk.filter (fun d => 2 * M < d.card)
  have hSk_sub : Sk ⊆ Sk_mid ∪ Sk_hi := by
    intro d hd
    obtain ⟨hdT, hgk⟩ := mem_filter.mp hd
    have hsub : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
    have hcard2 : 2 ≤ d.card := by
      by_contra hlt; push Not at hlt
      interval_cases hc : d.card
      · have hde : d = ∅ := Finset.card_eq_zero.mp hc
        rw [hde] at hgk; simp only [gapOf, Finset.sum_empty, sub_zero] at hgk; linarith
      · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
        have hpP : p ∈ primeSet w z := hsub (mem_singleton_self p)
        have hep : pExp w p ≤ B := (mem_primeSet_spec hw1 hpP).2.2.2.2
        unfold gapOf at hgk; rw [Finset.sum_singleton] at hgk; linarith
    by_cases hM : d.card ≤ 2 * M
    · exact mem_union_left _ (mem_filter.mpr ⟨hd, hcard2, hM⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hd, by omega⟩)
  have hsum_split : ∑ d ∈ Sk, (prodR d)⁻¹ ≤ (∑ d ∈ Sk_mid, (prodR d)⁻¹) + ∑ d ∈ Sk_hi, (prodR d)⁻¹ := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (prodR d)⁻¹) hSk_sub
      (fun d _ _ => by unfold prodR; positivity)
    exact h1.trans (sum_union_le_of_nonneg (f := fun d => (prodR d)⁻¹) (fun d => by unfold prodR; positivity))
  have hhi_le : ∑ d ∈ Sk_hi, (prodR d)⁻¹ ≤ 2 / B ^ 3 := by
    have hsub_hi : Sk_hi ⊆ (primeSet w z).powerset.filter (fun d => 2 * M ≤ d.card) := by
      intro d hd
      obtain ⟨hdSk, hgt⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hdSk).1).1, by omega⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (prodR d)⁻¹) hsub_hi
      (fun d _ _ => by unfold prodR; positivity)).trans (sum_large_card_le hw hz hB20 hlw_cm)
  let a₀ := 2 - Δ
  let N := ⌈(k - a₀) / Δ⌉₊
  have hN_le : a₀ + (N : ℝ) * Δ ≤ k + 1 := by
    have hka₀ : 0 ≤ k - a₀ := by dsimp [a₀]; linarith
    have h1 : (N : ℝ) < (k - a₀) / Δ + 1 := Nat.ceil_lt_add_one (div_nonneg hka₀ hΔ_pos.le)
    have h2 : (N : ℝ) * Δ < ((k - a₀) / Δ + 1) * Δ := mul_lt_mul_of_pos_right h1 hΔ_pos
    have h3 : ((k - a₀) / Δ + 1) * Δ = k - a₀ + Δ := by field_simp
    linarith
  let slab : ℕ → Finset (Finset ℕ) := fun i =>
    (admTree w z G).filter (fun d =>
      2 ≤ d.card ∧ d.card ≤ 2 * M ∧
      a₀ + (i : ℝ) * Δ < gapOf w G d ∧ gapOf w G d ≤ a₀ + (i : ℝ) * Δ + Δ)
  have hmid_sub : Sk_mid ⊆ (Finset.range N).biUnion slab := by
    intro d hd
    obtain ⟨hdSk, h2, hhi⟩ := mem_filter.mp hd
    obtain ⟨hdT, hgk⟩ := mem_filter.mp hdSk
    have hg2 : 2 ≤ gapOf w G d := admTree_gap_ge_two hw1 hB20 hG_lo hdT
    have hdiff_pos : 0 < (gapOf w G d - a₀) / Δ := div_pos (by dsimp [a₀]; linarith) hΔ_pos
    let idx := ⌈(gapOf w G d - a₀) / Δ⌉₊ - 1
    have hceil_pos : 1 ≤ ⌈(gapOf w G d - a₀) / Δ⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      intro h0; have := Nat.ceil_eq_zero.mp h0; linarith)
    have hidx_lt : idx < N := by
      have hle : ⌈(gapOf w G d - a₀) / Δ⌉₊ ≤ N :=
        Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith) hΔ_pos.le)
      omega
    have hidx_cast : (idx : ℝ) = (⌈(gapOf w G d - a₀) / Δ⌉₊ : ℝ) - 1 := by
      dsimp [idx]; rw [Nat.cast_sub hceil_pos, Nat.cast_one]
    have hlo : a₀ + (idx : ℝ) * Δ < gapOf w G d := by
      rw [hidx_cast]
      have h1 : ((⌈(gapOf w G d - a₀) / Δ⌉₊ : ℝ) - 1) * Δ < (gapOf w G d - a₀) / Δ * Δ :=
        mul_lt_mul_of_pos_right (by linarith [Nat.ceil_lt_add_one hdiff_pos.le]) hΔ_pos
      rw [div_mul_cancel₀ _ hΔ_pos.ne'] at h1
      linarith
    have hhi' : gapOf w G d ≤ a₀ + (idx : ℝ) * Δ + Δ := by
      rw [hidx_cast]
      have h1 : (gapOf w G d - a₀) / Δ * Δ ≤ (⌈(gapOf w G d - a₀) / Δ⌉₊ : ℝ) * Δ :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) hΔ_pos.le
      rw [div_mul_cancel₀ _ hΔ_pos.ne'] at h1
      linarith
    exact mem_biUnion.mpr ⟨idx, mem_range.mpr hidx_lt, mem_filter.mpr ⟨hdT, h2, hhi, hlo, hhi'⟩⟩
  have hmid_le : ∑ d ∈ Sk_mid, (prodR d)⁻¹ ≤ cSlab / B ^ 2 * ((k + 1) ^ 3 / 3) := by
    calc ∑ d ∈ Sk_mid, (prodR d)⁻¹
        ≤ ∑ d ∈ (Finset.range N).biUnion slab, (prodR d)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (prodR d)⁻¹) hmid_sub
            (fun d _ _ => by unfold prodR; positivity)
      _ ≤ ∑ i ∈ Finset.range N, ∑ d ∈ slab i, (prodR d)⁻¹ :=
          sum_biUnion_le_of_nonneg (f := fun d => (prodR d)⁻¹) (fun d => by unfold prodR; positivity)
      _ ≤ ∑ i ∈ Finset.range N, cSlab / B ^ 2 * cubicQ (a₀ + (i : ℝ) * Δ) Δ := by
          apply Finset.sum_le_sum
          intro i _
          have ha_i : 2 - Δ ≤ a₀ + (i : ℝ) * Δ := by
            dsimp [a₀]
            have : 0 ≤ (i : ℝ) * Δ := by positivity
            linarith
          exact slab_total_mass_le hw hz hlw_ge hB20 hlogB hG_lo hG_hi (a₀ + (i : ℝ) * Δ) ha_i
      _ = cSlab / B ^ 2 * ∑ i ∈ Finset.range N, cubicQ (a₀ + (i : ℝ) * Δ) Δ := by
          rw [← Finset.mul_sum]
      _ = cSlab / B ^ 2 * (((a₀ + (N : ℝ) * Δ) ^ 3 - a₀ ^ 3) / 3) := by
          rw [sum_cubicQ_range]
      _ ≤ cSlab / B ^ 2 * ((k + 1) ^ 3 / 3) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg cSlab_pos.le (sq_nonneg B))
          have ha₀_pos : 0 ≤ a₀ := by dsimp [a₀]; linarith only [hΔ_le]
          have hpow : (a₀ + (N : ℝ) * Δ) ^ 3 ≤ (k + 1) ^ 3 :=
            pow_le_pow_left₀ (by positivity) hN_le 3
          have ha₀3 : 0 ≤ a₀ ^ 3 := by positivity
          linarith only [hpow, ha₀3]
  have hB2_hi : B ^ 2 * (2 / B ^ 3) ≤ 1 := by
    have : B ^ 2 * (2 / B ^ 3) = 2 / B := by field_simp
    rw [this, div_le_one (by linarith only [hB20])]; linarith only [hB20]
  have hB2_mid : B ^ 2 * (cSlab / B ^ 2 * ((k + 1) ^ 3 / 3)) = cSlab * (k + 1) ^ 3 / 3 := by
    have : B ≠ 0 := by linarith only [hB20]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left (hsum_split.trans (add_le_add hmid_le hhi_le)) (sq_nonneg B)
  linarith only [hmul, hB2_hi, hB2_mid]

lemma poly_exp_le {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    (x + 1) ^ 2 * Real.exp (-α * x) ≤ 2 / α ^ 2 + 2 / α + 1 := by
  have ht : 0 ≤ α * x := mul_nonneg hα.le hx
  have hexp_ge : 1 + α * x + (α * x) ^ 2 / 2 ≤ Real.exp (α * x) := by
    have hsum := Real.sum_le_exp_of_nonneg ht 3
    simp [Finset.sum_range_succ, Nat.factorial] at hsum
    linarith
  have h1 : x ^ 2 ≤ (2 / α ^ 2) * Real.exp (α * x) := by
    have : (2 / α ^ 2) * ((α * x) ^ 2 / 2) = x ^ 2 := by field_simp
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hα)]
  have h2 : 2 * x ≤ (2 / α) * Real.exp (α * x) := by
    have : (2 / α) * (α * x) = 2 * x := by field_simp
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 2) hα, sq_nonneg (α * x)]
  have h3 : 1 ≤ 1 * Real.exp (α * x) := by nlinarith [sq_nonneg (α * x)]
  have hcomb : (x + 1) ^ 2 ≤ (2 / α ^ 2 + 2 / α + 1) * Real.exp (α * x) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcomb (Real.exp_pos (-α * x)).le
  have hcancel : Real.exp (α * x) * Real.exp (-α * x) = 1 := by rw [← Real.exp_add]; simp
  have hrearr : (2 / α ^ 2 + 2 / α + 1) * Real.exp (α * x) * Real.exp (-α * x) =
      2 / α ^ 2 + 2 / α + 1 := by rw [mul_assoc, hcancel, mul_one]
  linarith only [hmul, hrearr]

lemma geom_exp_slab_le {α Δ : ℝ} (hα : 0 < α) (hΔ : 0 < Δ) (hαΔ : α * Δ ≤ 1) (N : ℕ) :
    Δ * ∑ i ∈ Finset.range N, (Real.exp (-α * Δ)) ^ i ≤ 2 / α := by
  have hpos_prod : 0 < α * Δ := mul_pos hα hΔ
  have hr_lt1 : Real.exp (-α * Δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hr_ne1 : Real.exp (-α * Δ) ≠ 1 := hr_lt1.ne
  rw [geom_sum_eq hr_ne1]
  have hden_ge : α * Δ / 2 ≤ 1 - Real.exp (-α * Δ) := by
    have h1 : 1 + α * Δ ≤ Real.exp (α * Δ) := by linarith [Real.add_one_le_exp (α * Δ)]
    have h2 : Real.exp (-α * Δ) ≤ 1 / (1 + α * Δ) := by
      rw [neg_mul, Real.exp_neg, one_div]
      exact inv_anti₀ (by linarith) h1
    have h3 : 1 / (1 + α * Δ) ≤ 1 - α * Δ / 2 := by
      rw [div_le_iff₀ (by linarith : 0 < 1 + α * Δ)]
      nlinarith
    linarith
  have hnum_le : 1 - (Real.exp (-α * Δ)) ^ N ≤ 1 := by
    have : 0 ≤ (Real.exp (-α * Δ)) ^ N := by positivity
    linarith
  have hdiv_eq : ((Real.exp (-α * Δ)) ^ N - 1) / (Real.exp (-α * Δ) - 1) =
      (1 - (Real.exp (-α * Δ)) ^ N) / (1 - Real.exp (-α * Δ)) := by
    have hne1 : Real.exp (-α * Δ) - 1 ≠ 0 := sub_ne_zero.mpr hr_ne1
    have hne2 : 1 - Real.exp (-α * Δ) ≠ 0 := by linarith
    rw [div_eq_div_iff hne1 hne2]
    ring
  rw [hdiv_eq]
  calc Δ * ((1 - (Real.exp (-α * Δ)) ^ N) / (1 - Real.exp (-α * Δ)))
      ≤ Δ * (1 / (α * Δ / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hΔ.le
        exact div_le_div₀ zero_le_one hnum_le (by positivity) hden_ge
    _ = 2 / α := by field_simp

set_option maxHeartbeats 600000 in
/-- Uniform exponential tail bound on `admTree`: for any `c > 0` and `k ≥ 3`. -/
lemma tree_exp_tail_le {w z G c k : ℝ} (hw : 4 ≤ w) (hz : 4 ≤ z)
    (hlw_ge : max 4 (max (cA + 1) (c / 2)) ≤ Real.log w)
    (hB : 20 ≤ Real.log z / Real.log w)
    (hlogB : Real.log (Real.log z / Real.log w) ≤ 2 * Real.log w)
    (hG_lo : (19 : ℝ) / 10 * (Real.log z / Real.log w) ≤ G)
    (hG_hi : G ≤ 2 * (Real.log z / Real.log w))
    (hc : 0 < c) (hk : 3 ≤ k) :
    let B := Real.log z / Real.log w
    let α := c / 2
    B ^ 2 * ∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
      (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤
      (B ^ 2 + 2 * B ^ 2 * Real.log B) * Real.exp (-c * (9 / 10 * B)) + 2 / B +
      cSlab * (2 / α) * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) := by
  intro B α
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hlw_cA : cA + 1 ≤ Real.log w := ((le_max_left _ _).trans (le_max_right _ _)).trans hlw_ge
  have hlw_α : α ≤ Real.log w := ((le_max_right _ _).trans (le_max_right _ _)).trans hlw_ge
  have hlw_ge' : max 4 (cA + 1) ≤ Real.log w := max_le hlw4 hlw_cA
  have hlw_cm : 4 * CM + 2 ≤ Real.log w := by unfold cA at hlw_cA; linarith [CM_pos]
  let Δ := 1 / Real.log w
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 4 := by
    dsimp [Δ]; rw [one_div, inv_le_comm₀ hlw (by norm_num)]; norm_num; exact hlw4
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hαΔ_le1 : α * Δ ≤ 1 := by
    dsimp [Δ]; rw [mul_one_div, div_le_one hlw]; exact hlw_α
  let M := ⌈10 * Real.log B⌉₊
  let St := (admTree w z G).filter (fun d => k < gapOf w G d)
  let St_le1 := St.filter (fun d => d.card ≤ 1)
  let St_mid := St.filter (fun d => 2 ≤ d.card ∧ d.card ≤ 2 * M)
  let St_hi := St.filter (fun d => 2 * M < d.card)
  have hsub : St ⊆ St_le1 ∪ (St_mid ∪ St_hi) := by
    intro d hd
    by_cases h1 : d.card ≤ 1
    · exact mem_union_left _ (mem_filter.mpr ⟨hd, h1⟩)
    · by_cases h2 : d.card ≤ 2 * M
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hd, by omega, h2⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hd, by omega⟩))
  have hsplit : ∑ d ∈ St, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤
      (∑ d ∈ St_le1, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d)) +
      (∑ d ∈ St_mid, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d)) +
      (∑ d ∈ St_hi, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d)) := by
    have hnn : ∀ d : Finset ℕ, 0 ≤ (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) := fun d => by
      unfold prodR; positivity
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hnn d)
    have h2 := h1.trans (sum_union_le_of_nonneg hnn)
    have h3 := sum_union_le_of_nonneg (s₁ := St_mid) (s₂ := St_hi) hnn
    linarith only [h2, h3]
  have hle1_bound : ∑ d ∈ St_le1, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤
      (1 + 2 * Real.log B) * Real.exp (-c * (9 / 10 * B)) := by
    have hpt : ∀ d ∈ St_le1, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤
        (prodR d)⁻¹ * Real.exp (-c * (9 / 10 * B)) := by
      intro d hd
      obtain ⟨hdSt, hcard1⟩ := mem_filter.mp hd
      have hdT := (mem_filter.mp hdSt).1
      have hsub' : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
      have hgap : 9 / 10 * B ≤ gapOf w G d := by
        interval_cases hc' : d.card
        · have hde : d = ∅ := Finset.card_eq_zero.mp hc'
          rw [hde]; simp only [gapOf, Finset.sum_empty, sub_zero]; linarith
        · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc'
          have hep : pExp w p ≤ B := (mem_primeSet_spec hw1 (hsub' (mem_singleton_self p))).2.2.2.2
          unfold gapOf; rw [Finset.sum_singleton]; linarith
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
      unfold prodR; positivity
    have h1 := (Finset.sum_le_sum hpt).trans_eq (Finset.sum_mul _ _ _).symm
    have h2 : ∑ d ∈ St_le1, (prodR d)⁻¹ ≤ 1 + 2 * Real.log B := by
      have hsub1 : St_le1 ⊆ insert ∅ ((primeSet w z).image (fun p => ({p} : Finset ℕ))) := by
        intro d hd
        obtain ⟨hdSt, hcard1⟩ := mem_filter.mp hd
        have hsub' : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp (mem_filter.mp hdSt).1).1
        interval_cases hc' : d.card
        · have hde : d = ∅ := Finset.card_eq_zero.mp hc'
          rw [hde]; exact mem_insert_self _ _
        · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc'
          exact mem_insert_of_mem (mem_image.mpr ⟨p, hsub' (mem_singleton_self p), rfl⟩)
      have hsum_ins := Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (prodR d)⁻¹) hsub1
        (fun d _ _ => by unfold prodR; positivity)
      have hnot : (∅ : Finset ℕ) ∉ (primeSet w z).image (fun p => ({p} : Finset ℕ)) := by simp
      rw [Finset.sum_insert hnot] at hsum_ins
      have himg : ∑ d ∈ (primeSet w z).image (fun p => ({p} : Finset ℕ)), (prodR d)⁻¹ =
          ∑ p ∈ primeSet w z, (p : ℝ)⁻¹ := by
        rw [Finset.sum_image (fun p₁ _ p₂ _ h => Finset.singleton_injective h)]
        apply Finset.sum_congr rfl; intro p _; simp [prodR]
      have hemp : (prodR ∅)⁻¹ = 1 := by simp [prodR]
      rw [himg, hemp] at hsum_ins
      have hinv := sum_primeSet_inv_le hw hz hB hlw_cm
      linarith only [hsum_ins, hinv]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)
  have hhi_bound : ∑ d ∈ St_hi, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤ 2 / B ^ 3 := by
    have hpt : ∀ d ∈ St_hi, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤ (prodR d)⁻¹ := by
      intro d hd
      have hdT := (mem_filter.mp (mem_filter.mp hd).1).1
      have hg2 : 2 ≤ gapOf w G d := admTree_gap_ge_two hw1 hB hG_lo hdT
      have hexp : Real.exp (-c * gapOf w G d) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc (prodR d)⁻¹ * Real.exp (-c * gapOf w G d)
          ≤ (prodR d)⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp (by unfold prodR; positivity)
        _ = (prodR d)⁻¹ := mul_one _
    have hsub_hi : St_hi ⊆ (primeSet w z).powerset.filter (fun d => 2 * M ≤ d.card) := by
      intro d hd
      obtain ⟨hdSt, hgt⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hdSt).1).1, by omega⟩
    exact ((Finset.sum_le_sum hpt).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (prodR d)⁻¹) hsub_hi
        (fun d _ _ => by unfold prodR; positivity))).trans (sum_large_card_le hw hz hB hlw_cm)
  let N := ⌈max 0 (G - k) / Δ⌉₊
  let slab : ℕ → Finset (Finset ℕ) := fun i =>
    (admTree w z G).filter (fun d =>
      2 ≤ d.card ∧ d.card ≤ 2 * M ∧
      k + (i : ℝ) * Δ < gapOf w G d ∧ gapOf w G d ≤ k + (i : ℝ) * Δ + Δ)
  have hmid_sub : St_mid ⊆ (Finset.range N).biUnion slab := by
    intro d hd
    obtain ⟨hdSt, h2, hhi⟩ := mem_filter.mp hd
    obtain ⟨hdT, hgk⟩ := mem_filter.mp hdSt
    have hsub' : d ⊆ primeSet w z := mem_powerset.mp (mem_filter.mp hdT).1
    have hgG : gapOf w G d ≤ G := by
      unfold gapOf
      have hnn : 0 ≤ ∑ p ∈ d, pExp w p := Finset.sum_nonneg (fun p hp => by
        linarith [(mem_primeSet_spec hw1 (hsub' hp)).2.2.2.1])
      linarith
    have hdiff_pos : 0 < (gapOf w G d - k) / Δ := div_pos (by linarith) hΔ_pos
    let idx := ⌈(gapOf w G d - k) / Δ⌉₊ - 1
    have hceil_pos : 1 ≤ ⌈(gapOf w G d - k) / Δ⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      intro h0; have := Nat.ceil_eq_zero.mp h0; linarith)
    have hidx_lt : idx < N := by
      have hle : ⌈(gapOf w G d - k) / Δ⌉₊ ≤ N :=
        Nat.ceil_mono (div_le_div_of_nonneg_right ((by linarith : gapOf w G d - k ≤ G - k).trans (le_max_right _ _)) hΔ_pos.le)
      omega
    have hidx_cast : (idx : ℝ) = (⌈(gapOf w G d - k) / Δ⌉₊ : ℝ) - 1 := by
      dsimp [idx]; rw [Nat.cast_sub hceil_pos, Nat.cast_one]
    have hlo : k + (idx : ℝ) * Δ < gapOf w G d := by
      rw [hidx_cast]
      have h1 : ((⌈(gapOf w G d - k) / Δ⌉₊ : ℝ) - 1) * Δ < (gapOf w G d - k) / Δ * Δ :=
        mul_lt_mul_of_pos_right (by linarith [Nat.ceil_lt_add_one hdiff_pos.le]) hΔ_pos
      rw [div_mul_cancel₀ _ hΔ_pos.ne'] at h1; linarith
    have hhi' : gapOf w G d ≤ k + (idx : ℝ) * Δ + Δ := by
      rw [hidx_cast]
      have h1 : (gapOf w G d - k) / Δ * Δ ≤ (⌈(gapOf w G d - k) / Δ⌉₊ : ℝ) * Δ :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) hΔ_pos.le
      rw [div_mul_cancel₀ _ hΔ_pos.ne'] at h1; linarith
    exact mem_biUnion.mpr ⟨idx, mem_range.mpr hidx_lt, mem_filter.mpr ⟨hdT, h2, hhi, hlo, hhi'⟩⟩
  have hgeom_le : Δ * ∑ i ∈ Finset.range N, (Real.exp (-α * Δ)) ^ i ≤ 2 / α :=
    geom_exp_slab_le hα_pos hΔ_pos hαΔ_le1 N
  have hmid_bound : ∑ d ∈ St_mid, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤
      cSlab / B ^ 2 * (2 / α) * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) := by
    calc ∑ d ∈ St_mid, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d)
        ≤ ∑ d ∈ (Finset.range N).biUnion slab, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) :=
          Finset.sum_le_sum_of_subset_of_nonneg hmid_sub (fun d _ _ => by unfold prodR; positivity)
      _ ≤ ∑ i ∈ Finset.range N, ∑ d ∈ slab i, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) :=
          sum_biUnion_le_of_nonneg (f := fun d => (prodR d)⁻¹ * Real.exp (-c * gapOf w G d))
            (fun d => by unfold prodR; positivity)
      _ ≤ ∑ i ∈ Finset.range N,
            (cSlab / B ^ 2 * cubicQ (k + (i : ℝ) * Δ) Δ) * Real.exp (-c * (k + (i : ℝ) * Δ)) := by
          apply Finset.sum_le_sum
          intro i _
          have hpt : ∀ d ∈ slab i, (prodR d)⁻¹ * Real.exp (-c * gapOf w G d) ≤
              (prodR d)⁻¹ * Real.exp (-c * (k + (i : ℝ) * Δ)) := fun d hd => by
            have hlo := (mem_filter.mp hd).2.2.2.1
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
            unfold prodR; positivity
          have h1 := (Finset.sum_le_sum hpt).trans_eq (Finset.sum_mul _ _ _).symm
          have ha_i : 2 - Δ ≤ k + (i : ℝ) * Δ := by
            have : 0 ≤ (i : ℝ) * Δ := by positivity
            linarith
          have h2 := slab_total_mass_le hw hz hlw_ge' hB hlogB hG_lo hG_hi (k + (i : ℝ) * Δ) ha_i
          exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)
      _ ≤ ∑ i ∈ Finset.range N,
            cSlab / B ^ 2 * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) *
              (Δ * (Real.exp (-α * Δ)) ^ i) := by
          apply Finset.sum_le_sum
          intro i _
          let x := k + (i : ℝ) * Δ
          have hx_nn : 0 ≤ x := by dsimp [x]; positivity
          have hq_le : cubicQ x Δ ≤ Δ * (x + 1) ^ 2 := by
            have h1 := cubicQ_le_mul_sq hx_nn hΔ_pos.le
            have h2 : (x + Δ) ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
            nlinarith
          have hexp_split : Real.exp (-c * x) = Real.exp (-α * x) * (Real.exp (-α * k) * (Real.exp (-α * Δ)) ^ i) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
            congr 1; dsimp [x, α]; ring
          have hpe := poly_exp_le hα_pos hx_nn
          have h1 : cubicQ x Δ * Real.exp (-c * x) ≤
              (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) * (Δ * (Real.exp (-α * Δ)) ^ i) := by
            calc cubicQ x Δ * Real.exp (-c * x)
                ≤ (Δ * (x + 1) ^ 2) * Real.exp (-c * x) :=
                  mul_le_mul_of_nonneg_right hq_le (Real.exp_pos _).le
              _ = ((x + 1) ^ 2 * Real.exp (-α * x)) * (Real.exp (-α * k) * (Δ * (Real.exp (-α * Δ)) ^ i)) := by
                  rw [hexp_split]; ring
              _ ≤ (2 / α ^ 2 + 2 / α + 1) * (Real.exp (-α * k) * (Δ * (Real.exp (-α * Δ)) ^ i)) :=
                  mul_le_mul_of_nonneg_right hpe (by positivity)
              _ = (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) * (Δ * (Real.exp (-α * Δ)) ^ i) := by ring
          have h2 := mul_le_mul_of_nonneg_left h1 (div_nonneg cSlab_pos.le (sq_nonneg B))
          have hr1 : cSlab / B ^ 2 * cubicQ x Δ * Real.exp (-c * x) =
              cSlab / B ^ 2 * (cubicQ x Δ * Real.exp (-c * x)) := by ring
          have hr2 : cSlab / B ^ 2 * ((2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) * (Δ * (Real.exp (-α * Δ)) ^ i)) =
              cSlab / B ^ 2 * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) * (Δ * (Real.exp (-α * Δ)) ^ i) := by ring
          linarith only [h2, hr1, hr2]
      _ = cSlab / B ^ 2 * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) *
            (Δ * ∑ i ∈ Finset.range N, (Real.exp (-α * Δ)) ^ i) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ cSlab / B ^ 2 * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) * (2 / α) :=
          mul_le_mul_of_nonneg_left hgeom_le (by have := cSlab_pos; positivity)
      _ = cSlab / B ^ 2 * (2 / α) * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) := by ring
  have hsum_all := hsplit.trans (add_le_add (add_le_add hle1_bound hmid_bound) hhi_bound)
  have hmul := mul_le_mul_of_nonneg_left hsum_all (sq_nonneg B)
  have hBne : B ≠ 0 := by linarith
  have hdist : B ^ 2 * ((1 + 2 * Real.log B) * Real.exp (-c * (9 / 10 * B)) +
      cSlab / B ^ 2 * (2 / α) * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) + 2 / B ^ 3) =
      (B ^ 2 + 2 * B ^ 2 * Real.log B) * Real.exp (-c * (9 / 10 * B)) + 2 / B +
      cSlab * (2 / α) * (2 / α ^ 2 + 2 / α + 1) * Real.exp (-α * k) := by
    field_simp; ring
  linarith only [hmul, hdist]

end Erdos687H2.TreeMass

/-
# Unified Two-Sided Exponential Brun Sieve and Progression Corollaries

We merge the lower and upper Brun combinatorial sieves into a single parameterized proof
(`brun_sieve_one_sided`), yielding the uniform two-sided exponential Fundamental Lemma
(`brun_sieve_two_sided`) for all `z ≥ 16`, `s ≥ sBrun`, and `y ≥ z ^ s`.
We then transfer the sieve to arithmetic progressions `Z d Q` via CRT (`card_Z_eq_sievedCount`),
proving:
1. `brun_progression_envelope`: exponential relative error `cEnv * exp(-g(d)/4)` for `g(d) ≥ sBrun + 4`.
2. `brun_progression_upper_bad`: uniform `O(μ / D(d))` bound for all `d` with `g(d) ≥ 2` by
   sifting at the reduced cutoff `⌊w ^ α⌋₊` and applying `eulerProd_ratio_le`.
-/

namespace Erdos687H2.BrunSieve

open Finset Real Erdos687H2.Mertens

private lemma alternating_choose_sum {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) =
      (-1 : ℝ) ^ m * ((n - 1).choose m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpas : n.choose (m + 1) = (n - 1).choose m + (n - 1).choose (m + 1) := by
      have h := Nat.choose_succ_succ (n - 1) m
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hn] at h
      exact h
    have hpas_r : (n.choose (m + 1) : ℝ) = ((n - 1).choose m : ℝ) + ((n - 1).choose (m + 1) : ℝ) := by
      exact_mod_cast hpas
    rw [hpas_r, pow_succ (-1 : ℝ) m]
    ring

private lemma alternating_powerset_eq (B : Finset ℕ) (M : ℕ) :
    ∑ D ∈ B.powerset.filter (fun D => D.card ≤ M), (-1 : ℝ) ^ D.card =
      ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (B.card.choose j : ℝ) := by
  have hpart : B.powerset.filter (fun D => D.card ≤ M) =
      (Finset.range (M + 1)).biUnion (fun j => B.powersetCard j) := by
    ext D
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨hDB, hcard⟩
      exact ⟨D.card, by omega, hDB, rfl⟩
    · rintro ⟨j, hj, hDB, rfl⟩
      exact ⟨hDB, by omega⟩
  have hpw : (Finset.range (M + 1) : Set ℕ).PairwiseDisjoint (fun j => B.powersetCard j) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro D hDi hDj
    have hi := (mem_powersetCard.mp hDi).2
    have hj := (mem_powersetCard.mp hDj).2
    exact hij (hi.symm.trans hj)
  rw [hpart, Finset.sum_biUnion hpw]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∑ D ∈ B.powersetCard j, (-1 : ℝ) ^ D.card =
      ∑ _D ∈ B.powersetCard j, (-1 : ℝ) ^ j :=
    Finset.sum_congr rfl fun D hD => by rw [(mem_powersetCard.mp hD).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, mul_comm]

private lemma icc_succ_eq_insert {a b : ℕ} (h : a ≤ b + 1) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

private def brunCap (upper : Bool) (b : ℕ → ℕ) (i : ℕ) : ℕ :=
  if upper then 2 * b i else 2 * b i - 1

private def brunPredIco (upper : Bool) (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (i : ℕ) (D : Finset ℕ) : Prop :=
  ∀ j ∈ Ico 1 i, (D ∩ Q j).card ≤ brunCap upper b j

private instance instDecidableBrunPredIco (upper : Bool) (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (i : ℕ) :
    DecidablePred (brunPredIco upper Q b i) :=
  fun _ => Finset.decidableDforallFinset

private def brunPred (upper : Bool) (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (r : ℕ) (D : Finset ℕ) : Prop :=
  ∀ i ∈ Icc 1 r, (D ∩ Q i).card ≤ brunCap upper b i

private instance instDecidableBrunPred (upper : Bool) (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (r : ℕ) :
    DecidablePred (brunPred upper Q b r) :=
  fun _ => Finset.decidableDforallFinset

/-- Unified Brun pointwise bound: for `upper = true`, the truncated inclusion-exclusion sum
upper-bounds `1_{B = ∅}`; for `upper = false`, it lower-bounds `1_{B = ∅}`. -/
private lemma brun_pointwise (upper : Bool) (P : ℕ → Finset ℕ) (b : ℕ → ℕ)
    (hb1 : 1 ≤ b 1) (hb_mono : ∀ i, 1 ≤ i → b i ≤ b (i + 1))
    (hdisj : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → Disjoint (P i) (P j)) :
    ∀ (r : ℕ) (B : Finset ℕ), B ⊆ (Icc 1 r).biUnion P →
      let sgn : ℝ := if upper then 1 else -1
      0 ≤ sgn * (∑ D ∈ B.powerset.filter (brunPred upper (fun k => (Icc 1 k).biUnion P) b r),
          (-1 : ℝ) ^ D.card - (if B = ∅ then (1 : ℝ) else 0)) := by
  have hb_ge1 : ∀ k, 1 ≤ k → 1 ≤ b k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hb1
    | succ m hm ih => exact ih.trans (hb_mono m hm)
  have hcap_mono : ∀ i, 1 ≤ i → brunCap upper b i ≤ brunCap upper b (i + 1) := by
    intro i hi
    have := hb_mono i hi
    cases upper <;> dsimp [brunCap] <;> omega
  intro r
  induction r with
  | zero =>
    intro B hB
    have hBe : B = ∅ := by
      rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hB
      exact Finset.subset_empty.mp hB
    subst hBe
    have hfilt : (∅ : Finset ℕ).powerset.filter
        (brunPred upper (fun k => (Icc 1 k).biUnion P) b 0) = {∅} := by
      ext D; simp [brunPred]
    dsimp only
    rw [hfilt]; simp
  | succ r ih =>
    intro B hB
    let Q : ℕ → Finset ℕ := fun k => (Icc 1 k).biUnion P
    have hQsucc : Q (r + 1) = Q r ∪ P (r + 1) := by
      dsimp [Q]
      rw [icc_succ_eq_insert (by omega : 1 ≤ r + 1), Finset.biUnion_insert, Finset.union_comm]
    have hQdisj : Disjoint (Q r) (P (r + 1)) := by
      rw [Finset.disjoint_left]
      intro x hxQ hxP
      rw [mem_biUnion] at hxQ
      obtain ⟨j, hj, hxj⟩ := hxQ
      have hj_mem := mem_Icc.mp hj
      exact Finset.disjoint_left.mp (hdisj j (r + 1) hj_mem.1 (by omega) (by omega)) hxj hxP
    let B' := B ∩ Q r
    let B₁ := B ∩ P (r + 1)
    have hB_union : B = B' ∪ B₁ := by
      ext x
      simp only [B', B₁, mem_union, mem_inter]
      constructor
      · intro hxB
        have hxQ : x ∈ Q (r + 1) := hB hxB
        rw [hQsucc, mem_union] at hxQ
        rcases hxQ with h | h
        · exact Or.inl ⟨hxB, h⟩
        · exact Or.inr ⟨hxB, h⟩
      · rintro (⟨hxB, _⟩ | ⟨hxB, _⟩) <;> exact hxB
    by_cases hB₁_empty : B₁ = ∅
    · have hBeq : B = B' := by rw [hB_union, hB₁_empty, Finset.union_empty]
      have hB_sub : B ⊆ Q r := by rw [hBeq]; exact Finset.inter_subset_right
      have hfilt_eq :
          B.powerset.filter (brunPred upper Q b (r + 1)) =
          B.powerset.filter (brunPred upper Q b r) := by
        ext D
        simp only [mem_filter, mem_powerset, brunPred]
        constructor
        · rintro ⟨hDB, hall⟩
          exact ⟨hDB, fun i hi => hall i (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans (Nat.le_succ r)⟩)⟩
        · rintro ⟨hDB, hall⟩
          refine ⟨hDB, fun i hi => ?_⟩
          have hi' := mem_Icc.mp hi
          by_cases hir : i ≤ r
          · exact hall i (mem_Icc.mpr ⟨hi'.1, hir⟩)
          · have hieq : i = r + 1 := by omega
            subst hieq
            have hDsub : D ⊆ Q r := hDB.trans hB_sub
            have hDQ : D ∩ Q (r + 1) = D := by
              rw [hQsucc]
              exact Finset.inter_eq_left.mpr (hDsub.trans Finset.subset_union_left)
            rw [hDQ]
            by_cases hr0 : r = 0
            · subst hr0
              have hDe : D = ∅ := by
                dsimp [Q] at hDsub
                rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hDsub
                exact Finset.subset_empty.mp hDsub
              subst hDe
              simp only [Finset.card_empty]
              exact Nat.zero_le _
            · have hr1 : 1 ≤ r := by omega
              have hDr := hall r (mem_Icc.mpr ⟨hr1, le_rfl⟩)
              rw [Finset.inter_eq_left.mpr hDsub] at hDr
              exact hDr.trans (hcap_mono r hr1)
      dsimp only
      change 0 ≤ (if upper then (1 : ℝ) else -1) *
        (∑ D ∈ B.powerset.filter (brunPred upper Q b (r + 1)), (-1 : ℝ) ^ D.card -
          if B = ∅ then 1 else 0)
      rw [hfilt_eq]
      exact ih B hB_sub
    · have hB₁_ne : B₁.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB₁_empty
      have hB_ne : B ≠ ∅ := by
        intro h
        obtain ⟨x, hx⟩ := hB₁_ne
        simp [B₁, h] at hx
      dsimp only
      rw [if_neg hB_ne, sub_zero]
      let M := brunCap upper b (r + 1)
      have hM_sgn : (if upper then (1 : ℝ) else -1) * (-1 : ℝ) ^ M = 1 := by
        cases upper
        · simp only [Bool.false_eq_true, ↓reduceIte, M, brunCap]
          have hbr1 : 1 ≤ b (r + 1) := hb_ge1 (r + 1) (by omega)
          have hMeq : 2 * b (r + 1) - 1 = 2 * (b (r + 1) - 1) + 1 := by omega
          rw [hMeq, pow_succ, pow_mul]; norm_num
        · simp only [↓reduceIte, M, brunCap, one_mul]
          rw [pow_mul]; norm_num
      let F_prev := B'.powerset.filter (brunPred upper Q b r)
      let F_full := B.powerset.filter (brunPred upper Q b (r + 1))
      let S_sig := F_prev.sigma fun D' => B₁.powerset.filter (fun D₁ => D₁.card ≤ M - D'.card)
      have hD'_le_M : ∀ D' ∈ F_prev, D'.card ≤ M := by
        intro D' hD'
        have hD'sub : D' ⊆ Q r := (mem_powerset.mp (mem_filter.mp hD').1).trans Finset.inter_subset_right
        by_cases hr0 : r = 0
        · subst hr0
          dsimp [Q] at hD'sub
          rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hD'sub
          rw [Finset.subset_empty.mp hD'sub]
          simp [M]
        · have hr1 : 1 ≤ r := by omega
          have h := (mem_filter.mp hD').2 r (mem_Icc.mpr ⟨hr1, le_rfl⟩)
          rw [Finset.inter_eq_left.mpr hD'sub] at h
          exact h.trans (hcap_mono r hr1)
      have hbij : ∑ D ∈ F_full, (-1 : ℝ) ^ D.card =
          ∑ x ∈ S_sig, (-1 : ℝ) ^ (x.1 ∪ x.2).card := by
        refine (Finset.sum_nbij (fun x => x.1 ∪ x.2) ?_ ?_ ?_ ?_).symm
        · intro x hx
          rw [mem_sigma] at hx
          obtain ⟨hD', hD₁⟩ := hx
          have hD'p := mem_filter.mp hD'
          have hD₁p := mem_filter.mp hD₁
          have hD'B' : x.1 ⊆ B' := mem_powerset.mp hD'p.1
          have hD₁B₁ : x.2 ⊆ B₁ := mem_powerset.mp hD₁p.1
          have hdisj_x : Disjoint x.1 x.2 :=
            Disjoint.mono (hD'B'.trans Finset.inter_subset_right)
              (hD₁B₁.trans Finset.inter_subset_right) hQdisj
          refine mem_filter.mpr ⟨mem_powerset.mpr ?_, fun i hi => ?_⟩
          · rw [hB_union]; exact Finset.union_subset_union hD'B' hD₁B₁
          · have hi' := mem_Icc.mp hi
            by_cases hir : i ≤ r
            · have hQi_sub : Q i ⊆ Q r :=
                Finset.biUnion_subset_biUnion_of_subset_left P (Finset.Icc_subset_Icc_right hir)
              have hdisj_2 : Disjoint x.2 (Q i) :=
                Disjoint.mono (hD₁B₁.trans Finset.inter_subset_right) hQi_sub hQdisj.symm
              have hinter : (x.1 ∪ x.2) ∩ Q i = x.1 ∩ Q i := by
                rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj_2,
                  Finset.union_empty]
              rw [hinter]
              exact hD'p.2 i (mem_Icc.mpr ⟨hi'.1, hir⟩)
            · have hieq : i = r + 1 := by omega
              subst hieq
              have hsub_Q : x.1 ∪ x.2 ⊆ Q (r + 1) := by
                rw [hQsucc]
                exact Finset.union_subset_union (hD'B'.trans Finset.inter_subset_right)
                  (hD₁B₁.trans Finset.inter_subset_right)
              rw [Finset.inter_eq_left.mpr hsub_Q, Finset.card_union_of_disjoint hdisj_x]
              have h1 := hD'_le_M x.1 hD'
              have h2 : x.2.card ≤ M - x.1.card := hD₁p.2
              change x.1.card + x.2.card ≤ M
              omega
        · intro x hx y hy hxy
          rw [mem_coe, mem_sigma] at hx hy
          have hx1 : x.1 ⊆ Q r := (mem_powerset.mp (mem_filter.mp hx.1).1).trans Finset.inter_subset_right
          have hx2 : x.2 ⊆ P (r + 1) := (mem_powerset.mp (mem_filter.mp hx.2).1).trans Finset.inter_subset_right
          have hy1 : y.1 ⊆ Q r := (mem_powerset.mp (mem_filter.mp hy.1).1).trans Finset.inter_subset_right
          have hy2 : y.2 ⊆ P (r + 1) := (mem_powerset.mp (mem_filter.mp hy.2).1).trans Finset.inter_subset_right
          have heq1 : x.1 = y.1 := by
            have := congrArg (· ∩ Q r) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx1,
              Finset.inter_eq_left.mpr hy1,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx2 hQdisj.symm),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy2 hQdisj.symm),
              Finset.union_empty] using this
          have heq2 : x.2 = y.2 := by
            have := congrArg (· ∩ P (r + 1)) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx2,
              Finset.inter_eq_left.mpr hy2,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx1 hQdisj),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy1 hQdisj),
              Finset.empty_union] using this
          exact Sigma.ext heq1 (heq_of_eq heq2)
        · intro D hD
          rw [mem_coe] at hD
          have hDp := mem_filter.mp hD
          have hDB : D ⊆ B := mem_powerset.mp hDp.1
          let D' := D ∩ Q r
          let D₁ := D ∩ P (r + 1)
          have hD_eq : D' ∪ D₁ = D := by
            ext z
            simp only [D', D₁, mem_union, mem_inter]
            constructor
            · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
            · intro hz
              have hzQ : z ∈ Q (r + 1) := hB (hDB hz)
              rw [hQsucc, mem_union] at hzQ
              rcases hzQ with h | h
              · exact Or.inl ⟨hz, h⟩
              · exact Or.inr ⟨hz, h⟩
          have hD'mem : D' ∈ F_prev := by
            refine mem_filter.mpr ⟨mem_powerset.mpr (Finset.inter_subset_inter_right hDB), fun i hi => ?_⟩
            have hi' := mem_Icc.mp hi
            have hQi_sub : Q i ⊆ Q r :=
              Finset.biUnion_subset_biUnion_of_subset_left P (Finset.Icc_subset_Icc_right hi'.2)
            have hinter : D' ∩ Q i = D ∩ Q i := by
              dsimp [D']
              rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hQi_sub]
            rw [hinter]
            exact hDp.2 i (mem_Icc.mpr ⟨hi'.1, hi'.2.trans (Nat.le_succ r)⟩)
          have hD₁mem : D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card) := by
            refine mem_filter.mpr ⟨mem_powerset.mpr (Finset.inter_subset_inter_right hDB), ?_⟩
            have hdisj_D : Disjoint D' D₁ :=
              Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hQdisj
            have htot := hDp.2 (r + 1) (mem_Icc.mpr ⟨by omega, le_rfl⟩)
            have hDQ : D ∩ Q (r + 1) = D := Finset.inter_eq_left.mpr (hDB.trans hB)
            rw [hDQ, ← hD_eq, Finset.card_union_of_disjoint hdisj_D] at htot
            change D₁.card ≤ M - D'.card
            dsimp [M]
            omega
          exact ⟨⟨D', D₁⟩, mem_coe.mpr (mem_sigma.mpr ⟨hD'mem, hD₁mem⟩), hD_eq⟩
        · intro _ _; rfl
      change 0 ≤ (if upper then (1 : ℝ) else -1) * ∑ D ∈ F_full, (-1 : ℝ) ^ D.card
      rw [hbij, Finset.sum_sigma, Finset.mul_sum]
      refine Finset.sum_nonneg fun D' hD' => ?_
      have hD'sub : D' ⊆ Q r := (mem_powerset.mp (mem_filter.mp hD').1).trans Finset.inter_subset_right
      have hfactor : ∑ D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card),
          (-1 : ℝ) ^ (D' ∪ D₁).card =
          (-1 : ℝ) ^ D'.card *
            ∑ D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card), (-1 : ℝ) ^ D₁.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun D₁ hD₁ => ?_
        have hD₁sub : D₁ ⊆ P (r + 1) :=
          (mem_powerset.mp (mem_filter.mp hD₁).1).trans Finset.inter_subset_right
        have hdisj_D : Disjoint D' D₁ := Disjoint.mono hD'sub hD₁sub hQdisj
        rw [Finset.card_union_of_disjoint hdisj_D, pow_add]
      rw [hfactor, alternating_powerset_eq,
        alternating_choose_sum (Finset.card_pos.mpr hB₁_ne)]
      have hrearr : (if upper then (1 : ℝ) else -1) *
          ((-1 : ℝ) ^ D'.card * ((-1 : ℝ) ^ (M - D'.card) * ((B₁.card - 1).choose (M - D'.card) : ℝ))) =
          ((if upper then (1 : ℝ) else -1) * ((-1 : ℝ) ^ D'.card * (-1 : ℝ) ^ (M - D'.card))) *
            ((B₁.card - 1).choose (M - D'.card) : ℝ) := by ring
      rw [hrearr, ← pow_add, Nat.add_sub_of_le (hD'_le_M D' hD'), hM_sgn, one_mul]
      exact Nat.cast_nonneg _

/-- Counting elements of `[1, y]` in a fixed residue class modulo `d > 0` has error at most `1`. -/
lemma count_modEq_Icc_error {d : ℕ} (hd : 0 < d) (k y : ℕ) :
    |(((Icc 1 y).filter fun m => m ≡ k [MOD d]).card : ℝ) - (y : ℝ) / (d : ℝ)| ≤ 1 := by
  let r := k % d
  let r' := if r = 0 then d else r
  have hr_lt : r < d := Nat.mod_lt k hd
  have hr'1 : 1 ≤ r' := by dsimp [r', r]; split_ifs <;> omega
  have hr'd : r' ≤ d := by dsimp [r', r]; split_ifs <;> omega
  have hr'mod : r' % d = r := by
    dsimp [r', r]
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt hr_lt
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  by_cases hyr : y < r'
  · have hemp : ((Icc 1 y).filter fun m => m ≡ k [MOD d]) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      rw [mem_filter, mem_Icc] at hm
      have hmod : m % d = r := hm.2
      have hm_lt : m < d := by omega
      have hmr : m = r := by rwa [Nat.mod_eq_of_lt hm_lt] at hmod
      dsimp [r'] at hyr
      split_ifs at hyr with h0 <;> omega
    rw [hemp, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity), div_le_one hd_pos]
    exact_mod_cast (show y ≤ d by omega)
  · push Not at hyr
    let q := (y - r') / d
    have hcard : ((Icc 1 y).filter fun m => m ≡ k [MOD d]).card = q + 1 := by
      have himg : ((Icc 1 y).filter fun m => m ≡ k [MOD d]) =
          (Finset.range (q + 1)).image (fun j => j * d + r') := by
        ext m
        simp only [mem_filter, mem_Icc, mem_image, mem_range]
        constructor
        · rintro ⟨⟨hm1, hmy⟩, hmod⟩
          have hmr' : r' ≤ m := by
            by_contra hlt
            push Not at hlt
            have hm_lt_d : m < d := by omega
            have := Nat.mod_eq_of_lt hm_lt_d
            have hmd : m % d = r := hmod
            dsimp [r'] at hlt
            split_ifs at hlt with h0 <;> omega
          have hdvd : d ∣ m - r' := by
            have h1 : m ≡ r' [MOD d] := hmod.trans (Nat.ModEq.symm (by
              change r' % d = k % d; exact hr'mod))
            exact (Nat.modEq_iff_dvd' hmr').mp h1.symm
          obtain ⟨j, hj⟩ := hdvd
          have hmeq : j * d + r' = m := by rw [Nat.mul_comm]; omega
          refine ⟨j, ?_, hmeq⟩
          have hj_le : j ≤ q := by
            dsimp [q]; exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
          omega
        · rintro ⟨j, hj, rfl⟩
          have hj_le : j ≤ q := by omega
          have hmul : j * d ≤ y - r' := by
            have hqmul : q * d ≤ y - r' := Nat.div_mul_le_self (y - r') d
            exact (Nat.mul_le_mul_right d hj_le).trans hqmul
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          change (j * d + r') % d = k % d
          rw [Nat.mul_add_mod_self_right, hr'mod]
      rw [himg, Finset.card_image_of_injective _ (fun j₁ j₂ h => by
        exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_right_cancel h)), Finset.card_range]
    rw [hcard, abs_le]
    have hlo_nat : q * d ≤ y := (Nat.div_mul_le_self (y - r') d).trans (Nat.sub_le y r')
    have hhi_nat : y < (q + 2) * d := by
      have hlt : y - r' < (q + 1) * d := by
        dsimp [q]
        rw [Nat.add_mul, Nat.one_mul]
        have hdm : ((y - r') / d) * d + (y - r') % d = y - r' := by
          rw [Nat.mul_comm]; exact Nat.div_add_mod (y - r') d
        have := Nat.mod_lt (y - r') hd
        omega
      rw [show q + 2 = (q + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    have hlo : (q : ℝ) ≤ (y : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]; exact_mod_cast hlo_nat
    have hhi : (y : ℝ) / (d : ℝ) ≤ (q : ℝ) + 2 := by
      rw [div_le_iff₀ hd_pos]
      have : (y : ℝ) < ((q + 2 : ℕ) : ℝ) * (d : ℝ) := by exact_mod_cast hhi_nat
      push_cast at this; linarith
    push_cast
    constructor <;> linarith

private lemma finset_prod_dvd_of_nat_coprime {D : Finset ℕ} {n : ℕ}
    (hcop : Set.Pairwise (D : Set ℕ) (Function.onFun Nat.Coprime id))
    (hdvd : ∀ p ∈ D, p ∣ n) : (∏ p ∈ D, p) ∣ n := by
  induction D using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.prod_cons]
    have hcop_s : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime id) :=
      hcop.mono fun x hx => Finset.mem_coe.mpr (Finset.mem_cons_of_mem (Finset.mem_coe.mp hx))
    have hs_dvd : (∏ p ∈ s, p) ∣ n := ih hcop_s (fun p hp => hdvd p (Finset.mem_cons_of_mem hp))
    have ha_dvd : a ∣ n := hdvd a (Finset.mem_cons_self a s)
    have ha_cop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        hcop (Finset.mem_coe.mpr (Finset.mem_cons_self a s))
          (Finset.mem_coe.mpr (Finset.mem_cons_of_mem hp))
          (fun heq => has (heq ▸ hp))
    exact ha_cop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

/-- Chinese remainder theorem equivalence for a finite set of primes. -/
lemma exists_crt_residue {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (a : ℕ → ℕ) :
    ∃ k : ℕ, ∀ m : ℕ, (∀ p ∈ D, m ≡ a p [MOD p]) ↔ m ≡ k [MOD (∏ p ∈ D, p)] := by
  let d := ∏ p ∈ D, p
  have hs : ∀ p ∈ D, id p ≠ 0 := fun p hp => (hD p hp).ne_zero
  have pp : Set.Pairwise (D : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hD p hp) (hD q hq)).2 hpq
  let k := Nat.chineseRemainderOfFinset a id D hs pp
  refine ⟨k, fun m => ?_⟩
  constructor
  · intro hm
    have hmk : ∀ p ∈ D, m ≡ (k : ℕ) [MOD p] := fun p hp => (hm p hp).trans (k.2 p hp).symm
    rcases le_total (k : ℕ) m with hle | hle
    · apply Nat.ModEq.symm
      apply (Nat.modEq_iff_dvd' hle).mpr
      exact finset_prod_dvd_of_nat_coprime pp fun p hp => (Nat.modEq_iff_dvd' hle).mp (hmk p hp).symm
    · apply (Nat.modEq_iff_dvd' hle).mpr
      exact finset_prod_dvd_of_nat_coprime pp fun p hp => (Nat.modEq_iff_dvd' hle).mp (hmk p hp)
  · intro hmd p hp
    have hpd : p ∣ d := Finset.dvd_prod_of_mem id hp
    exact (hmd.of_dvd hpd).trans (k.2 p hp)

/-- Chinese remainder theorem count of simultaneous residue hits in `[1, y]`. -/
private lemma crt_count_sub_div_le_one {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime)
    (a : ℕ → ℕ) (y : ℕ) :
    |(((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
      (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤ 1 := by
  let d := ∏ p ∈ D, p
  have hd_pos : 0 < d := Finset.prod_pos fun p hp => (hD p hp).pos
  obtain ⟨k, hk⟩ := exists_crt_residue hD a
  have hfilt : ((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]) =
      ((Icc 1 y).filter fun m => m ≡ k [MOD d]) := by
    ext m; simp only [mem_filter]; exact and_congr_right fun _ => hk m
  have hprod : (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹) = (y : ℝ) / (d : ℝ) := by
    rw [div_eq_mul_inv]; congr 1; dsimp [d]; rw [Nat.cast_prod, Finset.prod_inv_distrib]
  rw [hfilt, hprod]
  exact count_modEq_Icc_error hd_pos k y

private lemma eulerProd_eq_powerset_sum (S : Finset ℕ) :
    ∏ p ∈ S, (1 - (p : ℝ)⁻¹) =
      ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
  have h1 : ∏ p ∈ S, (1 - (p : ℝ)⁻¹) = ∏ p ∈ S, (-(p : ℝ)⁻¹ + 1) :=
    Finset.prod_congr rfl fun _ _ => by ring
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg]

private lemma eulerProd_ge_inv {z : ℕ} (hz : 1 ≤ z) :
    (z : ℝ)⁻¹ ≤ ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  have htele : ∏ n ∈ Icc 2 z, (1 - (n : ℝ)⁻¹) = (z : ℝ)⁻¹ := by
    induction z, hz using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 1), ih]
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      push_cast; field_simp; ring
  rw [← htele]
  have hsub : (range (z + 1)).filter Nat.Prime ⊆ Icc 2 z := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    exact mem_Icc.mpr ⟨hp.2.two_le, by omega⟩
  rw [← Finset.prod_sdiff hsub]
  have hle1 : ∏ n ∈ Icc 2 z \ (range (z + 1)).filter Nat.Prime, (1 - (n : ℝ)⁻¹) ≤ 1 := by
    apply Finset.prod_le_one
    · intro n hn
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (mem_Icc.mp (mem_sdiff.mp hn).1).1
      have hinv : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn2
      linarith
    · intro n _; have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      linarith
  have hpos : 0 ≤ ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    (eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2).le
  calc (∏ n ∈ Icc 2 z \ (range (z + 1)).filter Nat.Prime, (1 - (n : ℝ)⁻¹)) *
        (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
      ≤ 1 * (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_right hle1 hpos
    _ = _ := one_mul _

/-- Rankin's trick bound on the tail of reciprocal products over subsets of size `≥ m`. -/
private lemma brun_tail_bound (Q : Finset ℕ) (m : ℕ) :
    ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹) ≤
      Real.exp (-(m : ℝ) + Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
  have h1 : ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹) ≤
      Real.exp (-(m : ℝ)) *
        ∑ D ∈ Q.powerset, (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
    rw [Finset.mul_sum]
    calc ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹)
        ≤ ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card),
            Real.exp (-(m : ℝ)) * (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum fun D hD => ?_
          have hmD : (m : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast (mem_filter.mp hD).2
          rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul, mul_one,
            ← mul_assoc, ← Real.exp_add]
          have hexp_ge1 : (1 : ℝ) ≤ Real.exp (-(m : ℝ) + (D.card : ℝ)) :=
            Real.one_le_exp (by linarith)
          have hprod_nn : 0 ≤ ∏ p ∈ D, (p : ℝ)⁻¹ := Finset.prod_nonneg fun _ _ => by positivity
          calc ∏ p ∈ D, (p : ℝ)⁻¹ = 1 * ∏ p ∈ D, (p : ℝ)⁻¹ := (one_mul _).symm
            _ ≤ Real.exp (-(m : ℝ) + (D.card : ℝ)) * ∏ p ∈ D, (p : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_right hexp_ge1 hprod_nn
      _ ≤ ∑ D ∈ Q.powerset, Real.exp (-(m : ℝ)) * (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => ?_
          positivity
  have h2 : ∑ D ∈ Q.powerset, (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) =
      ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) := by
    have hadd := Finset.prod_add (fun p : ℕ => Real.exp 1 * (p : ℝ)⁻¹) (fun _ => (1 : ℝ)) Q
    have hcomm : ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) =
        ∏ p ∈ Q, (Real.exp 1 * (p : ℝ)⁻¹ + 1) :=
      Finset.prod_congr rfl fun _ _ => add_comm _ _
    rw [hcomm, hadd]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [Finset.prod_const_one, mul_one]
  have h3 : ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) ≤
      Real.exp (Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro _ _; positivity
    · intro p _; linarith [Real.add_one_le_exp (Real.exp 1 * (p : ℝ)⁻¹)]
  calc ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹)
      ≤ Real.exp (-(m : ℝ)) * Real.exp (Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.le.trans h3) (by positivity))
    _ = Real.exp (-(m : ℝ) + Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := (Real.exp_add _ _).symm

/-- Distinct finite sets of primes have distinct products. -/
private lemma prime_finset_prod_injOn (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (P.powerset : Set (Finset ℕ)) := by
  intro D₁ hD₁ D₂ hD₂ heq
  have hD₁p : ∀ p ∈ D₁, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_coe.mp hD₁) hp)
  have hD₂p : ∀ p ∈ D₂, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_coe.mp hD₂) hp)
  dsimp only at heq
  ext p
  constructor
  · intro hp
    have hdvd : p ∣ ∏ q ∈ D₂, q := by rw [← heq]; exact Finset.dvd_prod_of_mem id hp
    obtain ⟨q, hq, hpq⟩ := ((hD₁p p hp).prime.dvd_finsetProd_iff id).mp hdvd
    have hpeq : p = q := ((hD₂p q hq).eq_one_or_self_of_dvd p hpq).resolve_left (hD₁p p hp).ne_one
    rwa [hpeq]
  · intro hp
    have hdvd : p ∣ ∏ q ∈ D₁, q := by rw [heq]; exact Finset.dvd_prod_of_mem id hp
    obtain ⟨q, hq, hpq⟩ := ((hD₂p p hp).prime.dvd_finsetProd_iff id).mp hdvd
    have hpeq : p = q := ((hD₁p q hq).eq_one_or_self_of_dvd p hpq).resolve_left (hD₂p p hp).ne_one
    rwa [hpeq]

/-- Summation by parts identity for Brun's dyadic block exponents. -/
private lemma brun_dyadic_weight_bound (b K : ℕ) :
    ∀ r : ℕ, 1 ≤ r →
      ((2 * b + 2 * K * r : ℝ) / (2 : ℝ) ^ (r - 1)) +
        ∑ i ∈ Icc 1 (r - 1), ((2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i) =
      (2 * b + 4 * K : ℝ) - (2 * K : ℝ) / (2 : ℝ) ^ (r - 1) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => simp; ring
  | succ m hm ih =>
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    have hIcc : Icc 1 m = insert m (Icc 1 (m - 1)) := by
      ext i; simp only [mem_Icc, mem_insert]; omega
    have hnotmem : m ∉ Icc 1 (m - 1) := by simp only [mem_Icc]; omega
    rw [hIcc, Finset.sum_insert hnotmem]
    have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm]
    have hsum_eq : ∑ i ∈ Icc 1 (m - 1), ((2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i) =
        (2 * b + 4 * K : ℝ) - (2 * K : ℝ) / (2 : ℝ) ^ (m - 1) -
          ((2 * b + 2 * K * m : ℝ) / (2 : ℝ) ^ (m - 1)) := by linarith
    rw [hsum_eq, hpow]
    have h2m : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
    push_cast; field_simp; ring

private lemma geom_half_sum_le_one (r : ℕ) :
    ∑ i ∈ Icc 1 r, ((1 / 2 : ℝ) ^ i) ≤ 1 := by
  have heq : ∀ n : ℕ, ∑ i ∈ Icc 1 n, ((1 / 2 : ℝ) ^ i) = 1 - (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, pow_succ]; ring
  rw [heq r]
  have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ r := by positivity
  linarith

private lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h1 : Real.exp 1 ≤ (2 : ℝ) ^ 2 := by linarith [Real.exp_one_lt_d9]
  have h2 := Real.log_le_log (Real.exp_pos 1) h1
  rw [Real.log_exp, Real.log_pow] at h2
  push_cast at h2; linarith

/-- Reciprocal prime sum over `(cut i, z]` using `Sec1_Mertens.sum_inv_p_Ioc_le`. -/
private lemma brun_block_recip_sum_le {z i : ℕ} (hz : 16 ≤ z) (hi : 1 ≤ i) :
    let L := Nat.log 2 z + 1
    let c := min z (2 ^ (L / 2 ^ i))
    ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹ ≤ (4 * CM + 1) + 2 * (i : ℝ) := by
  intro L c
  have hlog2_pos : 0 < Real.log 2 := by linarith [half_le_log_two]
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hL_ge5 : 5 ≤ L := by
    dsimp [L]
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 4 ≤ z)
    omega
  have hc_eq : c = 2 ^ (L / 2 ^ i) := by
    dsimp [c]
    apply min_eq_right
    have hdiv : L / 2 ^ i ≤ L - 1 := by
      have h2i : 2 ≤ 2 ^ i := calc
        2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      have hq : L / 2 ^ i ≤ L / 2 := Nat.div_le_div_left h2i (by norm_num)
      omega
    have h1 : 2 ^ (L / 2 ^ i) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hdiv
    have h2 : 2 ^ (L - 1) ≤ z := by
      rw [show L - 1 = Nat.log 2 z from Nat.add_sub_cancel _ 1]
      exact Nat.pow_log_le_self 2 (by omega)
    exact h1.trans h2
  have hc_le_z : c ≤ z := min_le_left _ _
  have hz_lt_2L : (z : ℝ) < (2 : ℝ) ^ L := by
    have : z < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z
    exact_mod_cast this
  have hlogz_le : Real.log (z : ℝ) ≤ (L : ℝ) * Real.log 2 := by
    have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (show 0 < z by omega)
    calc Real.log (z : ℝ) ≤ Real.log ((2 : ℝ) ^ L) := Real.log_le_log hz_pos hz_lt_2L.le
      _ = (L : ℝ) * Real.log 2 := Real.log_pow 2 L
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  by_cases hc2 : 2 ≤ c
  · have hq1 : 1 ≤ L / 2 ^ i := by
      by_contra h0
      push Not at h0
      have h0' : L / 2 ^ i = 0 := Nat.lt_one_iff.mp h0
      rw [h0', pow_zero] at hc_eq
      omega
    have hbase := sum_inv_p_Ioc_le hc2 hc_le_z
    have hlogc_eq : Real.log (c : ℝ) = ((L / 2 ^ i : ℕ) : ℝ) * Real.log 2 := by
      rw [hc_eq]; push_cast; rw [Real.log_pow]
    have hlogc_ge_half : (1 : ℝ) / 2 ≤ Real.log (c : ℝ) := by
      rw [hlogc_eq]
      have h1 : (1 : ℝ) ≤ ((L / 2 ^ i : ℕ) : ℝ) := by exact_mod_cast hq1
      nlinarith [half_le_log_two]
    have hlogc_pos : 0 < Real.log (c : ℝ) := by linarith
    have hratio : Real.log (z : ℝ) / Real.log (c : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
      rw [div_le_iff₀ hlogc_pos, hlogc_eq]
      have hnat : L ≤ 2 ^ (i + 1) * (L / 2 ^ i) := by
        rw [pow_succ, Nat.mul_assoc]
        have hdm := Nat.div_add_mod L (2 ^ i)
        have hmod := Nat.mod_lt L (Nat.two_pow_pos i)
        have hL_le : L ≤ 2 ^ i * (L / 2 ^ i + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        exact hL_le.trans (Nat.mul_le_mul_left _ (by omega : L / 2 ^ i + 1 ≤ 2 * (L / 2 ^ i)))
      have hnat_r : (L : ℝ) ≤ (2 : ℝ) ^ (i + 1) * ((L / 2 ^ i : ℕ) : ℝ) := by exact_mod_cast hnat
      calc Real.log (z : ℝ) ≤ (L : ℝ) * Real.log 2 := hlogz_le
        _ ≤ ((2 : ℝ) ^ (i + 1) * ((L / 2 ^ i : ℕ) : ℝ)) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hnat_r hlog2_pos.le
        _ = (2 : ℝ) ^ (i + 1) * (((L / 2 ^ i : ℕ) : ℝ) * Real.log 2) := by ring
    have hlog_ratio : Real.log (Real.log (z : ℝ) / Real.log (c : ℝ)) ≤ (i : ℝ) + 1 := by
      calc Real.log (Real.log (z : ℝ) / Real.log (c : ℝ))
          ≤ Real.log ((2 : ℝ) ^ (i + 1)) := Real.log_le_log (div_pos hlogz_pos hlogc_pos) hratio
        _ = ((i + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (i + 1)
        _ ≤ (i : ℝ) + 1 := by push_cast; nlinarith
    have herr : 2 * CM / Real.log (c : ℝ) ≤ 4 * CM := by
      rw [div_le_iff₀ hlogc_pos]; have := CM_pos; nlinarith
    have hi_r : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    linarith
  · push Not at hc2
    have hdiv0 : L / 2 ^ i = 0 := by
      by_contra hne
      have h1 : 1 ≤ L / 2 ^ i := Nat.pos_of_ne_zero hne
      have h2 : 2 ≤ 2 ^ (L / 2 ^ i) := calc
        2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (L / 2 ^ i) := Nat.pow_le_pow_right (by norm_num) h1
      rw [← hc_eq] at h2; omega
    have hL_lt : L < 2 ^ i := (Nat.div_eq_zero_iff.mp hdiv0).resolve_left (Nat.two_pow_pos i).ne'
    have hsub : (Ioc c z).filter Nat.Prime ⊆
        insert 2 ((Ioc 2 z).filter Nat.Prime) := by
      intro q hq
      rw [mem_filter, mem_Ioc] at hq
      rw [mem_insert, mem_filter, mem_Ioc]
      by_cases hq2 : q = 2
      · exact Or.inl hq2
      · have := hq.2.two_le; exact Or.inr ⟨⟨by omega, hq.1.2⟩, hq.2⟩
    have h2_not : 2 ∉ (Ioc 2 z).filter Nat.Prime := by simp
    have hsum_split : ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹ ≤
        (2 : ℝ)⁻¹ + ∑ q ∈ (Ioc 2 z).filter Nat.Prime, (q : ℝ)⁻¹ := by
      calc ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹
          ≤ ∑ q ∈ insert 2 ((Ioc 2 z).filter Nat.Prime), (q : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = (2 : ℝ)⁻¹ + ∑ q ∈ (Ioc 2 z).filter Nat.Prime, (q : ℝ)⁻¹ := by
            rw [Finset.sum_insert h2_not]; norm_num
    have hbase := sum_inv_p_Ioc_le (show 2 ≤ 2 by norm_num) (by omega : 2 ≤ z)
    have hratio : Real.log (z : ℝ) / Real.log (2 : ℝ) ≤ (2 : ℝ) ^ i := by
      rw [div_le_iff₀ hlog2_pos]
      have hL_le : (L : ℝ) ≤ (2 : ℝ) ^ i := by exact_mod_cast hL_lt.le
      calc Real.log (z : ℝ) ≤ (L : ℝ) * Real.log 2 := hlogz_le
        _ ≤ (2 : ℝ) ^ i * Real.log 2 := mul_le_mul_of_nonneg_right hL_le hlog2_pos.le
    have hlog_ratio : Real.log (Real.log (z : ℝ) / Real.log (2 : ℝ)) ≤ (i : ℝ) := by
      calc Real.log (Real.log (z : ℝ) / Real.log (2 : ℝ))
          ≤ Real.log ((2 : ℝ) ^ i) := Real.log_le_log (div_pos hlogz_pos hlog2_pos) hratio
        _ = (i : ℝ) * Real.log 2 := Real.log_pow 2 i
        _ ≤ (i : ℝ) := by nlinarith
    have herr : 2 * CM / Real.log (2 : ℝ) ≤ 4 * CM := by
      rw [div_le_iff₀ hlog2_pos]; have := CM_pos; nlinarith [half_le_log_two]
    have hi_r : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have hcast2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hcast2] at hbase
    linarith

/-- Product bound for every divisor set `D` retained in Brun's combinatorial sieve. -/
private lemma brun_prod_le {z b K : ℕ} (hz : 16 ≤ z)
    (D : Finset ℕ) (hD_sub : D ⊆ (range (z + 1)).filter Nat.Prime)
    (hD_brun :
      let L := Nat.log 2 z + 1
      let r := Nat.log 2 L + 1
      let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
      ∀ i ∈ Icc 1 r, (D ∩ (Ioc (cut i) z).filter Nat.Prime).card ≤ 2 * (b + K * i)) :
    ∏ p ∈ D, p ≤ z ^ (4 * b + 8 * K) := by
  let L := Nat.log 2 z + 1
  let r := Nat.log 2 L + 1
  let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
  let P : ℕ → Finset ℕ := fun i => (Ioc (cut i) (cut (i - 1))).filter Nat.Prime
  have hr_ge1 : 1 ≤ r := by dsimp [r]; omega
  have hcut_anti : Antitone cut := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst hi0; dsimp only [cut]; rw [if_pos rfl]; split_ifs
      · exact le_rfl
      · exact min_le_left z _
    · have hj0 : j ≠ 0 := by omega
      dsimp only [cut]; rw [if_neg hi0, if_neg hj0]
      apply min_le_min_left z
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hij) (Nat.two_pow_pos i))
  have hcut_r : cut r = 1 := by
    dsimp [cut, r]
    have hlt : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
    rw [Nat.div_eq_of_lt hlt, pow_zero]
    exact min_eq_right (by omega)
  have hcut_le_pow : ∀ i : ℕ, cut i ≤ 2 ^ (L / 2 ^ i) := by
    intro i; dsimp [cut]; split_ifs with h0
    · subst h0; rw [pow_zero, Nat.div_one]
      exact le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z)
    · exact min_le_right _ _
  have hP_disj : (Icc 1 r : Set ℕ).PairwiseDisjoint P := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have h1 := mem_Ioc.mp (mem_filter.mp hpi).1
    have h2 := mem_Ioc.mp (mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : cut (j - 1) ≤ cut i := hcut_anti (by omega); omega
    · have : cut (i - 1) ≤ cut j := hcut_anti (by omega); omega
  have hP_union : ∀ k ≤ r, (Icc 1 k).biUnion P = (Ioc (cut k) z).filter Nat.Prime := by
    intro k hk
    induction k with
    | zero => simp [cut]
    | succ m hm =>
      rw [icc_succ_eq_insert (by omega : 1 ≤ m + 1), Finset.biUnion_insert, hm (by omega)]
      ext p
      simp only [P, mem_union, mem_filter, mem_Ioc, Nat.add_sub_cancel]
      have hm1 : cut (m + 1) ≤ cut m := hcut_anti (Nat.le_succ m)
      have hm2 : cut m ≤ z := hcut_anti (Nat.zero_le m)
      constructor
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨h1, h2.trans hm2⟩, hp⟩
        · exact ⟨⟨lt_of_le_of_lt hm1 h1, h2⟩, hp⟩
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases hpm : p ≤ cut m
        · exact Or.inl ⟨⟨h1, hpm⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
  have hD_part : D = (Icc 1 r).biUnion (fun i => D ∩ P i) := by
    have hfull : (range (z + 1)).filter Nat.Prime = (Icc 1 r).biUnion P := by
      rw [hP_union r le_rfl, hcut_r]
      ext p; simp only [mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨hpz, hpp⟩; exact ⟨⟨hpp.one_lt, by omega⟩, hpp⟩
      · rintro ⟨⟨_, hpz⟩, hpp⟩; exact ⟨by omega, hpp⟩
    rw [← Finset.inter_biUnion, ← hfull, Finset.inter_eq_left.mpr hD_sub]
  have hDP_disj : (Icc 1 r : Set ℕ).PairwiseDisjoint (fun i => D ∩ P i) := by
    intro i hi j hj hij
    rw [Function.onFun]
    exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hP_disj hi hj hij)
  have hprod_bound : ∏ p ∈ D, p ≤ 2 ^ (∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1))) := by
    conv_lhs => rw [hD_part]
    rw [Finset.prod_biUnion hDP_disj, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun i _ => ?_
    calc ∏ p ∈ D ∩ P i, p ≤ ∏ _p ∈ D ∩ P i, 2 ^ (L / 2 ^ (i - 1)) := by
          refine Finset.prod_le_prod' fun p hp => ?_
          have hp_le : p ≤ cut (i - 1) := (mem_Ioc.mp (mem_filter.mp (mem_inter.mp hp).2).1).2
          exact hp_le.trans (hcut_le_pow (i - 1))
      _ = (2 ^ (L / 2 ^ (i - 1))) ^ (D ∩ P i).card := Finset.prod_const _
      _ = 2 ^ ((D ∩ P i).card * (L / 2 ^ (i - 1))) := by rw [← pow_mul, Nat.mul_comm]
  let N : ℕ → ℝ := fun k => ((D ∩ (Ioc (cut k) z).filter Nat.Prime).card : ℝ)
  have hN0 : N 0 = 0 := by simp [N, cut]
  have hN_step : ∀ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) = N i - N (i - 1) := by
    intro i hi
    have hi' := mem_Icc.mp hi
    have hdisj_i : Disjoint (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime) (D ∩ P i) := by
      rw [← hP_union (i - 1) (by omega), Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (mem_inter.mp hp1).2
      have h2 := (mem_inter.mp hp2).2
      rw [mem_biUnion] at h1
      obtain ⟨j, hj, hpj⟩ := h1
      have hj' := mem_Icc.mp hj
      exact Finset.disjoint_left.mp
        (hP_disj (mem_coe.mpr (mem_Icc.mpr ⟨hj'.1, by omega⟩)) (mem_coe.mpr hi) (by omega)) hpj h2
    have hunion_i : D ∩ (Ioc (cut i) z).filter Nat.Prime =
        (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime) ∪ (D ∩ P i) := by
      rw [← hP_union i hi'.2, ← hP_union (i - 1) (by omega)]
      have hIcc : Icc 1 i = insert i (Icc 1 (i - 1)) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, Finset.biUnion_insert, Finset.inter_union_distrib_left, Finset.union_comm]
    have hcard_add : (D ∩ (Ioc (cut i) z).filter Nat.Prime).card =
        (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime).card + (D ∩ P i).card := by
      rw [hunion_i, Finset.card_union_of_disjoint hdisj_i]
    have hcard_r : N i = N (i - 1) + ((D ∩ P i).card : ℝ) := by
      dsimp [N]; exact_mod_cast hcard_add
    linarith
  have hN_le : ∀ i ∈ Icc 1 r, N i ≤ (2 * b + 2 * K * i : ℝ) := by
    intro i hi
    have hle_r : N i ≤ ((2 * (b + K * i) : ℕ) : ℝ) := by dsimp [N]; exact_mod_cast hD_brun i hi
    push_cast at hle_r; linarith
  have hexp_real : ((∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1)) : ℕ) : ℝ) ≤
      ((2 * b + 4 * K) * L : ℝ) := by
    push_cast
    have h1 : ∑ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) * ((L / 2 ^ (i - 1) : ℕ) : ℝ) ≤
        ∑ i ∈ Icc 1 r, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [hN_step i hi]
      have hnn : 0 ≤ N i - N (i - 1) := by rw [← hN_step i hi]; exact Nat.cast_nonneg _
      have hdiv : ((L / 2 ^ (i - 1) : ℕ) : ℝ) ≤ (L : ℝ) / (2 : ℝ) ^ (i - 1) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self L (2 ^ (i - 1))
      exact mul_le_mul_of_nonneg_left hdiv hnn
    have hsbp : ∑ i ∈ Icc 1 r, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) =
        (L : ℝ) * (N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i) := by
      have htele : ∀ n : ℕ, 1 ≤ n →
          ∑ i ∈ Icc 1 n, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) =
          (L : ℝ) * (N n / (2 : ℝ) ^ (n - 1) + ∑ i ∈ Icc 1 (n - 1), N i / (2 : ℝ) ^ i) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => simp [hN0]; ring
        | succ m hm ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
          rw [show m + 1 - 1 = m by omega]
          have hIcc : Icc 1 m = insert m (Icc 1 (m - 1)) := by
            ext i; simp only [mem_Icc, mem_insert]; omega
          have hnotmem : m ∉ Icc 1 (m - 1) := by simp only [mem_Icc]; omega
          rw [hIcc, Finset.sum_insert hnotmem]
          have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hm]
          rw [hpow]
          have h2m : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
          field_simp; ring
      exact htele r hr_ge1
    have h2 : N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i ≤
        (2 * b + 4 * K : ℝ) := by
      have hterm1 : N r / (2 : ℝ) ^ (r - 1) ≤ (2 * b + 2 * K * r : ℝ) / (2 : ℝ) ^ (r - 1) :=
        div_le_div_of_nonneg_right (hN_le r (mem_Icc.mpr ⟨hr_ge1, le_rfl⟩)) (by positivity)
      have hterm2 : ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i ≤
          ∑ i ∈ Icc 1 (r - 1), (2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := mem_Icc.mp hi
        exact div_le_div_of_nonneg_right (hN_le i (mem_Icc.mpr ⟨hi'.1, by omega⟩)) (by positivity)
      have hident := brun_dyadic_weight_bound b K r hr_ge1
      have hKnn : (0 : ℝ) ≤ (2 * K : ℝ) / (2 : ℝ) ^ (r - 1) := by positivity
      linarith
    calc ∑ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) * ((L / 2 ^ (i - 1) : ℕ) : ℝ)
        ≤ (L : ℝ) * (N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i) :=
          h1.trans_eq hsbp
      _ ≤ (L : ℝ) * (2 * b + 4 * K : ℝ) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg L)
      _ = ((2 * b + 4 * K) * L : ℝ) := by ring
  have hexp_nat : ∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1)) ≤ (2 * b + 4 * K) * L := by
    exact_mod_cast hexp_real
  have h2L_le : 2 ^ L ≤ z ^ 2 := by
    have h1 : 2 ^ (Nat.log 2 z) ≤ z := Nat.pow_log_le_self 2 (by omega)
    dsimp [L]; rw [pow_succ, sq]; nlinarith
  calc ∏ p ∈ D, p ≤ 2 ^ (∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1))) := hprod_bound
    _ ≤ 2 ^ ((2 * b + 4 * K) * L) := Nat.pow_le_pow_right (by norm_num) hexp_nat
    _ = (2 ^ L) ^ (2 * b + 4 * K) := by rw [Nat.mul_comm, pow_mul]
    _ ≤ (z ^ 2) ^ (2 * b + 4 * K) := Nat.pow_le_pow_left h2L_le _
    _ = z ^ (4 * b + 8 * K) := by rw [← pow_mul]; congr 1; ring

/-- Explicit parameters for the unified exponential Brun sieve. -/
noncomputable def kBrun0 : ℕ := ⌈2 + Real.exp 1⌉₊
noncomputable def kBrun : ℕ := kBrun0 + 1
noncomputable def aBrun : ℝ := (kBrun0 : ℝ) * (4 * CM + 1)
noncomputable def sBrun : ℕ := 16 * kBrun + 12
noncomputable def cBrun : ℝ := Real.exp (aBrun + 4 * (kBrun : ℝ) + 3) + 1

lemma cBrun_pos : 0 < cBrun := by
  unfold cBrun; positivity

lemma sBrun_ge_twelve : 12 ≤ sBrun := by
  unfold sBrun; omega

/-- Sieved count in `[1, y]` avoiding `a p (mod p)` for all primes `p ≤ z`. -/
def sievedCount (y z : ℕ) (a : ℕ → ℕ) : ℕ :=
  ((Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card

/-- Euler product up to `z`. -/
noncomputable def Vprod (z : ℕ) : ℝ :=
  ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)

set_option maxHeartbeats 800000 in
/-- Unified one-sided exponential Brun bound (`upper = true` gives upper bound, `upper = false`
gives lower bound). -/
private lemma brun_sieve_one_sided (upper : Bool) {z y : ℕ} {s : ℝ}
    (hz16 : 16 ≤ z) (hs : (sBrun : ℝ) ≤ s) (hzy : (z : ℝ) ^ s ≤ (y : ℝ)) (a : ℕ → ℕ) :
    let sgn : ℝ := if upper then 1 else -1
    sgn * ((sievedCount y z a : ℝ) - (y : ℝ) * Vprod z) ≤
      cBrun * Real.exp (-s / 4) * ((y : ℝ) * Vprod z) := by
  intro sgn
  have hK0 : 2 + Real.exp 1 ≤ (kBrun0 : ℝ) := Nat.le_ceil _
  let K := kBrun
  let A := aBrun
  let sNat := ⌊s⌋₊
  have hsNat_ge : sBrun ≤ sNat := Nat.le_floor hs
  have hsNat_le_s : (sNat : ℝ) ≤ s := Nat.floor_le (by have := sBrun_ge_twelve; linarith [show (12 : ℝ) ≤ (sBrun : ℝ) by exact_mod_cast this])
  have hs_lt_succ : s < (sNat : ℝ) + 1 := Nat.lt_floor_add_one s
  let b : ℕ := (sNat - 16 * K - 4) / 8
  have hb1 : 1 ≤ b := by
    dsimp [b, K]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mpr (by unfold sBrun at hsNat_ge; omega)
  have hs_lo : 8 * b + 16 * K + 4 ≤ sNat := by
    have hmul : b * 8 ≤ sNat - 16 * K - 4 := Nat.div_mul_le_self (sNat - 16 * K - 4) 8
    unfold sBrun at hsNat_ge; dsimp [K] at *; omega
  have hs_hi : sNat ≤ 8 * b + 16 * K + 11 := by
    have hdm : b * 8 + (sNat - 16 * K - 4) % 8 = sNat - 16 * K - 4 := by
      dsimp [b]; rw [Nat.mul_comm]; exact Nat.div_add_mod _ 8
    have hlt : (sNat - 16 * K - 4) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    unfold sBrun at hsNat_ge; dsimp [K] at *; omega
  let P_all := (range (z + 1)).filter Nat.Prime
  let L := Nat.log 2 z + 1
  let r := Nat.log 2 L + 1
  let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
  let P : ℕ → Finset ℕ := fun i => (Ioc (cut i) (cut (i - 1))).filter Nat.Prime
  let Q : ℕ → Finset ℕ := fun i => (Ioc (cut i) z).filter Nat.Prime
  let bf : ℕ → ℕ := fun i => b + K * i
  have hr_ge1 : 1 ≤ r := by dsimp [r]; omega
  have hcut_anti : Antitone cut := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst hi0; dsimp only [cut]; rw [if_pos rfl]; split_ifs
      · exact le_rfl
      · exact min_le_left z _
    · have hj0 : j ≠ 0 := by omega
      dsimp only [cut]; rw [if_neg hi0, if_neg hj0]
      apply min_le_min_left z
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hij) (Nat.two_pow_pos i))
  have hcut_r : cut r = 1 := by
    dsimp [cut, r]
    have hlt : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
    rw [Nat.div_eq_of_lt hlt, pow_zero]
    exact min_eq_right (by omega)
  have hP_disj : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → Disjoint (P i) (P j) := by
    intro i j _ _ hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have h1 := mem_Ioc.mp (mem_filter.mp hpi).1
    have h2 := mem_Ioc.mp (mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : cut (j - 1) ≤ cut i := hcut_anti (by omega); omega
    · have : cut (i - 1) ≤ cut j := hcut_anti (by omega); omega
  have hQ_eq : ∀ k ≤ r, (Icc 1 k).biUnion P = Q k := by
    intro k hk
    induction k with
    | zero => simp [Q, cut]
    | succ m hm =>
      rw [icc_succ_eq_insert (by omega : 1 ≤ m + 1), Finset.biUnion_insert, hm (by omega)]
      ext p
      simp only [P, Q, mem_union, mem_filter, mem_Ioc, Nat.add_sub_cancel]
      have hm1 : cut (m + 1) ≤ cut m := hcut_anti (Nat.le_succ m)
      have hm2 : cut m ≤ z := hcut_anti (Nat.zero_le m)
      constructor
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨h1, h2.trans hm2⟩, hp⟩
        · exact ⟨⟨lt_of_le_of_lt hm1 h1, h2⟩, hp⟩
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases hpm : p ≤ cut m
        · exact Or.inl ⟨⟨h1, hpm⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
  have hP_all_eq : P_all = (Icc 1 r).biUnion P := by
    rw [hQ_eq r le_rfl]
    dsimp [P_all, Q]; rw [hcut_r]
    ext p; simp only [mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hpz, hpp⟩; exact ⟨⟨hpp.one_lt, by omega⟩, hpp⟩
    · rintro ⟨⟨_, hpz⟩, hpp⟩; exact ⟨by omega, hpp⟩
  let D_brun := P_all.powerset.filter (brunPred upper Q bf r)
  -- Step 1: Pointwise Brun bound summed over `m ∈ Icc 1 y`.
  have hstep1 :
      sgn * (sievedCount y z a : ℝ) ≤
      sgn * ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
        (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) := by
    let B : ℕ → Finset ℕ := fun m => P_all.filter (fun p => m ≡ a p [MOD p])
    have hsurv : (sievedCount y z a : ℝ) = ∑ m ∈ Icc 1 y, (if B m = ∅ then (1 : ℝ) else 0) := by
      unfold sievedCount
      rw [Finset.sum_boole]
      congr 2; ext m
      simp only [B, P_all, mem_filter, Finset.eq_empty_iff_forall_notMem, mem_range]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h p ⟨⟨hpz, hpp⟩, hmod⟩; exact h p (by omega) hpp hmod
      · intro h p hpz hpp hmod; exact h p ⟨⟨by omega, hpp⟩, hmod⟩
    have hswap :
        ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
          (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) =
        ∑ m ∈ Icc 1 y, ∑ D ∈ D_brun,
          if ∀ p ∈ D, m ≡ a p [MOD p] then (-1 : ℝ) ^ D.card else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_comm]
    rw [hsurv, hswap, ← sub_nonneg, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_nonneg fun m _ => ?_
    have hBm_sub : B m ⊆ (Icc 1 r).biUnion P := by rw [← hP_all_eq]; exact Finset.filter_subset _ _
    have hfilt_eq : D_brun.filter (fun D => ∀ p ∈ D, m ≡ a p [MOD p]) =
        (B m).powerset.filter (brunPred upper (fun k => (Icc 1 k).biUnion P) bf r) := by
      ext D
      simp only [D_brun, B, brunPred, mem_filter, mem_powerset]
      constructor
      · rintro ⟨⟨hDP, hDb⟩, hDm⟩
        refine ⟨fun p hp => mem_filter.mpr ⟨hDP hp, hDm p hp⟩, fun i hi => ?_⟩
        rw [hQ_eq i (mem_Icc.mp hi).2]; exact hDb i hi
      · rintro ⟨hDB, hDb⟩
        refine ⟨⟨fun p hp => (mem_filter.mp (hDB hp)).1, fun i hi => ?_⟩,
          fun p hp => (mem_filter.mp (hDB hp)).2⟩
        rw [← hQ_eq i (mem_Icc.mp hi).2]; exact hDb i hi
    rw [← Finset.sum_filter, hfilt_eq]
    exact brun_pointwise upper P bf (by dsimp [bf]; omega)
      (fun i _ => by dsimp [bf]; rw [Nat.mul_succ]; omega) hP_disj r (B m) hBm_sub
  -- Step 2: CRT approximation for every retained divisor `D ∈ D_brun`.
  have hstep2 :
      sgn * ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
        (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) ≤
      sgn * ((y : ℝ) * ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) +
        (D_brun.card : ℝ) := by
    have hdiff :
        |∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
          ((((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
            (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹))| ≤ (D_brun.card : ℝ) := by
      calc |∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
              ((((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
                (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹))|
          ≤ ∑ D ∈ D_brun, |(-1 : ℝ) ^ D.card *
              ((((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
                (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _D ∈ D_brun, (1 : ℝ) := by
            refine Finset.sum_le_sum fun D hD => ?_
            have hDp : ∀ p ∈ D, p.Prime := fun p hp =>
              (mem_filter.mp (mem_powerset.mp (mem_filter.mp hD).1 hp)).2
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            exact crt_count_sub_div_le_one hDp a y
        _ = (D_brun.card : ℝ) := by simp
    have hrew : ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
          ((((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
            (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹)) =
        (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
          (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ)) -
        (y : ℝ) * ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun _ _ => by ring
    rw [hrew] at hdiff
    have hsgn_abs : |sgn| = 1 := by dsimp [sgn]; cases upper <;> norm_num
    have hmul_abs : |sgn * ((∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
          (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ)) -
        (y : ℝ) * ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹))| ≤ (D_brun.card : ℝ) := by
      rw [abs_mul, hsgn_abs, one_mul]; exact hdiff
    have hmul := (abs_le.mp hmul_abs).2
    linarith
  -- Step 3: Bound the truncation tail `|Vprod z - ∑_{D ∈ D_brun} (-1)^|D| w(D)|`.
  have hVz_pos : 0 < Vprod z := eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2
  have htrunc :
      |Vprod z - ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤
        Real.exp (A - 2 * (b : ℝ)) * Vprod z := by
    have hsub_D : D_brun ⊆ P_all.powerset := Finset.filter_subset _ _
    let Bad : ℕ → Finset (Finset ℕ) := fun i =>
      P_all.powerset.filter fun D =>
        brunPredIco upper Q bf i D ∧ brunCap upper bf i + 1 ≤ (D ∩ Q i).card
    have hBad_pw : (Icc 1 r : Set ℕ).PairwiseDisjoint Bad := by
      intro i hi j hj hij
      rw [Function.onFun, Finset.disjoint_left]
      intro D hDi hDj
      have h1 := (mem_filter.mp hDi).2
      have h2 := (mem_filter.mp hDj).2
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have := h2.1 i (mem_Ico.mpr ⟨(mem_Icc.mp hi).1, hlt⟩); omega
      · have := h1.1 j (mem_Ico.mpr ⟨(mem_Icc.mp hj).1, hgt⟩); omega
    have hBad_eq : P_all.powerset \ D_brun = (Icc 1 r).biUnion Bad := by
      ext D
      simp only [Finset.mem_sdiff, mem_biUnion, D_brun, Bad, mem_filter]
      simp only [brunPred, brunPredIco]
      constructor
      · rintro ⟨hDP, hnot⟩
        let S := (Icc 1 r).filter fun i => brunCap upper bf i + 1 ≤ (D ∩ Q i).card
        have hS_ne : S.Nonempty := by
          by_contra hnone
          rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem] at hnone
          refine hnot ⟨hDP, fun i hi => ?_⟩
          have hni := hnone i
          simp only [S, mem_filter, hi, true_and, not_le] at hni; omega
        let i := S.min' hS_ne
        have hi_p := mem_filter.mp (Finset.min'_mem S hS_ne)
        refine ⟨i, hi_p.1, hDP, fun j hj => ?_, hi_p.2⟩
        have hj' := mem_Ico.mp hj
        have hj_not : j ∉ S := fun hjS => (not_le_of_gt hj'.2) (Finset.min'_le S j hjS)
        have hj_icc : j ∈ Icc 1 r := mem_Icc.mpr ⟨hj'.1, hj'.2.le.trans (mem_Icc.mp hi_p.1).2⟩
        simp only [S, mem_filter, hj_icc, true_and, not_le] at hj_not; omega
      · rintro ⟨i, hi, hDP, _, hviol⟩
        refine ⟨hDP, fun h => ?_⟩
        have hle := h.2 i hi; omega
    have hdiff_eq : Vprod z - ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) =
        ∑ i ∈ Icc 1 r, ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
      rw [show Vprod z = ∑ D ∈ P_all.powerset, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) from
        eulerProd_eq_powerset_sum P_all, ← Finset.sum_sdiff hsub_D, add_sub_cancel_right,
        hBad_eq, Finset.sum_biUnion hBad_pw]
    rw [hdiff_eq]
    have hterm_i : ∀ i ∈ Icc 1 r,
        |∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤
          Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * Vprod z := by
      intro i hi
      have hi' := mem_Icc.mp hi
      let P_lo := (range (cut i + 1)).filter Nat.Prime
      have hQP_disj : Disjoint (Q i) P_lo := by
        rw [Finset.disjoint_left]
        intro p hpQ hpL
        have h1 := (mem_Ioc.mp (mem_filter.mp hpQ).1).1
        have h2 := mem_range.mp (mem_filter.mp hpL).1
        omega
      have hQP_union : Q i ∪ P_lo = P_all := by
        ext p
        simp only [Q, P_lo, P_all, mem_union, mem_filter, mem_Ioc, mem_range]
        have hcz : cut i ≤ z := hcut_anti (Nat.zero_le i)
        constructor
        · rintro (⟨⟨_, h2⟩, hp⟩ | ⟨h1, hp⟩) <;> exact ⟨by omega, hp⟩
        · rintro ⟨h1, hp⟩
          by_cases hpc : p ≤ cut i
          · exact Or.inr ⟨by omega, hp⟩
          · exact Or.inl ⟨⟨by omega, by omega⟩, hp⟩
      let A_i := (Q i).powerset.filter fun D₁ =>
        brunPredIco upper Q bf i D₁ ∧ brunCap upper bf i + 1 ≤ D₁.card
      have hfac : ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) =
          (∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)) * Vprod (cut i) := by
        rw [show Vprod (cut i) = ∑ D₂ ∈ P_lo.powerset, (-1 : ℝ) ^ D₂.card * (∏ p ∈ D₂, (p : ℝ)⁻¹) from
          eulerProd_eq_powerset_sum P_lo, Finset.sum_mul_sum, ← Finset.sum_product']
        refine (Finset.sum_nbij (fun x : Finset ℕ × Finset ℕ => x.1 ∪ x.2) ?_ ?_ ?_ ?_).symm
        · intro x hx
          rw [mem_product] at hx
          obtain ⟨hD₁, hD₂⟩ := hx
          have hD₁p := mem_filter.mp hD₁
          have hD₁Q : x.1 ⊆ Q i := mem_powerset.mp hD₁p.1
          have hD₂L : x.2 ⊆ P_lo := mem_powerset.mp hD₂
          refine mem_filter.mpr ⟨mem_powerset.mpr ?_, fun j hj => ?_, ?_⟩
          · rw [← hQP_union]; exact Finset.union_subset_union hD₁Q hD₂L
          · have hj' := mem_Ico.mp hj
            have hQj_sub : Q j ⊆ Q i := by
              intro p hp
              rw [mem_filter, mem_Ioc] at hp ⊢
              have : cut i ≤ cut j := hcut_anti hj'.2.le
              exact ⟨⟨lt_of_le_of_lt this hp.1.1, hp.1.2⟩, hp.2⟩
            have hdisj2 : Disjoint x.2 (Q j) := Disjoint.mono hD₂L hQj_sub hQP_disj.symm
            rw [Finset.union_inter_distrib_right,
              Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            exact hD₁p.2.1 j hj
          · have hdisj2 : Disjoint x.2 (Q i) := Disjoint.mono_left hD₂L hQP_disj.symm
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hD₁Q,
              Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            exact hD₁p.2.2
        · intro x hx y hy hxy
          rw [mem_coe, mem_product] at hx hy
          have hx1 : x.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hx.1).1
          have hx2 : x.2 ⊆ P_lo := mem_powerset.mp hx.2
          have hy1 : y.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hy.1).1
          have hy2 : y.2 ⊆ P_lo := mem_powerset.mp hy.2
          have heq1 : x.1 = y.1 := by
            have := congrArg (· ∩ Q i) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx1,
              Finset.inter_eq_left.mpr hy1,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx2 hQP_disj.symm),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy2 hQP_disj.symm),
              Finset.union_empty] using this
          have heq2 : x.2 = y.2 := by
            have := congrArg (· ∩ P_lo) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx2,
              Finset.inter_eq_left.mpr hy2,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx1 hQP_disj),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy1 hQP_disj),
              Finset.empty_union] using this
          exact Prod.ext heq1 heq2
        · intro D hD
          rw [mem_coe] at hD
          have hDp := mem_filter.mp hD
          have hDP : D ⊆ P_all := mem_powerset.mp hDp.1
          let D₁ := D ∩ Q i
          let D₂ := D ∩ P_lo
          have hDeq : D₁ ∪ D₂ = D := by
            rw [← Finset.inter_union_distrib_left, hQP_union, Finset.inter_eq_left.mpr hDP]
          have hD₁mem : D₁ ∈ A_i := by
            refine mem_filter.mpr ⟨mem_powerset.mpr Finset.inter_subset_right, fun j hj => ?_, hDp.2.2⟩
            have hj' := mem_Ico.mp hj
            have hQj_sub : Q j ⊆ Q i := by
              intro p hp
              rw [mem_filter, mem_Ioc] at hp ⊢
              have : cut i ≤ cut j := hcut_anti hj'.2.le
              exact ⟨⟨lt_of_le_of_lt this hp.1.1, hp.1.2⟩, hp.2⟩
            dsimp [D₁]; rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hQj_sub]
            exact hDp.2.1 j hj
          exact ⟨(D₁, D₂), mem_coe.mpr (mem_product.mpr ⟨hD₁mem, mem_powerset.mpr Finset.inter_subset_right⟩), hDeq⟩
        · intro x hx
          rw [mem_product] at hx
          have hx1 : x.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hx.1).1
          have hx2 : x.2 ⊆ P_lo := mem_powerset.mp hx.2
          have hdisj : Disjoint x.1 x.2 := Disjoint.mono hx1 hx2 hQP_disj
          rw [Finset.card_union_of_disjoint hdisj, pow_add, Finset.prod_union hdisj]; ring
      have hVcut_pos : 0 < Vprod (cut i) := eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2
      rw [hfac, abs_mul, abs_of_pos hVcut_pos]
      have hAi_le : |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| ≤
          ∑ D₁ ∈ (Q i).powerset.filter (fun D₁ => 2 * bf i ≤ D₁.card),
            (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
        calc |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)|
            ≤ ∑ D₁ ∈ A_i, |(-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ D₁ ∈ A_i, (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
              refine Finset.sum_congr rfl fun D₁ _ => ?_
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
          _ ≤ ∑ D₁ ∈ (Q i).powerset.filter (fun D₁ => 2 * bf i ≤ D₁.card),
                (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ =>
                Finset.prod_nonneg fun _ _ => by positivity)
              intro D₁ hD₁
              have h := mem_filter.mp hD₁
              have hbf1 : 1 ≤ bf i := by dsimp [bf]; omega
              have hge : 2 * bf i ≤ brunCap upper bf i + 1 := by
                cases upper <;> dsimp [brunCap] <;> omega
              exact mem_filter.mpr ⟨h.1, hge.trans h.2.2⟩
      let S_i := ∑ q ∈ Q i, (q : ℝ)⁻¹
      have hV_ratio : Vprod (cut i) ≤ Real.exp (2 * S_i) * Vprod z := by
        have hVsplit : Vprod z = Vprod (cut i) * ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹) := by
          dsimp [Vprod]
          rw [show (range (z + 1)).filter Nat.Prime = Q i ∪ P_lo from hQP_union.symm,
            Finset.prod_union hQP_disj, mul_comm]
        have hQprod_pos : 0 < ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹) :=
          eulerProd_pos _ fun _ hq => (mem_filter.mp hq).2
        have hQinv : (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))⁻¹ ≤ Real.exp (2 * S_i) := by
          rw [← Finset.prod_inv_distrib, Finset.mul_sum, Real.exp_sum]
          apply Finset.prod_le_prod
          · intro q hq
            have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.two_le
            have hinv : (q : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq2
            exact inv_nonneg.mpr (by linarith)
          · intro q hq; exact one_sub_inv_inv_le_exp_two (mem_filter.mp hq).2.two_le
        rw [hVsplit]
        calc Vprod (cut i) = Vprod (cut i) * ((∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))⁻¹ *
              (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))) := by rw [inv_mul_cancel₀ hQprod_pos.ne', mul_one]
          _ ≤ Vprod (cut i) * (Real.exp (2 * S_i) * (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))) := by
              gcongr
          _ = Real.exp (2 * S_i) * (Vprod (cut i) * ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹)) := by ring
      have hS_i : S_i ≤ (4 * CM + 1) + 2 * (i : ℝ) := by
        have hcut_eq : cut i = min z (2 ^ (L / 2 ^ i)) := if_neg (by omega)
        dsimp [S_i, Q]; rw [hcut_eq]; exact brun_block_recip_sum_le hz16 hi'.1
      have htail := brun_tail_bound (Q i) (2 * bf i)
      have hcomb_exp : -(2 * bf i : ℕ) + Real.exp 1 * S_i + 2 * S_i ≤
          A - 2 * (b : ℝ) - 2 * (i : ℝ) := by
        have hS_nn : 0 ≤ S_i := Finset.sum_nonneg fun _ _ => by positivity
        have h1 : (2 + Real.exp 1) * S_i ≤ (kBrun0 : ℝ) * ((4 * CM + 1) + 2 * (i : ℝ)) :=
          mul_le_mul hK0 hS_i hS_nn (by positivity)
        have hbf_cast : ((2 * bf i : ℕ) : ℝ) = 2 * (b : ℝ) + 2 * ((kBrun0 : ℝ) + 1) * (i : ℝ) := by
          dsimp [bf, K, kBrun]; push_cast; ring
        rw [hbf_cast]
        dsimp [A, aBrun]; linarith
      have hexp_half : Real.exp (-2 * (i : ℝ)) ≤ (1 / 2 : ℝ) ^ i := by
        have h2e : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
        have he_le : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2e
        have hpow : Real.exp (-2 * (i : ℝ)) = (Real.exp (-2 : ℝ)) ^ i := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [hpow]; exact pow_le_pow_left₀ (by positivity) he_le i
      calc |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| * Vprod (cut i)
          ≤ Real.exp (-(2 * bf i : ℕ) + Real.exp 1 * S_i) * (Real.exp (2 * S_i) * Vprod z) :=
            mul_le_mul (hAi_le.trans htail) hV_ratio
              (eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2).le (by positivity)
        _ = Real.exp (-(2 * bf i : ℕ) + Real.exp 1 * S_i + 2 * S_i) * Vprod z := by
            rw [← mul_assoc, ← Real.exp_add]
        _ ≤ Real.exp (A - 2 * (b : ℝ) - 2 * (i : ℝ)) * Vprod z :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcomb_exp) hVz_pos.le
        _ = Real.exp (A - 2 * (b : ℝ)) * Real.exp (-2 * (i : ℝ)) * Vprod z := by
            rw [← Real.exp_add]; congr 2; ring
        _ ≤ Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * Vprod z := by
            have h1 := mul_le_mul_of_nonneg_left hexp_half (by positivity : 0 ≤ Real.exp (A - 2 * (b : ℝ)))
            exact mul_le_mul_of_nonneg_right h1 hVz_pos.le
    calc |∑ i ∈ Icc 1 r, ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)|
        ≤ ∑ i ∈ Icc 1 r, |∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Icc 1 r, Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * Vprod z :=
          Finset.sum_le_sum hterm_i
      _ = Real.exp (A - 2 * (b : ℝ)) * (∑ i ∈ Icc 1 r, (1 / 2 : ℝ) ^ i) * Vprod z := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ Real.exp (A - 2 * (b : ℝ)) * 1 * Vprod z := by
          have h1 := mul_le_mul_of_nonneg_left (geom_half_sum_le_one r)
            (by positivity : 0 ≤ Real.exp (A - 2 * (b : ℝ)))
          exact mul_le_mul_of_nonneg_right h1 hVz_pos.le
      _ = Real.exp (A - 2 * (b : ℝ)) * Vprod z := by rw [mul_one]
  -- Step 4: Bound `D_brun.card ≤ z ^ (4 * b + 8 * K)` using `brun_prod_le`.
  have hD_card : D_brun.card ≤ z ^ (4 * b + 8 * K) := by
    have hsub_D : D_brun ⊆ P_all.powerset := Finset.filter_subset _ _
    have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (D_brun : Set (Finset ℕ)) :=
      (prime_finset_prod_injOn P_all fun _ hp => (mem_filter.mp hp).2).mono
        (Finset.coe_subset.mpr hsub_D)
    have hmaps : Set.MapsTo (fun D : Finset ℕ => ∏ p ∈ D, p) (D_brun : Set (Finset ℕ))
        (Icc 1 (z ^ (4 * b + 8 * K)) : Set ℕ) := by
      intro D hD
      rw [mem_coe] at hD ⊢
      have hDp := mem_filter.mp hD
      have hDsub : D ⊆ P_all := mem_powerset.mp hDp.1
      have hpos : 1 ≤ ∏ p ∈ D, p :=
        Finset.prod_pos fun p hp => (mem_filter.mp (hDsub hp)).2.pos
      have hcap_le : ∀ i ∈ Icc 1 r, (D ∩ Q i).card ≤ 2 * (b + K * i) := fun i hi => by
        have h1 := hDp.2 i hi
        cases upper <;> dsimp [brunCap, bf] at h1 ⊢ <;> omega
      exact mem_Icc.mpr ⟨hpos, brun_prod_le hz16 D hDsub hcap_le⟩
    have hle := Finset.card_le_card_of_injOn (fun D : Finset ℕ => ∏ p ∈ D, p) hmaps hinj
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hle
  -- Step 5: Exponential bounds on both errors.
  have herr_trunc : Real.exp (A - 2 * (b : ℝ)) ≤
      Real.exp (A + 4 * (K : ℝ) + 3) * Real.exp (-s / 4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs_hi_r : (sNat : ℝ) ≤ 8 * (b : ℝ) + 16 * (K : ℝ) + 11 := by exact_mod_cast hs_hi
    linarith
  have herr_crt : (D_brun.card : ℝ) ≤ Real.exp (-s / 4) * ((y : ℝ) * Vprod z) := by
    have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (show 0 < z by omega)
    have hVz_ge : (z : ℝ)⁻¹ ≤ Vprod z := eulerProd_ge_inv (by omega)
    have hlogz_ge1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
      have h1 : Real.exp 1 ≤ (z : ℝ) := by
        have : (16 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz16
        linarith [Real.exp_one_lt_d9]
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h1
    have hs_pos : 0 < s := by
      have : (12 : ℝ) ≤ (sBrun : ℝ) := by exact_mod_cast sBrun_ge_twelve
      linarith
    have hexp_le_rpow : Real.exp (s / 4) ≤ (z : ℝ) ^ (s / 4) := by
      rw [Real.rpow_def_of_pos hz_pos]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hexp_sum : ((4 * b + 8 * K + 1 : ℕ) : ℝ) + s / 4 ≤ s := by
      have hlo_r : (8 * (b : ℝ) + 16 * (K : ℝ) + 4) ≤ (sNat : ℝ) := by exact_mod_cast hs_lo
      push_cast; linarith
    have hD_mul : (D_brun.card : ℝ) * (z : ℝ) * Real.exp (s / 4) ≤ (y : ℝ) := by
      have hcard_r : (D_brun.card : ℝ) ≤ (z : ℝ) ^ (4 * b + 8 * K) := by exact_mod_cast hD_card
      calc (D_brun.card : ℝ) * (z : ℝ) * Real.exp (s / 4)
          ≤ (z : ℝ) ^ (4 * b + 8 * K) * (z : ℝ) * (z : ℝ) ^ (s / 4) := by
            have h1 := mul_le_mul_of_nonneg_right hcard_r hz_pos.le
            exact mul_le_mul h1 hexp_le_rpow (Real.exp_pos _).le (by positivity)
        _ = (z : ℝ) ^ ((4 * b + 8 * K + 1 : ℕ) : ℝ) * (z : ℝ) ^ (s / 4) := by
            rw [Real.rpow_natCast, pow_succ]
        _ = (z : ℝ) ^ (((4 * b + 8 * K + 1 : ℕ) : ℝ) + s / 4) := (Real.rpow_add hz_pos _ _).symm
        _ ≤ (z : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ z by omega)) hexp_sum
        _ ≤ (y : ℝ) := hzy
    have hmul_inv := mul_le_mul_of_nonneg_right hD_mul (mul_nonneg (inv_nonneg.mpr hz_pos.le) (Real.exp_pos (-s / 4)).le)
    have hlhs : (D_brun.card : ℝ) * (z : ℝ) * Real.exp (s / 4) * ((z : ℝ)⁻¹ * Real.exp (-s / 4)) =
        (D_brun.card : ℝ) := by
      have h1 : Real.exp (s / 4) * Real.exp (-s / 4) = 1 := by
        rw [← Real.exp_add, show s / 4 + -s / 4 = 0 by ring, Real.exp_zero]
      have hz_ne : (z : ℝ) ≠ 0 := hz_pos.ne'
      calc (D_brun.card : ℝ) * (z : ℝ) * Real.exp (s / 4) * ((z : ℝ)⁻¹ * Real.exp (-s / 4))
          = (D_brun.card : ℝ) * ((z : ℝ) * (z : ℝ)⁻¹) * (Real.exp (s / 4) * Real.exp (-s / 4)) := by ring
        _ = (D_brun.card : ℝ) := by rw [mul_inv_cancel₀ hz_ne, h1, mul_one, mul_one]
    rw [hlhs] at hmul_inv
    calc (D_brun.card : ℝ) ≤ (y : ℝ) * ((z : ℝ)⁻¹ * Real.exp (-s / 4)) := hmul_inv
      _ = Real.exp (-s / 4) * ((y : ℝ) * (z : ℝ)⁻¹) := by ring
      _ ≤ Real.exp (-s / 4) * ((y : ℝ) * Vprod z) := by gcongr
  -- Step 6: Combine Steps 1-5.
  have hsgn_abs : |sgn| = 1 := by dsimp [sgn]; cases upper <;> norm_num
  have hmain : sgn * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) - Vprod z) ≤
      Real.exp (A + 4 * (K : ℝ) + 3) * Real.exp (-s / 4) * Vprod z := by
    have h1 : |sgn * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) - Vprod z)| ≤
        Real.exp (A - 2 * (b : ℝ)) * Vprod z := by
      rw [abs_mul, hsgn_abs, one_mul, abs_sub_comm]; exact htrunc
    exact (abs_le.mp h1).2.trans (mul_le_mul_of_nonneg_right herr_trunc hVz_pos.le)
  have hmain_y := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg y)
  have hcomb : sgn * ((sievedCount y z a : ℝ) - (y : ℝ) * Vprod z) ≤
      (y : ℝ) * (Real.exp (A + 4 * (K : ℝ) + 3) * Real.exp (-s / 4) * Vprod z) +
        (D_brun.card : ℝ) := by
    have h12 := hstep1.trans hstep2
    linarith
  have hcb_eq : cBrun * Real.exp (-s / 4) * ((y : ℝ) * Vprod z) =
      (y : ℝ) * (Real.exp (A + 4 * (K : ℝ) + 3) * Real.exp (-s / 4) * Vprod z) +
        Real.exp (-s / 4) * ((y : ℝ) * Vprod z) := by
    dsimp [cBrun, A, K]; ring
  linarith

/-- Uniform two-sided exponential Brun Fundamental Lemma for all `z ≥ 16`, `s ≥ sBrun`, `y ≥ z ^ s`. -/
lemma brun_sieve_two_sided {z y : ℕ} {s : ℝ} (hz : 16 ≤ z) (hs : (sBrun : ℝ) ≤ s)
    (hzy : (z : ℝ) ^ s ≤ (y : ℝ)) (a : ℕ → ℕ) :
    |(sievedCount y z a : ℝ) - (y : ℝ) * Vprod z| ≤
      cBrun * Real.exp (-s / 4) * ((y : ℝ) * Vprod z) := by
  rw [abs_le]
  have hup := brun_sieve_one_sided true hz hs hzy a
  have hlo := brun_sieve_one_sided false hz hs hzy a
  simp only [↓reduceIte, Bool.false_eq_true, one_mul, neg_one_mul] at hup hlo
  constructor <;> linarith

/-- Existence of modular inverse of `M` modulo a coprime `q > 1`. -/
private lemma exists_mul_modEq_one {M q : ℕ} (hcop : Nat.Coprime M q) :
    ∃ u : ℕ, M * u ≡ 1 [MOD q] := by
  by_cases hq0 : q = 0
  · subst hq0
    have hM1 : M = 1 := by simpa using hcop
    exact ⟨1, by simp [hM1]⟩
  · have hq_pos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hq0)
    let u : ℕ := ((Nat.gcdA M q) % (q : ℤ)).toNat
    have hu_nn : 0 ≤ (Nat.gcdA M q) % (q : ℤ) := Int.emod_nonneg _ hq_pos.ne'
    have hu_cast : (u : ℤ) = (Nat.gcdA M q) % (q : ℤ) := Int.toNat_of_nonneg hu_nn
    refine ⟨u, ?_⟩
    rw [← Int.natCast_modEq_iff]
    push_cast
    rw [hu_cast]
    have hbez : (1 : ℤ) = (M : ℤ) * Nat.gcdA M q + (q : ℤ) * Nat.gcdB M q := by
      have h := Nat.gcd_eq_gcd_ab M q
      rw [hcop.gcd_eq_one] at h
      exact_mod_cast h
    have h1 : (M : ℤ) * (Nat.gcdA M q % (q : ℤ)) ≡ (M : ℤ) * Nat.gcdA M q [ZMOD (q : ℤ)] :=
      Int.ModEq.mul_left _ (Int.mod_modEq _ _)
    have h2 : (M : ℤ) * Nat.gcdA M q ≡ (1 : ℤ) [ZMOD (q : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨Nat.gcdB M q, by linarith⟩
    exact h1.trans h2

section ProgressionCorollaries
open scoped Classical

/-- CRT reduction of a progression-sifted count `Z d Q` to a plain shifted sieve `sievedCount Y' z a'`
with `|Y' - Y / ∏ d| ≤ 1`. -/
lemma card_Z_eq_sievedCount {Y z : ℕ} {d : Finset ℕ}
    (hd_prime : ∀ p ∈ d, p.Prime) (hd_gt : ∀ p ∈ d, z < p) (a : ℕ → ℕ) :
    ∃ Y' : ℕ, ∃ a' : ℕ → ℕ,
      |((Y' : ℝ) - (Y : ℝ) / (∏ p ∈ d, (p : ℝ)))| ≤ 1 ∧
      ((Icc 1 Y).filter fun n =>
        (∀ p ∈ d, n ≡ a p [MOD p]) ∧
        ∀ q ∈ (range (z + 1)).filter Nat.Prime, ¬ (n ≡ a q [MOD q])).card =
      sievedCount Y' z a' := by
  let M : ℕ := ∏ p ∈ d, p
  have hM_pos : 0 < M := Finset.prod_pos fun p hp => (hd_prime p hp).pos
  have hM_cast : (M : ℝ) = ∏ p ∈ d, (p : ℝ) := by dsimp [M]; rw [Nat.cast_prod]
  obtain ⟨k, hk⟩ := exists_crt_residue hd_prime a
  let r := k % M
  let r₀ := if r = 0 then M else r
  have hr_lt : r < M := Nat.mod_lt k hM_pos
  have hr₀1 : 1 ≤ r₀ := by dsimp [r₀, r]; split_ifs <;> omega
  have hr₀M : r₀ ≤ M := by dsimp [r₀, r]; split_ifs <;> omega
  have hr₀mod : r₀ % M = r := by
    dsimp [r₀, r]
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt hr_lt
  -- Construct shifted residue function `a' q` for primes `q ≤ z`.
  have hcop_q : ∀ q : ℕ, q ≤ z → q.Prime → Nat.Coprime M q := by
    intro q hqz hqp
    dsimp [M]
    exact Nat.Coprime.prod_left fun p hp =>
      (Nat.coprime_primes (hd_prime p hp) hqp).mpr (by have := hd_gt p hp; omega)
  let a' : ℕ → ℕ := fun q =>
    if h : q ≤ z ∧ q.Prime then
      let u := Classical.choose (exists_mul_modEq_one (hcop_q q h.1 h.2))
      let t := (q - r₀ % q) % q
      (a q + t) * u + 1
    else 0
  by_cases hYr : Y < r₀
  · refine ⟨0, a', ?_, ?_⟩
    · rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity), ← hM_cast,
        div_le_one (by exact_mod_cast hM_pos)]
      exact_mod_cast (show Y ≤ M by omega)
    · have hemp : ((Icc 1 Y).filter fun n =>
          (∀ p ∈ d, n ≡ a p [MOD p]) ∧
          ∀ q ∈ (range (z + 1)).filter Nat.Prime, ¬ (n ≡ a q [MOD q])) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro n hn
        simp only [mem_filter, mem_Icc] at hn
        have hmod : n % M = r := (hk n).mp hn.2.1
        have hn_lt : n < M := by omega
        have hnr : n = r := by rwa [Nat.mod_eq_of_lt hn_lt] at hmod
        dsimp [r₀] at hYr
        split_ifs at hYr with h0 <;> omega
      rw [hemp, Finset.card_empty]
      unfold sievedCount; simp
  · push Not at hYr
    let qY := (Y - r₀) / M
    let Y' := qY + 1
    refine ⟨Y', a', ?_, ?_⟩
    · have hM_pos_r : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
      rw [← hM_cast, abs_le]
      have hlo_nat : qY * M ≤ Y := (Nat.div_mul_le_self (Y - r₀) M).trans (Nat.sub_le Y r₀)
      have hhi_nat : Y < (qY + 2) * M := by
        have hlt : Y - r₀ < (qY + 1) * M := by
          dsimp [qY]; rw [Nat.add_mul, Nat.one_mul]
          have hdm : ((Y - r₀) / M) * M + (Y - r₀) % M = Y - r₀ := by
            rw [Nat.mul_comm]; exact Nat.div_add_mod (Y - r₀) M
          have := Nat.mod_lt (Y - r₀) hM_pos; omega
        rw [show qY + 2 = (qY + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]; omega
      have hlo : (qY : ℝ) ≤ (Y : ℝ) / (M : ℝ) := by
        rw [le_div_iff₀ hM_pos_r]; exact_mod_cast hlo_nat
      have hhi : (Y : ℝ) / (M : ℝ) ≤ (qY : ℝ) + 2 := by
        rw [div_le_iff₀ hM_pos_r]
        have : (Y : ℝ) < ((qY + 2 : ℕ) : ℝ) * (M : ℝ) := by exact_mod_cast hhi_nat
        push_cast at this; linarith
      dsimp [Y']; push_cast; constructor <;> linarith
    · -- Bijection `j ∈ Icc 1 Y' ↦ (j - 1) * M + r₀`.
      have hiff_q : ∀ j : ℕ, 1 ≤ j → ∀ q : ℕ, q ≤ z → q.Prime →
          (((j - 1) * M + r₀) ≡ a q [MOD q] ↔ j ≡ a' q [MOD q]) := by
        intro j hj q hqz hqp
        have hspec := Classical.choose_spec (exists_mul_modEq_one (hcop_q q hqz hqp))
        set u := Classical.choose (exists_mul_modEq_one (hcop_q q hqz hqp))
        set t := (q - r₀ % q) % q
        have ha'_eq : a' q = (a q + t) * u + 1 := by
          dsimp [a']; rw [dif_pos ⟨hqz, hqp⟩]
        rw [ha'_eq]
        have hrt0 : r₀ + t ≡ 0 [MOD q] := by
          change (r₀ + t) % q = 0 % q
          rw [Nat.zero_mod, Nat.add_mod, Nat.mod_mod]
          have hlt : r₀ % q < q := Nat.mod_lt r₀ hqp.pos
          by_cases h0 : r₀ % q = 0
          · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero, Nat.zero_mod]
          · rw [Nat.mod_eq_of_lt (by omega : q - r₀ % q < q), Nat.add_sub_of_le hlt.le, Nat.mod_self]
        constructor
        · intro h
          have h1 : (j - 1) * M + (r₀ + t) ≡ a q + t [MOD q] := by
            have := h.add_right t; rwa [Nat.add_assoc] at this
          have h2 : (j - 1) * M + (r₀ + t) ≡ (j - 1) * M + 0 [MOD q] :=
            Nat.ModEq.add_left _ hrt0
          have h3 : (j - 1) * M ≡ a q + t [MOD q] := by
            have := h2.symm.trans h1; rwa [Nat.add_zero] at this
          have h4 : (j - 1) * (M * u) ≡ (a q + t) * u [MOD q] := by
            have := h3.mul_right u; rwa [Nat.mul_assoc] at this
          have h5 : (j - 1) * (M * u) ≡ (j - 1) * 1 [MOD q] := Nat.ModEq.mul_left _ hspec
          have h6 : j - 1 ≡ (a q + t) * u [MOD q] := by
            have := h5.symm.trans h4; rwa [Nat.mul_one] at this
          have h7 := h6.add_right 1
          rwa [Nat.sub_add_cancel hj] at h7
        · intro h
          have h1 : (j - 1) + 1 ≡ (a q + t) * u + 1 [MOD q] := by
            rwa [Nat.sub_add_cancel hj]
          have h2 : j - 1 ≡ (a q + t) * u [MOD q] := Nat.ModEq.add_right_cancel' 1 h1
          have h3 : (j - 1) * M ≡ (a q + t) * (M * u) [MOD q] := by
            have := h2.mul_right M
            simpa [Nat.mul_assoc, Nat.mul_comm u M] using this
          have h4 : (a q + t) * (M * u) ≡ (a q + t) * 1 [MOD q] := Nat.ModEq.mul_left _ hspec
          have h5 : (j - 1) * M ≡ a q + t [MOD q] := by
            have := h3.trans h4; rwa [Nat.mul_one] at this
          have h6 : (j - 1) * M + r₀ ≡ a q + (r₀ + t) [MOD q] := by
            have := h5.add_right r₀
            simpa [Nat.add_assoc, Nat.add_comm t r₀] using this
          have h7 : a q + (r₀ + t) ≡ a q + 0 [MOD q] := Nat.ModEq.add_left _ hrt0
          have h8 := h6.trans h7
          rwa [Nat.add_zero] at h8
      unfold sievedCount
      symm
      refine Finset.card_bij (fun j _ => (j - 1) * M + r₀) ?_ ?_ ?_
      · intro j hj
        rw [mem_filter, mem_Icc] at hj
        obtain ⟨⟨hj1, hjY'⟩, havoid⟩ := hj
        have hmul : (j - 1) * M ≤ Y - r₀ := by
          have hj_le : j - 1 ≤ qY := by dsimp [Y'] at hjY'; omega
          exact (Nat.mul_le_mul_right M hj_le).trans (Nat.div_mul_le_self (Y - r₀) M)
        simp only [mem_filter, mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
        · rw [hk]
          change ((j - 1) * M + r₀) % M = k % M
          rw [Nat.mul_add_mod_self_right, hr₀mod]
        · intro q hq hhit
          have hqz : q ≤ z := by have := mem_range.mp hq.1; omega
          exact havoid q hqz hq.2 ((hiff_q j hj1 q hqz hq.2).mp hhit)
      · intro j₁ hj₁ j₂ hj₂ heq
        have h1 : 1 ≤ j₁ := (mem_Icc.mp (mem_filter.mp hj₁).1).1
        have h2 : 1 ≤ j₂ := (mem_Icc.mp (mem_filter.mp hj₂).1).1
        have := Nat.eq_of_mul_eq_mul_right hM_pos (Nat.add_right_cancel heq)
        omega
      · intro n hn
        simp only [mem_filter, mem_Icc] at hn
        obtain ⟨⟨hn1, hnY⟩, hcong, havoid⟩ := hn
        have hmod : n ≡ k [MOD M] := (hk n).mp hcong
        have hnr₀ : r₀ ≤ n := by
          by_contra hlt; push Not at hlt
          have hn_lt : n < M := by omega
          have h1 := Nat.mod_eq_of_lt hn_lt
          have h2 : n % M = r := hmod
          dsimp [r₀] at hlt; split_ifs at hlt with h0 <;> omega
        have hdvd : M ∣ n - r₀ := by
          have h1 : n ≡ r₀ [MOD M] := hmod.trans (Nat.ModEq.symm (by
            change r₀ % M = k % M; exact hr₀mod))
          exact (Nat.modEq_iff_dvd' hnr₀).mp h1.symm
        obtain ⟨t, ht⟩ := hdvd
        have hneq : t * M + r₀ = n := by rw [Nat.mul_comm]; omega
        have ht_le : t ≤ qY := by
          dsimp [qY]; exact (Nat.le_div_iff_mul_le hM_pos).mpr (by omega)
        refine ⟨t + 1, ?_, by simpa [Nat.add_sub_cancel] using hneq⟩
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by dsimp [Y']; omega⟩, ?_⟩
        intro q hqz hqp hhit
        have hhit' : n ≡ a q [MOD q] := by
          rw [← hneq]
          have := (hiff_q (t + 1) (by omega) q hqz hqp).mpr hhit
          simpa [Nat.add_sub_cancel] using this
        exact havoid q ⟨mem_range.mpr (by omega), hqp⟩ hhit'

/-- Explicit constants for the two progression sieve corollaries. -/
noncomputable def cEnv : ℝ := 2 * cBrun * Real.exp (3 / 4) + Real.exp 2
noncomputable def cBad : ℝ :=
  2 * (1 + cBrun) * Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) + 1

lemma cEnv_pos : 0 < cEnv := by
  unfold cEnv; have := cBrun_pos; positivity

lemma cBad_pos : 0 < cBad := by
  unfold cBad; have := cBrun_pos; positivity

/-- Piece 1 corollary: exponential Brun envelope on long progressions `g(d) ≥ sBrun + 4`. -/
lemma brun_progression_envelope {w : ℝ} {Y : ℕ} (hw : 16 ≤ w)
    {d : Finset ℕ} (hd_prime : ∀ p ∈ d, p.Prime) (hd_gt : ∀ p ∈ d, ⌊w⌋₊ < p)
    (hg : (sBrun : ℝ) + 4 ≤ Real.log ((Y : ℝ) / (∏ p ∈ d, (p : ℝ))) / Real.log w + 2 - 1 / 100)
    (a : ℕ → ℕ) :
    let Q := (range (⌊w⌋₊ + 1)).filter Nat.Prime
    let D := ∏ p ∈ d, (p : ℝ)
    let μ := (Y : ℝ) * ∏ p ∈ Q, (1 - (p : ℝ)⁻¹)
    let g := Real.log ((Y : ℝ) / D) / Real.log w + 2 - 1 / 100
    |(((Icc 1 Y).filter fun n =>
        (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ Q, ¬ (n ≡ a p [MOD p])).card : ℝ) - μ / D| ≤
      cEnv * Real.exp (-g / 4) * (μ / D) := by
  intro Q D μ g
  have hw_pos : 0 < w := by linarith
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlw1 : 1 ≤ Real.log w := by
    have h1 : Real.exp 1 ≤ w := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h1
  have hz16 : 16 ≤ ⌊w⌋₊ := Nat.le_floor hw
  have hD_pos : 0 < D := Finset.prod_pos fun p hp => by exact_mod_cast (hd_prime p hp).pos
  have hV_pos : 0 < Vprod ⌊w⌋₊ := eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2
  have hY_div_pos : 0 < (Y : ℝ) / D := by
    by_contra hle; push Not at hle
    have hY0 : (Y : ℝ) / D = 0 := le_antisymm hle (div_nonneg (Nat.cast_nonneg Y) hD_pos.le)
    rw [hY0, Real.log_zero, zero_div] at hg
    have : (12 : ℝ) ≤ (sBrun : ℝ) := by exact_mod_cast sBrun_ge_twelve
    linarith
  have hY_div_eq : (Y : ℝ) / D = w ^ (g - 2 + 1 / 100) := by
    rw [Real.rpow_def_of_pos hw_pos]
    have h1 : (g - 2 + 1 / 100) * Real.log w = Real.log ((Y : ℝ) / D) := by
      dsimp [g]; field_simp; ring
    rw [mul_comm, h1, Real.exp_log hY_div_pos]
  let s := g - 3
  have hs_ge : (sBrun : ℝ) ≤ s := by dsimp [s, g]; linarith
  have hsBrun_ge12 : (12 : ℝ) ≤ (sBrun : ℝ) := by exact_mod_cast sBrun_ge_twelve
  have hs_pos : 0 < s := by linarith
  have hws_ge : 16 ≤ w ^ s := by
    calc (16 : ℝ) = 16 ^ (1 : ℝ) := (Real.rpow_one 16).symm
      _ ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hw (by norm_num)
      _ ≤ w ^ s := Real.rpow_le_rpow_of_exponent_le hw1.le (by linarith)
  have hY_div_ge : 16 * w ^ s ≤ (Y : ℝ) / D := by
    rw [hY_div_eq]
    have hadd : w ^ (g - 2 + 1 / 100) = w ^ s * w ^ (1 + 1 / 100 : ℝ) := by
      rw [← Real.rpow_add hw_pos]; congr 1; dsimp [s]; ring
    rw [hadd]
    have hw_extra : 16 ≤ w ^ (1 + 1 / 100 : ℝ) := by
      calc (16 : ℝ) = 16 ^ (1 : ℝ) := (Real.rpow_one 16).symm
        _ ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hw (by norm_num)
        _ ≤ w ^ (1 + 1 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw1.le (by norm_num)
    nlinarith
  obtain ⟨Y', a', hY'err, hcard⟩ := card_Z_eq_sievedCount hd_prime hd_gt a
  have hY'_ge_ws : w ^ s ≤ (Y' : ℝ) := by
    have hlo := (abs_le.mp hY'err).1
    dsimp [D] at hY_div_ge; linarith only [hlo, hY_div_ge, hws_ge]
  have hY'_ge_z : ((⌊w⌋₊ : ℕ) : ℝ) ^ s ≤ (Y' : ℝ) := by
    have h1 : ((⌊w⌋₊ : ℕ) : ℝ) ^ s ≤ w ^ s :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hw_pos.le) hs_pos.le
    exact h1.trans hY'_ge_ws
  have hY'_le_2 : (Y' : ℝ) ≤ 2 * ((Y : ℝ) / D) := by
    have hhi := (abs_le.mp hY'err).2
    dsimp [D] at hY_div_ge ⊢; linarith only [hhi, hY_div_ge, hws_ge]
  have hbrun := brun_sieve_two_sided hz16 hs_ge hY'_ge_z a'
  have hμD : μ / D = ((Y : ℝ) / D) * Vprod ⌊w⌋₊ := by
    dsimp [μ, Vprod, Q]; ring
  have htri :
      |(sievedCount Y' ⌊w⌋₊ a' : ℝ) - μ / D| ≤
      |(sievedCount Y' ⌊w⌋₊ a' : ℝ) - (Y' : ℝ) * Vprod ⌊w⌋₊| +
      |(Y' : ℝ) * Vprod ⌊w⌋₊ - μ / D| := by
    simpa [sub_add_sub_cancel] using abs_add_le
      ((sievedCount Y' ⌊w⌋₊ a' : ℝ) - (Y' : ℝ) * Vprod ⌊w⌋₊)
      ((Y' : ℝ) * Vprod ⌊w⌋₊ - μ / D)
  have hterm1 : |(sievedCount Y' ⌊w⌋₊ a' : ℝ) - (Y' : ℝ) * Vprod ⌊w⌋₊| ≤
      (2 * cBrun * Real.exp (3 / 4)) * Real.exp (-g / 4) * (μ / D) := by
    have hexp_s : Real.exp (-s / 4) = Real.exp (3 / 4) * Real.exp (-g / 4) := by
      rw [← Real.exp_add]; congr 1; dsimp [s]; ring
    have h1 := hbrun
    rw [hexp_s] at h1
    have h2 : cBrun * (Real.exp (3 / 4) * Real.exp (-g / 4)) * ((Y' : ℝ) * Vprod ⌊w⌋₊) ≤
        cBrun * (Real.exp (3 / 4) * Real.exp (-g / 4)) * ((2 * ((Y : ℝ) / D)) * Vprod ⌊w⌋₊) := by
      have := cBrun_pos
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hY'_le_2 hV_pos.le) (by positivity)
    rw [hμD]
    linarith [h1.trans h2]
  have hterm2 : |(Y' : ℝ) * Vprod ⌊w⌋₊ - μ / D| ≤ Real.exp 2 * Real.exp (-g / 4) * (μ / D) := by
    rw [hμD, ← sub_mul, abs_mul, abs_of_pos hV_pos]
    have h1 : |(Y' : ℝ) - (Y : ℝ) / D| * Vprod ⌊w⌋₊ ≤ 1 * Vprod ⌊w⌋₊ :=
      mul_le_mul_of_nonneg_right hY'err hV_pos.le
    have h2 : 1 ≤ Real.exp 2 * Real.exp (-g / 4) * ((Y : ℝ) / D) := by
      rw [hY_div_eq, Real.rpow_def_of_pos hw_pos, ← Real.exp_add, ← Real.exp_add]
      apply Real.one_le_exp
      have : (12 : ℝ) ≤ (sBrun : ℝ) := by exact_mod_cast sBrun_ge_twelve
      nlinarith
    have h3 : 1 * Vprod ⌊w⌋₊ ≤ (Real.exp 2 * Real.exp (-g / 4) * ((Y : ℝ) / D)) * Vprod ⌊w⌋₊ :=
      mul_le_mul_of_nonneg_right h2 hV_pos.le
    linarith [h1.trans h3]
  have hcard' : ((Icc 1 Y).filter fun n =>
      (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ Q, ¬ (n ≡ a p [MOD p])).card =
      sievedCount Y' ⌊w⌋₊ a' := by
    convert hcard
  rw [hcard']
  have hcEnv_eq : cEnv * Real.exp (-g / 4) * (μ / D) =
      (2 * cBrun * Real.exp (3 / 4)) * Real.exp (-g / 4) * (μ / D) +
      Real.exp 2 * Real.exp (-g / 4) * (μ / D) := by
    unfold cEnv; ring
  linarith

/-- Piece 3 corollary: uniform upper bound `|Z(d, Q) - μ/D| ≤ cBad * (μ/D)` for every
progression with `g(d) ≥ 2`, assuming `w ≥ 16` and `16 ≤ w ^ (1 / (200 * sBrun))`. -/
lemma brun_progression_upper_bad {w : ℝ} {Y : ℕ}
    (hw : 16 ≤ w) (hw16 : 16 ≤ w ^ ((1 : ℝ) / (200 * (sBrun : ℝ))))
    {d : Finset ℕ} (hd_prime : ∀ p ∈ d, p.Prime) (hd_gt : ∀ p ∈ d, ⌊w⌋₊ < p)
    (hg2 : (2 : ℝ) ≤ Real.log ((Y : ℝ) / (∏ p ∈ d, (p : ℝ))) / Real.log w + 2 - 1 / 100)
    (a : ℕ → ℕ) :
    let Q := (range (⌊w⌋₊ + 1)).filter Nat.Prime
    let D := ∏ p ∈ d, (p : ℝ)
    let μ := (Y : ℝ) * ∏ p ∈ Q, (1 - (p : ℝ)⁻¹)
    |(((Icc 1 Y).filter fun n =>
        (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ Q, ¬ (n ≡ a p [MOD p])).card : ℝ) - μ / D| ≤
      cBad * (μ / D) := by
  intro Q D μ
  let α : ℝ := 1 / (200 * (sBrun : ℝ))
  have hsBrun_ge12 : (12 : ℝ) ≤ (sBrun : ℝ) := by exact_mod_cast sBrun_ge_twelve
  have hsBrun_pos : (0 : ℝ) < (sBrun : ℝ) := by linarith
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hα_lt1 : α < 1 := by dsimp [α]; rw [div_lt_one (by positivity)]; linarith
  have hw_pos : 0 < w := by linarith
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hD_pos : 0 < D := Finset.prod_pos fun p hp => by exact_mod_cast (hd_prime p hp).pos
  have hVw_pos : 0 < Vprod ⌊w⌋₊ := eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2
  have hY_div_pos : 0 < (Y : ℝ) / D := by
    by_contra hle; push Not at hle
    have hY0 : (Y : ℝ) / D = 0 := le_antisymm hle (div_nonneg (Nat.cast_nonneg Y) hD_pos.le)
    rw [hY0, Real.log_zero, zero_div] at hg2; linarith
  have hlog_ge : (1 : ℝ) / 100 ≤ Real.log ((Y : ℝ) / D) / Real.log w := by dsimp [D]; linarith
  have hY_div_ge : w ^ ((1 : ℝ) / 100) ≤ (Y : ℝ) / D := by
    rw [Real.rpow_def_of_pos hw_pos, ← Real.exp_log hY_div_pos]
    apply Real.exp_le_exp.mpr
    have := (le_div_iff₀ hlw).mp hlog_ge
    linarith
  have hw_half_ge : 16 ≤ w ^ ((1 : ℝ) / 200) := by
    have hα_le : α ≤ 1 / 200 := by
      dsimp [α]
      exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by nlinarith)
    exact hw16.trans (Real.rpow_le_rpow_of_exponent_le hw1.le hα_le)
  have hY_div_ge16 : 16 * w ^ ((1 : ℝ) / 200) ≤ (Y : ℝ) / D := by
    have hsq : w ^ ((1 : ℝ) / 200) * w ^ ((1 : ℝ) / 200) = w ^ ((1 : ℝ) / 100) := by
      rw [← Real.rpow_add hw_pos]; congr 1; norm_num
    nlinarith
  let w' : ℕ := ⌊w ^ α⌋₊
  have hw'16 : 16 ≤ w' := Nat.le_floor hw16
  have hw'_le : w' ≤ ⌊w⌋₊ := by
    apply Nat.floor_mono
    calc w ^ α ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw1.le hα_lt1.le
      _ = w := Real.rpow_one w
  have hw'_rpow_le : (w' : ℝ) ^ (sBrun : ℝ) ≤ w ^ ((1 : ℝ) / 200) := by
    have h1 : (w' : ℝ) ≤ w ^ α := Nat.floor_le (by positivity)
    calc (w' : ℝ) ^ (sBrun : ℝ) ≤ (w ^ α) ^ (sBrun : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 hsBrun_pos.le
      _ = w ^ (α * (sBrun : ℝ)) := (Real.rpow_mul hw_pos.le α (sBrun : ℝ)).symm
      _ = w ^ ((1 : ℝ) / 200) := by
          congr 1; dsimp [α]; field_simp
  obtain ⟨Y', a', hY'err, hcard⟩ := card_Z_eq_sievedCount hd_prime hd_gt a
  have hY'_ge : (w' : ℝ) ^ (sBrun : ℝ) ≤ (Y' : ℝ) := by
    have hlo := (abs_le.mp hY'err).1
    dsimp [D] at hY_div_ge16; linarith only [hlo, hY_div_ge16, hw_half_ge, hw'_rpow_le]
  have hY'_le_2 : (Y' : ℝ) ≤ 2 * ((Y : ℝ) / D) := by
    have hhi := (abs_le.mp hY'err).2
    dsimp [D] at hY_div_ge16 ⊢; linarith only [hhi, hY_div_ge16, hw_half_ge]
  have hmono_sieve : sievedCount Y' ⌊w⌋₊ a' ≤ sievedCount Y' w' a' := by
    unfold sievedCount
    apply Finset.card_le_card
    intro m hm
    rw [mem_filter] at hm ⊢
    exact ⟨hm.1, fun p hp hpp => hm.2 p (hp.trans hw'_le) hpp⟩
  have hbrun_hi := brun_sieve_two_sided hw'16 le_rfl hY'_ge a'
  have hsieve_le : (sievedCount Y' w' a' : ℝ) ≤ (1 + cBrun) * ((Y' : ℝ) * Vprod w') := by
    have hhi := (abs_le.mp hbrun_hi).2
    have hexp_le1 : Real.exp (-(sBrun : ℝ) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hVw'_pos : 0 < Vprod w' := eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2
    have hc_pos := cBrun_pos
    have h1 : cBrun * Real.exp (-(sBrun : ℝ) / 4) * ((Y' : ℝ) * Vprod w') ≤
        cBrun * 1 * ((Y' : ℝ) * Vprod w') :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le1 hc_pos.le) (by positivity)
    linarith
  -- Bound `Vprod w'` in terms of `Vprod ⌊w⌋₊` using `eulerProd_ratio_le`.
  have hV_ratio : Vprod w' ≤
      Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) * Vprod ⌊w⌋₊ := by
    have hrat := eulerProd_ratio_le (by omega : 2 ≤ w') hw'_le
    have hw'_pos_r : (0 : ℝ) < (w' : ℝ) := by exact_mod_cast (show 0 < w' by omega)
    have hlw'_ge1 : 1 ≤ Real.log (w' : ℝ) := by
      have h1 : Real.exp 1 ≤ (w' : ℝ) := by
        have : (16 : ℝ) ≤ (w' : ℝ) := by exact_mod_cast hw'16
        linarith [Real.exp_one_lt_d9]
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h1
    have hlw'_pos : 0 < Real.log (w' : ℝ) := by linarith
    have hlw'_ge_half : (α / 2) * Real.log w ≤ Real.log (w' : ℝ) := by
      set t : ℝ := w ^ α
      have ht16 : 16 ≤ t := hw16
      have hsq : t ^ ((1 : ℝ) / 2) ≤ t - 1 := by
        have hsqrt : Real.sqrt t = t ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow t
        rw [← hsqrt]
        have h1 : 4 ≤ Real.sqrt t := by
          have : (4 : ℝ) ^ 2 ≤ t := by linarith
          calc (4 : ℝ) = Real.sqrt (4 ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
            _ ≤ Real.sqrt t := Real.sqrt_le_sqrt this
        have hsq_eq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (by linarith)
        nlinarith
      have hlt_floor : t - 1 < (w' : ℝ) := Nat.sub_one_lt_floor t
      have hpow_le : t ^ ((1 : ℝ) / 2) ≤ (w' : ℝ) := hsq.trans hlt_floor.le
      calc (α / 2) * Real.log w = ((1 : ℝ) / 2) * (α * Real.log w) := by ring
        _ = ((1 : ℝ) / 2) * Real.log t := by rw [Real.log_rpow hw_pos]
        _ = Real.log (t ^ ((1 : ℝ) / 2)) := (Real.log_rpow (by linarith) _).symm
        _ ≤ Real.log (w' : ℝ) := Real.log_le_log (by positivity) hpow_le
    have hlw_floor_le : Real.log ((⌊w⌋₊ : ℕ) : ℝ) ≤ Real.log w := by
      have hfpos : (0 : ℝ) < (⌊w⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊w⌋₊ by omega)
      exact Real.log_le_log hfpos (Nat.floor_le hw_pos.le)
    have hratio_log : Real.log ((⌊w⌋₊ : ℕ) : ℝ) / Real.log (w' : ℝ) ≤ 400 * (sBrun : ℝ) := by
      rw [div_le_iff₀ hlw'_pos]
      have h1 : 400 * (sBrun : ℝ) * ((α / 2) * Real.log w) = Real.log w := by
        dsimp [α]; field_simp; ring
      have h2 := mul_le_mul_of_nonneg_left hlw'_ge_half (by positivity : 0 ≤ 400 * (sBrun : ℝ))
      linarith
    have hlog_floor_pos : 0 < Real.log ((⌊w⌋₊ : ℕ) : ℝ) := by
      have hf16 : 16 ≤ ⌊w⌋₊ := Nat.le_floor hw
      exact Real.log_pos (by exact_mod_cast (show 1 < ⌊w⌋₊ by omega))
    have hlog_mono : Real.log (Real.log ((⌊w⌋₊ : ℕ) : ℝ) / Real.log (w' : ℝ)) ≤
        Real.log (400 * (sBrun : ℝ)) :=
      Real.log_le_log (div_pos hlog_floor_pos hlw'_pos) hratio_log
    have hcm_le : 2 * CM / Real.log (w' : ℝ) ≤ 2 * CM := by
      rw [div_le_iff₀ hlw'_pos]; have := CM_pos; nlinarith
    have hexp_le : Real.exp (2 * (Real.log (Real.log ((⌊w⌋₊ : ℕ) : ℝ) / Real.log (w' : ℝ)) +
        2 * CM / Real.log (w' : ℝ))) ≤
        Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) :=
      Real.exp_le_exp.mpr (by linarith)
    exact hrat.trans (mul_le_mul_of_nonneg_right hexp_le hVw_pos.le)
  have hZ_upper :
      (((Icc 1 Y).filter fun n =>
        (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ Q, ¬ (n ≡ a p [MOD p])).card : ℝ) ≤
      2 * (1 + cBrun) * Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) * (μ / D) := by
    have hcard' : ((Icc 1 Y).filter fun n =>
        (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ Q, ¬ (n ≡ a p [MOD p])).card =
        sievedCount Y' ⌊w⌋₊ a' := by
      convert hcard
    rw [hcard']
    have hmono_r : (sievedCount Y' ⌊w⌋₊ a' : ℝ) ≤ (sievedCount Y' w' a' : ℝ) := by
      exact_mod_cast hmono_sieve
    have hVw'_pos : 0 < Vprod w' := eulerProd_pos _ fun _ hp => (mem_filter.mp hp).2
    have hμD : μ / D = ((Y : ℝ) / D) * Vprod ⌊w⌋₊ := by dsimp [μ, Vprod, Q]; ring
    have hc_pos := cBrun_pos
    calc (sievedCount Y' ⌊w⌋₊ a' : ℝ)
        ≤ (sievedCount Y' w' a' : ℝ) := hmono_r
      _ ≤ (1 + cBrun) * ((Y' : ℝ) * Vprod w') := hsieve_le
      _ ≤ (1 + cBrun) * ((2 * ((Y : ℝ) / D)) *
            (Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) * Vprod ⌊w⌋₊)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul hY'_le_2 hV_ratio hVw'_pos.le (by positivity)
      _ = 2 * (1 + cBrun) * Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) * (μ / D) := by
          rw [hμD]; ring
  have hμD_nn : 0 ≤ μ / D := by
    have : μ / D = ((Y : ℝ) / D) * Vprod ⌊w⌋₊ := by dsimp [μ, Vprod, Q]; ring
    rw [this]; positivity
  have hZ_nn : (0 : ℝ) ≤ (((Icc 1 Y).filter fun n =>
      (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ Q, ¬ (n ≡ a p [MOD p])).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  have hcBad_eq : cBad = 2 * (1 + cBrun) * Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) + 1 := rfl
  have hcK_nn : 0 ≤ 2 * (1 + cBrun) * Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM)) := by
    have := cBrun_pos; positivity
  constructor
  · have hmul := mul_nonneg hcK_nn hμD_nn
    linarith only [hZ_nn, hμD_nn, hcBad_eq, hmul,
      show cBad * (μ / D) = (2 * (1 + cBrun) * Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM))) * (μ / D) + μ / D by
        rw [hcBad_eq]; ring]
  · linarith only [hZ_upper, hμD_nn, hcBad_eq,
      show cBad * (μ / D) = (2 * (1 + cBrun) * Real.exp (2 * (Real.log (400 * (sBrun : ℝ)) + 2 * CM))) * (μ / D) + μ / D by
        rw [hcBad_eq]; ring]

end ProgressionCorollaries

end Erdos687H2.BrunSieve

/-
# Final Assembly for `Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1.H2`

We combine the elementary Mertens estimates (`Sec1_Mertens`), the `r²/y` tree-mass barrier
(`Sec2_TreeMass`), and the two-sided exponential Brun sieve (`Sec3_BrunSieve`) via the
three-piece partition `E ⊆ E_long ∪ E_good ∪ A`, proving `OMA.solution`.
-/

namespace Erdos687H2.Main

open Filter Finset Real Erdos687H2.Mertens Erdos687H2.TreeMass Erdos687H2.BrunSieve
open scoped Classical

private lemma log_le_rpow_div_self {L p : ℝ} (hL : 0 < L) (hp : 0 < p) :
    Real.log L ≤ L ^ p / p := by
  have h1 : Real.log (L ^ p) ≤ L ^ p - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hL p)
  rw [Real.log_rpow hL] at h1
  rw [le_div_iff₀ hp]
  linarith

private lemma tail_decay_le {B : ℝ} (hB : 1 ≤ B) :
    (B ^ 2 + 2 * B ^ 2 * Real.log B) * Real.exp (-(1 / 4 : ℝ) * (9 / 10 * B)) + 2 / B ≤
      (768 / ((9 / 40 : ℝ) ^ 4) + 2) / B := by
  have hBpos : 0 < B := by linarith
  have hlogB : Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hBpos]
  have hpoly : B ^ 2 + 2 * B ^ 2 * Real.log B ≤ 3 * B ^ 3 := by
    have h1 : B ^ 2 ≤ B ^ 3 := by nlinarith
    have h2 : 2 * B ^ 2 * Real.log B ≤ 2 * B ^ 3 := by nlinarith
    linarith
  set β : ℝ := 9 / 40
  have hβ : 0 < β := by norm_num
  have hpow4 : (β * B) ^ 4 / 256 ≤ Real.exp (β * B) := by
    have h1 : (β * B) / 4 ≤ Real.exp ((β * B) / 4) := by
      linarith [Real.add_one_le_exp ((β * B) / 4)]
    have h2 : ((β * B) / 4) ^ 4 ≤ (Real.exp ((β * B) / 4)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h1 4
    rw [← Real.exp_nat_mul] at h2
    have heq1 : (4 : ℕ) * ((β * B) / 4) = β * B := by push_cast; ring
    have heq2 : ((β * B) / 4) ^ 4 = (β * B) ^ 4 / 256 := by ring
    rwa [heq1, heq2] at h2
  have hexp_le : Real.exp (-β * B) ≤ 256 / (β ^ 4 * B ^ 4) := by
    rw [neg_mul, Real.exp_neg, inv_eq_one_div]
    rw [div_le_div_iff₀ (Real.exp_pos _) (by positivity), one_mul]
    have hmul : (β * B) ^ 4 = β ^ 4 * B ^ 4 := mul_pow β B 4
    have h256 := mul_le_mul_of_nonneg_left hpow4 (by norm_num : (0 : ℝ) ≤ 256)
    have h256_eq : 256 * ((β * B) ^ 4 / 256) = β ^ 4 * B ^ 4 := by rw [hmul]; ring
    rw [h256_eq] at h256
    exact h256
  have heq_exp : -(1 / 4 : ℝ) * (9 / 10 * B) = -β * B := by dsimp [β]; ring
  rw [heq_exp]
  have hmain : (B ^ 2 + 2 * B ^ 2 * Real.log B) * Real.exp (-β * B) ≤ (768 / β ^ 4) / B := by
    calc (B ^ 2 + 2 * B ^ 2 * Real.log B) * Real.exp (-β * B)
        ≤ (3 * B ^ 3) * (256 / (β ^ 4 * B ^ 4)) :=
          mul_le_mul hpoly hexp_le (Real.exp_pos _).le (by positivity)
      _ = (768 / β ^ 4) / B := by field_simp; ring
  have hadd : (768 / β ^ 4 + 2) / B = (768 / β ^ 4) / B + 2 / B := by ring
  linarith

set_option maxHeartbeats 800000 in
lemma main_h2 :
    OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H2 := by
  unfold OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H2
  let K_tail : ℝ := 600 * cEnv * cSlab * 16 * 145
  let k : ℝ := max (max 3 ((sBrun : ℝ) + 4)) (8 * Real.log (K_tail + 1))
  let C_small : ℝ := 1 + cSlab * (k + 1) ^ 3 / 3
  let ε : ℝ := 1 / (300 * C_small)
  let δ : ℝ := 1 / (300 * cBad)
  have hk3 : 3 ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hksBrun : (sBrun : ℝ) + 4 ≤ k := (le_max_right _ _).trans (le_max_left _ _)
  have hklog : 8 * Real.log (K_tail + 1) ≤ k := le_max_right _ _
  have hK_tail_pos : 0 < K_tail := by
    dsimp [K_tail]; have := cEnv_pos; have := cSlab_pos; positivity
  have hC_small_pos : 0 < C_small := by
    dsimp [C_small]; have := cSlab_pos; positivity
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have hδ_pos : 0 < δ := by dsimp [δ]; have := cBad_pos; positivity
  refine ⟨k, ε, δ, hk3, hε_pos, hδ_pos, ?_⟩
  let β : ℝ := 9 / 40
  let B₀ : ℝ := max 60 (max (2 * k) (600 * cEnv * (768 / β ^ 4 + 2)))
  let W₀ : ℝ := max (max 16 (Real.exp (max 4 (max (cA + 1) ((1 / 4 : ℝ) / 2))))) ((16 : ℝ) ^ (200 * sBrun))
  let L₀ : ℝ := max (max 12 ((64 : ℝ) ^ 4)) (max ((64 * W₀) ^ 2) ((2 * B₀) ^ 2))
  rw [Filter.eventually_atTop]
  refine ⟨Real.exp L₀, fun z hz => ?_⟩
  dsimp only
  set L : ℝ := Real.log z
  set Y : ℕ := ⌊z ^ 2 / L ^ 2⌋₊
  set w : ℝ := L / (Real.log L) ^ 2
  set B : ℝ := L / Real.log w
  set P : Finset ℕ := (Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
  set Q : Finset ℕ := (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime
  set v : Finset ℕ → ℝ := fun S => ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
  set μ : ℝ := (Y : ℝ) * v Q
  set D : Finset ℕ → ℝ := fun d => ∏ p ∈ d, (p : ℝ)
  set g : Finset ℕ → ℝ := fun d => Real.log ((Y : ℝ) / D d) / Real.log w + 2 - 1 / 100
  set e : ℕ → ℝ := fun p => Real.log (p : ℝ) / Real.log w
  set T : Finset (Finset ℕ) := P.powerset.filter fun d => ∀ p ∈ d,
    let A := d.filter (p ≤ ·)
    Even A.card → max (2 * e p) (e p + 2) ≤ g A
  -- Establish all asymptotic parameter inequalities from `Real.exp L₀ ≤ z`.
  have hL_ge : L₀ ≤ L := by
    have h1 := Real.log_le_log (Real.exp_pos L₀) hz
    rwa [Real.log_exp] at h1
  have hL12 : 12 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL_ge
  have hL64 : (64 : ℝ) ^ 4 ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL_ge
  have hLW0 : (64 * W₀) ^ 2 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL_ge
  have hLB0 : (2 * B₀) ^ 2 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL_ge
  have hL_pos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hz_pos : 0 < z := lt_of_lt_of_le (Real.exp_pos L₀) hz
  have hz_ge_poly : 2 * L ^ 2 ≤ z := by
    have hsum := Real.sum_le_exp_of_nonneg hL_pos.le 4
    simp [Finset.sum_range_succ, Nat.factorial] at hsum
    rw [Real.exp_log hz_pos] at hsum
    have hL3 : 2 * L ^ 2 ≤ L ^ 3 / 6 := by nlinarith
    have hnn : 0 ≤ 1 + L + L ^ 2 / 2 := by positivity
    linarith
  have hz4 : 4 ≤ z := by nlinarith
  have hz2L2_ge2 : 2 ≤ z ^ 2 / L ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hL_pos)]
    nlinarith
  have hY_lo : (1 / 2 : ℝ) * (z ^ 2 / L ^ 2) ≤ (Y : ℝ) := by
    have h1 : z ^ 2 / L ^ 2 - 1 < (Y : ℝ) := Nat.sub_one_lt_floor _
    linarith
  have hY_hi : (Y : ℝ) ≤ z ^ 2 / L ^ 2 := Nat.floor_le (by positivity)
  have hY_pos : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogL_ge1 : 1 ≤ Real.log L := by
    have h1 : Real.exp 1 ≤ L := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h1
  have hlogL_pos : 0 < Real.log L := by linarith
  have hlogL_le_rpow8 : Real.log L ≤ 8 * L ^ ((1 : ℝ) / 8) := by
    have h := log_le_rpow_div_self hL_pos (by norm_num : (0 : ℝ) < 1 / 8)
    linarith [show L ^ ((1 : ℝ) / 8) / ((1 : ℝ) / 8) = 8 * L ^ ((1 : ℝ) / 8) by ring]
  have hw_ge_rpow : L ^ ((3 : ℝ) / 4) / 64 ≤ w := by
    dsimp [w]
    have hsq : (Real.log L) ^ 2 ≤ 64 * L ^ ((1 : ℝ) / 4) := by
      have h1 : (Real.log L) ^ 2 ≤ (8 * L ^ ((1 : ℝ) / 8)) ^ 2 :=
        pow_le_pow_left₀ hlogL_pos.le hlogL_le_rpow8 2
      have h2 : (8 * L ^ ((1 : ℝ) / 8)) ^ 2 = 64 * (L ^ ((1 : ℝ) / 8)) ^ 2 := by ring
      have h3 : (L ^ ((1 : ℝ) / 8)) ^ 2 = L ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]; congr 1; norm_num
      linarith
    rw [div_le_div_iff₀ (by norm_num) (sq_pos_of_pos hlogL_pos)]
    have hmul : L ^ ((3 : ℝ) / 4) * (64 * L ^ ((1 : ℝ) / 4)) = 64 * L := by
      have : L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) = L := by
        rw [← Real.rpow_add hL_pos]; norm_num
      linarith [show L ^ ((3 : ℝ) / 4) * (64 * L ^ ((1 : ℝ) / 4)) =
        64 * (L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) by ring]
    have hstep := mul_le_mul_of_nonneg_left hsq (Real.rpow_pos_of_pos hL_pos ((3 : ℝ) / 4)).le
    linarith
  have hW0_pos : 0 < W₀ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans (le_max_left _ _))
  have hw_ge_W0 : W₀ ≤ w := by
    have h1 : 64 * W₀ ≤ L ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      calc 64 * W₀ = Real.sqrt ((64 * W₀) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hLW0
    have h2 : L ^ ((1 : ℝ) / 2) ≤ L ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    linarith
  have hw16 : 16 ≤ w := ((le_max_left _ _).trans (le_max_left _ _)).trans hw_ge_W0
  have hw4 : 4 ≤ w := by linarith
  have hw1 : 1 < w := by linarith
  have hlw_ge : max 4 (max (cA + 1) ((1 / 4 : ℝ) / 2)) ≤ Real.log w := by
    have h1 : Real.exp (max 4 (max (cA + 1) ((1 / 4 : ℝ) / 2))) ≤ w :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hw_ge_W0
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h1
  have hlw_ge' : max 4 (cA + 1) ≤ Real.log w :=
    max_le ((le_max_left _ _).trans hlw_ge) (((le_max_left _ _).trans (le_max_right _ _)).trans hlw_ge)
  have hlw_pos : 0 < Real.log w := Real.log_pos hw1
  have hlw4 : 4 ≤ Real.log w := (le_max_left _ _).trans hlw_ge
  have hw_alpha : 16 ≤ w ^ ((1 : ℝ) / (200 * (sBrun : ℝ))) := by
    have h1 : (16 : ℝ) ^ (200 * sBrun) ≤ w := (le_max_right _ _).trans hw_ge_W0
    have hsBrun_ge12 : (12 : ℝ) ≤ (sBrun : ℝ) := by exact_mod_cast sBrun_ge_twelve
    have hs_pos : (0 : ℝ) < 200 * (sBrun : ℝ) := by linarith
    have hs_ne : (sBrun : ℝ) ≠ 0 := by linarith
    have h2 : ((16 : ℝ) ^ (200 * sBrun)) ^ ((1 : ℝ) / (200 * (sBrun : ℝ))) ≤
        w ^ ((1 : ℝ) / (200 * (sBrun : ℝ))) :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    have h3 : ((16 : ℝ) ^ (200 * sBrun)) ^ ((1 : ℝ) / (200 * (sBrun : ℝ))) = 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have hexp : ((200 * sBrun : ℕ) : ℝ) * ((1 : ℝ) / (200 * (sBrun : ℝ))) = 1 := by
        push_cast; field_simp
      rw [hexp, Real.rpow_one]
    linarith
  have hlw_le_logL : Real.log w ≤ Real.log L := by
    apply Real.log_le_log (by linarith)
    dsimp [w]
    exact div_le_self hL_pos.le (by nlinarith)
  have hhalf_logL_le_lw : (1 / 2 : ℝ) * Real.log L ≤ Real.log w := by
    have h1 : Real.log (L ^ ((3 : ℝ) / 4) / 64) ≤ Real.log w :=
      Real.log_le_log (by positivity) hw_ge_rpow
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hL_pos] at h1
    have h2 : 4 * Real.log 64 ≤ Real.log L := by
      have := Real.log_le_log (by positivity) hL64
      rw [Real.log_pow] at this; push_cast at this; linarith
    linarith
  have hB0_pos : 0 < B₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hB_ge_B0 : B₀ ≤ B := by
    have hlogL_le_half : Real.log L ≤ 2 * L ^ ((1 : ℝ) / 2) := by
      have h := log_le_rpow_div_self hL_pos (by norm_num : (0 : ℝ) < 1 / 2)
      linarith [show L ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) = 2 * L ^ ((1 : ℝ) / 2) by ring]
    have h1 : 2 * B₀ ≤ L ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      calc 2 * B₀ = Real.sqrt ((2 * B₀) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hLB0
    dsimp [B]
    rw [le_div_iff₀ hlw_pos]
    have hsq : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L := by
      rw [← Real.rpow_add hL_pos]; norm_num
    have h2 : B₀ * Real.log w ≤ B₀ * (2 * L ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (hlw_le_logL.trans hlogL_le_half) hB0_pos.le
    nlinarith [Real.rpow_pos_of_pos hL_pos ((1 : ℝ) / 2)]
  have hB60 : 60 ≤ B := (le_max_left _ _).trans hB_ge_B0
  have hB20 : 20 ≤ B := by linarith
  have hB2k : 2 * k ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB_ge_B0
  have hB_tail : 600 * cEnv * (768 / β ^ 4 + 2) ≤ B :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hB_ge_B0
  have hB_pos : 0 < B := by linarith
  have hlogB_le : Real.log B ≤ 2 * Real.log w := by
    have hB_le_L : B ≤ L := by
      dsimp [B]; exact div_le_self hL_pos.le (by linarith)
    have h1 : Real.log B ≤ Real.log L := Real.log_le_log hB_pos hB_le_L
    linarith
  -- Define `G := Real.log (Y : ℝ) / Real.log w + 2 - 1 / 100` and verify `(19/10)*B ≤ G ≤ 2*B`.
  set G : ℝ := Real.log (Y : ℝ) / Real.log w + 2 - 1 / 100
  have hG_hi : G ≤ 2 * B := by
    have h1 : Real.log (Y : ℝ) ≤ Real.log (z ^ 2 / L ^ 2) := Real.log_le_log hY_pos hY_hi
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    have h2 : Real.log (Y : ℝ) / Real.log w ≤ 2 * B - 2 * (Real.log L / Real.log w) := by
      rw [show 2 * B - 2 * (Real.log L / Real.log w) = (2 * L - 2 * Real.log L) / Real.log w by
        dsimp [B]; ring]
      exact div_le_div_of_nonneg_right h1 hlw_pos.le
    have h3 : 1 ≤ Real.log L / Real.log w := (one_le_div hlw_pos).mpr hlw_le_logL
    dsimp [G]; linarith
  have hG_lo : (19 : ℝ) / 10 * B ≤ G := by
    have h1 : Real.log ((1 / 2 : ℝ) * (z ^ 2 / L ^ 2)) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by positivity) hY_lo
    rw [Real.log_mul (by norm_num) (by positivity), one_div, Real.log_inv,
      Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    have hlog2_le : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) (by linarith)
    have h2 : 2 * L - 3 * Real.log L ≤ Real.log (Y : ℝ) := by linarith
    have h3 : 2 * B - 3 * (Real.log L / Real.log w) ≤ Real.log (Y : ℝ) / Real.log w := by
      rw [show 2 * B - 3 * (Real.log L / Real.log w) = (2 * L - 3 * Real.log L) / Real.log w by
        dsimp [B]; ring]
      exact div_le_div_of_nonneg_right h2 hlw_pos.le
    have h4 : Real.log L / Real.log w ≤ 2 := by
      rw [div_le_iff₀ hlw_pos]; linarith
    dsimp [G]; linarith
  -- Match `g d = gapOf w G d` and `T = admTree w z G`.
  have hg_eq : ∀ d ⊆ P, g d = gapOf w G d := by
    intro d hd
    have hdp : ∀ p ∈ d, p.Prime := fun p hp => (mem_filter.mp (hd hp)).2
    have hD_pos : 0 < D d := Finset.prod_pos fun p hp => by exact_mod_cast (hdp p hp).pos
    have hlogD : Real.log (D d) = ∑ p ∈ d, Real.log (p : ℝ) := by
      dsimp [D]
      exact Real.log_prod fun p hp => by exact_mod_cast (hdp p hp).pos.ne'
    dsimp [g, G]
    unfold gapOf pExp
    rw [Real.log_div hY_pos.ne' hD_pos.ne', hlogD, sub_div, Finset.sum_div]
    ring
  have hT_eq : T = admTree w z G := by
    ext d
    simp only [T, admTree, primeSet, P, mem_filter, mem_powerset]
    refine and_congr_right fun hd => ?_
    refine forall₂_congr fun p _ => ?_
    have hAsub : d.filter (p ≤ ·) ⊆ P := (Finset.filter_subset _ _).trans hd
    rw [hg_eq _ hAsub]
    rfl
  -- Now prove the bound for arbitrary `a`, `E ⊆ T`, and `hA`.
  intro a
  set Z : Finset ℕ → Finset ℕ → Finset ℕ := fun d S =>
    (Finset.Icc 1 Y).filter fun n =>
      (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ S, ¬ (n ≡ a p [MOD p])
  intro E hET
  set A : Finset (Finset ℕ) := E.filter fun d => g d ≤ k ∧ ε < |((Z d Q).card : ℝ) / (μ / D d) - 1|
  intro hA
  have hvQ_pos : 0 < v Q := eulerProd_pos Q fun _ hp => (mem_filter.mp hp).2
  have hμ_pos : 0 < μ := mul_pos hY_pos hvQ_pos
  -- Partition `E` into three pieces: `E_long`, `E_good`, `A`.
  let E_long := E.filter fun d => k < g d
  let E_good := E.filter fun d => g d ≤ k ∧ |((Z d Q).card : ℝ) / (μ / D d) - 1| ≤ ε
  have hE_sub : E ⊆ E_long ∪ (E_good ∪ A) := by
    intro d hd
    by_cases hgt : k < g d
    · exact mem_union_left _ (mem_filter.mpr ⟨hd, hgt⟩)
    · push Not at hgt
      by_cases hbad : ε < |((Z d Q).card : ℝ) / (μ / D d) - 1|
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hd, hgt, hbad⟩))
      · push Not at hbad
        exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hd, hgt, hbad⟩))
  have hsum_split :
      ∑ d ∈ E, |((Z d Q).card : ℝ) - μ / D d| ≤
      (∑ d ∈ E_long, |((Z d Q).card : ℝ) - μ / D d|) +
      (∑ d ∈ E_good, |((Z d Q).card : ℝ) - μ / D d|) +
      (∑ d ∈ A, |((Z d Q).card : ℝ) - μ / D d|) := by
    have hnn : ∀ d : Finset ℕ, 0 ≤ |((Z d Q).card : ℝ) - μ / D d| := fun _ => abs_nonneg _
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hE_sub (fun d _ _ => hnn d)
    have h2 := h1.trans (sum_union_le_of_nonneg hnn)
    have h3 := sum_union_le_of_nonneg (s₁ := E_good) (s₂ := A) hnn
    linarith only [h2, h3]
  -- Piece 1: Long progressions (`k < g d`).
  have hPiece1 : ∑ d ∈ E_long, |((Z d Q).card : ℝ) - μ / D d| ≤ μ * (1 / (300 * B ^ 2)) := by
    have hpt : ∀ d ∈ E_long,
        |((Z d Q).card : ℝ) - μ / D d| ≤
        μ * cEnv * ((prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d)) := by
      intro d hd
      obtain ⟨hdE, hgk⟩ := mem_filter.mp hd
      have hdT : d ∈ T := hET hdE
      have hdP : d ⊆ P := mem_powerset.mp (mem_filter.mp hdT).1
      have hdp : ∀ p ∈ d, p.Prime := fun p hp => (mem_filter.mp (hdP hp)).2
      have hdgt : ∀ p ∈ d, ⌊w⌋₊ < p := fun p hp => by
        have := (mem_Icc.mp (mem_filter.mp (hdP hp)).1).1; omega
      have hgsBrun : (sBrun : ℝ) + 4 ≤
          Real.log ((Y : ℝ) / (∏ p ∈ d, (p : ℝ))) / Real.log w + 2 - 1 / 100 := by
        change (sBrun : ℝ) + 4 ≤ g d; linarith
      have henv := brun_progression_envelope hw16 hdp hdgt hgsBrun a
      have hrew : cEnv * Real.exp (-g d / 4) * (μ / D d) =
          μ * cEnv * ((prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d)) := by
        rw [← hg_eq d hdP]
        have hD_eq : D d = prodR d := rfl
        rw [hD_eq, show -g d / 4 = -(1 / 4 : ℝ) * g d by ring]
        ring
      rw [← hrew]
      exact henv
    have hsub_long : E_long ⊆ (admTree w z G).filter (fun d => k < gapOf w G d) := by
      intro d hd
      obtain ⟨hdE, hgk⟩ := mem_filter.mp hd
      have hdT : d ∈ T := hET hdE
      have hdP : d ⊆ P := mem_powerset.mp (mem_filter.mp hdT).1
      rw [← hT_eq]
      exact mem_filter.mpr ⟨hdT, by rwa [← hg_eq d hdP]⟩
    have hsum1 : ∑ d ∈ E_long, |((Z d Q).card : ℝ) - μ / D d| ≤
        μ * cEnv * ∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
          (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d) := by
      calc ∑ d ∈ E_long, |((Z d Q).card : ℝ) - μ / D d|
          ≤ ∑ d ∈ E_long, μ * cEnv * ((prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d)) :=
            Finset.sum_le_sum hpt
        _ = μ * cEnv * ∑ d ∈ E_long, (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d) := by
            rw [← Finset.mul_sum]
        _ ≤ μ * cEnv * ∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
              (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hμ_pos.le cEnv_pos.le)
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub_long (fun d _ _ => by unfold prodR; positivity)
    have htail := tree_exp_tail_le (c := 1 / 4) (k := k) hw4 hz4 hlw_ge hB20 hlogB_le hG_lo hG_hi
      (by norm_num) hk3
    have hdec : cEnv * ((B ^ 2 + 2 * B ^ 2 * Real.log B) * Real.exp (-(1 / 4 : ℝ) * (9 / 10 * B)) + 2 / B) ≤
        1 / 600 := by
      have h1 := tail_decay_le (by linarith : 1 ≤ B)
      have h2 : cEnv * ((768 / β ^ 4 + 2) / B) ≤ 1 / 600 := by
        rw [show cEnv * ((768 / β ^ 4 + 2) / B) = cEnv * (768 / β ^ 4 + 2) / B by ring,
          div_le_div_iff₀ hB_pos (by norm_num)]
        linarith
      exact (mul_le_mul_of_nonneg_left h1 cEnv_pos.le).trans h2
    have hexpk : cEnv * (cSlab * (2 / ((1 / 4 : ℝ) / 2)) *
        (2 / ((1 / 4 : ℝ) / 2) ^ 2 + 2 / ((1 / 4 : ℝ) / 2) + 1) * Real.exp (-((1 / 4 : ℝ) / 2) * k)) ≤
        1 / 600 := by
      have hconst : cEnv * (cSlab * (2 / ((1 / 4 : ℝ) / 2)) *
          (2 / ((1 / 4 : ℝ) / 2) ^ 2 + 2 / ((1 / 4 : ℝ) / 2) + 1)) = K_tail / 600 := by
        dsimp [K_tail]; ring
      have hexp_le : Real.exp (-((1 / 4 : ℝ) / 2) * k) ≤ (K_tail + 1)⁻¹ := by
        rw [← Real.exp_log (by linarith : 0 < K_tail + 1), ← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        linarith
      have h1 : (K_tail / 600) * (K_tail + 1)⁻¹ ≤ 1 / 600 := by
        have hrew1 : K_tail / 600 * (K_tail + 1)⁻¹ = K_tail / (600 * (K_tail + 1)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
        rw [hrew1, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hrew : cEnv * (cSlab * (2 / ((1 / 4 : ℝ) / 2)) *
          (2 / ((1 / 4 : ℝ) / 2) ^ 2 + 2 / ((1 / 4 : ℝ) / 2) + 1) * Real.exp (-((1 / 4 : ℝ) / 2) * k)) =
          (K_tail / 600) * Real.exp (-((1 / 4 : ℝ) / 2) * k) := by
        rw [← hconst]; ring
      rw [hrew]
      exact (mul_le_mul_of_nonneg_left hexp_le (by positivity)).trans h1
    have hB2_bound : cEnv * (B ^ 2 * ∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
        (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d)) ≤ 1 / 300 := by
      have htail' : B ^ 2 * ∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
          (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d) ≤
          (B ^ 2 + 2 * B ^ 2 * Real.log B) * Real.exp (-(1 / 4 : ℝ) * (9 / 10 * B)) + 2 / B +
          cSlab * (2 / ((1 / 4 : ℝ) / 2)) *
            (2 / ((1 / 4 : ℝ) / 2) ^ 2 + 2 / ((1 / 4 : ℝ) / 2) + 1) * Real.exp (-((1 / 4 : ℝ) / 2) * k) :=
        htail
      have h1 := mul_le_mul_of_nonneg_left htail' cEnv_pos.le
      rw [mul_add] at h1
      linarith only [h1, hdec, hexpk]
    have hdivB2 : cEnv * ∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
        (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d) ≤ 1 / (300 * B ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [show cEnv * (∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
          (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d)) * (300 * B ^ 2) =
        300 * (cEnv * (B ^ 2 * ∑ d ∈ (admTree w z G).filter (fun d => k < gapOf w G d),
          (prodR d)⁻¹ * Real.exp (-(1 / 4 : ℝ) * gapOf w G d))) by ring]
    exact hsum1.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hdivB2 hμ_pos.le)
  -- Piece 2: Good compact words (`g d ≤ k` and relative error `≤ ε`).
  have hPiece2 : ∑ d ∈ E_good, |((Z d Q).card : ℝ) - μ / D d| ≤ μ * (1 / (300 * B ^ 2)) := by
    have hpt : ∀ d ∈ E_good, |((Z d Q).card : ℝ) - μ / D d| ≤ μ * ε * (prodR d)⁻¹ := by
      intro d hd
      obtain ⟨hdE, _, hrel⟩ := mem_filter.mp hd
      have hdP : d ⊆ P := mem_powerset.mp (mem_filter.mp (hET hdE)).1
      have hD_pos : 0 < D d := Finset.prod_pos fun p hp => by
        exact_mod_cast (mem_filter.mp (hdP hp)).2.pos
      have hμD_pos : 0 < μ / D d := div_pos hμ_pos hD_pos
      have hmul := mul_le_mul_of_nonneg_right hrel hμD_pos.le
      have hlhs : |((Z d Q).card : ℝ) / (μ / D d) - 1| * (μ / D d) =
          |((Z d Q).card : ℝ) - μ / D d| := by
        calc |((Z d Q).card : ℝ) / (μ / D d) - 1| * (μ / D d)
            = |((Z d Q).card : ℝ) / (μ / D d) - 1| * |μ / D d| := by rw [abs_of_pos hμD_pos]
          _ = |(((Z d Q).card : ℝ) / (μ / D d) - 1) * (μ / D d)| := (abs_mul _ _).symm
          _ = |((Z d Q).card : ℝ) - μ / D d| := by rw [sub_mul, one_mul, div_mul_cancel₀ _ hμD_pos.ne']
      rw [hlhs] at hmul
      have hrhs : ε * (μ / D d) = μ * ε * (prodR d)⁻¹ := by
        have : D d = prodR d := rfl
        rw [this]; ring
      linarith
    have hsub_good : E_good ⊆ (admTree w z G).filter (fun d => gapOf w G d ≤ k) := by
      intro d hd
      obtain ⟨hdE, hgk, _⟩ := mem_filter.mp hd
      have hdT : d ∈ T := hET hdE
      have hdP : d ⊆ P := mem_powerset.mp (mem_filter.mp hdT).1
      rw [← hT_eq]
      exact mem_filter.mpr ⟨hdT, by rwa [← hg_eq d hdP]⟩
    have hcomp := tree_compact_mass_le hw4 hz4 hlw_ge' (max_le hB20 hB2k) hlogB_le hG_lo hG_hi hk3
    have hsum2 : ∑ d ∈ E_good, |((Z d Q).card : ℝ) - μ / D d| ≤
        μ * ε * ∑ d ∈ (admTree w z G).filter (fun d => gapOf w G d ≤ k), (prodR d)⁻¹ := by
      calc ∑ d ∈ E_good, |((Z d Q).card : ℝ) - μ / D d|
          ≤ ∑ d ∈ E_good, μ * ε * (prodR d)⁻¹ := Finset.sum_le_sum hpt
        _ = μ * ε * ∑ d ∈ E_good, (prodR d)⁻¹ := by rw [← Finset.mul_sum]
        _ ≤ μ * ε * ∑ d ∈ (admTree w z G).filter (fun d => gapOf w G d ≤ k), (prodR d)⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hμ_pos.le hε_pos.le)
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub_good (fun d _ _ => by unfold prodR; positivity)
    have hε_bound : ε * ∑ d ∈ (admTree w z G).filter (fun d => gapOf w G d ≤ k), (prodR d)⁻¹ ≤
        1 / (300 * B ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hcomp' : B ^ 2 * ∑ d ∈ (admTree w z G).filter (fun d => gapOf w G d ≤ k), (prodR d)⁻¹ ≤
          C_small := hcomp
      have h1 := mul_le_mul_of_nonneg_left hcomp' (by positivity : 0 ≤ 300 * ε)
      have h2 : 300 * ε * C_small = 1 := by dsimp [ε]; field_simp
      linarith only [h1, h2, show ε * (∑ d ∈ (admTree w z G).filter (fun d => gapOf w G d ≤ k), (prodR d)⁻¹) * (300 * B ^ 2) =
        300 * ε * (B ^ 2 * ∑ d ∈ (admTree w z G).filter (fun d => gapOf w G d ≤ k), (prodR d)⁻¹) by ring]
    exact hsum2.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hε_bound hμ_pos.le)
  -- Piece 3: Bad compact words (`A`).
  have hPiece3 : ∑ d ∈ A, |((Z d Q).card : ℝ) - μ / D d| ≤ μ * (1 / (300 * B ^ 2)) := by
    have hpt : ∀ d ∈ A, |((Z d Q).card : ℝ) - μ / D d| ≤ μ * cBad * (D d)⁻¹ := by
      intro d hd
      have hdT : d ∈ T := hET (mem_filter.mp hd).1
      have hdP : d ⊆ P := mem_powerset.mp (mem_filter.mp hdT).1
      have hdp : ∀ p ∈ d, p.Prime := fun p hp => (mem_filter.mp (hdP hp)).2
      have hdgt : ∀ p ∈ d, ⌊w⌋₊ < p := fun p hp => by
        have := (mem_Icc.mp (mem_filter.mp (hdP hp)).1).1; omega
      have hdAdm : d ∈ admTree w z G := by rwa [← hT_eq]
      have hg2 : (2 : ℝ) ≤ Real.log ((Y : ℝ) / (∏ p ∈ d, (p : ℝ))) / Real.log w + 2 - 1 / 100 := by
        change (2 : ℝ) ≤ g d
        rw [hg_eq d hdP]
        exact admTree_gap_ge_two hw1 hB20 hG_lo hdAdm
      have hbad := brun_progression_upper_bad hw16 hw_alpha hdp hdgt hg2 a
      have hrhs : cBad * (μ / D d) = μ * cBad * (D d)⁻¹ := by ring
      rw [← hrhs]
      exact hbad
    have hsum3 : ∑ d ∈ A, |((Z d Q).card : ℝ) - μ / D d| ≤ μ * cBad * ∑ d ∈ A, (D d)⁻¹ := by
      calc ∑ d ∈ A, |((Z d Q).card : ℝ) - μ / D d|
          ≤ ∑ d ∈ A, μ * cBad * (D d)⁻¹ := Finset.sum_le_sum hpt
        _ = μ * cBad * ∑ d ∈ A, (D d)⁻¹ := by rw [← Finset.mul_sum]
    have hδ_bound : cBad * ∑ d ∈ A, (D d)⁻¹ ≤ 1 / (300 * B ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hA (by have := cBad_pos; positivity : 0 ≤ 300 * cBad)
      have h2 : 300 * cBad * δ = 1 := by dsimp [δ]; have := cBad_pos; field_simp
      linarith [show cBad * (∑ d ∈ A, (D d)⁻¹) * (300 * B ^ 2) =
        300 * cBad * (B ^ 2 * ∑ d ∈ A, (D d)⁻¹) by ring]
    exact hsum3.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hδ_bound hμ_pos.le)
  -- Combine Pieces 1, 2, 3: `1/300 + 1/300 + 1/300 = 1/100`.
  have h100 : μ * (1 / (300 * B ^ 2)) + μ * (1 / (300 * B ^ 2)) + μ * (1 / (300 * B ^ 2)) =
      μ * (1 / (100 * B ^ 2)) := by ring
  linarith only [hsum_split, hPiece1, hPiece2, hPiece3, h100]

end Erdos687H2.Main

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H2 :=
  Erdos687H2.Main.main_h2
