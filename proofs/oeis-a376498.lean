import OMAStatements.S_oeis_a376498

-- Problem: A376498: Array read by ascending antidiagonals: A(n, k) = 2^k*Sum_{j=1..n} cos((2*j - 1)*Pi/(2*n + 1))^k.
-- Upstream: formal-conjectures statements/oeis-a376498.lean:0 (declaration OMA.S_oeis_a376498.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof. Put N = 2n+1 and theta_j = (2j+1) pi / N.
-- 1. (2 cos t)^k = sum_{m <= k} C(k,m) cos((2m-k) t)   (two_cos_pow).
-- 2. 2 sin x * sum_{j<n} cos((2j+1) x) = sin(2n x)       (sin_mul_sum).
-- 3. For c = 2m-k: 2 * sum_{j<n} cos(c theta_j) is (-1)^k * 2n if N divides c, and -(-1)^k
--    otherwise                                           (sum_cos).
-- 4. Hence 2 * entry n k = (-1)^k * (2n * 2^k - N * B), where B is the sum of C(k,m) over the
--    m <= k with N not dividing 2m-k (two_entry). The involution m -> k-m has no fixed point on
--    that index set and preserves C(k,m), so B is even (even_B), and entry n k is an integer.

namespace OMA.A376498

open Finset

lemma two_cos_pow (t : ℝ) (k : ℕ) :
    (2 * Real.cos t) ^ k
      = ∑ m ∈ range (k + 1), (k.choose m : ℝ) * Real.cos ((2 * (m : ℝ) - k) * t) := by
  have h : ((2 * Real.cos t : ℝ) : ℂ) ^ k
      = ∑ m ∈ range (k + 1), ((k.choose m : ℝ) : ℂ) *
          Complex.exp ((((2 * (m : ℝ) - k) * t : ℝ) : ℂ) * Complex.I) := by
    have h2 : ((2 * Real.cos t : ℝ) : ℂ)
        = Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I) := by
      rw [← Complex.two_cos]
      simp
    rw [h2, add_pow]
    apply sum_congr rfl
    intro m hm
    have hmk : m ≤ k := by
      have := mem_range.mp hm
      omega
    have e : Complex.exp ((t : ℂ) * Complex.I) ^ m * Complex.exp (-(t : ℂ) * Complex.I) ^ (k - m)
        = Complex.exp ((((2 * (m : ℝ) - k) * t : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast [Nat.cast_sub hmk]
      ring
    rw [e, mul_comm]
    simp
  have h3 := congrArg Complex.re h
  rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum] at h3
  rw [h3]
  apply sum_congr rfl
  intro m _
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma sin_mul_sum (x : ℝ) (n : ℕ) :
    2 * Real.sin x * ∑ j ∈ range n, Real.cos ((2 * (j : ℝ) + 1) * x)
      = Real.sin (2 * (n : ℝ) * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 := Real.sin_add ((2 * (n : ℝ) + 1) * x) x
    have h2 := Real.sin_sub ((2 * (n : ℝ) + 1) * x) x
    have e1 : (2 * (n : ℝ) + 1) * x + x = 2 * ((n + 1 : ℕ) : ℝ) * x := by
      push_cast
      ring
    have e2 : (2 * (n : ℝ) + 1) * x - x = 2 * (n : ℝ) * x := by ring
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2]
    ring

lemma neg_one_zpow_eq (e : ℤ) (k : ℕ) (h : Even e ↔ Even k) :
    (-1 : ℝ) ^ e = (-1 : ℝ) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [(h.mpr hk).neg_one_zpow, hk.neg_one_pow]
  · have he : Odd e := by
      rw [← Int.not_even_iff_odd]
      intro h'
      exact (Nat.not_even_iff_odd.mpr hk) (h.mp h')
    rw [he.neg_one_zpow, hk.neg_one_pow]

lemma sum_cos (n k m : ℕ) :
    2 * ∑ j ∈ range n,
        Real.cos ((2 * (m : ℝ) - k) * ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)))
      = (-1 : ℝ) ^ k * (2 * (n : ℝ) - (2 * (n : ℝ) + 1) *
          (if ((2 * n + 1 : ℕ) : ℤ) ∣ (2 * (m : ℤ) - k) then 0 else 1)) := by
  have hN : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = 2 * (m : ℤ) - k := ⟨_, rfl⟩
  have hcr : (2 * (m : ℝ) - k) = (c : ℝ) := by
    rw [hc]
    push_cast
    ring
  rw [hcr, ← hc]
  have hck : Even c ↔ Even k := by
    rw [Int.even_iff, Nat.even_iff]
    omega
  by_cases hdvd : ((2 * n + 1 : ℕ) : ℤ) ∣ c
  · rw [if_pos hdvd]
    obtain ⟨t, ht⟩ := hdvd
    have htr : (c : ℝ) = (2 * (n : ℝ) + 1) * t := by
      rw [ht]
      push_cast
      ring
    have hNodd : ¬ Even ((2 * n + 1 : ℕ) : ℤ) := by
      rw [Int.even_iff]
      omega
    have hct : Even c ↔ Even t := by
      rw [ht, Int.even_mul]
      tauto
    have each : ∀ j ∈ range n,
        Real.cos ((c : ℝ) * ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))) = (-1 : ℝ) ^ k := by
      intro j _
      have e : (c : ℝ) * ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))
          = (((2 * (j : ℤ) + 1) * t : ℤ) : ℝ) * Real.pi := by
        rw [htr]
        push_cast
        field_simp
      rw [e, Real.cos_int_mul_pi]
      apply neg_one_zpow_eq
      have hjodd : ¬ Even (2 * (j : ℤ) + 1) := by
        rw [Int.even_iff]
        omega
      rw [Int.even_mul]
      tauto
    rw [sum_congr rfl each, sum_const, card_range, nsmul_eq_mul]
    ring
  · rw [if_neg hdvd]
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (c : ℝ) * Real.pi / (2 * (n : ℝ) + 1) := ⟨_, rfl⟩
    have e : ∀ j ∈ range n,
        Real.cos ((c : ℝ) * ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)))
          = Real.cos ((2 * (j : ℝ) + 1) * x) := by
      intro j _
      congr 1
      rw [hx]
      ring
    rw [sum_congr rfl e]
    have hA := sin_mul_sum x n
    have e2 : 2 * (n : ℝ) * x = (c : ℝ) * Real.pi - x := by
      rw [hx]
      field_simp
      ring
    rw [e2, Real.sin_int_mul_pi_sub] at hA
    have hsin : Real.sin x ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := Real.sin_eq_zero_iff.mp h0
      have h5 : (t : ℝ) * (2 * (n : ℝ) + 1) * Real.pi = (c : ℝ) * Real.pi := by
        have h4 : (t : ℝ) * Real.pi * (2 * (n : ℝ) + 1) = (c : ℝ) * Real.pi := by
          rw [ht, hx]
          field_simp
        rw [← h4]
        ring
      have h6 : (t : ℝ) * (2 * (n : ℝ) + 1) = (c : ℝ) := mul_right_cancel₀ Real.pi_ne_zero h5
      have h7 : c = ((2 * n + 1 : ℕ) : ℤ) * t := by
        have h8 : (c : ℝ) = ((((2 * n + 1 : ℕ) : ℤ) * t : ℤ) : ℝ) := by
          push_cast
          rw [← h6]
          ring
        exact_mod_cast h8
      exact hdvd ⟨t, h7⟩
    have h8 : (2 * ∑ j ∈ range n, Real.cos ((2 * (j : ℝ) + 1) * x)) * Real.sin x
        = (-((-1 : ℝ) ^ c)) * Real.sin x := by
      linear_combination hA
    have h9 := mul_right_cancel₀ hsin h8
    rw [h9, neg_one_zpow_eq c k hck]
    ring

lemma two_entry (n k : ℕ) :
    2 * OMA.S_oeis_a376498.entry n k
      = (-1 : ℝ) ^ k * (2 * (n : ℝ) * 2 ^ k - (2 * (n : ℝ) + 1) *
          ((∑ m ∈ range (k + 1),
            if ¬ ((2 * n + 1 : ℕ) : ℤ) ∣ (2 * (m : ℤ) - k) then k.choose m else 0 : ℕ) : ℝ)) := by
  unfold OMA.S_oeis_a376498.entry OMA.S_oeis_a376498.theta
  have h1 : ∀ j ∈ range n,
      (2 : ℝ) ^ k * Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)) ^ k
        = ∑ m ∈ range (k + 1), (k.choose m : ℝ) *
            Real.cos ((2 * (m : ℝ) - k) * ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))) := by
    intro j _
    rw [← mul_pow, two_cos_pow]
  have h2 : (2 : ℝ) ^ k *
      ∑ j ∈ range n, Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)) ^ k
        = ∑ m ∈ range (k + 1), (k.choose m : ℝ) * ∑ j ∈ range n,
            Real.cos ((2 * (m : ℝ) - k) * ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))) := by
    rw [mul_sum, sum_congr rfl h1, sum_comm]
    apply sum_congr rfl
    intro m _
    rw [mul_sum]
  rw [h2, mul_sum]
  have h3 : ∀ m ∈ range (k + 1),
      2 * ((k.choose m : ℝ) * ∑ j ∈ range n,
          Real.cos ((2 * (m : ℝ) - k) * ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))))
        = (-1 : ℝ) ^ k * (2 * (n : ℝ) * (k.choose m : ℝ) - (2 * (n : ℝ) + 1) *
            ((if ¬ ((2 * n + 1 : ℕ) : ℤ) ∣ (2 * (m : ℤ) - k) then k.choose m else 0 : ℕ) : ℝ)) := by
    intro m _
    rw [mul_left_comm, sum_cos n k m]
    by_cases hd : ((2 * n + 1 : ℕ) : ℤ) ∣ (2 * (m : ℤ) - k)
    · rw [if_pos hd, if_neg (not_not.mpr hd)]
      push_cast
      ring
    · rw [if_neg hd, if_pos hd]
      ring
  rw [sum_congr rfl h3, ← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum]
  have h4 : ∑ m ∈ range (k + 1), (k.choose m : ℝ) = 2 ^ k := by
    have h5 := Nat.sum_range_choose k
    exact_mod_cast h5
  rw [h4]
  push_cast
  ring

lemma even_B (n k : ℕ) :
    Even (∑ m ∈ range (k + 1),
      if ¬ ((2 * n + 1 : ℕ) : ℤ) ∣ (2 * (m : ℤ) - k) then k.choose m else 0) := by
  rw [← sum_filter]
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine Finset.sum_involution (fun a _ => k - a) ?_ ?_ ?_ ?_
  · intro a ha
    have hak : a ≤ k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    rw [Nat.choose_symm hak]
    exact CharTwo.add_self_eq_zero _
  · intro a ha _ heq
    have hak : a ≤ k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    apply (mem_filter.mp ha).2
    have h0 : 2 * (a : ℤ) - k = 0 := by omega
    rw [h0]
    exact dvd_zero _
  · intro a ha
    have hak : a ≤ k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    rw [mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    intro hd
    apply (mem_filter.mp ha).2
    have h0 : 2 * (a : ℤ) - k = -(2 * ((k - a : ℕ) : ℤ) - k) := by
      push_cast [Nat.cast_sub hak]
      ring
    rw [h0]
    exact (dvd_neg).mpr hd
  · intro a ha
    have hak : a ≤ k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    show k - (k - a) = a
    omega

end OMA.A376498

theorem OMA.solution : type_of% @OMA.S_oeis_a376498.main := by
  intro n k
  obtain ⟨r, hr⟩ := OMA.A376498.even_B n k
  have h := OMA.A376498.two_entry n k
  rw [hr] at h
  refine ⟨(-1) ^ k * ((n : ℤ) * 2 ^ k - (2 * (n : ℤ) + 1) * r), ?_⟩
  push_cast at h ⊢
  linear_combination h / 2
