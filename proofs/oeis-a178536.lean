import OMAStatements.S_oeis_a178536

/-!
Proof of Mats Granvik's conjecture on OEIS A178536:
Let `T` be the lower-triangular matrix `A178534`, and `a` the first column of `T⁻¹`.
We prove `T = M * D` where `M(n, j) = f(n - j)` (`f(0) = 1`, `f(d) = Fib(d)` for `d ≥ 1`) and
`D(j, k) = [k ∣ j]`. Then Möbius inversion and the Fibonacci even-step sum identity yield
`T * a₀ = e₁`, and uniqueness of the inverse first column gives `a = a₀`.
-/

namespace A178536Proof

open Finset OMA.S_oeis_a178536

private def f (d : ℕ) : ℤ :=
  if d = 0 then 1 else (Nat.fib d : ℤ)

private lemma fib_sum (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n, (Nat.fib r : ℤ) = (Nat.fib (n + 2) : ℤ) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    have hfib : Nat.fib (n + 1 + 2) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    rw [hfib]
    push_cast
    ring

private lemma f_even_sum : ∀ n : ℕ, 2 ≤ n →
    ∑ m ∈ Finset.Icc 1 (n / 2), f (n - 2 * m) = f (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases eq_or_ne n 2 with rfl | hne2
    · simp [f]
    rcases eq_or_ne n 3 with rfl | hne3
    · simp [f]
    have hn4 : 4 ≤ n := by omega
    have hsplit : ∑ m ∈ Finset.Icc 1 (n / 2), f (n - 2 * m) =
        f (n - 2) + ∑ m ∈ Finset.Icc 1 ((n - 2) / 2), f ((n - 2) - 2 * m) := by
      have hdiv : n / 2 = (n - 2) / 2 + 1 := by omega
      rw [hdiv]
      have h1 : Finset.Icc 1 ((n - 2) / 2 + 1) =
          insert 1 ((Finset.Icc 1 ((n - 2) / 2)).image (· + 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image]
        constructor
        · intro hx
          rcases eq_or_ne x 1 with rfl | h1
          · exact Or.inl rfl
          · exact Or.inr ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
        · rintro (rfl | ⟨y, hy, rfl⟩) <;> omega
      rw [h1, Finset.sum_insert (by simp)]
      rw [Finset.sum_image (fun x _ y _ h => by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      congr 1
      omega
    rw [hsplit, ih (n - 2) (by omega) (by omega)]
    set r := n - 3
    have h1 : n - 1 = r + 2 := by omega
    have h2 : n - 2 = r + 1 := by omega
    have h3 : n - 2 - 1 = r := by omega
    rw [h1, h3, h2]
    simp only [f, show r ≠ 0 by omega, show r + 1 ≠ 0 by omega, show r + 2 ≠ 0 by omega,
      ↓reduceIte, Nat.fib_add_two]
    push_cast
    ring

private def S (n k : ℕ) : ℤ :=
  if k = 0 then 0 else ∑ m ∈ Finset.Icc 1 (n / k), f (n - m * k)

private lemma S_eq_zero_of_lt {n k : ℕ} (h : n < k) : S n k = 0 := by
  unfold S
  split_ifs with hk
  · rfl
  · have hdiv : n / k = 0 := Nat.div_eq_of_lt h
    rw [hdiv]
    simp

private lemma S_diag {n : ℕ} (hn : 1 ≤ n) : S n n = 1 := by
  unfold S
  rw [if_neg (by omega), Nat.div_self hn]
  simp [f]

private lemma S_col1 {n : ℕ} (hn : 1 ≤ n) : S n 1 = (Nat.fib (n + 1) : ℤ) := by
  unfold S
  rw [if_neg (by decide), Nat.div_one]
  have hsplit : ∑ m ∈ Finset.Icc 1 n, f (n - m * 1) =
      f 0 + ∑ r ∈ Finset.Icc 1 (n - 1), f r := by
    rw [show Finset.Icc 1 n = Finset.Icc 1 ((n - 1) + 1) by congr 1; omega,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n - 1 + 1)]
    simp only [show n - 1 + 1 = n by omega, mul_one, Nat.sub_self]
    rw [add_comm]
    congr 1
    apply Finset.sum_bij (fun m _ => n - m)
    · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
    · intro m₁ hm₁ m₂ hm₂ h; rw [Finset.mem_Icc] at hm₁ hm₂; omega
    · intro r hr; rw [Finset.mem_Icc] at hr; exact ⟨n - r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro m _; rfl
  rw [hsplit]
  have hf : ∑ r ∈ Finset.Icc 1 (n - 1), f r = ∑ r ∈ Finset.Icc 1 (n - 1), (Nat.fib r : ℤ) := by
    apply Finset.sum_congr rfl
    intro r hr; rw [Finset.mem_Icc] at hr; simp [f, show r ≠ 0 by omega]
  rw [hf, fib_sum, show f 0 = 1 by simp [f], show n - 1 + 2 = n + 1 by omega]
  ring

private lemma sum_S_window {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.range k, S (n - i) k = ∑ r ∈ Finset.range (n - k + 1), f r := by
  have h1 : ∀ i ∈ Finset.range k,
      S (n - i) k = ∑ m ∈ Finset.Icc 1 ((n - i) / k), f ((n - i) - m * k) := by
    intro i _; unfold S; rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl h1, Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => n - (p.2 * k + p.1))
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    have hmul : p.2 * k ≤ n - p.1 :=
      le_trans (Nat.mul_le_mul_right k hp.2.2) (Nat.div_mul_le_self (n - p.1) k)
    have hge : k ≤ p.2 * k := le_trans (by simp) (Nat.mul_le_mul_right k hp.2.1)
    omega
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp₁ hp₂
    have hm1 : p₁.2 * k ≤ n - p₁.1 := le_trans (Nat.mul_le_mul_right k hp₁.2.2) (Nat.div_mul_le_self _ k)
    have hm2 : p₂.2 * k ≤ n - p₂.1 := le_trans (Nat.mul_le_mul_right k hp₂.2.2) (Nat.div_mul_le_self _ k)
    have hsum : p₁.2 * k + p₁.1 = p₂.2 * k + p₂.1 := by omega
    have hq : p₁.2 = p₂.2 := by
      have h1' := congrArg (· / k) hsum
      rw [mul_comm p₁.2 k, mul_comm p₂.2 k, Nat.mul_add_div hk, Nat.mul_add_div hk,
        Nat.div_eq_of_lt hp₁.1, Nat.div_eq_of_lt hp₂.1] at h1'
      omega
    have hr : p₁.1 = p₂.1 := by
      rw [hq] at hsum; omega
    exact Sigma.ext hr (heq_of_eq hq)
  · intro r hr
    rw [Finset.mem_range] at hr
    set j := n - r
    have hj_ge : k ≤ j := by omega
    have hj_le : j ≤ n := by omega
    refine ⟨⟨j % k, j / k⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc]
      refine ⟨Nat.mod_lt j hk, Nat.div_pos hj_ge hk, ?_⟩
      have hdm : k * (j / k) + j % k = j := Nat.div_add_mod j k
      have hle : (j / k) * k ≤ n - j % k := by
        have h1' : (j / k) * k + j % k ≤ n := by linarith [mul_comm k (j / k)]
        omega
      exact (Nat.le_div_iff_mul_le hk).mpr hle
    · have hdm : (j / k) * k + j % k = j := by linarith [Nat.div_add_mod j k, mul_comm k (j / k)]
      rw [hdm]
      omega
  · intro p _
    congr 1
    omega

private lemma T_eq_S : ∀ n k : ℕ, T n k = S n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k
    rw [T]
    by_cases h0 : k = 0 ∨ n < k
    · rw [if_pos h0]
      rcases h0 with rfl | hlt
      · simp [S]
      · exact (S_eq_zero_of_lt hlt).symm
    · rw [if_neg h0]
      push Not at h0
      have hk1 : 1 ≤ k := by omega
      have hkn : k ≤ n := by omega
      by_cases hkeq : k = 1
      · rw [if_pos hkeq, hkeq, S_col1 (by omega)]
      · rw [if_neg hkeq]
        have hk2 : 2 ≤ k := by omega
        have h1 : ∑ i ∈ Finset.range (k - 1), T (n - (i + 1)) (k - 1) =
            ∑ i ∈ Finset.range (k - 1), S (n - (i + 1)) (k - 1) := by
          apply Finset.sum_congr rfl
          intro i _; exact ih (n - (i + 1)) (by omega) (k - 1)
        have h2 : ∑ i ∈ Finset.range (k - 1), T (n - (i + 1)) k =
            ∑ i ∈ Finset.range (k - 1), S (n - (i + 1)) k := by
          apply Finset.sum_congr rfl
          intro i _; exact ih (n - (i + 1)) (by omega) k
        rw [h1, h2]
        have hwin1 : ∑ i ∈ Finset.range k, S (n - i) k =
            S n k + ∑ i ∈ Finset.range (k - 1), S (n - (i + 1)) k := by
          rw [show Finset.range k = Finset.range ((k - 1) + 1) by congr 1; omega,
            Finset.sum_range_succ']
          simp only [Nat.sub_zero, add_comm]
        have hwin2 : ∑ i ∈ Finset.range (k - 1), S (n - (i + 1)) (k - 1) =
            ∑ i ∈ Finset.range (k - 1), S ((n - 1) - i) (k - 1) := by
          apply Finset.sum_congr rfl
          intro i _; congr 1; omega
        have heq1 := sum_S_window hk1 hkn
        have heq2 := sum_S_window (show 1 ≤ k - 1 by omega) (show k - 1 ≤ n - 1 by omega)
        have hsub : n - 1 - (k - 1) = n - k := by omega
        rw [hsub] at heq2
        rw [hwin2, heq2, ← heq1, hwin1]
        ring

private def w (k : ℕ) : ℤ :=
  (if k = 1 then 1 else 0) - (if 2 ∣ k then 1 else 0)

private def a0 (n : ℕ) : ℤ :=
  ∑ k ∈ n.divisors, (ArithmeticFunction.moebius (n / k) : ℤ) * w k

private lemma sum_moebius_divisors_eq (m : ℕ) (hm : 1 ≤ m) :
    ∑ q ∈ m.divisors, (ArithmeticFunction.moebius q : ℤ) = if m = 1 then 1 else 0 := by
  have h := congrArg (fun g : ArithmeticFunction ℤ => g m) ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    Nat.cast_ite, Nat.cast_zero, Nat.cast_one, mul_ite, mul_zero, mul_one] at h
  have hlhs : ∑ x ∈ m.divisorsAntidiagonal,
      (if x.2 = 0 then (0 : ℤ) else (ArithmeticFunction.moebius x.1 : ℤ)) =
      ∑ q ∈ m.divisors, (ArithmeticFunction.moebius q : ℤ) := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
      if b = 0 then (0 : ℤ) else (ArithmeticFunction.moebius a : ℤ))]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Nat.mem_divisors] at hq
    have hq_pos : 0 < q := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_dvd_iff] at hq; omega)
    have hmq_ne : m / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hq.1) hq_pos).ne'
    rw [if_neg hmq_ne]
  rw [← hlhs]
  exact h

private lemma sum_divisors_a0 {j : ℕ} (hj : 1 ≤ j) :
    ∑ k ∈ j.divisors, a0 k = w j := by
  have hj0 : j ≠ 0 := by omega
  have h1 : ∑ k ∈ j.divisors, a0 k =
      ∑ k ∈ j.divisors, ∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℤ) * w d := rfl
  rw [h1]
  have hswap : ∑ k ∈ j.divisors, ∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℤ) * w d =
      ∑ d ∈ j.divisors, w d * ∑ q ∈ (j / d).divisors, (ArithmeticFunction.moebius q : ℤ) := by
    simp only [Finset.mul_sum, Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
    · intro p hp
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp ⊢
      obtain ⟨⟨hkj, _⟩, ⟨hdk, hk0⟩⟩ := hp
      have hd0 : p.2 ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hdk; exact hk0 hdk
      have hdj : p.2 ∣ j := dvd_trans hdk hkj
      have hq : p.1 / p.2 ∣ j / p.2 := by
        obtain ⟨r, hr⟩ := hdk
        obtain ⟨s, hs⟩ := hkj
        rw [hr, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
        have hjd : j / p.2 = r * s := by
          rw [hs, hr, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
        rw [hjd]; exact dvd_mul_right r s
      exact ⟨⟨hdj, hj0⟩, ⟨hq, (Nat.div_pos (Nat.le_of_dvd (by omega) hdj) (Nat.pos_of_ne_zero hd0)).ne'⟩⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp₁ hp₂
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨hd, hq⟩ := heq
      have h1' : p₁.1 = p₁.2 * (p₁.1 / p₁.2) := (Nat.mul_div_cancel' hp₁.2.1).symm
      have h2' : p₂.1 = p₂.2 * (p₂.1 / p₂.2) := (Nat.mul_div_cancel' hp₂.2.1).symm
      have hk : p₁.1 = p₂.1 := by rw [h1', h2', hq, hd]
      exact Sigma.ext hk (heq_of_eq hd)
    · intro q hq
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hq
      obtain ⟨⟨hdj, _⟩, ⟨hqd, hj_d0⟩⟩ := hq
      have hd0 : q.1 ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hdj; exact hj0 hdj
      have hq0 : q.2 ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hqd; exact hj_d0 hqd
      refine ⟨⟨q.1 * q.2, q.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Nat.mem_divisors]
        have hmul_dvd : q.1 * q.2 ∣ j := by
          obtain ⟨t, ht⟩ := hqd
          refine ⟨t, ?_⟩
          have := Nat.mul_div_cancel' hdj
          rw [ht] at this
          linarith
        exact ⟨⟨hmul_dvd, hj0⟩, ⟨dvd_mul_right _ _, Nat.mul_ne_zero hd0 hq0⟩⟩
      · exact Sigma.ext rfl (heq_of_eq (Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)))
    · intro p _
      ring
  rw [hswap]
  have hmob : ∀ d ∈ j.divisors,
      ∑ q ∈ (j / d).divisors, (ArithmeticFunction.moebius q : ℤ) = if d = j then 1 else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h => by rw [h, zero_dvd_iff] at hd; exact hj0 hd.1)
    have hjd_pos : 1 ≤ j / d := Nat.div_pos (Nat.le_of_dvd (by omega) hd.1) hd_pos
    rw [sum_moebius_divisors_eq (j / d) hjd_pos]
    by_cases heq : d = j
    · rw [if_pos heq, heq, Nat.div_self (by omega), if_pos rfl]
    · rw [if_neg heq, if_neg]
      intro h1
      have := Nat.mul_div_cancel' hd.1
      rw [h1, mul_one] at this
      exact heq this
  rw [Finset.sum_congr rfl (fun d hd => by rw [hmob d hd])]
  rw [Finset.sum_eq_single j]
  · simp
  · intro d _ hne; simp [hne]
  · intro hnot; exact (hnot (Nat.mem_divisors.mpr ⟨dvd_rfl, hj0⟩)).elim

private lemma T_mul_a0 {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, T n k * a0 k = if n = 1 then 1 else 0 := by
  have hT : ∑ k ∈ Finset.Icc 1 n, T n k * a0 k = ∑ k ∈ Finset.Icc 1 n, S n k * a0 k := by
    apply Finset.sum_congr rfl
    intro k _; rw [T_eq_S]
  rw [hT]
  have hswap : ∑ k ∈ Finset.Icc 1 n, S n k * a0 k =
      ∑ j ∈ Finset.Icc 1 n, f (n - j) * (∑ k ∈ j.divisors, a0 k) := by
    have hS : ∀ k ∈ Finset.Icc 1 n,
        S n k * a0 k = ∑ m ∈ Finset.Icc 1 (n / k), f (n - m * k) * a0 k := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      unfold S
      rw [if_neg (by omega), Finset.sum_mul]
    rw [Finset.sum_congr rfl hS]
    simp only [Finset.mul_sum, Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨p.2 * p.1, p.1⟩)
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
      have hmul : p.2 * p.1 ≤ n :=
        le_trans (Nat.mul_le_mul_right p.1 hp.2.2) (Nat.div_mul_le_self n p.1)
      have hpos : 1 ≤ p.2 * p.1 := Nat.mul_pos hp.2.1 hp.1.1
      exact ⟨⟨hpos, hmul⟩, ⟨dvd_mul_left p.1 p.2, by omega⟩⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hp₁ hp₂
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨hmul, hk⟩ := heq
      rw [hk] at hmul
      have hm : p₁.2 = p₂.2 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < p₂.1) hmul
      exact Sigma.ext hk (heq_of_eq hm)
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hq
      have hq2pos : 0 < q.2 := Nat.pos_of_ne_zero (fun h => by rw [h, zero_dvd_iff] at hq; exact hq.2.2 hq.2.1)
      have hdiv_pos : 1 ≤ q.1 / q.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hq.2.1) hq2pos
      have hdiv_le : q.1 / q.2 ≤ n / q.2 := Nat.div_le_div_right hq.1.2
      have hq2le : q.2 ≤ n := le_trans (Nat.le_of_dvd (by omega) hq.2.1) hq.1.2
      refine ⟨⟨q.2, q.1 / q.2⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_Icc]
        exact ⟨⟨hq2pos, hq2le⟩, ⟨hdiv_pos, hdiv_le⟩⟩
      · exact Sigma.ext (Nat.div_mul_cancel hq.2.1) HEq.rfl
    · intro p _
      rfl
  rw [hswap]
  have hsub : ∑ j ∈ Finset.Icc 1 n, f (n - j) * (∑ k ∈ j.divisors, a0 k) =
      ∑ j ∈ Finset.Icc 1 n, f (n - j) * w j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [sum_divisors_a0 hj.1]
  rw [hsub]
  rcases eq_or_ne n 1 with rfl | hne1
  · simp [f, w]
  · rw [if_neg hne1]
    have hn2 : 2 ≤ n := by omega
    have hsplit : ∑ j ∈ Finset.Icc 1 n, f (n - j) * w j =
        f (n - 1) - ∑ m ∈ Finset.Icc 1 (n / 2), f (n - 2 * m) := by
      have hw1 : ∑ j ∈ Finset.Icc 1 n, f (n - j) * w j =
          ∑ j ∈ Finset.Icc 1 n, (if j = 1 then f (n - j) else 0) -
          ∑ j ∈ Finset.Icc 1 n, (if 2 ∣ j then f (n - j) else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        unfold w
        split_ifs <;> ring
      rw [hw1]
      congr 1
      · rw [Finset.sum_eq_single 1]
        · simp
        · intro j _ hj; simp [hj]
        · intro hnot; exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)).elim
      · rw [← Finset.sum_filter]
        apply Finset.sum_bij (fun j _ => j / 2)
        · intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          rw [Finset.mem_Icc]
          obtain ⟨⟨hj1, hjn⟩, ⟨m, hm⟩⟩ := hj
          omega
        · intro j₁ hj₁ j₂ hj₂ heq
          rw [Finset.mem_filter] at hj₁ hj₂
          obtain ⟨m₁, hm₁⟩ := hj₁.2
          obtain ⟨m₂, hm₂⟩ := hj₂.2
          omega
        · intro m hm
          rw [Finset.mem_Icc] at hm
          refine ⟨2 * m, ?_, by omega⟩
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩⟩
        · intro j hj
          rw [Finset.mem_filter] at hj
          obtain ⟨m, hm⟩ := hj.2
          congr 1
          omega
    rw [hsplit, f_even_sum n hn2, sub_self]

theorem solve : type_of% @OMA.S_oeis_a178536.main := by
  intro a ha n hn
  have heq : ∀ m : ℕ, 1 ≤ m → a m = a0 m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      have h1 := ha m hm
      have h2 := T_mul_a0 hm
      rw [show Finset.Icc 1 m = Finset.Icc 1 ((m - 1) + 1) by congr 1; omega,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ m - 1 + 1)] at h1 h2
      rw [show m - 1 + 1 = m by omega] at h1 h2
      have hdiag : T m m = 1 := by rw [T_eq_S, S_diag hm]
      rw [hdiag, one_mul] at h1 h2
      have hprev : ∑ k ∈ Finset.Icc 1 (m - 1), T m k * a k =
          ∑ k ∈ Finset.Icc 1 (m - 1), T m k * a0 k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [ih k (by omega) hk.1]
      linarith
  exact heq n hn

end A178536Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a178536.main :=
  A178536Proof.solve
