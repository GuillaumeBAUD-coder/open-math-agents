import OMAStatements.S_oeis_a290194

section Rule705Proof
open OMA.S_oeis_a290194
open PowerSeries

def patOdd (x y : ℤ) : Bool :=
  decide ((x = 0 ∧ y = 0) ∨ 2 ≤ |x| ∨ 2 ≤ |y|)

def patEven (x y : ℤ) : Bool :=
  decide (2 ≤ |x| ∨ 2 ≤ |y|)

set_option maxHeartbeats 2000000 in
lemma step_patOdd (x y : ℤ) : step patOdd x y = patEven x y := by
  unfold step patOdd patEven
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases h with ⟨hx, hy⟩
    rcases abs_le.mp hx with ⟨hx1, hx2⟩
    rcases abs_le.mp hy with ⟨hy1, hy2⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · have hfar : 4 ≤ |x| ∨ 4 ≤ |y| := by omega
    rcases hfar with hx4 | hy4
    · have hc : 2 ≤ |x| := by omega
      have h1 : 2 ≤ |x - 1| := by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega
      have h2 : 2 ≤ |x + 1| := by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega
      simp only [hc, h1, h2, true_or, or_true, decide_true]
      decide
    · have hc : 2 ≤ |y| := by omega
      have h1 : 2 ≤ |y - 1| := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have h2 : 2 ≤ |y + 1| := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      simp only [hc, h1, h2, or_true, decide_true]
      decide

set_option maxHeartbeats 2000000 in
lemma step_patEven (x y : ℤ) : step patEven x y = patOdd x y := by
  unfold step patEven patOdd
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases h with ⟨hx, hy⟩
    rcases abs_le.mp hx with ⟨hx1, hx2⟩
    rcases abs_le.mp hy with ⟨hy1, hy2⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · have hfar : 4 ≤ |x| ∨ 4 ≤ |y| := by omega
    rcases hfar with hx4 | hy4
    · have hc : 2 ≤ |x| := by omega
      have h1 : 2 ≤ |x - 1| := by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega
      have h2 : 2 ≤ |x + 1| := by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega
      simp only [hc, h1, h2, true_or, or_true, decide_true]
      decide
    · have hc : 2 ≤ |y| := by omega
      have h1 : 2 ≤ |y - 1| := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have h2 : 2 ≤ |y + 1| := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      simp only [hc, h1, h2, or_true, decide_true]
      decide

set_option maxHeartbeats 2000000 in
lemma state_three_eq : state 3 = patOdd := by
  funext x y
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases h with ⟨hx, hy⟩
    rcases abs_le.mp hx with ⟨hx1, hx2⟩
    rcases abs_le.mp hy with ⟨hy1, hy2⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · have hout3 : ∀ u v : ℤ, 3 < |u| ∨ 3 < |v| → state 3 u v = true := by
      intro u v huv
      have hout2 : ∀ p q : ℤ, 2 < |p| ∨ 2 < |q| → state 2 p q = true := by
        intro p q hpq
        have hout1 : ∀ a b : ℤ, 1 < |a| ∨ 1 < |b| → state 1 a b = true := by
          intro a b hab
          have hout0 : ∀ c d : ℤ, ¬(c = 0 ∧ d = 0) → state 0 c d = false := by
            intro c d hcd; simp [state, hcd]
          change step (state 0) a b = true
          unfold step
          rw [hout0 a b (by cases abs_cases a <;> cases abs_cases b <;> omega),
              hout0 (a - 1) b (by cases abs_cases a <;> cases abs_cases b <;> omega),
              hout0 (a + 1) b (by cases abs_cases a <;> cases abs_cases b <;> omega),
              hout0 a (b - 1) (by cases abs_cases a <;> cases abs_cases b <;> omega),
              hout0 a (b + 1) (by cases abs_cases a <;> cases abs_cases b <;> omega)]
          decide
        change step (state 1) p q = true
        unfold step
        rw [hout1 p q (by omega),
            hout1 (p - 1) q (by cases abs_cases p <;> cases abs_cases (p - 1) <;> omega),
            hout1 (p + 1) q (by cases abs_cases p <;> cases abs_cases (p + 1) <;> omega),
            hout1 p (q - 1) (by cases abs_cases q <;> cases abs_cases (q - 1) <;> omega),
            hout1 p (q + 1) (by cases abs_cases q <;> cases abs_cases (q + 1) <;> omega)]
        decide
      change step (state 2) u v = true
      unfold step
      rw [hout2 u v (by omega),
          hout2 (u - 1) v (by cases abs_cases u <;> cases abs_cases (u - 1) <;> omega),
          hout2 (u + 1) v (by cases abs_cases u <;> cases abs_cases (u + 1) <;> omega),
          hout2 u (v - 1) (by cases abs_cases v <;> cases abs_cases (v - 1) <;> omega),
          hout2 u (v + 1) (by cases abs_cases v <;> cases abs_cases (v + 1) <;> omega)]
      decide
    have hfar : 3 < |x| ∨ 3 < |y| := by omega
    rw [hout3 x y hfar]
    unfold patOdd
    rcases hfar with hx3 | hy3
    · simp [show 2 ≤ |x| by omega]
    · simp [show 2 ≤ |y| by omega]

lemma state_ge3 (k : ℕ) :
    state (2 * k + 3) = patOdd ∧ state (2 * k + 4) = patEven := by
  induction k with
  | zero =>
    refine ⟨state_three_eq, ?_⟩
    change step (state 3) = patEven
    rw [state_three_eq]
    funext x y; exact step_patOdd x y
  | succ k ih =>
    have h1 : state (2 * (k + 1) + 3) = patOdd := by
      have heq : 2 * (k + 1) + 3 = (2 * k + 4) + 1 := by omega
      rw [heq]
      change step (state (2 * k + 4)) = patOdd
      rw [ih.2]
      funext x y; exact step_patEven x y
    have h2 : state (2 * (k + 1) + 4) = patEven := by
      have heq : 2 * (k + 1) + 4 = (2 * (k + 1) + 3) + 1 := by omega
      rw [heq]
      change step (state (2 * (k + 1) + 3)) = patEven
      rw [h1]
      funext x y; exact step_patOdd x y
    exact ⟨h1, h2⟩

lemma geom_two_nat (m : ℕ) : (∑ i ∈ Finset.range m, 2 ^ i) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; omega

lemma sum_pow2_high (n : ℕ) (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range (n - 1), 2 ^ (n - i)) = 2 ^ (n + 1) - 4 := by
  have h1 : ∀ i ∈ Finset.range (n - 1), 2 ^ (n - i) = 4 * 2 ^ (n - 2 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have heq : n - i = 2 + (n - 2 - i) := by omega
    rw [heq, pow_add]; norm_num
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have href : (∑ i ∈ Finset.range (n - 1), 2 ^ (n - 2 - i)) =
      ∑ i ∈ Finset.range (n - 1), 2 ^ i := by
    have := Finset.sum_range_reflect (fun i => 2 ^ i) (n - 1)
    have hsub : n - 1 - 1 = n - 2 := by omega
    simpa [hsub] using this
  rw [href]
  have hg := geom_two_nat (n - 1)
  have hp : 4 * 2 ^ (n - 1) = 2 ^ (n + 1) := by
    have heq : n + 1 = 2 + (n - 1) := by omega
    rw [heq, pow_add]; norm_num
  omega

lemma a_closed_ge3 (n : ℕ) (hn : 3 ≤ n) : a n = 2 ^ (n + 1) - 4 + n % 2 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hst : state (2 * (k + 2)) = patEven := by
      have heq : 2 * (k + 2) = 2 * k + 4 := by omega
      rw [heq]; exact (state_ge3 k).2
    unfold a
    rw [hst]
    have hsplit : 2 * (k + 2) + 1 = (2 * (k + 2) - 1) + 2 := by omega
    conv_lhs => rw [hsplit, Finset.sum_range_add]
    have hhead : ∑ i ∈ Finset.range (2 * (k + 2) - 1),
        (patEven ((i : ℤ) - ↑(2 * (k + 2))) ((i : ℤ) - ↑(2 * (k + 2)))).toNat *
          2 ^ (2 * (k + 2) - i) =
        ∑ i ∈ Finset.range (2 * (k + 2) - 1), 2 ^ (2 * (k + 2) - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hpat : patEven ((i : ℤ) - ↑(2 * (k + 2))) ((i : ℤ) - ↑(2 * (k + 2))) = true := by
        unfold patEven
        exact decide_eq_true (Or.inl (by cases abs_cases ((i : ℤ) - ↑(2 * (k + 2))) <;> omega))
      rw [hpat]; simp
    have htail : ∑ j ∈ Finset.range 2,
        (patEven (((2 * (k + 2) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 2)))
          (((2 * (k + 2) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 2)))).toNat *
          2 ^ (2 * (k + 2) - (2 * (k + 2) - 1 + j)) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have c0 : (((2 * (k + 2) - 1 + 0 : ℕ) : ℤ) - ↑(2 * (k + 2))) = -1 := by omega
      have c1 : (((2 * (k + 2) - 1 + 1 : ℕ) : ℤ) - ↑(2 * (k + 2))) = 0 := by omega
      rw [c0, c1]
      have p0 : patEven (-1) (-1) = false := by decide
      have p1 : patEven 0 0 = false := by decide
      simp [p0, p1]
    rw [hhead, htail, add_zero, sum_pow2_high (2 * (k + 2)) (by omega)]
    have hmod : (2 * (k + 2)) % 2 = 0 := by omega
    rw [hmod, add_zero]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hst : state (2 * (k + 1) + 1) = patOdd := by
      have heq : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [heq]; exact (state_ge3 k).1
    unfold a
    rw [hst]
    have hsplit : (2 * (k + 1) + 1) + 1 = ((2 * (k + 1) + 1) - 1) + 2 := by omega
    conv_lhs => rw [hsplit, Finset.sum_range_add]
    have hhead : ∑ i ∈ Finset.range ((2 * (k + 1) + 1) - 1),
        (patOdd ((i : ℤ) - ↑(2 * (k + 1) + 1)) ((i : ℤ) - ↑(2 * (k + 1) + 1))).toNat *
          2 ^ ((2 * (k + 1) + 1) - i) =
        ∑ i ∈ Finset.range ((2 * (k + 1) + 1) - 1), 2 ^ ((2 * (k + 1) + 1) - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hpat : patOdd ((i : ℤ) - ↑(2 * (k + 1) + 1)) ((i : ℤ) - ↑(2 * (k + 1) + 1)) = true := by
        unfold patOdd
        exact decide_eq_true (Or.inr (Or.inl (by cases abs_cases ((i : ℤ) - ↑(2 * (k + 1) + 1)) <;> omega)))
      rw [hpat]; simp
    have htail : ∑ j ∈ Finset.range 2,
        (patOdd ((((2 * (k + 1) + 1) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 1) + 1))
          ((((2 * (k + 1) + 1) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 1) + 1))).toNat *
          2 ^ ((2 * (k + 1) + 1) - ((2 * (k + 1) + 1) - 1 + j)) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have c0 : ((((2 * (k + 1) + 1) - 1 + 0 : ℕ) : ℤ) - ↑(2 * (k + 1) + 1)) = -1 := by omega
      have c1 : ((((2 * (k + 1) + 1) - 1 + 1 : ℕ) : ℤ) - ↑(2 * (k + 1) + 1)) = 0 := by omega
      have s1 : (2 * (k + 1) + 1) - ((2 * (k + 1) + 1) - 1 + 1) = 0 := by omega
      rw [c0, c1, s1]
      have p0 : patOdd (-1) (-1) = false := by decide
      have p1 : patOdd 0 0 = true := by decide
      simp [p0, p1]
    rw [hhead, htail, sum_pow2_high (2 * (k + 1) + 1) (by omega)]
    have hmod : (2 * (k + 1) + 1) % 2 = 1 := by omega
    rw [hmod]

lemma a_fib_le3 (n : ℕ) (hn : n ≤ 3) : a n = Nat.fib (2 * n + 1) := by
  interval_cases n <;> decide

lemma a_step_even (n : ℕ) (hn : 3 < n) (he : n % 2 = 0) : a n = 2 * a (n - 1) + 2 := by
  rw [a_closed_ge3 n (by omega), a_closed_ge3 (n - 1) (by omega)]
  have ho : (n - 1) % 2 = 1 := by omega
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hn1 : n - 1 + 1 = n := by omega
  have hge : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hn1, he, ho, hp]
  omega

lemma a_step_odd (n : ℕ) (hn : 3 < n) (ho : n % 2 = 1) : a n = 2 * a (n - 1) + 5 := by
  rw [a_closed_ge3 n (by omega), a_closed_ge3 (n - 1) (by omega)]
  have he : (n - 1) % 2 = 0 := by omega
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hn1 : n - 1 + 1 = n := by omega
  have hge : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hn1, ho, he, hp]
  omega

lemma rec_rel (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) := by
  by_cases he : n % 2 = 0
  · have s0 := a_step_even n (by omega) he
    have s2 := a_step_even (n - 2) (by omega) (by omega)
    have hsub : n - 2 - 1 = n - 3 := by omega
    rw [hsub] at s2
    omega
  · have ho : n % 2 = 1 := by omega
    have s0 := a_step_odd n (by omega) ho
    have s2 := a_step_odd (n - 2) (by omega) (by omega)
    have hsub : n - 2 - 1 = n - 3 := by omega
    rw [hsub] at s2
    omega

set_option maxHeartbeats 1000000 in
lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (X + 1) * (2 * X - 1)) =
      2 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 1 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hring : s * ((X - 1) * (X + 1) * (2 * X - 1)) =
      C (1 : ℤ) * (s * X ^ 0) + C (-2 : ℤ) * (s * X ^ 1) +
      C (-1 : ℤ) * (s * X ^ 2) + C (2 : ℤ) * (s * X ^ 3) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hring]
  have hrhs : (2 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 1 : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 0 + C (3 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (2 : ℤ) * X ^ 5 := by
    simp only [map_one, map_ofNat]; ring
  rw [hrhs]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 6
  · have v0 : a 0 = 1 := by decide
    have v1 : a 1 = 2 := by decide
    have v2 : a 2 = 5 := by decide
    have v3 : a 3 = 13 := by decide
    have v4 : a 4 = 28 := by decide
    have v5 : a 5 = 61 := by decide
    interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5]
  · have h5 : 5 < n := by omega
    have hrec := rec_rel n h5
    have n0 : n ≠ 0 := by omega
    have n3 : n ≠ 3 := by omega
    have n4 : n ≠ 4 := by omega
    have n5 : n ≠ 5 := by omega
    simp [n0, n3, n4, n5, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    linarith

end Rule705Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a290194.main :=
  ⟨a_fib_le3, a_step_even, a_step_odd, a_closed_ge3, rec_rel, gf_eq⟩
