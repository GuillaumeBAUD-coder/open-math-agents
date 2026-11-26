import FormalConjectures.Wikipedia.DirichletDivisorProblem

-- Problem: Dirichlet divisor problem — divisor error dirichlet
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/DirichletDivisorProblem.lean:70 (declaration DirichletDivisorProblem.divisor_error_dirichlet)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

/-- `∑_{n ≤ N} d(n) = ∑_{a ≤ N} ⌊N / a⌋` (swap the order of summation). -/
lemma sum_card_divisors_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, N / a := by
  have h1 : ∀ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, if a ∣ n then 1 else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    rw [← card_filter]
    congr 1
    ext a
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [mem_Icc] at ha
  rw [← card_filter, ← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

/-- For `1 ≤ a`, the number of `b ∈ [1, N]` with `a b ≤ N` is `⌊N / a⌋`. -/
lemma count_mul_le (N a : ℕ) (ha : 1 ≤ a) :
    ∑ b ∈ Icc 1 N, (if a * b ≤ N then 1 else 0) = N / a := by
  rw [← card_filter]
  have : (Icc 1 N).filter (fun b => a * b ≤ N) = Icc 1 (N / a) := by
    ext b
    simp only [mem_filter, mem_Icc]
    rw [Nat.le_div_iff_mul_le (by omega)]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, by linarith [mul_comm a b]⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, by linarith [mul_comm a b]⟩
      nlinarith
  rw [this, Nat.card_Icc, Nat.add_sub_cancel]

/-- Dirichlet's hyperbola identity: `D(N) + y² = 2 ∑_{a ≤ y} ⌊N / a⌋` with `y = ⌊√N⌋`. -/
lemma hyperbola (N : ℕ) :
    ∑ a ∈ Icc 1 N, N / a + N.sqrt * N.sqrt = 2 * ∑ a ∈ Icc 1 N.sqrt, N / a := by
  set y := N.sqrt with hy
  have hy1 : y * y ≤ N := Nat.sqrt_le N
  have hy2 : N < (y + 1) * (y + 1) := Nat.lt_succ_sqrt N
  have hyN : y ≤ N := Nat.sqrt_le_self N
  -- Pointwise inclusion-exclusion on the pairs `(a, b)`.
  have key : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      (if a * b ≤ N then 1 else 0) + (if a ≤ y ∧ b ≤ y then 1 else 0) =
        (if a * b ≤ N ∧ a ≤ y then 1 else 0) + (if a * b ≤ N ∧ b ≤ y then 1 else 0) := by
    intro a _ b _
    by_cases hP : a * b ≤ N <;> by_cases hA : a ≤ y <;> by_cases hB : b ≤ y <;>
      simp only [hP, hA, hB, and_self, and_true, and_false, true_and, false_and, if_true,
        if_false] <;> first
      | rfl
      | (exfalso; have := Nat.mul_le_mul hA hB; omega)
      | (exfalso; have := Nat.mul_le_mul (Nat.not_le.mp hA) (Nat.not_le.mp hB); nlinarith)
  have hsum := sum_congr rfl fun a ha => sum_congr rfl (key a ha)
  simp only [sum_add_distrib] at hsum
  -- Identify each of the four double sums.
  have e1 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a * b ≤ N then 1 else 0) = ∑ a ∈ Icc 1 N, N / a :=
    sum_congr rfl fun a ha => count_mul_le N a (mem_Icc.mp ha).1
  have c1 : ∑ a ∈ Icc 1 N, (if a ≤ y then 1 else 0) = y := by
    rw [← card_filter]
    have : (Icc 1 N).filter (· ≤ y) = Icc 1 y := by
      ext a; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  have e2 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a ≤ y ∧ b ≤ y then 1 else 0) = y * y := by
    have : ∀ a b : ℕ, (if a ≤ y ∧ b ≤ y then 1 else 0 : ℕ) =
        (if a ≤ y then 1 else 0) * (if b ≤ y then 1 else 0) := by
      intro a b
      by_cases ha : a ≤ y <;> by_cases hb : b ≤ y <;> simp [ha, hb]
    simp_rw [this]
    rw [← sum_mul_sum, c1]
  have row : ∀ a ∈ Icc 1 N,
      ∑ b ∈ Icc 1 N, (if a * b ≤ N ∧ a ≤ y then 1 else 0) = if a ≤ y then N / a else 0 := by
    intro a ha
    split_ifs with hA
    · simp only [hA, and_true]; exact count_mul_le N a (mem_Icc.mp ha).1
    · simp [hA]
  have e3 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a * b ≤ N ∧ a ≤ y then 1 else 0) =
      ∑ a ∈ Icc 1 y, N / a := by
    rw [sum_congr rfl row, ← sum_filter]
    congr 1
    ext a; simp only [mem_filter, mem_Icc]; omega
  have e4 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a * b ≤ N ∧ b ≤ y then 1 else 0) =
      ∑ a ∈ Icc 1 y, N / a := by
    rw [sum_comm, ← e3]
    simp_rw [mul_comm]
  rw [e1, e2, e3, e4] at hsum
  omega

set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @DirichletDivisorProblem.divisor_error_dirichlet := by
  apply Asymptotics.IsBigO.of_bound 13
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with x hx
  set N := ⌊x⌋₊ with hN
  set y := N.sqrt with hy
  have hx0 : 0 ≤ x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hN4 : 4 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hy2 : 2 ≤ y := by rw [hy, Nat.le_sqrt]; omega
  have hyy : y * y ≤ N := Nat.sqrt_le N
  have hyy' : N < (y + 1) * (y + 1) := Nat.lt_succ_sqrt N
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hyyR : (y : ℝ) * y ≤ x := by
    have : ((y * y : ℕ) : ℝ) ≤ N := by exact_mod_cast hyy
    push_cast at this; linarith
  have hxy1 : x < ((y : ℝ) + 1) * ((y : ℝ) + 1) := by
    have : (N : ℝ) + 1 ≤ (((y + 1) * (y + 1) : ℕ) : ℝ) := by exact_mod_cast hyy'
    push_cast at this; linarith
  set s := Real.sqrt x with hs
  have hss : s * s = x := Real.mul_self_sqrt hx0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hys : (y : ℝ) ≤ s := by nlinarith
  have hsy : s < y + 1 := by nlinarith
  have hspos : 0 < s := by linarith
  -- `D(x) = 2 S - y²` with `S = ∑_{a ≤ y} ⌊N / a⌋`.
  set S : ℕ := ∑ a ∈ Icc 1 y, N / a with hSdef
  have hD : DirichletDivisorProblem.divisorSummatory x = 2 * (S : ℝ) - (y : ℝ) * y := by
    unfold DirichletDivisorProblem.divisorSummatory
    rw [← hN, ← Nat.cast_sum, sum_card_divisors_eq N]
    have h := hyperbola N
    rw [← hy] at h
    have h' : ((∑ a ∈ Icc 1 N, N / a : ℕ) : ℝ) + (y : ℝ) * y = 2 * (S : ℝ) := by
      rw [hSdef]; exact_mod_cast h
    linarith
  -- `S = x H - E` with `0 ≤ E ≤ y`, where `H = ∑_{a ≤ y} 1 / a`.
  set H : ℝ := ∑ a ∈ Icc 1 y, (1 / (a : ℝ)) with hHdef
  have hterm : ∀ a ∈ Icc 1 y, ((N / a : ℕ) : ℝ) ≤ x * (1 / (a : ℝ)) ∧
      x * (1 / (a : ℝ)) - 1 < ((N / a : ℕ) : ℝ) := by
    intro a ha
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Icc.mp ha).1
    have hfl : ⌊x / a⌋₊ = N / a := Nat.floor_div_natCast x a
    rw [← hfl, mul_one_div]
    exact ⟨Nat.floor_le (by positivity), by linarith [Nat.lt_floor_add_one (x / a)]⟩
  have hS1 : (S : ℝ) ≤ x * H := by
    rw [hSdef, Nat.cast_sum, hHdef, mul_sum]
    exact sum_le_sum fun a ha => (hterm a ha).1
  have hS2 : x * H - y ≤ (S : ℝ) := by
    rw [hSdef, Nat.cast_sum, hHdef, mul_sum]
    have : ∑ a ∈ Icc 1 y, (x * (1 / (a : ℝ)) - 1) ≤ ∑ a ∈ Icc 1 y, ((N / a : ℕ) : ℝ) :=
      sum_le_sum fun a ha => (hterm a ha).2.le
    rw [sum_sub_distrib] at this
    simpa using this
  -- Euler-Mascheroni: `H - log (y+1) < γ < H - log y`.
  have hH : H = (harmonic y : ℝ) := by
    rw [hHdef, harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  have hg1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant y
  have hg2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' y
  unfold Real.eulerMascheroniSeq at hg1
  unfold Real.eulerMascheroniSeq' at hg2
  rw [if_neg (by omega)] at hg2
  rw [← hH] at hg1 hg2
  -- Logarithms.
  set u : ℝ := 1 / (y : ℝ) with hu
  have hyu : u * y = 1 := by rw [hu]; field_simp
  have hu0 : 0 ≤ u := by positivity
  have hlogy : Real.log ((y : ℝ) + 1) - Real.log y ≤ u := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < ((y : ℝ) + 1) / y by positivity)
    have e : ((y : ℝ) + 1) / y - 1 = 1 / y := by field_simp; ring
    rw [hu]; linarith
  have hL0 : Real.log y ≤ Real.log s := Real.log_le_log (by positivity) hys
  have hL1 : Real.log s ≤ Real.log ((y : ℝ) + 1) := Real.log_le_log hspos hsy.le
  have hlogx : Real.log x = 2 * Real.log s := by
    rw [← hss, Real.log_mul hspos.ne' hspos.ne']; ring
  -- Assemble `Δ = 2 x r - 2 x L - 2 E + (x - y²)`.
  set r := H - Real.log y - Real.eulerMascheroniConstant with hr
  set L := Real.log s - Real.log y with hL
  set E := x * H - S with hE
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r ≤ u := by rw [hr]; linarith
  have hL0' : 0 ≤ L := by rw [hL]; linarith
  have hL1' : L ≤ u := by rw [hL]; linarith
  have hxr : x * r ≤ x * u := mul_le_mul_of_nonneg_left hr1 hx0
  have hxL : x * L ≤ x * u := mul_le_mul_of_nonneg_left hL1' hx0
  have hxr0 : 0 ≤ x * r := mul_nonneg hx0 hr0
  have hxL0 : 0 ≤ x * L := mul_nonneg hx0 hL0'
  have hxu : x * u ≤ 2 * s := by
    have h2y : s ≤ 2 * y := by linarith
    have hsu : s * u ≤ 2 := by
      calc s * u ≤ (2 * y) * u := mul_le_mul_of_nonneg_right h2y hu0
        _ = 2 * (u * y) := by ring
        _ = 2 := by rw [hyu, mul_one]
    calc x * u = s * (s * u) := by rw [← hss]; ring
      _ ≤ s * 2 := mul_le_mul_of_nonneg_left hsu hs0
      _ = 2 * s := by ring
  have hid : DirichletDivisorProblem.divisorError x =
      2 * (x * r) - 2 * (x * L) - 2 * E + (x - (y : ℝ) * y) := by
    unfold DirichletDivisorProblem.divisorError
    rw [hD, hlogx, hr, hL, hE]
    ring
  have hE0 : 0 ≤ E := by rw [hE]; linarith
  have hE1 : E ≤ y := by rw [hE]; linarith
  have hx2 : x - (y : ℝ) * y ≤ 2 * y + 1 := by nlinarith [hxy1]
  have hx3 : 0 ≤ x - (y : ℝ) * y := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs0, hid, abs_le]
  constructor <;> linarith
