import OMAStatements.S_oeis_a266516

namespace OMA.S_oeis_a266516


/-- Rule 29 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (29 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A266516(n): row `n`, cells `-n..n` (leftmost first), read as a binary number. -/
def ca (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0


/-! ## A finite certificate: rows `0..2` on the window `[-3, 3]` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => rule (bg t) (bg t) (bg t)

lemma light_cone (t : ℕ) : ∀ i : ℤ, ((t : ℤ) < i ∨ (t : ℤ) < -i) → cstate t i = bg t := by
  induction t with
  | zero => intro i hi; simp only [cstate, bg, decide_eq_false_iff_not]; omega
  | succ t ih =>
    intro i hi
    push_cast at hi
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = rule (bg t) (bg t) (bg t)
    rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]

def W : ℕ := 3

/-- A row: the background bit and the cells `-W..W` as a bitset (bit `i + W` is cell `i`). -/
def decode (s : Bool × ℕ) (i : ℤ) : Bool :=
  if -(W : ℤ) ≤ i ∧ i ≤ W then s.2.testBit (i + W).toNat else s.1

def stepOK (s s' : Bool × ℕ) : Bool :=
  (s'.1 == rule s.1 s.1 s.1) && (List.range (2 * W + 1)).all fun j =>
    decode s' ((j : ℤ) - W) ==
      rule (decode s ((j : ℤ) - W - 1)) (decode s ((j : ℤ) - W)) (decode s ((j : ℤ) - W + 1))

def initOK (s : Bool × ℕ) : Bool :=
  (s.1 == false) && (List.range (2 * W + 1)).all fun j =>
    decode s ((j : ℤ) - W) == decide ((j : ℤ) - W = 0)

lemma in_window (i : ℤ) (h : -(W : ℤ) ≤ i ∧ i ≤ W) : ∃ j < 2 * W + 1, i = (j : ℤ) - W :=
  ⟨(i + W).toNat, by omega, by omega⟩

lemma init_ok (s : Bool × ℕ) (h : initOK s = true) : ∀ i, cstate 0 i = decode s i := by
  simp only [initOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hbg, hcells⟩ := h
  intro i
  by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
  · obtain ⟨j, hj, rfl⟩ := in_window i hw
    rw [hcells j hj]
    rfl
  · unfold decode
    rw [if_neg hw, hbg]
    show decide (i = 0) = false
    simp only [decide_eq_false_iff_not]
    omega

lemma step_ok (t : ℕ) (s s' : Bool × ℕ) (ht : t + 1 ≤ W) (hs : ∀ i, cstate t i = decode s i)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ i, cstate (t + 1) i = decode s' i := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro i
  by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
  · obtain ⟨j, hj, rfl⟩ := in_window i hw
    rw [hcells j hj]
    show rule (cstate t ((j : ℤ) - W - 1)) (cstate t ((j : ℤ) - W)) (cstate t ((j : ℤ) - W + 1)) = _
    rw [hs, hs, hs]
  · rw [light_cone (t + 1) i (by push_cast; omega)]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The rows `0..2`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 8),
    (true, 123),
    (false, 8)]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × ℕ) : Bool := (decode s (-(W : ℤ)) == s.1) && (decode s (W : ℤ) == s.1)

lemma step_border (t : ℕ) (s s' : Bool × ℕ) (hs : ∀ i, cstate t i = decode s i)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ i, cstate (t + 1) i = decode s' i := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  simp only [borderOK, Bool.and_eq_true, beq_iff_eq] at hbd
  obtain ⟨hbg, hcells⟩ := hok
  intro i
  by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
  · obtain ⟨j, hj, rfl⟩ := in_window i hw
    rw [hcells j hj]
    show rule (cstate t ((j : ℤ) - W - 1)) (cstate t ((j : ℤ) - W)) (cstate t ((j : ℤ) - W + 1)) = _
    rw [hs, hs, hs]
  · have hout : ∀ k : ℤ, (k = i - 1 ∨ k = i ∨ k = i + 1) → decode s k = s.1 := by
      intro k hk
      by_cases hkw : -(W : ℤ) ≤ k ∧ k ≤ W
      · have hk2 : k = -(W : ℤ) ∨ k = (W : ℤ) := by omega
        rcases hk2 with rfl | rfl
        · exact hbd.1
        · exact hbd.2
      · unfold decode; rw [if_neg hkw]
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = decode s' i
    rw [hs, hs, hs, hout _ (Or.inl rfl), hout _ (Or.inr (Or.inl rfl)), hout _ (Or.inr (Or.inr rfl))]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 2, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 2, borderOK (stages.getD (0 + r) default) = true) ∧
    stages.getD 2 default = stages.getD 0 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 2) :
    (stages.getD t default).1 = bg t ∧ ∀ i, cstate t i = decode (stages.getD t default) i := by
  induction t with
  | zero =>
    have h := stages_ok.1
    refine ⟨?_, init_ok _ h⟩
    simp only [initOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  | succ t ih =>
    obtain ⟨hb, hs⟩ := ih (by omega)
    have hok := stages_ok.2.1 t (by omega)
    refine ⟨?_, step_ok t _ _ (by unfold W; omega) hs hb hok⟩
    simp only [stepOK, Bool.and_eq_true, beq_iff_eq] at hok
    rw [hok.1, hb]
    rfl

lemma periodic_all (m : ℕ) :
    ∀ i, cstate (0 + m) i = decode (stages.getD (0 + m % 2) default) i := by
  induction m with
  | zero => simpa using (certified 0 (by norm_num)).2
  | succ m ih =>
    have hr : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 2) hr
    have hok := stages_ok.2.1 (0 + m % 2) (by omega)
    rcases (by omega : m % 2 + 1 < 2 ∨ m % 2 + 1 = 2) with h | h
    · rw [show (m + 1) % 2 = m % 2 + 1 by omega]
      exact step_border (0 + m) _ _ ih hb hok
    · rw [show (m + 1) % 2 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 2 = 0 + m % 2 + 1 by omega]
      exact step_border (0 + m) _ _ ih hb hok

/-- The row shown at time `t`. -/
def stageOf (t : ℕ) : Bool × ℕ :=
  if t < 0 then stages.getD t default else stages.getD (0 + (t - 0) % 2) default

def sim (t : ℕ) : ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : cstate t = sim t := by
  funext i
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 i
  · obtain ⟨m, rfl⟩ : ∃ m, t = 0 + m := ⟨t - 0, by omega⟩
    rw [periodic_all m i, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 0 ≤ t) : cstate (t + 2) = cstate t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 2 - 0) % 2 = (t - 0) % 2 by omega]

/-- The background bit shown at time `t ≥ 0`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (0 + (t - 0) % 2) default).1

lemma outside (t : ℕ) (ht : 0 ≤ t) (i : ℤ) (hi : ¬ (-(W : ℤ) ≤ i ∧ i ≤ W)) :
    cstate t i = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hi, if_neg (show ¬ (t < 0) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if sim n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..21); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 21, ca n = ([1, 3, 4, 111, 16, 1983, 64, 32511, 256, 523263, 1024, 8384511, 4096, 134201343, 16384, 2147418111, 65536, 34359476223, 262144, 549754765311, 1048576, 8796088827903] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 3 := vals 1 (by norm_num)
lemma v2 : ca 2 = 4 := vals 2 (by norm_num)
lemma v3 : ca 3 = 111 := vals 3 (by norm_num)
lemma v4 : ca 4 = 16 := vals 4 (by norm_num)
lemma v5 : ca 5 = 1983 := vals 5 (by norm_num)
lemma v6 : ca 6 = 64 := vals 6 (by norm_num)
lemma v7 : ca 7 = 32511 := vals 7 (by norm_num)
lemma v8 : ca 8 = 256 := vals 8 (by norm_num)
lemma v9 : ca 9 = 523263 := vals 9 (by norm_num)
lemma v10 : ca 10 = 1024 := vals 10 (by norm_num)
lemma v11 : ca 11 = 8384511 := vals 11 (by norm_num)
lemma v12 : ca 12 = 4096 := vals 12 (by norm_num)
lemma v13 : ca 13 = 134201343 := vals 13 (by norm_num)
lemma v14 : ca 14 = 16384 := vals 14 (by norm_num)
lemma v15 : ca 15 = 2147418111 := vals 15 (by norm_num)
lemma v16 : ca 16 = 65536 := vals 16 (by norm_num)
lemma v17 : ca 17 = 34359476223 := vals 17 (by norm_num)
lemma v18 : ca 18 = 262144 := vals 18 (by norm_num)
lemma v19 : ca 19 = 549754765311 := vals 19 (by norm_num)
lemma v20 : ca 20 = 1048576 := vals 20 (by norm_num)
lemma v21 : ca 21 = 8796088827903 := vals 21 (by norm_num)

lemma rel (n : ℕ) (hn : 3 ≤ n) :
    ca (n + 2) = (if bgOf n then ∑ k ∈ Finset.range 2, 2 ^ (2 * n + (2 * 2 - k)) else 0) +
      2 ^ 2 * ca n + (if bgOf n then ∑ j ∈ Finset.range 2, 2 ^ (2 - 1 - j) else 0) := by
  unfold ca
  rw [show 2 * (n + 2) + 1 = 2 + (2 * n + 1) + 2 by ring, Finset.sum_range_add,
    Finset.sum_range_add, period n (by omega), Finset.mul_sum]
  congr 1
  congr 1
  · have h : ∀ k ∈ Finset.range 2, (if cstate n ((k : ℤ) - ((n + 2 : ℕ) : ℤ)) then
        2 ^ (2 * (n + 2) - k) else 0) = if bgOf n then 2 ^ (2 * n + (2 * 2 - k)) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [outside n (by omega) _ (by unfold W; push_cast; omega),
        show 2 * (n + 2) - k = 2 * n + (2 * 2 - k) by omega]
    rw [Finset.sum_congr rfl h]
    cases bgOf n <;> simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [show (((2 + k : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = (k : ℤ) - n by push_cast; ring]
    split_ifs
    · rw [← pow_add]; congr 1; omega
    · simp
  · have h : ∀ j ∈ Finset.range 2, (if cstate n ((((2 + (2 * n + 1) + j) : ℕ) : ℤ) -
        ((n + 2 : ℕ) : ℤ)) then 2 ^ (2 * (n + 2) - (2 + (2 * n + 1) + j)) else 0) =
        if bgOf n then 2 ^ (2 - 1 - j) else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [outside n (by omega) _ (by unfold W; push_cast; omega),
        show 2 * (n + 2) - (2 + (2 * n + 1) + j) = 2 - 1 - j by omega]
    rw [Finset.sum_congr rfl h]
    cases bgOf n <;> simp


lemma cf0 (m : ℕ) : (2 : ℚ) ^ 4 * (((2 : ℚ) - 1) * (ca (4 + 2 * m) : ℚ) -
    0 * (2 : ℚ) ^ (2 * (4 + 2 * m) + 1) + 0) = (16 : ℚ) * (2 : ℚ) ^ (4 + 2 * m) := by
  have hb : ∀ m, bgOf (4 + 2 * m) = false := by
    intro m
    unfold bgOf
    rw [show (4 + 2 * m - 0) % 2 = 0 by omega]
    rfl
  induction m with
  | zero =>
    rw [show 4 + 2 * 0 = 4 by ring, v4]
    norm_num
  | succ m ih =>
    rw [show 4 + 2 * (m + 1) = (4 + 2 * m) + 2 by ring, rel _ (by omega), hb m, if_neg (by decide), if_neg (by decide)]
    push_cast
    try simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    linear_combination (2 : ℚ) ^ 2 * ih

lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 2 = 0) :
    (2 : ℚ) ^ 4 * (((2 : ℚ) - 1) * (ca n : ℚ) - 0 * (2 : ℚ) ^ (2 * n + 1) + 0) =
      (16 : ℚ) * (2 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + 2 * m := ⟨(n - 4) / 2, by omega⟩
  exact cf0 m


lemma cf1 (m : ℕ) : (2 : ℚ) ^ 3 * (((2 : ℚ) - 1) * (ca (3 + 2 * m) : ℚ) -
    1 * (2 : ℚ) ^ (2 * (3 + 2 * m) + 1) + 1) = (-16 : ℚ) * (2 : ℚ) ^ (3 + 2 * m) := by
  have hb : ∀ m, bgOf (3 + 2 * m) = true := by
    intro m
    unfold bgOf
    rw [show (3 + 2 * m - 0) % 2 = 1 by omega]
    rfl
  induction m with
  | zero =>
    rw [show 3 + 2 * 0 = 3 by ring, v3]
    norm_num
  | succ m ih =>
    rw [show 3 + 2 * (m + 1) = (3 + 2 * m) + 2 by ring, rel _ (by omega), hb m, if_pos rfl, if_pos rfl]
    push_cast
    try simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    linear_combination (2 : ℚ) ^ 2 * ih

lemma cfn1 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 2 = 1) :
    (2 : ℚ) ^ 3 * (((2 : ℚ) - 1) * (ca n : ℚ) - 1 * (2 : ℚ) ^ (2 * n + 1) + 1) =
      (-16 : ℚ) * (2 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + 2 * m := ⟨(n - 3) / 2, by omega⟩
  exact cf1 m


/-- a(n) = 21*a(n-2) - 84*a(n-4) + 64*a(n-6) for n>5 -/
theorem recurrence0 (n : ℕ) (hn : 6 ≤ n) : (ca n : ℤ) = ((((21 : ℤ) * (ca (n - 2) : ℤ)) - ((84 : ℤ) * (ca (n - 4) : ℤ))) + ((64 : ℤ) * (ca (n - 6) : ℤ))) := by
  rcases Nat.lt_or_ge n 9 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at *
  · suffices hq : (ca n : ℚ) = ((((21 : ℚ) * (ca (n - 2) : ℚ)) - ((84 : ℚ) * (ca (n - 4) : ℚ))) + ((64 : ℚ) * (ca (n - 6) : ℚ))) by exact_mod_cast hq
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 10 + 2 * q := ⟨(n - 10) / 2, by omega⟩
      have c0 := cfn0 (10 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 2 = 8 + 2 * q by omega]
      have c2 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 4 = 6 + 2 * q by omega]
      have c4 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 6 = 4 + 2 * q by omega]
      have c6 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c0 + (-((21 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c2 + (-((-84 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c4 + (-((64 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 9 + 2 * q := ⟨(n - 9) / 2, by omega⟩
      have c0 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 2 = 7 + 2 * q by omega]
      have c2 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 4 = 5 + 2 * q by omega]
      have c4 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 6 = 3 + 2 * q by omega]
      have c6 := cfn1 (3 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 3 * ((2 : ℚ) - 1))) * c0 + (-((21 : ℚ)) / ((2 : ℚ) ^ 3 * ((2 : ℚ) - 1))) * c2 + (-((-84 : ℚ)) / ((2 : ℚ) ^ 3 * ((2 : ℚ) - 1))) * c4 + (-((64 : ℚ)) / ((2 : ℚ) ^ 3 * ((2 : ℚ) - 1))) * c6


/-- a(n) = 2*(4^n - 2^n) - 1 for odd n -/
theorem closed1 (n : ℕ) (hp : n % 2 = 1) : (ca n : ℚ) = (((2 : ℚ) * (((4 : ℚ) ^ n) - ((2 : ℚ) ^ n))) - (1 : ℚ)) := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3] at *
  · rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · omega
    · obtain ⟨q, rfl⟩ : ∃ q, n = 3 + 2 * q := ⟨(n - 3) / 2, by omega⟩
      have c0 := cfn1 (3 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 ⊢
      try rw [show (4 : ℚ) = 2 ^ 2 by norm_num] at c0
      try rw [show (4 : ℚ) = 2 ^ 2 by norm_num]
      try simp only [mul_pow, ← pow_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 3 * ((2 : ℚ) - 1))) * c0


/-- a(n) = 2^n for even n -/
theorem closed2 (n : ℕ) (hp : n % 2 = 0) : (ca n : ℚ) = ((2 : ℚ) ^ n) := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3] at *
  · rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 4 + 2 * q := ⟨(n - 4) / 2, by omega⟩
      have c0 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c0
    · omega


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 6 ≤ n → (ca n : ℤ) = ((((21 : ℤ) * (ca (n - 2) : ℤ)) - ((84 : ℤ) * (ca (n - 4) : ℤ))) + ((64 : ℤ) * (ca (n - 6) : ℤ)))) ∧
    (∀ n : ℕ, n % 2 = 1 → (ca n : ℚ) = (((2 : ℚ) * (((4 : ℚ) ^ n) - ((2 : ℚ) ^ n))) - (1 : ℚ))) ∧
    (∀ n : ℕ, n % 2 = 0 → (ca n : ℚ) = ((2 : ℚ) ^ n)) :=
  ⟨recurrence0, closed1, closed2⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries





theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 29 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 29 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 29 (state 29 t) i
    rw [ih, rule_eq]
    rfl

theorem row_eq (n : ℕ) :
    rowValue (state 29 n) n = ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0 := by
  rw [rowValue, ← cstate_eq]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show ((n : ℤ) - ((2 * n + 1 - 1 - k : ℕ) : ℤ)) = (k : ℤ) - n by omega,
    show 2 * n + 1 - 1 - k = 2 * n - k by omega]
  cases cstate n ((k : ℤ) - n) <;> simp

theorem a_eq_ca : a = ca := by
  funext n
  rw [a, ca, row_eq]

theorem controls : ∀ n ≤ 21, a n = ([1, 3, 4, 111, 16, 1983, 64, 32511, 256, 523263, 1024, 8384511, 4096, 134201343, 16384, 2147418111, 65536, 34359476223, 262144, 549754765311, 1048576, 8796088827903] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, Odd n → (a n : ℚ) = 2 * (4 ^ n - 2 ^ n) - 1) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 2 ^ n) := by
  rw [a_eq_ca]
  exact ⟨fun n hp => (closed1 n (Nat.odd_iff.mp hp)).trans (by ring),
    fun n hp => (closed2 n (Nat.even_iff.mp hp)).trans (by ring)⟩

end OMA.S_oeis_a266516

theorem OMA.solution : type_of% @OMA.S_oeis_a266516.main :=
  OMA.S_oeis_a266516.conj
