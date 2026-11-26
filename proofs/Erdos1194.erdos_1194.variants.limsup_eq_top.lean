import FormalConjectures.ErdosProblems.«1194»

-- Problem: Erdős Problem 1194 — limsup eq top
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1194.lean:147 (declaration Erdos1194.erdos_1194.variants.limsup_eq_top)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- Cubes are eventually dominated by powers of two. -/
lemma OMA.cube_le_two_pow (J : ℕ) (hJ : 10 ≤ J) : J ^ 3 ≤ 2 ^ J := by
  induction J, hJ using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 10 * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right _ hn
    have h2 : 10 * n ≤ n * n := Nat.mul_le_mul_right _ hn
    have h3 : (n + 1) ^ 3 = n * (n * n) + 3 * (n * n) + 3 * n + 1 := by ring
    have h4 : n ^ 3 = n * (n * n) := by ring
    have h5 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

/-- The combinatorial core. Suppose every positive integer is a difference of two elements of `A`,
and the larger element of any pair is less than `K` times the difference. Then in each dyadic
window `(y, 2y]` the elements of `A` are spread out by more than `y / K`, so there are at most
`K + 1` of them; hence `A` has only about `K * J` elements up to `2 ^ J`, far too few for their
differences to cover every integer up to `2 ^ J / K`. -/
lemma OMA.core (A : Set ℕ) (K : ℕ)
    (hsurj : ∀ n, 0 < n → ∃ a ∈ A, ∃ b ∈ A, a = b + n)
    (hK : ∀ a ∈ A, ∀ b ∈ A, b < a → a < K * (a - b)) : False := by
  classical
  -- at most `K + 1` elements of `A` in each window `(y, 2y]`
  have hwin : ∀ y, 0 < y → ((Finset.Ioc y (2 * y)).filter (· ∈ A)).card ≤ K + 1 := by
    intro y hy
    have key : ∀ a b, a ∈ A → b ∈ A → y < b → b < a → K * a / y ≠ K * b / y := by
      intro a b ha hb hyb hba heq
      have h1 := hK a ha b hb hba
      have h2 : K * (a - b) = K * a - K * b := Nat.mul_sub K a b
      have h3 : K * b / y * y ≤ K * b := Nat.div_mul_le_self _ _
      have h4 : K * a < K * a / y * y + y := Nat.lt_div_mul_add hy
      rw [heq] at h4
      omega
    have hcard : ((Finset.Ioc y (2 * y)).filter (· ∈ A)).card ≤ (Finset.Icc K (2 * K)).card := by
      apply Finset.card_le_card_of_injOn (fun a => K * a / y)
      · intro a ha
        simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at ha
        simp only [Finset.coe_Icc, Set.mem_Icc]
        constructor
        · rw [Nat.le_div_iff_mul_le hy]
          exact Nat.mul_le_mul_left K ha.1.1.le
        · apply Nat.div_le_of_le_mul
          have h := Nat.mul_le_mul_left K ha.1.2
          have e : K * (2 * y) = y * (2 * K) := by ring
          omega
      · intro a ha b hb heq
        simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at ha hb
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact key b a hb.2 ha.2 ha.1.1 h heq.symm
        · exact key a b ha.2 hb.2 hb.1.1 h heq
    rw [Nat.card_Icc] at hcard
    omega
  -- hence at most `2 + j * (K + 1)` elements of `A` up to `2 ^ j`
  have hG : ∀ j : ℕ, ((Finset.range (2 ^ j + 1)).filter (· ∈ A)).card ≤ 2 + j * (K + 1) := by
    intro j
    induction j with
    | zero =>
      have h := Finset.card_filter_le (Finset.range (2 ^ 0 + 1)) (· ∈ A)
      simp only [pow_zero, Finset.card_range] at h
      simpa using h
    | succ j ih =>
      have hsub : (Finset.range (2 ^ (j + 1) + 1)).filter (· ∈ A) ⊆
          (Finset.range (2 ^ j + 1)).filter (· ∈ A) ∪
            (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter (· ∈ A) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc] at ha ⊢
        have e : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        by_cases h : a < 2 ^ j + 1
        · exact Or.inl ⟨h, ha.2⟩
        · exact Or.inr ⟨⟨by omega, by omega⟩, ha.2⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((Finset.range (2 ^ j + 1)).filter (· ∈ A))
        ((Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter (· ∈ A))
      have h3 := hwin (2 ^ j) (by positivity)
      have e : (j + 1) * (K + 1) = j * (K + 1) + (K + 1) := by ring
      omega
  -- every `n ≤ 2 ^ J` is a difference of two elements of `A` below `2 ^ (J + K)`
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * (K + 1) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = c * c + K + 12 := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = (Finset.range (2 ^ (J + K) + 1)).filter (· ∈ A) := ⟨_, rfl⟩
  have hcover : Finset.Icc 1 (2 ^ J) ⊆ (S ×ˢ S).image (fun p : ℕ × ℕ => p.1 - p.2) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨a, ha, b, hb, hab⟩ := hsurj n hn.1
    have h1 := hK a ha b hb (by omega)
    have h2 : a - b = n := by omega
    rw [h2] at h1
    have h3 : K * n ≤ K * 2 ^ J := Nat.mul_le_mul_left K hn.2
    have h4 : K * 2 ^ J < 2 ^ K * 2 ^ J :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by positivity)
    have h5 : 2 ^ (J + K) = 2 ^ K * 2 ^ J := by ring
    rw [Finset.mem_image]
    refine ⟨(a, b), ?_, h2⟩
    rw [hS]
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, ha⟩, ⟨by omega, hb⟩⟩
  have hcard : 2 ^ J ≤ S.card * S.card := by
    calc 2 ^ J = (Finset.Icc 1 (2 ^ J)).card := by simp
      _ ≤ ((S ×ˢ S).image (fun p : ℕ × ℕ => p.1 - p.2)).card := Finset.card_le_card hcover
      _ ≤ (S ×ˢ S).card := Finset.card_image_le
      _ = S.card * S.card := Finset.card_product S S
  -- but `A` has too few elements below `2 ^ (J + K)`
  have hSle : S.card ≤ 2 + (J + K) * (K + 1) := by
    rw [hS]
    exact hG (J + K)
  have hJK : J + K + 2 ≤ 2 * J := by omega
  have hbound : S.card ≤ c * J := by
    have h := Nat.mul_le_mul_right (K + 1) hJK
    have e1 : (J + K + 2) * (K + 1) = (J + K) * (K + 1) + 2 * (K + 1) := by ring
    have e2 : 2 * J * (K + 1) = c * J := by rw [hc]; ring
    omega
  have hpow := OMA.cube_le_two_pow J (by omega)
  have hsq : S.card * S.card ≤ (c * J) * (c * J) := Nat.mul_le_mul hbound hbound
  have hlt : (c * J) * (c * J) < J ^ 3 := by
    have hcc : c * c < J := by omega
    have hJpos : 0 < J * J := Nat.mul_pos (by omega) (by omega)
    calc (c * J) * (c * J) = (c * c) * (J * J) := by ring
      _ < J * (J * J) := Nat.mul_lt_mul_of_pos_right hcc hJpos
      _ = J ^ 3 := by ring
  omega

theorem OMA.solution : type_of% @Erdos1194.erdos_1194.variants.limsup_eq_top := by
  intro A hA C
  by_contra hcon
  unfold Erdos1194.HasLargeElement at hcon
  rw [Filter.not_frequently, Filter.eventually_atTop] at hcon
  obtain ⟨n0, hn0⟩ := hcon
  obtain ⟨K0, hK0⟩ := exists_nat_ge C
  choose! f hf using (fun d (hd : 0 < d) => hA.exists_isLargerElement hd)
  refine OMA.core A (K0 + 1 + ∑ d ∈ Finset.range n0, f d) ?_ ?_
  · intro n hn
    obtain ⟨ha, b, hb, hab⟩ := hf n hn
    exact ⟨f n, ha, b, hb, hab⟩
  · intro a ha b hb hba
    have hpos : 0 < a - b := by omega
    have hL : Erdos1194.IsLargerElement A (a - b) a := ⟨ha, b, hb, by omega⟩
    by_cases hlt : a - b < n0
    · have hfa : a = f (a - b) := Erdos1194.IsLargerElement.unique hA hpos hL (hf _ hpos)
      have hsum : f (a - b) ≤ ∑ d ∈ Finset.range n0, f d :=
        Finset.single_le_sum (f := f) (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hlt)
      have hmul : (K0 + 1 + ∑ d ∈ Finset.range n0, f d) * 1 ≤
          (K0 + 1 + ∑ d ∈ Finset.range n0, f d) * (a - b) := Nat.mul_le_mul_left _ hpos
      omega
    · have hge : n0 ≤ a - b := by omega
      have h1 := hn0 (a - b) hge
      have h2 : (a : ℝ) < C * ((a - b : ℕ) : ℝ) := by
        by_contra h
        exact h1 ⟨a, hL, not_lt.1 h⟩
      have h3 : C * ((a - b : ℕ) : ℝ) ≤ (K0 : ℝ) * ((a - b : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hK0 (Nat.cast_nonneg _)
      have h4 : (a : ℝ) < ((K0 * (a - b) : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        linarith
      have h5 : a < K0 * (a - b) := by exact_mod_cast h4
      have h6 : K0 * (a - b) ≤ (K0 + 1 + ∑ d ∈ Finset.range n0, f d) * (a - b) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
