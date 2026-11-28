import OMAStatements.S_oeis_a189457

namespace OMA.S_oeis_a189457

/-! ### sqrt 2 -/

lemma r_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma r_pos : 0 < Real.sqrt 2 := by positivity

lemma one_lt_r : 1 < Real.sqrt 2 := by nlinarith [r_sq, r_pos]

lemma r_lt : Real.sqrt 2 < 3 / 2 := by nlinarith [r_sq, r_pos]

lemma div_t (y : ℝ) : y / (1 + Real.sqrt 2) = y * (Real.sqrt 2 - 1) := by
  rw [div_eq_iff (by positivity)]
  linear_combination (-y) * r_sq

lemma floor_lt (n : ℕ) (hn : 1 ≤ n) : (⌊(n : ℝ) * Real.sqrt 2⌋₊ : ℝ) < n * Real.sqrt 2 := by
  have hirr : Irrational ((n : ℝ) * Real.sqrt 2) :=
    irrational_sqrt_two.natCast_mul (by omega)
  have hle : (⌊(n : ℝ) * Real.sqrt 2⌋₊ : ℝ) ≤ n * Real.sqrt 2 := Nat.floor_le (by positivity)
  exact lt_of_le_of_ne hle (fun h => hirr.ne_nat _ h.symm)

/-! ### The two sides -/

lemma c_eq (n : ℕ) (hn : 1 ≤ n) :
    c n + 1 + ⌊(n : ℝ) * Real.sqrt 2⌋₊ = n + ⌊2 * ((n : ℝ) * Real.sqrt 2)⌋₊ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq := floor_lt n hn
  have hq1 : (n : ℝ) * Real.sqrt 2 < ⌊(n : ℝ) * Real.sqrt 2⌋₊ + 1 := Nat.lt_floor_add_one _
  have e1 : (n : ℝ) * 2 / (1 + Real.sqrt 2) = 2 * ((n : ℝ) * Real.sqrt 2) - ((2 * n : ℕ) : ℝ) := by
    rw [div_t]
    push_cast
    ring
  have e2 : (n : ℝ) * Real.sqrt 2 / (1 + Real.sqrt 2) = 2 * n - (n : ℝ) * Real.sqrt 2 := by
    rw [div_t]
    linear_combination (n : ℝ) * r_sq
  have f1 : ⌊2 * ((n : ℝ) * Real.sqrt 2) - ((2 * n : ℕ) : ℝ)⌋₊ + 2 * n =
      ⌊2 * ((n : ℝ) * Real.sqrt 2)⌋₊ := by
    have h0 : (0 : ℝ) ≤ 2 * ((n : ℝ) * Real.sqrt 2) - ((2 * n : ℕ) : ℝ) := by
      push_cast
      nlinarith [one_lt_r]
    have := Nat.floor_add_natCast h0 (2 * n)
    rw [sub_add_cancel] at this
    omega
  have hlt : ⌊(n : ℝ) * Real.sqrt 2⌋₊ < 2 * n := by
    have : (⌊(n : ℝ) * Real.sqrt 2⌋₊ : ℝ) < 2 * n := by nlinarith [r_lt]
    exact_mod_cast this
  obtain ⟨d, hd⟩ : ∃ d, 2 * n = d + 1 + ⌊(n : ℝ) * Real.sqrt 2⌋₊ :=
    ⟨2 * n - 1 - ⌊(n : ℝ) * Real.sqrt 2⌋₊, by omega⟩
  have hd' : (2 * n : ℝ) = d + 1 + ⌊(n : ℝ) * Real.sqrt 2⌋₊ := by exact_mod_cast hd
  have f2 : ⌊2 * (n : ℝ) - (n : ℝ) * Real.sqrt 2⌋₊ = d := by
    rw [Nat.floor_eq_iff (by linarith)]
    constructor <;> linarith
  unfold c
  rw [e1, e2, f2]
  omega

lemma tri_iff (n i : ℕ) (hn : 1 ≤ n) :
    i * (i + 1) / 2 < n ^ 2 ↔ i ≤ ⌊(n : ℝ) * Real.sqrt 2 - 1 / 2⌋₊ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : ((n : ℝ) * Real.sqrt 2) * ((n : ℝ) * Real.sqrt 2) = 2 * n ^ 2 := by
    linear_combination (n : ℝ) ^ 2 * r_sq
  have hxpos : 0 < (n : ℝ) * Real.sqrt 2 := by positivity
  rw [Nat.div_lt_iff_lt_mul (by norm_num), Nat.le_floor_iff (by nlinarith [one_lt_r])]
  constructor
  · intro h
    have h' : ((i * (i + 1) : ℕ) : ℝ) + 1 ≤ ((n ^ 2 * 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    by_contra hc
    rw [not_le] at hc
    nlinarith [hc]
  · intro h
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h' : ((i * (i + 1) : ℕ) : ℝ) < ((n ^ 2 * 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith [h]
    exact_mod_cast h'

lemma A186222_eq (n : ℕ) (hn : 1 ≤ n) :
    A186222 n = n + ⌊(n : ℝ) * Real.sqrt 2 - 1 / 2⌋₊ := by
  unfold A186222
  have hset : {i : ℕ | 1 ≤ i ∧ i * (i + 1) / 2 < n ^ 2} =
      ↑(Finset.Icc 1 ⌊(n : ℝ) * Real.sqrt 2 - 1 / 2⌋₊) := by
    ext i
    constructor
    · rintro ⟨h1, h2⟩
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨h1, (tri_iff n i hn).mp h2⟩)
    · intro h
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp h)
      exact ⟨h1, (tri_iff n i hn).mpr h2⟩
  rw [hset, Set.ncard_coe_finset, Nat.card_Icc]
  omega

lemma floor_id (x : ℝ) (hx : 1 ≤ x) : ⌊2 * x⌋₊ = ⌊x⌋₊ + 1 + ⌊x - 1 / 2⌋₊ := by
  have h0 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h1 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hq : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hq' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hq
  rcases lt_or_ge (x - ⌊x⌋₊) (1 / 2) with h | h
  · have a1 : ⌊2 * x⌋₊ = 2 * ⌊x⌋₊ := by
      rw [Nat.floor_eq_iff (by linarith)]
      push_cast
      constructor <;> linarith
    obtain ⟨d, hd⟩ : ∃ d, ⌊x⌋₊ = d + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
    have hd' : (⌊x⌋₊ : ℝ) = d + 1 := by exact_mod_cast hd
    have a2 : ⌊x - 1 / 2⌋₊ = d := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> linarith
    omega
  · have a1 : ⌊2 * x⌋₊ = 2 * ⌊x⌋₊ + 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      push_cast
      constructor <;> linarith
    have a2 : ⌊x - 1 / 2⌋₊ = ⌊x⌋₊ := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> linarith
    omega

theorem conjecture : ∀ n : ℕ, 1 ≤ n → c n = A186222 n := by
  intro n hn
  have hx : 1 ≤ (n : ℝ) * Real.sqrt 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [one_lt_r]
  have h1 := c_eq n hn
  have h2 := floor_id ((n : ℝ) * Real.sqrt 2) hx
  rw [A186222_eq n hn]
  omega

end OMA.S_oeis_a189457

theorem OMA.solution : type_of% @OMA.S_oeis_a189457.main :=
  OMA.S_oeis_a189457.conjecture
