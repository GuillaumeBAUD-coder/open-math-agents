import OMAStatements.S_mo_462095
import Mathlib

/-! Proof of MathOverflow 462095, following the accepted answer: the colouring
`n ↦ ⌊12 {n / √2}⌋` has no such repetition. Equal colours force the fractional parts of `a_i / √2`
and `a_{i+l} / √2` within `1/12`; the second-difference condition makes `a_{i+l} - a_i` grow by
`2l` per step, so some integer `m` has `(l - 1) |√2 l - m| < 1/6`; but `2l² - m²` is a nonzero
integer, which gives `|√2 l - m| > 1 / (3l)`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P462095

noncomputable abbrev s : ℝ := Real.sqrt 2
lemma s_pos : 0 < s := by positivity
lemma s_sq : s * s = 2 := Real.mul_self_sqrt (by norm_num)
lemma s_lt : s < 1.415 := by nlinarith [s_sq, s_pos]
lemma s_gt : 1.414 < s := by nlinarith [s_sq, s_pos]

/-- The colouring `n ↦ ⌊12 {n / √2}⌋`. -/
noncomputable def col (n : ℕ) : Fin 12 :=
  ⟨⌊12 * Int.fract ((n : ℝ) / s)⌋₊, by
    rw [Nat.floor_lt (by positivity)]
    have := Int.fract_lt_one ((n : ℝ) / s)
    push_cast; linarith⟩

lemma close_of_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : ⌊12 * u⌋₊ = ⌊12 * v⌋₊) : |u - v| < 1 / 12 := by
  have h1 := Nat.floor_le (show 0 ≤ 12 * u by positivity)
  have h2 := Nat.lt_floor_add_one (12 * u)
  have h3 := Nat.floor_le (show 0 ≤ 12 * v by positivity)
  have h4 := Nat.lt_floor_add_one (12 * v)
  rw [h] at h1 h2
  rw [abs_sub_lt_iff]; constructor <;> linarith

/-- The Diophantine core: for `l ≥ 2` and an integer `m` within `1/6` of `√2 l`,
`|√2 l - m| > 1 / (3 l)`. -/
lemma dioph (l : ℕ) (hl : 2 ≤ l) (m : ℤ) (h : |s * l - m| < 1 / 6) :
    1 / (3 * l) < |s * l - m| := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  rw [abs_lt] at h
  have hm : (0 : ℝ) < m := by nlinarith [s_gt]
  have hsum : s * l + m < 3 * l := by nlinarith [s_lt]
  have hsum0 : 0 < s * l + m := by nlinarith [s_pos]
  have hne : (m : ℤ) ^ 2 ≠ 2 * (l : ℤ) ^ 2 := by
    intro he
    have hq : ((m : ℝ) / l) ^ 2 = 2 := by
      have : (m : ℝ) ^ 2 = 2 * (l : ℝ) ^ 2 := by exact_mod_cast he
      field_simp; linarith
    have hpos : 0 < (m : ℝ) / l := by positivity
    have : (m : ℝ) / l = s := by
      rw [show s = Real.sqrt 2 from rfl, ← hq, Real.sqrt_sq hpos.le]
    exact irrational_sqrt_two (by
      refine ⟨(m : ℚ) / l, ?_⟩
      push_cast; exact this)
  have hint : (1 : ℝ) ≤ |(2 * (l : ℝ) ^ 2 - (m : ℝ) ^ 2)| := by
    have : (1 : ℤ) ≤ |2 * (l : ℤ) ^ 2 - m ^ 2| := by
      apply Int.one_le_abs; intro h0; apply hne; linarith
    exact_mod_cast this
  have hprod : (s * l - m) * (s * l + m) = 2 * (l : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
    nlinarith [s_sq]
  have key : 1 ≤ |s * l - m| * (s * l + m) := by
    rw [← abs_of_pos hsum0, ← abs_mul, hprod]; exact hint
  rw [div_lt_iff₀ (by positivity)]
  calc (1 : ℝ) ≤ |s * l - m| * (s * l + m) := key
    _ < |s * l - m| * (3 * l) := by
        apply mul_lt_mul_of_pos_left hsum
        have : |s * l - m| ≠ 0 := by
          intro h0; rw [h0] at key; linarith
        exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)

/-- Sequences with second difference `2`: `a j = a 0 + D j + j² - j`. -/
lemma closed (l : ℕ) (a : ℕ → ℕ)
    (hrec : ∀ i, i + 2 < 2 * l → a i + a (i + 2) = 2 * a (i + 1) + 2) :
    ∀ j, j < 2 * l → (a j : ℤ) = a 0 + ((a 1 : ℤ) - a 0) * j + (j : ℤ) * j - j := by
  have two : ∀ j, j + 1 < 2 * l →
      (a j : ℤ) = a 0 + ((a 1 : ℤ) - a 0) * j + (j : ℤ) * j - j ∧
      (a (j + 1) : ℤ) = a 0 + ((a 1 : ℤ) - a 0) * (j + 1 : ℕ) + ((j + 1 : ℕ) : ℤ) * (j + 1 : ℕ) - (j + 1 : ℕ) := by
    intro j
    induction j with
    | zero => intro _; constructor <;> push_cast <;> ring
    | succ k ih =>
      intro hk
      obtain ⟨h0, h1⟩ := ih (by omega)
      refine ⟨h1, ?_⟩
      have hr := hrec k (by omega)
      have hr' : (a k : ℤ) + a (k + 2) = 2 * a (k + 1) + 2 := by exact_mod_cast hr
      push_cast at h0 h1 ⊢
      linear_combination hr' - h0 + 2 * h1
  intro j hj
  rcases j with _ | j
  · push_cast; ring
  · exact (two j (by omega)).2

theorem no_rep (l : ℕ) (hl : 2 ≤ l) (a : ℕ → ℕ)
    (hrec : ∀ i, i + 2 < 2 * l → a i + a (i + 2) = 2 * a (i + 1) + 2)
    (hcol : ∀ i < l, col (a i) = col (a (i + l))) : False := by
  have hcl := closed l a hrec
  set F : ℕ → ℤ := fun n => ⌊(n : ℝ) / s⌋ with hF
  set e : ℕ → ℝ := fun i => Int.fract ((a (i + l) : ℝ) / s) - Int.fract ((a i : ℝ) / s) with he
  set K : ℕ → ℤ := fun i => (F (a (i + l)) - F (a i)) - (F (a l) - F (a 0)) with hK
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  -- each `e i` is small
  have he_small : ∀ i, i < l → |e i| < 1 / 12 := by
    intro i hi
    have h := congrArg Fin.val (hcol i hi)
    simp only [col] at h
    have := close_of_eq (Int.fract_nonneg _) (Int.fract_nonneg _) h
    simp only [he]; rw [abs_sub_comm]; exact this
  -- `e i - e 0 = i (√2 l) - K i`
  have hid : ∀ i, i < l → e i - e 0 = (i : ℝ) * (s * l) - K i := by
    intro i hi
    have hz : ((a (i + l) : ℤ) - a i) - ((a l : ℤ) - a 0) = 2 * i * l := by
      have h1 := hcl (i + l) (by omega)
      have h2 := hcl i (by omega)
      have h3 := hcl l (by omega)
      push_cast at h1 h2 h3
      rw [h1, h2, h3]; ring
    have hr : ((a (i + l) : ℝ) - a i) - ((a l : ℝ) - a 0) = 2 * i * l := by
      have := congrArg (Int.cast : ℤ → ℝ) hz; push_cast at this; exact this
    simp only [he, hK, hF, Int.fract, zero_add]
    push_cast
    have hs := s_pos
    have key : (2 * (i : ℝ) * l) / s = (i : ℝ) * (s * l) := by
      field_simp; nlinarith [s_sq]
    rw [← key, ← hr]
    field_simp
    ring
  -- consecutive differences
  have hstep : ∀ i, i + 1 < l → |s * l - ((K (i + 1) - K i : ℤ) : ℝ)| < 1 / 6 := by
    intro i hi
    have h1 := hid (i + 1) hi
    have h2 := hid i (by omega)
    have e1 := he_small (i + 1) hi
    have e2 := he_small i (by omega)
    have : s * l - ((K (i + 1) - K i : ℤ) : ℝ) = e (i + 1) - e i := by
      push_cast at h1 ⊢; linarith
    rw [this]
    calc |e (i + 1) - e i| ≤ |e (i + 1)| + |e i| := abs_sub _ _
      _ < 1 / 12 + 1 / 12 := by linarith
      _ = 1 / 6 := by norm_num
  have hK0 : K 0 = 0 := by simp [hK]
  set m : ℤ := K 1 - K 0 with hm
  have hm6 : |s * l - (m : ℝ)| < 1 / 6 := hstep 0 (by omega)
  have hKi : ∀ i, i < l → K i = i * m := by
    intro i
    induction i with
    | zero => intro _; simp [hK0]
    | succ k ih =>
      intro hk
      have h1 := hstep k hk
      have hd : |(((K (k + 1) - K k) - m : ℤ) : ℝ)| < 1 := by
        have : (((K (k + 1) - K k) - m : ℤ) : ℝ)
            = (s * l - (m : ℝ)) - (s * l - ((K (k + 1) - K k : ℤ) : ℝ)) := by push_cast; ring
        rw [this]
        calc _ ≤ |s * l - (m : ℝ)| + |s * l - ((K (k + 1) - K k : ℤ) : ℝ)| := abs_sub _ _
          _ < 1 / 6 + 1 / 6 := by linarith
          _ < 1 := by norm_num
      have hz : (K (k + 1) - K k) - m = 0 := by
        have : |(K (k + 1) - K k) - m| < 1 := by exact_mod_cast hd
        exact Int.abs_lt_one_iff.mp this
      rw [ih (by omega)] at hz
      push_cast; linarith
  -- telescoped bound at `i = l - 1`
  have hlast := hid (l - 1) (by omega)
  have hKl := hKi (l - 1) (by omega)
  have hel := he_small (l - 1) (by omega)
  have he0 := he_small 0 (by omega)
  have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hKl, hcast] at hlast
  push_cast at hlast
  rw [hcast] at hlast
  have hbig : ((l : ℝ) - 1) * |s * l - m| < 1 / 6 := by
    have : ((l : ℝ) - 1) * |s * l - m| = |e (l - 1) - e 0| := by
      rw [hlast, show ((l : ℝ) - 1) * (s * l) - ((l : ℝ) - 1) * m = ((l : ℝ) - 1) * (s * l - m) by ring,
        abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (l:ℝ) - 1 by linarith)]
    rw [this]
    calc |e (l - 1) - e 0| ≤ |e (l - 1)| + |e 0| := abs_sub _ _
      _ < 1 / 12 + 1 / 12 := by linarith
      _ = 1 / 6 := by norm_num
  have hlow := dioph l hl m hm6
  have : ((l : ℝ) - 1) * (1 / (3 * l)) ≥ 1 / 6 := by
    rw [ge_iff_le, div_le_iff₀ (by norm_num : (0:ℝ) < 6)]
    field_simp
    nlinarith
  have : ((l : ℝ) - 1) * (1 / (3 * l)) < ((l : ℝ) - 1) * |s * l - m| :=
    mul_lt_mul_of_pos_left hlow (by linarith)
  linarith

end OMA.P462095

theorem OMA.solution : type_of% @OMA.S_mo_462095.main := by
  intro h
  obtain ⟨l, hl, a, hrec, hcol⟩ := h 12 OMA.P462095.col
  exact OMA.P462095.no_rep l hl a hrec hcol

