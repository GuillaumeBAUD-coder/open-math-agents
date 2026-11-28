import OMAStatements.S_oeis_a267211

-- Problem: A267211: number of ON cells after n steps of the Rule 109 elementary cellular automaton.
-- Upstream: statements/oeis-a267211.lean (declaration OMA.S_oeis_a267211.main)
-- Proof: an explicit description f of the automaton (background, edges, a 12-periodic interior
-- pattern, a 3-periodic centre column) is checked against the rule; the count then satisfies
-- W (t + 12) = W t + 14 for t >= 2, which gives the recurrence and the generating function.

namespace OMA.A267211Proof

open OMA.S_oeis_a267211

/-- The 12-periodic pattern of the interior. -/
def Lf (x : ℤ) : Bool :=
  (x % 12 == 2) || (x % 12 == 4) || (x % 12 == 6) || (x % 12 == 7) || (x % 12 == 8) ||
    (x % 12 == 9) || (x % 12 == 10)

lemma Lf_mod (x : ℤ) : Lf x = Lf (x % 12) := by
  simp [Lf, Int.emod_emod_of_dvd]

lemma Lf_congr {x y : ℤ} (h : x % 12 = y % 12) : Lf x = Lf y := by
  rw [Lf_mod x, Lf_mod y, h]

/-- Explicit description of the automaton. -/
def f (t : ℕ) (i : ℤ) : Bool :=
  if (t : ℤ) < i ∨ i < -(t : ℤ) then decide (t % 2 = 1)
  else if i = t ∨ i = -(t : ℤ) then decide (t % 2 = 0)
  else if i = (t : ℤ) - 1 ∨ i = -((t : ℤ) - 1) then true
  else if i = 0 then decide (t % 3 ≠ 0)
  else if i < 0 then Lf (4 * t + i) else Lf (4 * t - i)

lemma f_out {t : ℕ} {i : ℤ} (h : (t : ℤ) < i ∨ i < -(t : ℤ)) : f t i = decide (t % 2 = 1) := by
  unfold f; rw [if_pos h]

lemma f_edge {t : ℕ} {i : ℤ} (h : i = t ∨ i = -(t : ℤ)) : f t i = decide (t % 2 = 0) := by
  unfold f; rw [if_neg (by omega), if_pos h]

lemma f_off1 {t : ℕ} {i : ℤ} (ht : 1 ≤ t) (h : i = (t : ℤ) - 1 ∨ i = -((t : ℤ) - 1)) :
    f t i = true := by
  unfold f; rw [if_neg (by omega), if_neg (by omega), if_pos h]

lemma f_center {t : ℕ} (ht : 2 ≤ t) : f t 0 = decide (t % 3 ≠ 0) := by
  unfold f; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

lemma f_left {t : ℕ} {i : ℤ} (h1 : -(t : ℤ) + 2 ≤ i) (h2 : i < 0) : f t i = Lf (4 * t + i) := by
  unfold f; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos h2]

lemma f_right {t : ℕ} {i : ℤ} (h1 : 0 < i) (h2 : i ≤ (t : ℤ) - 2) : f t i = Lf (4 * t - i) := by
  unfold f; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

lemma f_symm (t : ℕ) (i : ℤ) : f t (-i) = f t i := by
  unfold f
  by_cases h1 : (t : ℤ) < i ∨ i < -(t : ℤ)
  · rw [if_pos (by omega), if_pos h1]
  rw [if_neg (by omega), if_neg h1]
  by_cases h2 : i = t ∨ i = -(t : ℤ)
  · rw [if_pos (by omega), if_pos h2]
  rw [if_neg (by omega), if_neg h2]
  by_cases h3 : i = (t : ℤ) - 1 ∨ i = -((t : ℤ) - 1)
  · rw [if_pos (by omega), if_pos h3]
  rw [if_neg (by omega), if_neg h3]
  by_cases h4 : i = 0
  · subst h4; try simp
  rw [if_neg (by omega), if_neg h4]
  by_cases h5 : i < 0
  · rw [if_neg (by omega), if_pos h5]; congr 1; try ring
  · rw [if_pos (by omega), if_neg h5]; congr 1; try ring

lemma rule_symm (l c r : Bool) : ruleOut 109 l c r = ruleOut 109 r c l := by
  cases l <;> cases c <;> cases r <;> decide

lemma rule_bg (t : ℕ) :
    ruleOut 109 (decide (t % 2 = 1)) (decide (t % 2 = 1)) (decide (t % 2 = 1))
      = decide ((t + 1) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;>
    simp [h, Nat.succ_mod_two_eq_one_iff] <;> decide

/-- Step for nonpositive positions, t ≥ 8. -/
lemma step_neg (t : ℕ) (ht : 8 ≤ t) (i : ℤ) (hi : i ≤ 0) :
    ruleOut 109 (f t (i - 1)) (f t i) (f t (i + 1)) = f (t + 1) i := by
  have ht' : (8 : ℤ) ≤ t := by exact_mod_cast ht
  rcases (show i ≤ -(t : ℤ) - 2 ∨ i = -(t : ℤ) - 1 ∨ i = -(t : ℤ) ∨ i = -(t : ℤ) + 1 ∨
      i = -(t : ℤ) + 2 ∨ (-(t : ℤ) + 3 ≤ i ∧ i ≤ -2) ∨ i = -1 ∨ i = 0 by omega) with
    h | h | h | h | h | h | h | h
  · rw [f_out (by omega), f_out (by omega), f_out (by omega), f_out (by push_cast; omega)]
    exact rule_bg t
  · rw [f_out (by omega), f_out (by omega), f_edge (by omega), f_edge (by push_cast; omega)]
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2 <;>
      simp [h2, Nat.succ_mod_two_eq_zero_iff] <;> decide
  · rw [f_out (by omega), f_edge (by omega), f_off1 (by omega) (by omega),
      f_off1 (by omega) (by push_cast; omega)]
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2 <;> simp [h2] <;> decide
  · rw [f_edge (by omega), f_off1 (by omega) (by omega), f_left (by omega) (by omega),
      f_left (by push_cast; omega) (by omega)]
    have h4 : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [Lf_mod, Lf_mod (4 * ((t + 1 : ℕ) : ℤ) + i)]
    subst h
    have e2 : t % 2 = (t % 4) % 2 := by omega
    rw [e2]
    interval_cases hm : t % 4
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 1 + 1)) % 12 = 2 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 1)) % 12 = 5 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 1 + 1)) % 12 = 5 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 1)) % 12 = 8 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 1 + 1)) % 12 = 8 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 1)) % 12 = 11 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 1 + 1)) % 12 = 11 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 1)) % 12 = 2 by push_cast; omega]; decide
  · rw [f_off1 (by omega) (by omega), f_left (by omega) (by omega), f_left (by omega) (by omega),
      f_left (by push_cast; omega) (by omega)]
    rw [Lf_mod, Lf_mod (4 * (t : ℤ) + (i + 1)), Lf_mod (4 * ((t + 1 : ℕ) : ℤ) + i)]
    subst h
    have h4 : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : t % 4
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 2)) % 12 = 2 by omega,
        show (4 * (t : ℤ) + (-(t : ℤ) + 2 + 1)) % 12 = 3 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 2)) % 12 = 6 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 2)) % 12 = 5 by omega,
        show (4 * (t : ℤ) + (-(t : ℤ) + 2 + 1)) % 12 = 6 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 2)) % 12 = 9 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 2)) % 12 = 8 by omega,
        show (4 * (t : ℤ) + (-(t : ℤ) + 2 + 1)) % 12 = 9 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 2)) % 12 = 0 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-(t : ℤ) + 2)) % 12 = 11 by omega,
        show (4 * (t : ℤ) + (-(t : ℤ) + 2 + 1)) % 12 = 0 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + (-(t : ℤ) + 2)) % 12 = 3 by push_cast; omega]; decide
  · rw [f_left (by omega) (by omega), f_left (by omega) (by omega), f_left (by omega) (by omega),
      f_left (by push_cast; omega) (by omega)]
    set x := 4 * (t : ℤ) + i with hx
    rw [show 4 * (t : ℤ) + (i - 1) = x - 1 by omega, show 4 * (t : ℤ) + (i + 1) = x + 1 by omega,
      show 4 * ((t + 1 : ℕ) : ℤ) + i = x + 4 by push_cast; omega]
    rw [Lf_mod (x - 1), Lf_mod x, Lf_mod (x + 1), Lf_mod (x + 4)]
    have : x % 12 = 0 ∨ x % 12 = 1 ∨ x % 12 = 2 ∨ x % 12 = 3 ∨ x % 12 = 4 ∨ x % 12 = 5 ∨
        x % 12 = 6 ∨ x % 12 = 7 ∨ x % 12 = 8 ∨ x % 12 = 9 ∨ x % 12 = 10 ∨ x % 12 = 11 := by omega
    rcases this with h | h | h | h | h | h | h | h | h | h | h | h <;>
    · rw [show (x - 1) % 12 = (x % 12 + 11) % 12 by omega, show (x + 1) % 12 = (x % 12 + 1) % 12 by omega,
        show (x + 4) % 12 = (x % 12 + 4) % 12 by omega, h]
      decide
  · subst h
    rw [show (-1 : ℤ) + 1 = 0 by norm_num]
    rw [f_left (by omega) (by omega), f_left (by omega) (by omega), f_center (by omega),
      f_left (by push_cast; omega) (by omega)]
    rw [Lf_mod, Lf_mod (4 * (t : ℤ) + -1), Lf_mod (4 * ((t + 1 : ℕ) : ℤ) + -1)]
    have h3 : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : t % 3
    · rw [show (4 * (t : ℤ) + (-1 - 1)) % 12 = 10 by omega,
        show (4 * (t : ℤ) + -1) % 12 = 11 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + -1) % 12 = 3 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-1 - 1)) % 12 = 2 by omega,
        show (4 * (t : ℤ) + -1) % 12 = 3 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + -1) % 12 = 7 by push_cast; omega]; decide
    · rw [show (4 * (t : ℤ) + (-1 - 1)) % 12 = 6 by omega,
        show (4 * (t : ℤ) + -1) % 12 = 7 by omega,
        show (4 * ((t + 1 : ℕ) : ℤ) + -1) % 12 = 11 by push_cast; omega]; decide
  · subst h
    rw [f_left (by omega) (by omega), f_center (by omega), f_right (by omega) (by omega),
      f_center (by omega)]
    rw [Lf_mod, Lf_mod (4 * (t : ℤ) - (0 + 1))]
    have h3 : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have e : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
    rw [e]
    interval_cases hm : t % 3
    · rw [show (4 * (t : ℤ) + (0 - 1)) % 12 = 11 by omega,
        show (4 * (t : ℤ) - (0 + 1)) % 12 = 11 by omega]; decide
    · rw [show (4 * (t : ℤ) + (0 - 1)) % 12 = 3 by omega,
        show (4 * (t : ℤ) - (0 + 1)) % 12 = 3 by omega]; decide
    · rw [show (4 * (t : ℤ) + (0 - 1)) % 12 = 7 by omega,
        show (4 * (t : ℤ) - (0 + 1)) % 12 = 7 by omega]; decide


lemma step (t : ℕ) (i : ℤ) :
    ruleOut 109 (f t (i - 1)) (f t i) (f t (i + 1)) = f (t + 1) i := by
  by_cases ht : 8 ≤ t
  · by_cases hi : i ≤ 0
    · exact step_neg t ht i hi
    · have h := step_neg t ht (-i) (by omega)
      rw [← f_symm t (i - 1), ← f_symm t i, ← f_symm t (i + 1), ← f_symm (t + 1) i, ← h,
        rule_symm]
      congr 2 <;> ring_nf
  · by_cases hb : (t : ℤ) + 2 ≤ i ∨ i ≤ -(t : ℤ) - 2
    · rw [f_out (by omega), f_out (by omega), f_out (by omega), f_out (by push_cast; omega)]
      exact rule_bg t
    · have hi1 : -(t : ℤ) - 1 ≤ i := by omega
      have hi2 : i ≤ (t : ℤ) + 1 := by omega
      interval_cases t <;> interval_cases i <;> decide

lemma cell_eq (t : ℕ) (i : ℤ) : cell 109 t i = f t i := by
  induction t generalizing i with
  | zero =>
    by_cases h : i = 0
    · subst h; decide
    · rw [f_out (by push_cast; omega)]
      simp [cell, h]
  | succ t ih =>
    show ruleOut 109 (cell 109 t (i - 1)) (cell 109 t i) (cell 109 t (i + 1)) = f (t + 1) i
    rw [ih, ih, ih, step]


lemma onCount_eq (t : ℕ) :
    onCount 109 t = ∑ j ∈ Finset.range (2 * t + 1), if f t ((j : ℤ) - t) then 1 else 0 := by
  unfold onCount
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cell_eq]

/-- Half count. -/
def P (t : ℕ) : ℕ := ∑ k ∈ Finset.range t, if f t ((k : ℤ) + 1) then 1 else 0

lemma count_split (t : ℕ) : onCount 109 t = 2 * P t + (if f t 0 then 1 else 0) := by
  rw [onCount_eq, show 2 * t + 1 = t + (t + 1) by ring, Finset.sum_range_add,
    Finset.sum_range_succ']
  have h1 : ∑ j ∈ Finset.range t, (if f t ((j : ℤ) - t) then 1 else 0) = P t := by
    rw [← Finset.sum_range_reflect]
    unfold P
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [show (((t - 1 - j : ℕ) : ℤ) - t) = -((j : ℤ) + 1) by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring, f_symm]
  have h2 : ∑ k ∈ Finset.range t, (if f t (((t + (k + 1) : ℕ) : ℤ) - t) then 1 else 0) = P t := by
    unfold P
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (((t + (k + 1) : ℕ) : ℤ) - t) = (k : ℤ) + 1 by push_cast; ring]
  rw [h1, h2, show (((t + 0 : ℕ) : ℤ) - t) = 0 by push_cast; ring]
  ring

/-- Interior count. -/
def Q (t : ℕ) : ℕ := ∑ k ∈ Finset.range (t - 2), if Lf (4 * t - ((k : ℤ) + 1)) then 1 else 0

lemma P_eq {t : ℕ} (ht : 2 ≤ t) : P t = Q t + 1 + (if t % 2 = 0 then 1 else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
  unfold P Q
  rw [Finset.sum_range_succ, Finset.sum_range_succ, show m + 2 - 2 = m by omega]
  rw [f_off1 (by omega) (by push_cast; left; ring), f_edge (by push_cast; left; ring)]
  have h : ∑ k ∈ Finset.range m, (if f (m + 2) ((k : ℤ) + 1) then 1 else 0)
      = ∑ k ∈ Finset.range m, (if Lf (4 * ((m + 2 : ℕ) : ℤ) - ((k : ℤ) + 1)) then 1 else 0) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    rw [f_right (by omega) (by push_cast; omega)]
  rw [h]
  by_cases he : (m + 2) % 2 = 0 <;> simp [he]

lemma sum12 (x : ℤ) : ∑ k ∈ Finset.range 12, (if Lf (x - k) then 1 else 0) = 7 := by
  have key : ∀ r : ℤ, 0 ≤ r → r < 12 →
      ∑ k ∈ Finset.range 12, (if Lf (r - k) then 1 else 0) = 7 := by
    intro r h0 h1
    interval_cases r <;> (simp only [Finset.sum_range_succ, Finset.sum_range_zero]; decide)
  rw [← key (x % 12) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Lf_congr (show (x - k) % 12 = (x % 12 - k) % 12 by omega)]

lemma Q_add {t : ℕ} (ht : 2 ≤ t) : Q (t + 12) = Q t + 7 := by
  unfold Q
  rw [show t + 12 - 2 = (t - 2) + 12 by omega, Finset.sum_range_add]
  have h1 : ∑ k ∈ Finset.range (t - 2), (if Lf (4 * ((t + 12 : ℕ) : ℤ) - ((k : ℤ) + 1)) then 1 else 0)
      = ∑ k ∈ Finset.range (t - 2), (if Lf (4 * (t : ℤ) - ((k : ℤ) + 1)) then 1 else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Lf_congr (show (4 * ((t + 12 : ℕ) : ℤ) - ((k : ℤ) + 1)) % 12
      = (4 * (t : ℤ) - ((k : ℤ) + 1)) % 12 by push_cast; omega)]
  have h2 : ∑ k ∈ Finset.range 12,
      (if Lf (4 * ((t + 12 : ℕ) : ℤ) - (((t - 2 + k : ℕ) : ℤ) + 1)) then 1 else 0) = 7 := by
    rw [← sum12 (3 * (t : ℤ) + 49)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (4 * ((t + 12 : ℕ) : ℤ) - (((t - 2 + k : ℕ) : ℤ) + 1)) = 3 * (t : ℤ) + 49 - k by
      have : ((t - 2 + k : ℕ) : ℤ) = (t : ℤ) - 2 + k := by omega
      rw [this]; push_cast; ring]
  rw [h1, h2]

/-- Closed form for the count. -/
def W (t : ℕ) : ℕ :=
  if t < 2 then 1 else
    2 * (Q t + 1 + (if t % 2 = 0 then 1 else 0)) + (if t % 3 ≠ 0 then 1 else 0)

lemma onCount_W (t : ℕ) : onCount 109 t = W t := by
  by_cases ht : t < 2
  · interval_cases t <;> decide
  · rw [count_split, P_eq (by omega), f_center (by omega)]
    unfold W
    rw [if_neg ht]
    by_cases h3 : t % 3 ≠ 0 <;> simp [h3]

lemma W_add {t : ℕ} (ht : 2 ≤ t) : W (t + 12) = W t + 14 := by
  have h1 : ¬ (t + 12 < 2) := by omega
  have h1' : ¬ (t < 2) := by omega
  have h2 : (t + 12) % 2 = t % 2 := by omega
  have h3 : (t + 12) % 3 = t % 3 := by omega
  unfold W
  simp only [h1, h1', if_false, Q_add ht, h2, h3]
  ring

lemma W_rec (n : ℕ) (hn : 8 ≤ n) : W n + W (n - 7) = W (n - 3) + W (n - 4) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hb : n < 21
    · interval_cases n <;> decide
    · have h := ih (n - 12) (by omega) (by omega)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      rw [show m + 12 - 12 = m by omega] at h
      rw [show m + 12 - 7 = (m - 7) + 12 by omega, show m + 12 - 3 = (m - 3) + 12 by omega,
        show m + 12 - 4 = (m - 4) + 12 by omega, W_add (by omega), W_add (by omega),
        W_add (by omega), W_add (by omega)]
      omega

end OMA.A267211Proof

open OMA.A267211Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267211.main := by
  have ha : ∀ n, (OMA.S_oeis_a267211.a n : ℚ) = (W n : ℚ) := by
    intro n
    simp [OMA.S_oeis_a267211.a, onCount_W]
  have hrec : ∀ n : ℕ, 8 ≤ n → (W n : ℚ) = W (n - 3) + W (n - 4) - W (n - 7) := by
    intro n hn
    have h := W_rec n hn
    have h' : ((W n + W (n - 7) : ℕ) : ℚ) = ((W (n - 3) + W (n - 4) : ℕ) : ℚ) := by rw [h]
    push_cast at h'
    linarith
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [ha, ha, ha, ha]
    exact hrec n hn
  · have hW : W 0 = 1 ∧ W 1 = 1 ∧ W 2 = 5 ∧ W 3 = 2 ∧ W 4 = 7 ∧ W 5 = 7 ∧ W 6 = 10 ∧ W 7 = 5 := by
      decide
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := hW
    rw [show ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ)
        = 1 - X ^ 3 - X ^ 4 + X ^ 7 by ring]
    rw [show (5 : PowerSeries ℚ) = C 5 from (map_ofNat C 5).symm,
      show (3 : PowerSeries ℚ) = C 3 from (map_ofNat C 3).symm]
    ext n
    simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
      coeff_X_pow, coeff_one, coeff_X, ha, coeff_C]
    by_cases hn : 8 ≤ n
    · have h3 : 3 ≤ n := by omega
      have h4 : 4 ≤ n := by omega
      have h7 : 7 ≤ n := by omega
      have h2 : 2 ≤ n := by omega
      have h6 : 6 ≤ n := by omega
      simp only [h2, h3, h4, h6, h7, if_true, show n - 2 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
        show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n ≠ 0 by omega, show n ≠ 1 by omega,
        show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
        show n ≠ 6 by omega, show n ≠ 7 by omega, if_false]
      rw [hrec n hn]
      ring
    · interval_cases n <;> simp [w0, w1, w2, w3, w4, w5, w6, w7] <;> norm_num
