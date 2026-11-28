import OMAStatements.S_oeis_a270013

namespace OeisA270013_A270009


/-- Rule 5: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 5). -/
def ruleR (c : Bool) (k : ℕ) : Bool := (5 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrsR (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateR : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q))


/-- A270009(n): the number of ON cells of stage `n + 1` in `[-(n+1), n+1]²` minus that of stage `n` in `[-n, n]²`. -/
def aR (n : ℕ) : ℤ :=
  ((∑ x ∈ Finset.range (2 * (n + 1) + 1), ∑ y ∈ Finset.range (2 * (n + 1) + 1), if stateR (n + 1) ((x : ℤ) - (n + 1 : ℕ), (y : ℤ) - (n + 1 : ℕ)) then 1 else 0 : ℕ) : ℤ) - ((∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), if stateR n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0 : ℕ) : ℤ)


/-! ## A finite certificate: stages `0..4` on the window `[-4, 4]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => ruleR (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrsR p, f q = b) :
    (nbrsR p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrsR])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrsR])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrsR])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrsR])
  cases b <;> simp [nbrsR, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → stateR t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [stateR, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show ruleR (stateR t p) _ = ruleR (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrsR, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 4

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == ruleR s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == ruleR (decode s (cell i j)) ((nbrsR (cell i j)).countP (decode s))

def initOK (s : Bool × List ℕ) : Bool :=
  (s.1 == false) && (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s (cell i j) == decide (cell i j = (0, 0))

lemma in_window (p : ℤ × ℤ) (h : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, p = cell i j := by
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨(x + W).toNat, by omega, (y + W).toNat, by omega, ?_⟩
  simp only [cell, Prod.mk.injEq]
  constructor <;> omega

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, stateR 0 p = decode s p := by
  simp only [initOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hbg, hcells⟩ := h
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    rfl
  · unfold decode
    rw [if_neg hw, hbg]
    show decide (p = (0, 0)) = false
    simp only [decide_eq_false_iff_not]
    rintro rfl
    exact hw ⟨by simp, by simp, by simp, by simp⟩

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, stateR t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..4`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 0, 16, 0, 0, 0, 0]),
    (true, [511, 511, 511, 511, 495, 511, 511, 511, 511]),
    (false, [0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (true, [511, 511, 511, 511, 511, 511, 511, 511, 511]),
    (false, [0, 0, 0, 0, 0, 0, 0, 0, 0])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrsR p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrsR, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, stateR t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrsR p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q)) = decode s' p
    rw [hs, show (fun q => stateR t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 4, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 2, borderOK (stages.getD (2 + r) default) = true) ∧
    stages.getD 4 default = stages.getD 2 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 4) :
    (stages.getD t default).1 = bg t ∧ ∀ p, stateR t p = decode (stages.getD t default) p := by
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
    ∀ p, stateR (2 + m) p = decode (stages.getD (2 + m % 2) default) p := by
  induction m with
  | zero => simpa using (certified 2 (by norm_num)).2
  | succ m ih =>
    have hr : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 2) hr
    have hok := stages_ok.2.1 (2 + m % 2) (by omega)
    rcases (by omega : m % 2 + 1 < 2 ∨ m % 2 + 1 = 2) with h | h
    · rw [show (m + 1) % 2 = m % 2 + 1 by omega]
      exact step_border (2 + m) _ _ ih hb hok
    · rw [show (m + 1) % 2 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 4 = 2 + m % 2 + 1 by omega]
      exact step_border (2 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 2 then stages.getD t default else stages.getD (2 + (t - 2) % 2) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : stateR t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 2 + m := ⟨t - 2, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 2 ≤ t) : stateR (t + 2) = stateR t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 2 - 2) % 2 = (t - 2) % 2 by omega]

/-- The background bit shown at time `t ≥ 2`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (2 + (t - 2) % 2) default).1

lemma outside (t : ℕ) (ht : 2 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : stateR t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 2) by omega)]

def aSim (n : ℕ) : ℤ :=
  ((∑ x ∈ Finset.range (2 * (n + 1) + 1), ∑ y ∈ Finset.range (2 * (n + 1) + 1), if sim (n + 1) ((x : ℤ) - (n + 1 : ℕ), (y : ℤ) - (n + 1 : ℕ)) then 1 else 0 : ℕ) : ℤ) - ((∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), if sim n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0 : ℕ) : ℤ)

lemma a_eq (n : ℕ) : aR n = aSim n := by
  unfold aR aSim
  simp only [state_eq]

/-- The values a(0..21); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 21, aR n = ([7, -8, 49, -49, 121, -121, 225, -225, 361, -361, 529, -529, 729, -729, 961, -961, 1225, -1225, 1521, -1521, 1849, -1849] : List ℤ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : aR 0 = 7 := vals 0 (by norm_num)
lemma v1 : aR 1 = -8 := vals 1 (by norm_num)
lemma v2 : aR 2 = 49 := vals 2 (by norm_num)
lemma v3 : aR 3 = -49 := vals 3 (by norm_num)
lemma v4 : aR 4 = 121 := vals 4 (by norm_num)
lemma v5 : aR 5 = -121 := vals 5 (by norm_num)
lemma v6 : aR 6 = 225 := vals 6 (by norm_num)
lemma v7 : aR 7 = -225 := vals 7 (by norm_num)
lemma v8 : aR 8 = 361 := vals 8 (by norm_num)
lemma v9 : aR 9 = -361 := vals 9 (by norm_num)
lemma v10 : aR 10 = 529 := vals 10 (by norm_num)
lemma v11 : aR 11 = -529 := vals 11 (by norm_num)
lemma v12 : aR 12 = 729 := vals 12 (by norm_num)
lemma v13 : aR 13 = -729 := vals 13 (by norm_num)
lemma v14 : aR 14 = 961 := vals 14 (by norm_num)
lemma v15 : aR 15 = -961 := vals 15 (by norm_num)
lemma v16 : aR 16 = 1225 := vals 16 (by norm_num)
lemma v17 : aR 17 = -1225 := vals 17 (by norm_num)
lemma v18 : aR 18 = 1521 := vals 18 (by norm_num)
lemma v19 : aR 19 = -1521 := vals 19 (by norm_num)
lemma v20 : aR 20 = 1849 := vals 20 (by norm_num)
lemma v21 : aR 21 = -1849 := vals 21 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if stateR n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if stateR n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 2 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 4 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if stateR n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 4 ≤ n) (h2 : n % 2 = 0) :
    (cnt n : ℚ) = 0 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 2 + (n - 2) % 2 = 2 := by omega
  have hb : bgOf n = false := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_neg (by decide)] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cntn1 (n : ℕ) (h1 : 4 ≤ n) (h2 : n % 2 = 1) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 2 + (n - 2) % 2 = 3 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 4 ≤ n) (h2 : n % 2 = 0) :
    (aR n : ℚ) = (1 * (2 * (n : ℚ) + 3) ^ 2 + (0 : ℚ)) - (0 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ)) := by
  have e1 := cntn1 (n + 1) (by omega) (by omega)
  have e0 := cntn0 n h1 h2
  have ha : (aR n : ℚ) = (cnt (n + 1) : ℚ) - (cnt n : ℚ) := by
    show (((cnt (n + 1) : ℤ) - (cnt n : ℤ) : ℤ) : ℚ) = _
    push_cast
    ring
  rw [ha, e1, e0]
  push_cast
  ring


lemma cfn1 (n : ℕ) (h1 : 4 ≤ n) (h2 : n % 2 = 1) :
    (aR n : ℚ) = (0 * (2 * (n : ℚ) + 3) ^ 2 + (0 : ℚ)) - (1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ)) := by
  have e1 := cntn0 (n + 1) (by omega) (by omega)
  have e0 := cntn1 n h1 h2
  have ha : (aR n : ℚ) = (cnt (n + 1) : ℚ) - (cnt n : ℚ) := by
    show (((cnt (n + 1) : ℤ) - (cnt n : ℤ) : ℤ) : ℚ) = _
    push_cast
    ring
  rw [ha, e1, e0]
  push_cast
  ring


/-- a(n) = 4+5*(-1)^n+(4+8*(-1)^n)*n+4*(-1)^n*n^2 for n>1 -/
theorem closed0 (n : ℕ) (hn : 2 ≤ n) : (aR n : ℚ) = ((((4 : ℚ) + ((5 : ℚ) * ((-(1 : ℚ)) ^ n))) + (((4 : ℚ) + ((8 : ℚ) * ((-(1 : ℚ)) ^ n))) * (n : ℚ))) + (((4 : ℚ) * ((-(1 : ℚ)) ^ n)) * ((n : ℚ) ^ 2))) := by
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 4 + 2 * q := ⟨(n - 4) / 2, by omega⟩
      have c0 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0
    · obtain ⟨q, rfl⟩ : ∃ q, n = 5 + 2 * q := ⟨(n - 5) / 2, by omega⟩
      have c0 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0


/-- a(n) = 4*n^2+12*n+9 for n>1 and n even -/
theorem closed1 (n : ℕ) (hn : 2 ≤ n) (hp : n % 2 = 0) : (aR n : ℚ) = ((((4 : ℚ) * ((n : ℚ) ^ 2)) + ((12 : ℚ) * (n : ℚ))) + (9 : ℚ)) := by
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 4 + 2 * q := ⟨(n - 4) / 2, by omega⟩
      have c0 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0
    · omega


/-- a(n) = -4*n^2-4*n-1 for n>1 and n odd -/
theorem closed2 (n : ℕ) (hn : 2 ≤ n) (hp : n % 2 = 1) : (aR n : ℚ) = ((((-(4 : ℚ)) * ((n : ℚ) ^ 2)) - ((4 : ℚ) * (n : ℚ))) - (1 : ℚ)) := by
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · omega
    · obtain ⟨q, rfl⟩ : ∃ q, n = 5 + 2 * q := ⟨(n - 5) / 2, by omega⟩
      have c0 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0


/-- a(n) = -a(n-1)+2*a(n-2)+2*a(n-3)-a(n-4)-a(n-5) for n>6 -/
theorem recurrence3 (n : ℕ) (hn : 7 ≤ n) : (aR n : ℤ) = (((((-(aR (n - 1) : ℤ)) + ((2 : ℤ) * (aR (n - 2) : ℤ))) + ((2 : ℤ) * (aR (n - 3) : ℤ))) - (aR (n - 4) : ℤ)) - (aR (n - 5) : ℤ)) := by
  rcases Nat.lt_or_ge n 9 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at *
  · suffices hq : (aR n : ℚ) = (((((-(aR (n - 1) : ℚ)) + ((2 : ℚ) * (aR (n - 2) : ℚ))) + ((2 : ℚ) * (aR (n - 3) : ℚ))) - (aR (n - 4) : ℚ)) - (aR (n - 5) : ℚ)) by exact_mod_cast hq
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 10 + 2 * q := ⟨(n - 10) / 2, by omega⟩
      have c0 := cfn0 (10 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 1 = 9 + 2 * q by omega]
      have c1 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 2 = 8 + 2 * q by omega]
      have c2 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 3 = 7 + 2 * q by omega]
      have c3 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 4 = 6 + 2 * q by omega]
      have c4 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 5 = 5 + 2 * q by omega]
      have c5 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5
    · obtain ⟨q, rfl⟩ : ∃ q, n = 9 + 2 * q := ⟨(n - 9) / 2, by omega⟩
      have c0 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 1 = 8 + 2 * q by omega]
      have c1 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 2 = 7 + 2 * q by omega]
      have c2 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 3 = 6 + 2 * q by omega]
      have c3 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 4 = 5 + 2 * q by omega]
      have c4 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 5 = 4 + 2 * q by omega]
      have c5 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5


lemma gfrec4 (n : ℕ) (hn : 7 ≤ n) : (aR n : ℚ) = ((-1 : ℚ)) * (aR (n - 1) : ℚ) + ((2 : ℚ)) * (aR (n - 2) : ℚ) + ((2 : ℚ)) * (aR (n - 3) : ℚ) + ((-1 : ℚ)) * (aR (n - 4) : ℚ) + ((-1 : ℚ)) * (aR (n - 5) : ℚ) := by
  rcases Nat.lt_or_ge n 9 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 10 + 2 * q := ⟨(n - 10) / 2, by omega⟩
      have c0 := cfn0 (10 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 1 = 9 + 2 * q by omega]
      have c1 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 2 = 8 + 2 * q by omega]
      have c2 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 3 = 7 + 2 * q by omega]
      have c3 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 4 = 6 + 2 * q by omega]
      have c4 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 5 = 5 + 2 * q by omega]
      have c5 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5
    · obtain ⟨q, rfl⟩ : ∃ q, n = 9 + 2 * q := ⟨(n - 9) / 2, by omega⟩
      have c0 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 1 = 8 + 2 * q by omega]
      have c1 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 2 = 7 + 2 * q by omega]
      have c2 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 3 = 6 + 2 * q by omega]
      have c3 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 4 = 5 + 2 * q by omega]
      have c4 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 5 = 4 + 2 * q by omega]
      have c5 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5

open PowerSeries in
/-- G.f.: (7-x+27*x^2+2*x^3-3*x^4-x^5+x^6) / ((1-x)^2*(1+x)^3) -/
theorem gf4 : PowerSeries.mk (fun n => (aR n : ℚ)) = ((7-X+27*X ^ 2+2*X ^ 3-3*X ^ 4-X ^ 5+X ^ 6)) * (((1-X) ^ 2*(1+X) ^ 3))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (aR n : ℚ))
  have hden : constantCoeff ((((1-X) ^ 2*(1+X) ^ 3)) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X) ^ 2*(1+X) ^ 3)) = C ((1 : ℚ)) * G + C ((1 : ℚ)) * (G * X ^ 1) + C ((-2 : ℚ)) * (G * X ^ 2) + C ((-2 : ℚ)) * (G * X ^ 3) + C ((1 : ℚ)) * (G * X ^ 4) + C ((1 : ℚ)) * (G * X ^ 5) := by
    simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]; ring
  have eP : (((7-X+27*X ^ 2+2*X ^ 3-3*X ^ 4-X ^ 5+X ^ 6)) : ℚ⟦X⟧) = C ((7 : ℚ)) + C ((-1 : ℚ)) * X ^ 1 + C ((27 : ℚ)) * X ^ 2 + C ((2 : ℚ)) * X ^ 3 + C ((-3 : ℚ)) * X ^ 4 + C ((-1 : ℚ)) * X ^ 5 + C ((1 : ℚ)) * X ^ 6 := by
    simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]; ring
  have key : G * (((1-X) ^ 2*(1+X) ^ 3)) = (7-X+27*X ^ 2+2*X ^ 3-3*X ^ 4-X ^ 5+X ^ 6) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec4 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 2 ≤ n → (aR n : ℚ) = ((((4 : ℚ) + ((5 : ℚ) * ((-(1 : ℚ)) ^ n))) + (((4 : ℚ) + ((8 : ℚ) * ((-(1 : ℚ)) ^ n))) * (n : ℚ))) + (((4 : ℚ) * ((-(1 : ℚ)) ^ n)) * ((n : ℚ) ^ 2)))) ∧
    (∀ n : ℕ, 2 ≤ n → n % 2 = 0 → (aR n : ℚ) = ((((4 : ℚ) * ((n : ℚ) ^ 2)) + ((12 : ℚ) * (n : ℚ))) + (9 : ℚ))) ∧
    (∀ n : ℕ, 2 ≤ n → n % 2 = 1 → (aR n : ℚ) = ((((-(4 : ℚ)) * ((n : ℚ) ^ 2)) - ((4 : ℚ) * (n : ℚ))) - (1 : ℚ))) ∧
    (∀ n : ℕ, 7 ≤ n → (aR n : ℤ) = (((((-(aR (n - 1) : ℤ)) + ((2 : ℤ) * (aR (n - 2) : ℤ))) + ((2 : ℤ) * (aR (n - 3) : ℤ))) - (aR (n - 4) : ℤ)) - (aR (n - 5) : ℤ))) ∧
    (PowerSeries.mk (fun n => (aR n : ℚ)) = ((7-X+27*X ^ 2+2*X ^ 3-3*X ^ 4-X ^ 5+X ^ 6)) * (((1-X) ^ 2*(1+X) ^ 3))⁻¹) :=
  ⟨closed0, closed1, closed2, recurrence3, gf4⟩


end OeisA270013_A270009

namespace OMA.S_oeis_a270013








/-! ## A finite certificate: stages `0..3` on the window `[-3, 3]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => rule (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrs p, f q = b) :
    (nbrs p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrs])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrs])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrs])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrs])
  cases b <;> simp [nbrs, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → state t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [state, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show rule (state t p) _ = rule (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 3

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == rule s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == rule (decode s (cell i j)) ((nbrs (cell i j)).countP (decode s))

def initOK (s : Bool × List ℕ) : Bool :=
  (s.1 == false) && (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s (cell i j) == decide (cell i j = (0, 0))

lemma in_window (p : ℤ × ℤ) (h : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, p = cell i j := by
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨(x + W).toNat, by omega, (y + W).toNat, by omega, ?_⟩
  simp only [cell, Prod.mk.injEq]
  constructor <;> omega

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, state 0 p = decode s p := by
  simp only [initOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hbg, hcells⟩ := h
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    rfl
  · unfold decode
    rw [if_neg hw, hbg]
    show decide (p = (0, 0)) = false
    simp only [decide_eq_false_iff_not]
    rintro rfl
    exact hw ⟨by simp, by simp, by simp, by simp⟩

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, state t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, state (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show rule (state t (cell i j)) ((nbrs (cell i j)).countP (fun q => state t q)) = _
    rw [hs, show (fun q => state t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..3`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 8, 0, 0, 0]),
    (true, [127, 127, 127, 127, 127, 127, 127]),
    (false, [0, 0, 0, 0, 0, 0, 0]),
    (true, [127, 127, 127, 127, 127, 127, 127])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrs p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrs, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, state t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, state (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show rule (state t (cell i j)) ((nbrs (cell i j)).countP (fun q => state t q)) = _
    rw [hs, show (fun q => state t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrs p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show rule (state t p) ((nbrs p).countP (fun q => state t q)) = decode s' p
    rw [hs, show (fun q => state t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 3, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 2, borderOK (stages.getD (1 + r) default) = true) ∧
    stages.getD 3 default = stages.getD 1 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 3) :
    (stages.getD t default).1 = bg t ∧ ∀ p, state t p = decode (stages.getD t default) p := by
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
    ∀ p, state (1 + m) p = decode (stages.getD (1 + m % 2) default) p := by
  induction m with
  | zero => simpa using (certified 1 (by norm_num)).2
  | succ m ih =>
    have hr : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 2) hr
    have hok := stages_ok.2.1 (1 + m % 2) (by omega)
    rcases (by omega : m % 2 + 1 < 2 ∨ m % 2 + 1 = 2) with h | h
    · rw [show (m + 1) % 2 = m % 2 + 1 by omega]
      exact step_border (1 + m) _ _ ih hb hok
    · rw [show (m + 1) % 2 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 3 = 1 + m % 2 + 1 by omega]
      exact step_border (1 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 1 then stages.getD t default else stages.getD (1 + (t - 1) % 2) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : state t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 1 + m := ⟨t - 1, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 1 ≤ t) : state (t + 2) = state t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 2 - 1) % 2 = (t - 1) % 2 by omega]

/-- The background bit shown at time `t ≥ 1`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (1 + (t - 1) % 2) default).1

lemma outside (t : ℕ) (ht : 1 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : state t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 1) by omega)]

def aSim (n : ℕ) : ℤ :=
  ((∑ x ∈ Finset.range (2 * (n + 1) + 1), ∑ y ∈ Finset.range (2 * (n + 1) + 1), if sim (n + 1) ((x : ℤ) - (n + 1 : ℕ), (y : ℤ) - (n + 1 : ℕ)) then 1 else 0 : ℕ) : ℤ) - ((∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), if sim n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0 : ℕ) : ℤ)

lemma a_eq (n : ℕ) : a n = aSim n := by
  unfold a aSim
  simp only [state_eq]

/-- The values a(0..19); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 19, a n = ([8, -9, 49, -49, 121, -121, 225, -225, 361, -361, 529, -529, 729, -729, 961, -961, 1225, -1225, 1521, -1521] : List ℤ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : a 0 = 8 := vals 0 (by norm_num)
lemma v1 : a 1 = -9 := vals 1 (by norm_num)
lemma v2 : a 2 = 49 := vals 2 (by norm_num)
lemma v3 : a 3 = -49 := vals 3 (by norm_num)
lemma v4 : a 4 = 121 := vals 4 (by norm_num)
lemma v5 : a 5 = -121 := vals 5 (by norm_num)
lemma v6 : a 6 = 225 := vals 6 (by norm_num)
lemma v7 : a 7 = -225 := vals 7 (by norm_num)
lemma v8 : a 8 = 361 := vals 8 (by norm_num)
lemma v9 : a 9 = -361 := vals 9 (by norm_num)
lemma v10 : a 10 = 529 := vals 10 (by norm_num)
lemma v11 : a 11 = -529 := vals 11 (by norm_num)
lemma v12 : a 12 = 729 := vals 12 (by norm_num)
lemma v13 : a 13 = -729 := vals 13 (by norm_num)
lemma v14 : a 14 = 961 := vals 14 (by norm_num)
lemma v15 : a 15 = -961 := vals 15 (by norm_num)
lemma v16 : a 16 = 1225 := vals 16 (by norm_num)
lemma v17 : a 17 = -1225 := vals 17 (by norm_num)
lemma v18 : a 18 = 1521 := vals 18 (by norm_num)
lemma v19 : a 19 = -1521 := vals 19 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if state n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if state n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 1 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 3 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if state n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 2 = 0) :
    (cnt n : ℚ) = 0 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 1 + (n - 1) % 2 = 2 := by omega
  have hb : bgOf n = false := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_neg (by decide)] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cntn1 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 2 = 1) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 1 + (n - 1) % 2 = 1 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 2 = 0) :
    (a n : ℚ) = (1 * (2 * (n : ℚ) + 3) ^ 2 + (0 : ℚ)) - (0 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ)) := by
  have e1 := cntn1 (n + 1) (by omega) (by omega)
  have e0 := cntn0 n h1 h2
  have ha : (a n : ℚ) = (cnt (n + 1) : ℚ) - (cnt n : ℚ) := by
    show (((cnt (n + 1) : ℤ) - (cnt n : ℤ) : ℤ) : ℚ) = _
    push_cast
    ring
  rw [ha, e1, e0]
  push_cast
  ring


lemma cfn1 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 2 = 1) :
    (a n : ℚ) = (0 * (2 * (n : ℚ) + 3) ^ 2 + (0 : ℚ)) - (1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ)) := by
  have e1 := cntn0 (n + 1) (by omega) (by omega)
  have e0 := cntn1 n h1 h2
  have ha : (a n : ℚ) = (cnt (n + 1) : ℚ) - (cnt n : ℚ) := by
    show (((cnt (n + 1) : ℤ) - (cnt n : ℤ) : ℤ) : ℚ) = _
    push_cast
    ring
  rw [ha, e1, e0]
  push_cast
  ring


/-- a(n) = 4+5*(-1)^n+(4+8*(-1)^n)*n+4*(-1)^n*n^2 for n>0, = A270009(n) for n>1 -/
theorem closed0 (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((((4 : ℚ) + ((5 : ℚ) * ((-(1 : ℚ)) ^ n))) + (((4 : ℚ) + ((8 : ℚ) * ((-(1 : ℚ)) ^ n))) * (n : ℚ))) + (((4 : ℚ) * ((-(1 : ℚ)) ^ n)) * ((n : ℚ) ^ 2))) := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 4 + 2 * q := ⟨(n - 4) / 2, by omega⟩
      have c0 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0
    · obtain ⟨q, rfl⟩ : ∃ q, n = 3 + 2 * q := ⟨(n - 3) / 2, by omega⟩
      have c0 := cfn1 (3 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0


/-- a(n) = 4*n^2+12*n+9 for n>0 and even -/
theorem closed1 (n : ℕ) (hn : 1 ≤ n) (hp : n % 2 = 0) : (a n : ℚ) = ((((4 : ℚ) * ((n : ℚ) ^ 2)) + ((12 : ℚ) * (n : ℚ))) + (9 : ℚ)) := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 4 + 2 * q := ⟨(n - 4) / 2, by omega⟩
      have c0 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0
    · omega


/-- a(n) = -4*n^2-4*n-1 for n>0 and odd -/
theorem closed2 (n : ℕ) (hn : 1 ≤ n) (hp : n % 2 = 1) : (a n : ℚ) = ((((-(4 : ℚ)) * ((n : ℚ) ^ 2)) - ((4 : ℚ) * (n : ℚ))) - (1 : ℚ)) := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · omega
    · obtain ⟨q, rfl⟩ : ∃ q, n = 3 + 2 * q := ⟨(n - 3) / 2, by omega⟩
      have c0 := cfn1 (3 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / (1 : ℚ)) * c0


/-- a(n) = -a(n-1)+2*a(n-2)+2*a(n-3)-a(n-4)-a(n-5) for n>5 -/
theorem recurrence3 (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = (((((-(a (n - 1) : ℤ)) + ((2 : ℤ) * (a (n - 2) : ℤ))) + ((2 : ℤ) * (a (n - 3) : ℤ))) - (a (n - 4) : ℤ)) - (a (n - 5) : ℤ)) := by
  rcases Nat.lt_or_ge n 8 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8] at *
  · suffices hq : (a n : ℚ) = (((((-(a (n - 1) : ℚ)) + ((2 : ℚ) * (a (n - 2) : ℚ))) + ((2 : ℚ) * (a (n - 3) : ℚ))) - (a (n - 4) : ℚ)) - (a (n - 5) : ℚ)) by exact_mod_cast hq
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 8 + 2 * q := ⟨(n - 8) / 2, by omega⟩
      have c0 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 1 = 7 + 2 * q by omega]
      have c1 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 2 = 6 + 2 * q by omega]
      have c2 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 3 = 5 + 2 * q by omega]
      have c3 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 4 = 4 + 2 * q by omega]
      have c4 := cfn0 (4 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 5 = 3 + 2 * q by omega]
      have c5 := cfn1 (3 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5
    · obtain ⟨q, rfl⟩ : ∃ q, n = 9 + 2 * q := ⟨(n - 9) / 2, by omega⟩
      have c0 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 1 = 8 + 2 * q by omega]
      have c1 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 2 = 7 + 2 * q by omega]
      have c2 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 3 = 6 + 2 * q by omega]
      have c3 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 4 = 5 + 2 * q by omega]
      have c4 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 5 = 4 + 2 * q by omega]
      have c5 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5


lemma gfrec4 (n : ℕ) (hn : 6 ≤ n) : (a n : ℚ) = ((-1 : ℚ)) * (a (n - 1) : ℚ) + ((2 : ℚ)) * (a (n - 2) : ℚ) + ((2 : ℚ)) * (a (n - 3) : ℚ) + ((-1 : ℚ)) * (a (n - 4) : ℚ) + ((-1 : ℚ)) * (a (n - 5) : ℚ) := by
  rcases Nat.lt_or_ge n 8 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 8 + 2 * q := ⟨(n - 8) / 2, by omega⟩
      have c0 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 1 = 7 + 2 * q by omega]
      have c1 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 2 = 6 + 2 * q by omega]
      have c2 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 3 = 5 + 2 * q by omega]
      have c3 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 4 = 4 + 2 * q by omega]
      have c4 := cfn0 (4 + 2 * q) (by omega) (by omega)
      rw [show 8 + 2 * q - 5 = 3 + 2 * q by omega]
      have c5 := cfn1 (3 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5
    · obtain ⟨q, rfl⟩ : ∃ q, n = 9 + 2 * q := ⟨(n - 9) / 2, by omega⟩
      have c0 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 1 = 8 + 2 * q by omega]
      have c1 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 2 = 7 + 2 * q by omega]
      have c2 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 3 = 6 + 2 * q by omega]
      have c3 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 4 = 5 + 2 * q by omega]
      have c4 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 5 = 4 + 2 * q by omega]
      have c5 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 c4 c5 ⊢
      push_cast at c0 c1 c2 c3 c4 c5 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((-1 : ℚ)) / (1 : ℚ)) * c1 + (-((2 : ℚ)) / (1 : ℚ)) * c2 + (-((2 : ℚ)) / (1 : ℚ)) * c3 + (-((-1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c5

open PowerSeries in
/-- G.f.: (8-x+24*x^2+2*x^3-x^5) / ((1-x)^2*(1+x)^3) -/
theorem gf4 : PowerSeries.mk (fun n => (a n : ℚ)) = ((8-X+24*X ^ 2+2*X ^ 3-X ^ 5)) * (((1-X) ^ 2*(1+X) ^ 3))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((((1-X) ^ 2*(1+X) ^ 3)) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X) ^ 2*(1+X) ^ 3)) = C ((1 : ℚ)) * G + C ((1 : ℚ)) * (G * X ^ 1) + C ((-2 : ℚ)) * (G * X ^ 2) + C ((-2 : ℚ)) * (G * X ^ 3) + C ((1 : ℚ)) * (G * X ^ 4) + C ((1 : ℚ)) * (G * X ^ 5) := by
    simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]; ring
  have eP : (((8-X+24*X ^ 2+2*X ^ 3-X ^ 5)) : ℚ⟦X⟧) = C ((8 : ℚ)) + C ((-1 : ℚ)) * X ^ 1 + C ((24 : ℚ)) * X ^ 2 + C ((2 : ℚ)) * X ^ 3 + C ((-1 : ℚ)) * X ^ 5 := by
    simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]; ring
  have key : G * (((1-X) ^ 2*(1+X) ^ 3)) = (8-X+24*X ^ 2+2*X ^ 3-X ^ 5) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec4 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = ((((4 : ℚ) + ((5 : ℚ) * ((-(1 : ℚ)) ^ n))) + (((4 : ℚ) + ((8 : ℚ) * ((-(1 : ℚ)) ^ n))) * (n : ℚ))) + (((4 : ℚ) * ((-(1 : ℚ)) ^ n)) * ((n : ℚ) ^ 2)))) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → (a n : ℚ) = ((((4 : ℚ) * ((n : ℚ) ^ 2)) + ((12 : ℚ) * (n : ℚ))) + (9 : ℚ))) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 1 → (a n : ℚ) = ((((-(4 : ℚ)) * ((n : ℚ) ^ 2)) - ((4 : ℚ) * (n : ℚ))) - (1 : ℚ))) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = (((((-(a (n - 1) : ℤ)) + ((2 : ℤ) * (a (n - 2) : ℤ))) + ((2 : ℤ) * (a (n - 3) : ℤ))) - (a (n - 4) : ℤ)) - (a (n - 5) : ℤ))) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) = ((8-X+24*X ^ 2+2*X ^ 3-X ^ 5)) * (((1-X) ^ 2*(1+X) ^ 3))⁻¹) :=
  ⟨closed0, closed1, closed2, recurrence3, gf4⟩


theorem xref_A270009 (n : ℕ) (hn : 2 ≤ n) : a n = OeisA270013_A270009.aR n := by
  have h1 := closed0 n (by omega)
  have h2 := OeisA270013_A270009.closed0 n (by omega)
  exact_mod_cast h1.trans h2.symm


/-! ## The statement's definitions and the bridge -/

open PowerSeries





theorem stateOf_A270009 (t : ℕ) : OeisA270013_A270009.stateR t = stateOf 5 t := by
  induction t with
  | zero => funext p; rfl
  | succ t ih =>
    funext p
    show OeisA270013_A270009.ruleR (OeisA270013_A270009.stateR t p)
        ((OeisA270013_A270009.nbrsR p).countP (fun q => OeisA270013_A270009.stateR t q)) =
      ruleOf 5 (stateOf 5 t p) ((nbrs p).countP (fun q => stateOf 5 t q))
    rw [ih]
    rfl

theorem aOf_A270009 (n : ℕ) : OeisA270013_A270009.aR n = aOf 5 n := by
  rw [OeisA270013_A270009.aR, aOf]
  simp only [stateOf_A270009]

theorem controls_A270009 : ∀ n ≤ 21, aOf 5 n = ([7, -8, 49, -49, 121, -121, 225, -225, 361, -361, 529, -529, 729, -729, 961, -961, 1225, -1225, 1521, -1521, 1849, -1849] : List ℤ).getD n 0 := by
  intro n hn
  rw [← aOf_A270009]
  exact OeisA270013_A270009.vals n hn

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 0 < n →
      (a n : ℚ) = 4 + 5 * (-1) ^ n + (4 + 8 * (-1) ^ n) * n + 4 * (-1) ^ n * n ^ 2) ∧
    (∀ n : ℕ, 1 < n → a n = aOf 5 n) ∧
    (∀ n : ℕ, 0 < n → Even n → (a n : ℚ) = 4 * n ^ 2 + 12 * n + 9) ∧
    (∀ n : ℕ, 0 < n → Odd n → (a n : ℚ) = -4 * n ^ 2 - 4 * n - 1) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = -a (n - 1) + 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - a (n - 5)) ∧
    A = (8 - X + 24 * X ^ 2 + 2 * X ^ 3 - X ^ 5) * ((1 - X) ^ 2 * (1 + X) ^ 3)⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl]
  exact ⟨fun n hn => (closed0 n (by omega)).trans (by ring),
    fun n hn => (xref_A270009 n (by omega)).trans (aOf_A270009 n),
    fun n hn hp => (closed1 n (by omega) (Nat.even_iff.mp hp)).trans (by ring),
    fun n hn hp => (closed2 n (by omega) (Nat.odd_iff.mp hp)).trans (by ring),
    fun n hn => (recurrence3 n (by omega)).trans (by ring),
    gf4⟩

end OMA.S_oeis_a270013

theorem OMA.solution : type_of% @OMA.S_oeis_a270013.main :=
  OMA.S_oeis_a270013.conj
