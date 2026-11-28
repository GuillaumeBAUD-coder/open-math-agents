import OMAStatements.S_oeis_a267524

namespace OMA.S_oeis_a267524


/-- Rule 139 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (139 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A267524(n): the states of cell 0 in rows `0..n` (row 0 first) as binary digits read in base 10. -/
def ca (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), if cstate t 0 then 10 ^ (n - t) else 0


/-! ## A finite certificate: rows `0..5` on the window `[-6, 6]` -/

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

def W : ℕ := 6

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

/-- The rows `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 64),
    (true, 7999),
    (true, 8095),
    (true, 8143),
    (true, 8167),
    (true, 8179)]

lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    ∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ i, cstate t i = decode (stages.getD t default) i := by
  induction t with
  | zero =>
    have h := stages_ok.1
    refine ⟨?_, init_ok _ h⟩
    simp only [initOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  | succ t ih =>
    obtain ⟨hb, hs⟩ := ih (by omega)
    have hok := stages_ok.2 t (by omega)
    refine ⟨?_, step_ok t _ _ (by unfold W; omega) hs hb hok⟩
    simp only [stepOK, Bool.and_eq_true, beq_iff_eq] at hok
    rw [hok.1, hb]
    rfl


def sim (t : ℕ) : ℤ → Bool := decode (stages.getD t default)

/-! ## The regime from row 5 on -/

def bgT : List Bool := [true]
def flT : List Bool := [true]
/-- Bit `j` of the left edge block: cell `-t + j`. -/
def elT : List ℕ := [1]
/-- Bit `j` of the right edge block: cell `t - j`. -/
def erT : List ℕ := [7]
/-- Bit `m` of the center block: cell `m - 0`. -/
def coT : List ℕ := [1]

def V (t : ℕ) (i : ℤ) : Bool :=
  if i < -(t : ℤ) ∨ (t : ℤ) < i then bgT.getD ((t - 5) % 1) false
  else if i + t ≤ 2 then (elT.getD ((t - 5) % 1) 0).testBit (i + t).toNat
  else if (t : ℤ) - i ≤ 2 then (erT.getD ((t - 5) % 1) 0).testBit ((t : ℤ) - i).toNat
  else if -(0 : ℤ) ≤ i ∧ i ≤ 0 then (coT.getD ((t - 5) % 1) 0).testBit (i + 0).toNat
  else flT.getD ((t - 5) % 1) false

lemma V_out (t : ℕ) (i : ℤ) (h : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    V t i = bgT.getD ((t - 5) % 1) false := by
  unfold V; rw [if_pos h]

lemma V_el (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (j : ℕ) (hj : i + t = j) (hjA : j ≤ 2) :
    V t i = (elT.getD ((t - 5) % 1) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_er (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (j : ℕ) (hj : (t : ℤ) - i = j) (hjA : j ≤ 2) :
    V t i = (erT.getD ((t - 5) % 1) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_co (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (m : ℕ) (hm : i + 0 = m) (hmK : m ≤ 2 * 0) :
    V t i = (coT.getD ((t - 5) % 1) 0).testBit m := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_fl (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (h1 : (2 : ℤ) < i + t) (h2 : (2 : ℤ) < (t : ℤ) - i)
    (h3 : i < -(0 : ℤ) ∨ (0 : ℤ) < i) : V t i = flT.getD ((t - 5) % 1) false := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]


set_option maxHeartbeats 4000000 in
lemma stepV (t : ℕ) (ht : 5 ≤ t) (i : ℤ) :
    rule (V t (i - 1)) (V t i) (V t (i + 1)) = V (t + 1) i := by
  rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (i + t + 1 = 4) ∨ (4 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 4 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 4) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_el t ht (i + 1) 2 (by omega) (by norm_num), V_el (t + 1) (by omega) i 2 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_el t ht i 2 (by omega) (by norm_num), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 2 (by omega) (by norm_num), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_er t ht (i + 1) 2 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_er t ht i 2 (by omega) (by norm_num), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 2 (by omega) (by norm_num), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_er (t + 1) (by omega) i 2 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 1 ∧ (t - 5) % 1 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 5) % 1 = (q + 1) % 1 by omega, hqq]
    interval_cases q <;> decide

lemma base_ok : (∀ j < 2 * W + 1, decode (stages.getD 5 default) ((j : ℤ) - W) = V 5 ((j : ℤ) - W)) ∧
    (stages.getD 5 default).1 = bgT.getD 0 false := by
  decide +kernel

lemma pattern (t : ℕ) (ht : 5 ≤ t) : ∀ i, cstate t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(certified 5 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 5 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 5) : sim t = cstate t := funext fun i => ((certified t ht).2 i).symm


lemma state_eq_V (t : ℕ) (ht : 5 ≤ t) : cstate t = V t := funext (pattern t ht)

/-- The rows as computed: the certificate up to row 5, then `V`. -/
def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 5 then sim t else V t

lemma state_eq (t : ℕ) : cstate t = rowOf t := by
  unfold rowOf
  split_ifs with h
  · exact (sim_V t h).symm
  · exact state_eq_V t (by omega)

def aSim (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), if rowOf t 0 then 10 ^ (n - t) else 0

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..16); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 16, ca n = ([1, 10, 100, 1001, 10011, 100111, 1001111, 10011111, 100111111, 1001111111, 10011111111, 100111111111, 1001111111111, 10011111111111, 100111111111111, 1001111111111111, 10011111111111111] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 10 := vals 1 (by norm_num)
lemma v2 : ca 2 = 100 := vals 2 (by norm_num)
lemma v3 : ca 3 = 1001 := vals 3 (by norm_num)
lemma v4 : ca 4 = 10011 := vals 4 (by norm_num)
lemma v5 : ca 5 = 100111 := vals 5 (by norm_num)
lemma v6 : ca 6 = 1001111 := vals 6 (by norm_num)
lemma v7 : ca 7 = 10011111 := vals 7 (by norm_num)
lemma v8 : ca 8 = 100111111 := vals 8 (by norm_num)
lemma v9 : ca 9 = 1001111111 := vals 9 (by norm_num)
lemma v10 : ca 10 = 10011111111 := vals 10 (by norm_num)
lemma v11 : ca 11 = 100111111111 := vals 11 (by norm_num)
lemma v12 : ca 12 = 1001111111111 := vals 12 (by norm_num)
lemma v13 : ca 13 = 10011111111111 := vals 13 (by norm_num)
lemma v14 : ca 14 = 100111111111111 := vals 14 (by norm_num)
lemma v15 : ca 15 = 1001111111111111 := vals 15 (by norm_num)
lemma v16 : ca 16 = 10011111111111111 := vals 16 (by norm_num)

lemma rel (n : ℕ) :
    ca (n + 1) = 10 ^ 1 * ca n + ∑ j ∈ Finset.range 1, (if cstate (n + 1 + j) 0 then 10 ^ (1 - 1 - j) else 0) := by
  unfold ca
  rw [show n + 1 + 1 = (n + 1) + 1 by ring, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : d < n + 1 := Finset.mem_range.mp hd
    split_ifs
    · rw [← pow_add]; congr 1; omega
    · simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [show n + 1 - (n + 1 + j) = 1 - 1 - j by omega]

lemma colv (t : ℕ) (ht : 5 ≤ t) : cstate t 0 = (coT.getD ((t - 5) % 1) 0).testBit 0 := by
  rw [state_eq_V t ht, V_co t ht 0 0 (by norm_num) (by norm_num)]


lemma cf0 (m : ℕ) : (10 : ℚ) ^ 5 * (((10 : ℚ) ^ 1 - 1) * (ca (5 + 1 * m) : ℚ) + 1) =
    (901000 : ℚ) * (10 : ℚ) ^ (5 + 1 * m) := by
  induction m with
  | zero =>
    rw [show 5 + 1 * 0 = 5 by ring, v5]
    norm_num
  | succ m ih =>
    rw [show 5 + 1 * (m + 1) = (5 + 1 * m) + 1 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (5 + 1 * m + 1 + 0) (by omega), show (5 + 1 * m + 1 + 0 - 5) % 1 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 1 * ih

lemma cfn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 1 = 0) :
    (10 : ℚ) ^ 5 * (((10 : ℚ) ^ 1 - 1) * (ca n : ℚ) + 1) = (901000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + 1 * m := ⟨(n - 5) / 1, by omega⟩
  exact cf0 m


/-- a(n) = 11*a(n-1) - 10*a(n-2) for n > 3. [n range correction -/
theorem recurrence0 (n : ℕ) (hn : 4 ≤ n) : (ca n : ℤ) = (((11 : ℤ) * (ca (n - 1) : ℤ)) - ((10 : ℤ) * (ca (n - 2) : ℤ))) := by
  rcases Nat.lt_or_ge n 7 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7] at *
  · suffices hq : (ca n : ℚ) = (((11 : ℚ) * (ca (n - 1) : ℚ)) - ((10 : ℚ) * (ca (n - 2) : ℚ))) by exact_mod_cast hq
    obtain ⟨q, rfl⟩ : ∃ q, n = 7 + q := ⟨n - 7, by omega⟩
    have c0 := cfn0 (7 + q) (by omega) (by omega)
    rw [show 7 + q - 1 = 6 + q by omega]
    have c1 := cfn0 (6 + q) (by omega) (by omega)
    rw [show 7 + q - 2 = 5 + q by omega]
    have c2 := cfn0 (5 + q) (by omega) (by omega)
    try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c1 c2 ⊢
    push_cast at c0 c1 c2 ⊢
    linear_combination (1 / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 1 - 1))) * c0 + (-((11 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 1 - 1))) * c1 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 1 - 1))) * c2


lemma gfrec1 (n : ℕ) (hn : 4 ≤ n) : (ca n : ℚ) = ((11 : ℚ)) * (ca (n - 1) : ℚ) + ((-10 : ℚ)) * (ca (n - 2) : ℚ) := by
  rcases Nat.lt_or_ge n 7 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7] at *
  · obtain ⟨q, rfl⟩ : ∃ q, n = 7 + q := ⟨n - 7, by omega⟩
    have c0 := cfn0 (7 + q) (by omega) (by omega)
    rw [show 7 + q - 1 = 6 + q by omega]
    have c1 := cfn0 (6 + q) (by omega) (by omega)
    rw [show 7 + q - 2 = 5 + q by omega]
    have c2 := cfn0 (5 + q) (by omega) (by omega)
    try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c1 c2 ⊢
    push_cast at c0 c1 c2 ⊢
    linear_combination (1 / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 1 - 1))) * c0 + (-((11 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 1 - 1))) * c1 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 1 - 1))) * c2

open PowerSeries in
/-- G.f.: (1-x+x^3) / ((1-x)*(1-10*x)) -/
theorem gf1 : PowerSeries.mk (fun n => (ca n : ℚ)) = ((1-X+X ^ 3)) * (((1-X)*(1-10*X)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1-X)*(1-10*X))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X)*(1-10*X))) = C ((1 : ℚ)) * G + C ((-11 : ℚ)) * (G * X ^ 1) + C ((10 : ℚ)) * (G * X ^ 2) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1-X+X ^ 3)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((-1 : ℚ)) * X ^ 1 + C ((1 : ℚ)) * X ^ 3 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X)*(1-10*X))) = (1-X+X ^ 3) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec1 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 4 ≤ n → (ca n : ℤ) = (((11 : ℤ) * (ca (n - 1) : ℤ)) - ((10 : ℤ) * (ca (n - 2) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (ca n : ℚ)) = ((1-X+X ^ 3)) * (((1-X)*(1-10*X)))⁻¹) :=
  ⟨recurrence0, gf1⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 139 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 139 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 139 (state 139 t) i
    rw [ih, rule_eq]
    rfl

theorem a_eq_ca : a = ca := by
  funext n
  rw [a, ca]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [c, ← cstate_eq]
  cases cstate k 0 <;> simp

theorem controls : ∀ n ≤ 16, a n = ([1, 10, 100, 1001, 10011, 100111, 1001111, 10011111, 100111111, 1001111111, 10011111111, 100111111111, 1001111111111, 10011111111111, 100111111111111, 1001111111111111, 10011111111111111] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    A = (1 - X + X ^ 3) * ((1 - X) * (1 - 10 * X))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨fun n hn => (recurrence0 n (by omega)).trans (by ring),
    gf1⟩

end OMA.S_oeis_a267524

theorem OMA.solution : type_of% @OMA.S_oeis_a267524.main :=
  OMA.S_oeis_a267524.conj
