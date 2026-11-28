import OMAStatements.S_oeis_a267209

namespace OMA.S_oeis_a267209


/-- Rule 109 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (109 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A267209(n): the states of cell 0 in rows `0..n` (row 0 first) as binary digits read in base 10. -/
def ca (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), if cstate t 0 then 10 ^ (n - t) else 0


/-! ## A finite certificate: rows `0..40` on the window `[-41, 41]` -/

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

def W : ℕ := 41

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

/-- The rows `0..40`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 2199023255552),
    (true, 9671406556911535839510527),
    (false, 17042430230528),
    (true, 9671406556891469752303615),
    (false, 64733747085312),
    (true, 9671406556828728870043647),
    (false, 273744035577856),
    (true, 9671406556506417344282623),
    (false, 1037586789302272),
    (true, 9671406555501940457865215),
    (false, 4374473583099904),
    (true, 9671406550354773267185663),
    (false, 16599305032826880),
    (true, 9671406534269910021832703),
    (false, 69998934474358784),
    (true, 9671406451919147082186751),
    (false, 265583252742340608),
    (true, 9671406194570403694772223),
    (false, 1119981212388032512),
    (true, 9671404876945247027855359),
    (false, 4249339388722413568),
    (true, 9671400759369218147745791),
    (false, 17919693791950274560),
    (true, 9671379677375797729689599),
    (false, 67989428479588171776),
    (true, 9671313796146383090810879),
    (false, 286715108017394647040),
    (true, 9670976484255522827583487),
    (false, 1087830850067104456704),
    (true, 9669922384593974675353599),
    (false, 4587441726538427987968),
    (true, 9664525394327257975786495),
    (false, 17405293608419858558464),
    (true, 9647659799746353954355967),
    (false, 73399067619008546770816),
    (true, 9561307955487972835436735),
    (false, 278484697732977850383072),
    (true, 9291458442180556003905455),
    (false, 1174385081911482935912696),
    (true, 7909828934050324515715723),
    (false, 4455755163722039305080750)]

lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    ∀ t < 40, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 40) :
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

/-! ## The regime from row 40 on -/

def bgT : List Bool := [false, true, false, true, false, true, false, true, false, true, false, true]
def elT : List ℕ := [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2]
def erT : List ℕ := [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2]
def coT : List ℕ := [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0]
def flLT : List ℕ := [2004, 2298, 1311, 3747, 2004, 2298, 1311, 3747, 2004, 2298, 1311, 3747]
def flRT : List ℕ := [2004, 2298, 1311, 3747, 2004, 2298, 1311, 3747, 2004, 2298, 1311, 3747]

def V (t : ℕ) (i : ℤ) : Bool :=
  if i < -(t : ℤ) ∨ (t : ℤ) < i then bgT.getD ((t - 40) % 12) false
  else if i + t ≤ 1 then (elT.getD ((t - 40) % 12) 0).testBit (i + t).toNat
  else if (t : ℤ) - i ≤ 1 then (erT.getD ((t - 40) % 12) 0).testBit ((t : ℤ) - i).toNat
  else if -(0 : ℤ) ≤ i ∧ i ≤ 0 then (coT.getD ((t - 40) % 12) 0).testBit (i + 0).toNat
  else if i < 0 then (flLT.getD ((t - 40) % 12) 0).testBit ((i + t) % 12).toNat
  else (flRT.getD ((t - 40) % 12) 0).testBit (((t : ℤ) - i) % 12).toNat

lemma V_out (t : ℕ) (i : ℤ) (h : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    V t i = bgT.getD ((t - 40) % 12) false := by
  unfold V; rw [if_pos h]

lemma V_el (t : ℕ) (ht : 40 ≤ t) (i : ℤ) (j : ℕ) (hj : i + t = j) (hjA : j ≤ 1) :
    V t i = (elT.getD ((t - 40) % 12) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_er (t : ℕ) (ht : 40 ≤ t) (i : ℤ) (j : ℕ) (hj : (t : ℤ) - i = j) (hjA : j ≤ 1) :
    V t i = (erT.getD ((t - 40) % 12) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_co (t : ℕ) (ht : 40 ≤ t) (i : ℤ) (m : ℕ) (hm : i + 0 = m) (hmK : m ≤ 2 * 0) :
    V t i = (coT.getD ((t - 40) % 12) 0).testBit m := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_fll (t : ℕ) (ht : 40 ≤ t) (i : ℤ) (s : ℕ) (hs : (i + t) % 12 = s)
    (h1 : (1 : ℤ) < i + t) (h3 : i < -(0 : ℤ)) :
    V t i = (flLT.getD ((t - 40) % 12) 0).testBit s := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_flr (t : ℕ) (ht : 40 ≤ t) (i : ℤ) (s : ℕ) (hs : ((t : ℤ) - i) % 12 = s)
    (h2 : (1 : ℤ) < (t : ℤ) - i) (h3 : (0 : ℤ) < i) :
    V t i = (flRT.getD ((t - 40) % 12) 0).testBit s := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega


set_option maxHeartbeats 16000000 in
lemma stepV (t : ℕ) (ht : 40 ≤ t) (i : ℤ) :
    rule (V t (i - 1)) (V t i) (V t (i + 1)) = V (t + 1) i := by
  obtain ⟨q, hq, hqq⟩ : ∃ q, q < 12 ∧ (t - 40) % 12 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
  have hq1 : (t + 1 - 40) % 12 = (q + 1) % 12 := by omega
  interval_cases q
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 3 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ (i + t + 1) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 10 (by omega) (by omega) (by omega), V_fll t ht i 11 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 11 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 4 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 4 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 5 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 4 (by omega) (by omega) (by omega), V_fll t ht i 5 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 6 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 5 (by omega) (by omega) (by omega), V_fll t ht i 6 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 7 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 6 (by omega) (by omega) (by omega), V_fll t ht i 7 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 8 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 7 (by omega) (by omega) (by omega), V_fll t ht i 8 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 9 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 8 (by omega) (by omega) (by omega), V_fll t ht i 9 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 10 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 9 (by omega) (by omega) (by omega), V_fll t ht i 10 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 11 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 12 ∧ ((t : ℤ) + 1 - i) % 12 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 11 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 10 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 11 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 4 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 4 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 5 (by omega) (by omega) (by omega), V_flr t ht i 4 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 5 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 6 (by omega) (by omega) (by omega), V_flr t ht i 5 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 4 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 6 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 7 (by omega) (by omega) (by omega), V_flr t ht i 6 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 5 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 7 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 8 (by omega) (by omega) (by omega), V_flr t ht i 7 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 6 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 8 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 9 (by omega) (by omega) (by omega), V_flr t ht i 8 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 7 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 9 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 10 (by omega) (by omega) (by omega), V_flr t ht i 9 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 8 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 10 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 11 (by omega) (by omega) (by omega), V_flr t ht i 10 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 9 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 11 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide

lemma base_ok : (∀ j < 2 * W + 1, decode (stages.getD 40 default) ((j : ℤ) - W) = V 40 ((j : ℤ) - W)) ∧
    (stages.getD 40 default).1 = bgT.getD 0 false := by
  decide +kernel

lemma pattern (t : ℕ) (ht : 40 ≤ t) : ∀ i, cstate t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(certified 40 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 40 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 40) : sim t = cstate t := funext fun i => ((certified t ht).2 i).symm

lemma state_eq_V (t : ℕ) (ht : 40 ≤ t) : cstate t = V t := funext (pattern t ht)

def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 40 then sim t else V t

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

/-- The values a(0..68); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 68, ca n = ([1, 11, 111, 1110, 11101, 111011, 1110110, 11101101, 111011011, 1110110110, 11101101101, 111011011011, 1110110110110, 11101101101101, 111011011011011, 1110110110110110, 11101101101101101, 111011011011011011, 1110110110110110110, 11101101101101101101, 111011011011011011011, 1110110110110110110110, 11101101101101101101101, 111011011011011011011011, 1110110110110110110110110, 11101101101101101101101101, 111011011011011011011011011, 1110110110110110110110110110, 11101101101101101101101101101, 111011011011011011011011011011, 1110110110110110110110110110110, 11101101101101101101101101101101, 111011011011011011011011011011011, 1110110110110110110110110110110110, 11101101101101101101101101101101101, 111011011011011011011011011011011011, 1110110110110110110110110110110110110, 11101101101101101101101101101101101101, 111011011011011011011011011011011011011, 1110110110110110110110110110110110110110, 11101101101101101101101101101101101101101, 111011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011011011011] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 11 := vals 1 (by norm_num)
lemma v2 : ca 2 = 111 := vals 2 (by norm_num)
lemma v3 : ca 3 = 1110 := vals 3 (by norm_num)
lemma v4 : ca 4 = 11101 := vals 4 (by norm_num)
lemma v5 : ca 5 = 111011 := vals 5 (by norm_num)
lemma v6 : ca 6 = 1110110 := vals 6 (by norm_num)
lemma v7 : ca 7 = 11101101 := vals 7 (by norm_num)
lemma v8 : ca 8 = 111011011 := vals 8 (by norm_num)
lemma v9 : ca 9 = 1110110110 := vals 9 (by norm_num)
lemma v10 : ca 10 = 11101101101 := vals 10 (by norm_num)
lemma v11 : ca 11 = 111011011011 := vals 11 (by norm_num)
lemma v12 : ca 12 = 1110110110110 := vals 12 (by norm_num)
lemma v13 : ca 13 = 11101101101101 := vals 13 (by norm_num)
lemma v14 : ca 14 = 111011011011011 := vals 14 (by norm_num)
lemma v15 : ca 15 = 1110110110110110 := vals 15 (by norm_num)
lemma v16 : ca 16 = 11101101101101101 := vals 16 (by norm_num)
lemma v17 : ca 17 = 111011011011011011 := vals 17 (by norm_num)
lemma v18 : ca 18 = 1110110110110110110 := vals 18 (by norm_num)
lemma v19 : ca 19 = 11101101101101101101 := vals 19 (by norm_num)
lemma v20 : ca 20 = 111011011011011011011 := vals 20 (by norm_num)
lemma v21 : ca 21 = 1110110110110110110110 := vals 21 (by norm_num)
lemma v22 : ca 22 = 11101101101101101101101 := vals 22 (by norm_num)
lemma v23 : ca 23 = 111011011011011011011011 := vals 23 (by norm_num)
lemma v24 : ca 24 = 1110110110110110110110110 := vals 24 (by norm_num)
lemma v25 : ca 25 = 11101101101101101101101101 := vals 25 (by norm_num)
lemma v26 : ca 26 = 111011011011011011011011011 := vals 26 (by norm_num)
lemma v27 : ca 27 = 1110110110110110110110110110 := vals 27 (by norm_num)
lemma v28 : ca 28 = 11101101101101101101101101101 := vals 28 (by norm_num)
lemma v29 : ca 29 = 111011011011011011011011011011 := vals 29 (by norm_num)
lemma v30 : ca 30 = 1110110110110110110110110110110 := vals 30 (by norm_num)
lemma v31 : ca 31 = 11101101101101101101101101101101 := vals 31 (by norm_num)
lemma v32 : ca 32 = 111011011011011011011011011011011 := vals 32 (by norm_num)
lemma v33 : ca 33 = 1110110110110110110110110110110110 := vals 33 (by norm_num)
lemma v34 : ca 34 = 11101101101101101101101101101101101 := vals 34 (by norm_num)
lemma v35 : ca 35 = 111011011011011011011011011011011011 := vals 35 (by norm_num)
lemma v36 : ca 36 = 1110110110110110110110110110110110110 := vals 36 (by norm_num)
lemma v37 : ca 37 = 11101101101101101101101101101101101101 := vals 37 (by norm_num)
lemma v38 : ca 38 = 111011011011011011011011011011011011011 := vals 38 (by norm_num)
lemma v39 : ca 39 = 1110110110110110110110110110110110110110 := vals 39 (by norm_num)
lemma v40 : ca 40 = 11101101101101101101101101101101101101101 := vals 40 (by norm_num)
lemma v41 : ca 41 = 111011011011011011011011011011011011011011 := vals 41 (by norm_num)
lemma v42 : ca 42 = 1110110110110110110110110110110110110110110 := vals 42 (by norm_num)
lemma v43 : ca 43 = 11101101101101101101101101101101101101101101 := vals 43 (by norm_num)
lemma v44 : ca 44 = 111011011011011011011011011011011011011011011 := vals 44 (by norm_num)
lemma v45 : ca 45 = 1110110110110110110110110110110110110110110110 := vals 45 (by norm_num)
lemma v46 : ca 46 = 11101101101101101101101101101101101101101101101 := vals 46 (by norm_num)
lemma v47 : ca 47 = 111011011011011011011011011011011011011011011011 := vals 47 (by norm_num)
lemma v48 : ca 48 = 1110110110110110110110110110110110110110110110110 := vals 48 (by norm_num)
lemma v49 : ca 49 = 11101101101101101101101101101101101101101101101101 := vals 49 (by norm_num)
lemma v50 : ca 50 = 111011011011011011011011011011011011011011011011011 := vals 50 (by norm_num)
lemma v51 : ca 51 = 1110110110110110110110110110110110110110110110110110 := vals 51 (by norm_num)
lemma v52 : ca 52 = 11101101101101101101101101101101101101101101101101101 := vals 52 (by norm_num)
lemma v53 : ca 53 = 111011011011011011011011011011011011011011011011011011 := vals 53 (by norm_num)
lemma v54 : ca 54 = 1110110110110110110110110110110110110110110110110110110 := vals 54 (by norm_num)
lemma v55 : ca 55 = 11101101101101101101101101101101101101101101101101101101 := vals 55 (by norm_num)
lemma v56 : ca 56 = 111011011011011011011011011011011011011011011011011011011 := vals 56 (by norm_num)
lemma v57 : ca 57 = 1110110110110110110110110110110110110110110110110110110110 := vals 57 (by norm_num)
lemma v58 : ca 58 = 11101101101101101101101101101101101101101101101101101101101 := vals 58 (by norm_num)
lemma v59 : ca 59 = 111011011011011011011011011011011011011011011011011011011011 := vals 59 (by norm_num)
lemma v60 : ca 60 = 1110110110110110110110110110110110110110110110110110110110110 := vals 60 (by norm_num)
lemma v61 : ca 61 = 11101101101101101101101101101101101101101101101101101101101101 := vals 61 (by norm_num)
lemma v62 : ca 62 = 111011011011011011011011011011011011011011011011011011011011011 := vals 62 (by norm_num)
lemma v63 : ca 63 = 1110110110110110110110110110110110110110110110110110110110110110 := vals 63 (by norm_num)
lemma v64 : ca 64 = 11101101101101101101101101101101101101101101101101101101101101101 := vals 64 (by norm_num)
lemma v65 : ca 65 = 111011011011011011011011011011011011011011011011011011011011011011 := vals 65 (by norm_num)
lemma v66 : ca 66 = 1110110110110110110110110110110110110110110110110110110110110110110 := vals 66 (by norm_num)
lemma v67 : ca 67 = 11101101101101101101101101101101101101101101101101101101101101101101 := vals 67 (by norm_num)
lemma v68 : ca 68 = 111011011011011011011011011011011011011011011011011011011011011011011 := vals 68 (by norm_num)

lemma rel (n : ℕ) :
    ca (n + 12) = 10 ^ 12 * ca n + ∑ j ∈ Finset.range 12, (if cstate (n + 1 + j) 0 then 10 ^ (12 - 1 - j) else 0) := by
  unfold ca
  rw [show n + 12 + 1 = (n + 1) + 12 by ring, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : d < n + 1 := Finset.mem_range.mp hd
    split_ifs
    · rw [← pow_add]; congr 1; omega
    · simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [show n + 12 - (n + 1 + j) = 12 - 1 - j by omega]

lemma colv (t : ℕ) (ht : 40 ≤ t) : cstate t 0 = (coT.getD ((t - 40) % 12) 0).testBit 0 := by
  rw [state_eq_V t ht, V_co t ht 0 0 (by norm_num) (by norm_num)]


lemma cf0 (m : ℕ) : (10 : ℚ) ^ 48 * (((10 : ℚ) ^ 12 - 1) * (ca (48 + 12 * m) : ℚ) + 110110110110) =
    (1110110110109000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (48 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 48 + 12 * 0 = 48 by ring, v48]
    norm_num
  | succ m ih =>
    rw [show 48 + 12 * (m + 1) = (48 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (48 + 12 * m + 1 + 0) (by omega), show (48 + 12 * m + 1 + 0 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 1) (by omega), show (48 + 12 * m + 1 + 1 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 2) (by omega), show (48 + 12 * m + 1 + 2 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (48 + 12 * m + 1 + 3) (by omega), show (48 + 12 * m + 1 + 3 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 4) (by omega), show (48 + 12 * m + 1 + 4 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 5) (by omega), show (48 + 12 * m + 1 + 5 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (48 + 12 * m + 1 + 6) (by omega), show (48 + 12 * m + 1 + 6 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 7) (by omega), show (48 + 12 * m + 1 + 7 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 8) (by omega), show (48 + 12 * m + 1 + 8 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (48 + 12 * m + 1 + 9) (by omega), show (48 + 12 * m + 1 + 9 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 10) (by omega), show (48 + 12 * m + 1 + 10 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (48 + 12 * m + 1 + 11) (by omega), show (48 + 12 * m + 1 + 11 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn0 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 0) :
    (10 : ℚ) ^ 48 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 110110110110) = (1110110110109000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 48 + 12 * m := ⟨(n - 48) / 12, by omega⟩
  exact cf0 m


lemma cf1 (m : ℕ) : (10 : ℚ) ^ 49 * (((10 : ℚ) ^ 12 - 1) * (ca (49 + 12 * m) : ℚ) + 101101101101) =
    (11101101101090000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (49 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 49 + 12 * 0 = 49 by ring, v49]
    norm_num
  | succ m ih =>
    rw [show 49 + 12 * (m + 1) = (49 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (49 + 12 * m + 1 + 0) (by omega), show (49 + 12 * m + 1 + 0 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (49 + 12 * m + 1 + 1) (by omega), show (49 + 12 * m + 1 + 1 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (49 + 12 * m + 1 + 2) (by omega), show (49 + 12 * m + 1 + 2 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (49 + 12 * m + 1 + 3) (by omega), show (49 + 12 * m + 1 + 3 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (49 + 12 * m + 1 + 4) (by omega), show (49 + 12 * m + 1 + 4 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (49 + 12 * m + 1 + 5) (by omega), show (49 + 12 * m + 1 + 5 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (49 + 12 * m + 1 + 6) (by omega), show (49 + 12 * m + 1 + 6 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (49 + 12 * m + 1 + 7) (by omega), show (49 + 12 * m + 1 + 7 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (49 + 12 * m + 1 + 8) (by omega), show (49 + 12 * m + 1 + 8 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (49 + 12 * m + 1 + 9) (by omega), show (49 + 12 * m + 1 + 9 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (49 + 12 * m + 1 + 10) (by omega), show (49 + 12 * m + 1 + 10 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (49 + 12 * m + 1 + 11) (by omega), show (49 + 12 * m + 1 + 11 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn1 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 1) :
    (10 : ℚ) ^ 49 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 101101101101) = (11101101101090000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 49 + 12 * m := ⟨(n - 49) / 12, by omega⟩
  exact cf1 m


lemma cf2 (m : ℕ) : (10 : ℚ) ^ 50 * (((10 : ℚ) ^ 12 - 1) * (ca (50 + 12 * m) : ℚ) + 11011011011) =
    (111011011010900000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (50 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 50 + 12 * 0 = 50 by ring, v50]
    norm_num
  | succ m ih =>
    rw [show 50 + 12 * (m + 1) = (50 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (50 + 12 * m + 1 + 0) (by omega), show (50 + 12 * m + 1 + 0 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (50 + 12 * m + 1 + 1) (by omega), show (50 + 12 * m + 1 + 1 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (50 + 12 * m + 1 + 2) (by omega), show (50 + 12 * m + 1 + 2 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (50 + 12 * m + 1 + 3) (by omega), show (50 + 12 * m + 1 + 3 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (50 + 12 * m + 1 + 4) (by omega), show (50 + 12 * m + 1 + 4 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (50 + 12 * m + 1 + 5) (by omega), show (50 + 12 * m + 1 + 5 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (50 + 12 * m + 1 + 6) (by omega), show (50 + 12 * m + 1 + 6 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (50 + 12 * m + 1 + 7) (by omega), show (50 + 12 * m + 1 + 7 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (50 + 12 * m + 1 + 8) (by omega), show (50 + 12 * m + 1 + 8 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (50 + 12 * m + 1 + 9) (by omega), show (50 + 12 * m + 1 + 9 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (50 + 12 * m + 1 + 10) (by omega), show (50 + 12 * m + 1 + 10 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (50 + 12 * m + 1 + 11) (by omega), show (50 + 12 * m + 1 + 11 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn2 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 2) :
    (10 : ℚ) ^ 50 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 11011011011) = (111011011010900000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 50 + 12 * m := ⟨(n - 50) / 12, by omega⟩
  exact cf2 m


lemma cf3 (m : ℕ) : (10 : ℚ) ^ 51 * (((10 : ℚ) ^ 12 - 1) * (ca (51 + 12 * m) : ℚ) + 110110110110) =
    (1110110110109000000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (51 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 51 + 12 * 0 = 51 by ring, v51]
    norm_num
  | succ m ih =>
    rw [show 51 + 12 * (m + 1) = (51 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (51 + 12 * m + 1 + 0) (by omega), show (51 + 12 * m + 1 + 0 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 1) (by omega), show (51 + 12 * m + 1 + 1 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 2) (by omega), show (51 + 12 * m + 1 + 2 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (51 + 12 * m + 1 + 3) (by omega), show (51 + 12 * m + 1 + 3 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 4) (by omega), show (51 + 12 * m + 1 + 4 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 5) (by omega), show (51 + 12 * m + 1 + 5 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (51 + 12 * m + 1 + 6) (by omega), show (51 + 12 * m + 1 + 6 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 7) (by omega), show (51 + 12 * m + 1 + 7 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 8) (by omega), show (51 + 12 * m + 1 + 8 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (51 + 12 * m + 1 + 9) (by omega), show (51 + 12 * m + 1 + 9 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 10) (by omega), show (51 + 12 * m + 1 + 10 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (51 + 12 * m + 1 + 11) (by omega), show (51 + 12 * m + 1 + 11 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn3 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 3) :
    (10 : ℚ) ^ 51 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 110110110110) = (1110110110109000000000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 51 + 12 * m := ⟨(n - 51) / 12, by omega⟩
  exact cf3 m


lemma cf4 (m : ℕ) : (10 : ℚ) ^ 40 * (((10 : ℚ) ^ 12 - 1) * (ca (40 + 12 * m) : ℚ) + 101101101101) =
    (11101101101090000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (40 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 40 + 12 * 0 = 40 by ring, v40]
    norm_num
  | succ m ih =>
    rw [show 40 + 12 * (m + 1) = (40 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (40 + 12 * m + 1 + 0) (by omega), show (40 + 12 * m + 1 + 0 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (40 + 12 * m + 1 + 1) (by omega), show (40 + 12 * m + 1 + 1 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (40 + 12 * m + 1 + 2) (by omega), show (40 + 12 * m + 1 + 2 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (40 + 12 * m + 1 + 3) (by omega), show (40 + 12 * m + 1 + 3 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (40 + 12 * m + 1 + 4) (by omega), show (40 + 12 * m + 1 + 4 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (40 + 12 * m + 1 + 5) (by omega), show (40 + 12 * m + 1 + 5 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (40 + 12 * m + 1 + 6) (by omega), show (40 + 12 * m + 1 + 6 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (40 + 12 * m + 1 + 7) (by omega), show (40 + 12 * m + 1 + 7 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (40 + 12 * m + 1 + 8) (by omega), show (40 + 12 * m + 1 + 8 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (40 + 12 * m + 1 + 9) (by omega), show (40 + 12 * m + 1 + 9 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (40 + 12 * m + 1 + 10) (by omega), show (40 + 12 * m + 1 + 10 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (40 + 12 * m + 1 + 11) (by omega), show (40 + 12 * m + 1 + 11 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn4 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 4) :
    (10 : ℚ) ^ 40 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 101101101101) = (11101101101090000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 40 + 12 * m := ⟨(n - 40) / 12, by omega⟩
  exact cf4 m


lemma cf5 (m : ℕ) : (10 : ℚ) ^ 41 * (((10 : ℚ) ^ 12 - 1) * (ca (41 + 12 * m) : ℚ) + 11011011011) =
    (111011011010900000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (41 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 41 + 12 * 0 = 41 by ring, v41]
    norm_num
  | succ m ih =>
    rw [show 41 + 12 * (m + 1) = (41 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (41 + 12 * m + 1 + 0) (by omega), show (41 + 12 * m + 1 + 0 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (41 + 12 * m + 1 + 1) (by omega), show (41 + 12 * m + 1 + 1 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (41 + 12 * m + 1 + 2) (by omega), show (41 + 12 * m + 1 + 2 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (41 + 12 * m + 1 + 3) (by omega), show (41 + 12 * m + 1 + 3 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (41 + 12 * m + 1 + 4) (by omega), show (41 + 12 * m + 1 + 4 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (41 + 12 * m + 1 + 5) (by omega), show (41 + 12 * m + 1 + 5 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (41 + 12 * m + 1 + 6) (by omega), show (41 + 12 * m + 1 + 6 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (41 + 12 * m + 1 + 7) (by omega), show (41 + 12 * m + 1 + 7 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (41 + 12 * m + 1 + 8) (by omega), show (41 + 12 * m + 1 + 8 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (41 + 12 * m + 1 + 9) (by omega), show (41 + 12 * m + 1 + 9 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (41 + 12 * m + 1 + 10) (by omega), show (41 + 12 * m + 1 + 10 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (41 + 12 * m + 1 + 11) (by omega), show (41 + 12 * m + 1 + 11 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn5 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 5) :
    (10 : ℚ) ^ 41 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 11011011011) = (111011011010900000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 41 + 12 * m := ⟨(n - 41) / 12, by omega⟩
  exact cf5 m


lemma cf6 (m : ℕ) : (10 : ℚ) ^ 42 * (((10 : ℚ) ^ 12 - 1) * (ca (42 + 12 * m) : ℚ) + 110110110110) =
    (1110110110109000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (42 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 42 + 12 * 0 = 42 by ring, v42]
    norm_num
  | succ m ih =>
    rw [show 42 + 12 * (m + 1) = (42 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (42 + 12 * m + 1 + 0) (by omega), show (42 + 12 * m + 1 + 0 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 1) (by omega), show (42 + 12 * m + 1 + 1 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 2) (by omega), show (42 + 12 * m + 1 + 2 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (42 + 12 * m + 1 + 3) (by omega), show (42 + 12 * m + 1 + 3 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 4) (by omega), show (42 + 12 * m + 1 + 4 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 5) (by omega), show (42 + 12 * m + 1 + 5 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (42 + 12 * m + 1 + 6) (by omega), show (42 + 12 * m + 1 + 6 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 7) (by omega), show (42 + 12 * m + 1 + 7 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 8) (by omega), show (42 + 12 * m + 1 + 8 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (42 + 12 * m + 1 + 9) (by omega), show (42 + 12 * m + 1 + 9 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 10) (by omega), show (42 + 12 * m + 1 + 10 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (42 + 12 * m + 1 + 11) (by omega), show (42 + 12 * m + 1 + 11 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn6 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 6) :
    (10 : ℚ) ^ 42 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 110110110110) = (1110110110109000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 42 + 12 * m := ⟨(n - 42) / 12, by omega⟩
  exact cf6 m


lemma cf7 (m : ℕ) : (10 : ℚ) ^ 43 * (((10 : ℚ) ^ 12 - 1) * (ca (43 + 12 * m) : ℚ) + 101101101101) =
    (11101101101090000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (43 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 43 + 12 * 0 = 43 by ring, v43]
    norm_num
  | succ m ih =>
    rw [show 43 + 12 * (m + 1) = (43 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (43 + 12 * m + 1 + 0) (by omega), show (43 + 12 * m + 1 + 0 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (43 + 12 * m + 1 + 1) (by omega), show (43 + 12 * m + 1 + 1 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (43 + 12 * m + 1 + 2) (by omega), show (43 + 12 * m + 1 + 2 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (43 + 12 * m + 1 + 3) (by omega), show (43 + 12 * m + 1 + 3 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (43 + 12 * m + 1 + 4) (by omega), show (43 + 12 * m + 1 + 4 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (43 + 12 * m + 1 + 5) (by omega), show (43 + 12 * m + 1 + 5 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (43 + 12 * m + 1 + 6) (by omega), show (43 + 12 * m + 1 + 6 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (43 + 12 * m + 1 + 7) (by omega), show (43 + 12 * m + 1 + 7 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (43 + 12 * m + 1 + 8) (by omega), show (43 + 12 * m + 1 + 8 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (43 + 12 * m + 1 + 9) (by omega), show (43 + 12 * m + 1 + 9 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (43 + 12 * m + 1 + 10) (by omega), show (43 + 12 * m + 1 + 10 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (43 + 12 * m + 1 + 11) (by omega), show (43 + 12 * m + 1 + 11 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn7 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 7) :
    (10 : ℚ) ^ 43 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 101101101101) = (11101101101090000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 43 + 12 * m := ⟨(n - 43) / 12, by omega⟩
  exact cf7 m


lemma cf8 (m : ℕ) : (10 : ℚ) ^ 44 * (((10 : ℚ) ^ 12 - 1) * (ca (44 + 12 * m) : ℚ) + 11011011011) =
    (111011011010900000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (44 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 44 + 12 * 0 = 44 by ring, v44]
    norm_num
  | succ m ih =>
    rw [show 44 + 12 * (m + 1) = (44 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (44 + 12 * m + 1 + 0) (by omega), show (44 + 12 * m + 1 + 0 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (44 + 12 * m + 1 + 1) (by omega), show (44 + 12 * m + 1 + 1 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (44 + 12 * m + 1 + 2) (by omega), show (44 + 12 * m + 1 + 2 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (44 + 12 * m + 1 + 3) (by omega), show (44 + 12 * m + 1 + 3 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (44 + 12 * m + 1 + 4) (by omega), show (44 + 12 * m + 1 + 4 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (44 + 12 * m + 1 + 5) (by omega), show (44 + 12 * m + 1 + 5 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (44 + 12 * m + 1 + 6) (by omega), show (44 + 12 * m + 1 + 6 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (44 + 12 * m + 1 + 7) (by omega), show (44 + 12 * m + 1 + 7 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (44 + 12 * m + 1 + 8) (by omega), show (44 + 12 * m + 1 + 8 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (44 + 12 * m + 1 + 9) (by omega), show (44 + 12 * m + 1 + 9 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (44 + 12 * m + 1 + 10) (by omega), show (44 + 12 * m + 1 + 10 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (44 + 12 * m + 1 + 11) (by omega), show (44 + 12 * m + 1 + 11 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn8 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 8) :
    (10 : ℚ) ^ 44 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 11011011011) = (111011011010900000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 44 + 12 * m := ⟨(n - 44) / 12, by omega⟩
  exact cf8 m


lemma cf9 (m : ℕ) : (10 : ℚ) ^ 45 * (((10 : ℚ) ^ 12 - 1) * (ca (45 + 12 * m) : ℚ) + 110110110110) =
    (1110110110109000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (45 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 45 + 12 * 0 = 45 by ring, v45]
    norm_num
  | succ m ih =>
    rw [show 45 + 12 * (m + 1) = (45 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (45 + 12 * m + 1 + 0) (by omega), show (45 + 12 * m + 1 + 0 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 1) (by omega), show (45 + 12 * m + 1 + 1 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 2) (by omega), show (45 + 12 * m + 1 + 2 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (45 + 12 * m + 1 + 3) (by omega), show (45 + 12 * m + 1 + 3 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 4) (by omega), show (45 + 12 * m + 1 + 4 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 5) (by omega), show (45 + 12 * m + 1 + 5 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (45 + 12 * m + 1 + 6) (by omega), show (45 + 12 * m + 1 + 6 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 7) (by omega), show (45 + 12 * m + 1 + 7 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 8) (by omega), show (45 + 12 * m + 1 + 8 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (45 + 12 * m + 1 + 9) (by omega), show (45 + 12 * m + 1 + 9 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 10) (by omega), show (45 + 12 * m + 1 + 10 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (45 + 12 * m + 1 + 11) (by omega), show (45 + 12 * m + 1 + 11 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn9 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 9) :
    (10 : ℚ) ^ 45 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 110110110110) = (1110110110109000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 45 + 12 * m := ⟨(n - 45) / 12, by omega⟩
  exact cf9 m


lemma cf10 (m : ℕ) : (10 : ℚ) ^ 46 * (((10 : ℚ) ^ 12 - 1) * (ca (46 + 12 * m) : ℚ) + 101101101101) =
    (11101101101090000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (46 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 46 + 12 * 0 = 46 by ring, v46]
    norm_num
  | succ m ih =>
    rw [show 46 + 12 * (m + 1) = (46 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (46 + 12 * m + 1 + 0) (by omega), show (46 + 12 * m + 1 + 0 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    rw [colv (46 + 12 * m + 1 + 1) (by omega), show (46 + 12 * m + 1 + 1 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (46 + 12 * m + 1 + 2) (by omega), show (46 + 12 * m + 1 + 2 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (46 + 12 * m + 1 + 3) (by omega), show (46 + 12 * m + 1 + 3 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (46 + 12 * m + 1 + 4) (by omega), show (46 + 12 * m + 1 + 4 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (46 + 12 * m + 1 + 5) (by omega), show (46 + 12 * m + 1 + 5 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (46 + 12 * m + 1 + 6) (by omega), show (46 + 12 * m + 1 + 6 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (46 + 12 * m + 1 + 7) (by omega), show (46 + 12 * m + 1 + 7 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (46 + 12 * m + 1 + 8) (by omega), show (46 + 12 * m + 1 + 8 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (46 + 12 * m + 1 + 9) (by omega), show (46 + 12 * m + 1 + 9 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (46 + 12 * m + 1 + 10) (by omega), show (46 + 12 * m + 1 + 10 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (46 + 12 * m + 1 + 11) (by omega), show (46 + 12 * m + 1 + 11 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn10 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 10) :
    (10 : ℚ) ^ 46 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 101101101101) = (11101101101090000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 46 + 12 * m := ⟨(n - 46) / 12, by omega⟩
  exact cf10 m


lemma cf11 (m : ℕ) : (10 : ℚ) ^ 47 * (((10 : ℚ) ^ 12 - 1) * (ca (47 + 12 * m) : ℚ) + 11011011011) =
    (111011011010900000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ (47 + 12 * m) := by
  induction m with
  | zero =>
    rw [show 47 + 12 * 0 = 47 by ring, v47]
    norm_num
  | succ m ih =>
    rw [show 47 + 12 * (m + 1) = (47 + 12 * m) + 12 by ring, rel]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [colv (47 + 12 * m + 1 + 0) (by omega), show (47 + 12 * m + 1 + 0 - 40) % 12 = 8 by omega, show (coT.getD 8 0).testBit 0 = false from by decide]
    rw [colv (47 + 12 * m + 1 + 1) (by omega), show (47 + 12 * m + 1 + 1 - 40) % 12 = 9 by omega, show (coT.getD 9 0).testBit 0 = true from by decide]
    rw [colv (47 + 12 * m + 1 + 2) (by omega), show (47 + 12 * m + 1 + 2 - 40) % 12 = 10 by omega, show (coT.getD 10 0).testBit 0 = true from by decide]
    rw [colv (47 + 12 * m + 1 + 3) (by omega), show (47 + 12 * m + 1 + 3 - 40) % 12 = 11 by omega, show (coT.getD 11 0).testBit 0 = false from by decide]
    rw [colv (47 + 12 * m + 1 + 4) (by omega), show (47 + 12 * m + 1 + 4 - 40) % 12 = 0 by omega, show (coT.getD 0 0).testBit 0 = true from by decide]
    rw [colv (47 + 12 * m + 1 + 5) (by omega), show (47 + 12 * m + 1 + 5 - 40) % 12 = 1 by omega, show (coT.getD 1 0).testBit 0 = true from by decide]
    rw [colv (47 + 12 * m + 1 + 6) (by omega), show (47 + 12 * m + 1 + 6 - 40) % 12 = 2 by omega, show (coT.getD 2 0).testBit 0 = false from by decide]
    rw [colv (47 + 12 * m + 1 + 7) (by omega), show (47 + 12 * m + 1 + 7 - 40) % 12 = 3 by omega, show (coT.getD 3 0).testBit 0 = true from by decide]
    rw [colv (47 + 12 * m + 1 + 8) (by omega), show (47 + 12 * m + 1 + 8 - 40) % 12 = 4 by omega, show (coT.getD 4 0).testBit 0 = true from by decide]
    rw [colv (47 + 12 * m + 1 + 9) (by omega), show (47 + 12 * m + 1 + 9 - 40) % 12 = 5 by omega, show (coT.getD 5 0).testBit 0 = false from by decide]
    rw [colv (47 + 12 * m + 1 + 10) (by omega), show (47 + 12 * m + 1 + 10 - 40) % 12 = 6 by omega, show (coT.getD 6 0).testBit 0 = true from by decide]
    rw [colv (47 + 12 * m + 1 + 11) (by omega), show (47 + 12 * m + 1 + 11 - 40) % 12 = 7 by omega, show (coT.getD 7 0).testBit 0 = true from by decide]
    simp only [↓reduceIte, Bool.false_eq_true]
    push_cast at ih ⊢
    try simp only [Nat.reduceSub, Nat.reduceAdd]
    linear_combination (10 : ℚ) ^ 12 * ih

lemma cfn11 (n : ℕ) (h1 : 40 ≤ n) (h2 : n % 12 = 11) :
    (10 : ℚ) ^ 47 * (((10 : ℚ) ^ 12 - 1) * (ca n : ℚ) + 11011011011) = (111011011010900000000000000000000000000000000000000000000000 : ℚ) * (10 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 47 + 12 * m := ⟨(n - 47) / 12, by omega⟩
  exact cf11 m


/-- a(n) = 10*a(n-1)+a(n-3)-10*a(n-4) for n>3 -/
theorem recurrence0 (n : ℕ) (hn : 4 ≤ n) : (ca n : ℤ) = ((((10 : ℤ) * (ca (n - 1) : ℤ)) + (ca (n - 3) : ℤ)) - ((10 : ℤ) * (ca (n - 4) : ℤ))) := by
  rcases Nat.lt_or_ge n 44 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44] at *
  · suffices hq : (ca n : ℚ) = ((((10 : ℚ) * (ca (n - 1) : ℚ)) + (ca (n - 3) : ℚ)) - ((10 : ℚ) * (ca (n - 4) : ℚ))) by exact_mod_cast hq
    rcases (by omega : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 5 ∨ n % 12 = 6 ∨ n % 12 = 7 ∨ n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11) with hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 48 + 12 * q := ⟨(n - 48) / 12, by omega⟩
      have c0 := cfn0 (48 + 12 * q) (by omega) (by omega)
      rw [show 48 + 12 * q - 1 = 47 + 12 * q by omega]
      have c1 := cfn11 (47 + 12 * q) (by omega) (by omega)
      rw [show 48 + 12 * q - 3 = 45 + 12 * q by omega]
      have c3 := cfn9 (45 + 12 * q) (by omega) (by omega)
      rw [show 48 + 12 * q - 4 = 44 + 12 * q by omega]
      have c4 := cfn8 (44 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 49 + 12 * q := ⟨(n - 49) / 12, by omega⟩
      have c0 := cfn1 (49 + 12 * q) (by omega) (by omega)
      rw [show 49 + 12 * q - 1 = 48 + 12 * q by omega]
      have c1 := cfn0 (48 + 12 * q) (by omega) (by omega)
      rw [show 49 + 12 * q - 3 = 46 + 12 * q by omega]
      have c3 := cfn10 (46 + 12 * q) (by omega) (by omega)
      rw [show 49 + 12 * q - 4 = 45 + 12 * q by omega]
      have c4 := cfn9 (45 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 50 + 12 * q := ⟨(n - 50) / 12, by omega⟩
      have c0 := cfn2 (50 + 12 * q) (by omega) (by omega)
      rw [show 50 + 12 * q - 1 = 49 + 12 * q by omega]
      have c1 := cfn1 (49 + 12 * q) (by omega) (by omega)
      rw [show 50 + 12 * q - 3 = 47 + 12 * q by omega]
      have c3 := cfn11 (47 + 12 * q) (by omega) (by omega)
      rw [show 50 + 12 * q - 4 = 46 + 12 * q by omega]
      have c4 := cfn10 (46 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 51 + 12 * q := ⟨(n - 51) / 12, by omega⟩
      have c0 := cfn3 (51 + 12 * q) (by omega) (by omega)
      rw [show 51 + 12 * q - 1 = 50 + 12 * q by omega]
      have c1 := cfn2 (50 + 12 * q) (by omega) (by omega)
      rw [show 51 + 12 * q - 3 = 48 + 12 * q by omega]
      have c3 := cfn0 (48 + 12 * q) (by omega) (by omega)
      rw [show 51 + 12 * q - 4 = 47 + 12 * q by omega]
      have c4 := cfn11 (47 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 52 + 12 * q := ⟨(n - 52) / 12, by omega⟩
      have c0 := cfn4 (52 + 12 * q) (by omega) (by omega)
      rw [show 52 + 12 * q - 1 = 51 + 12 * q by omega]
      have c1 := cfn3 (51 + 12 * q) (by omega) (by omega)
      rw [show 52 + 12 * q - 3 = 49 + 12 * q by omega]
      have c3 := cfn1 (49 + 12 * q) (by omega) (by omega)
      rw [show 52 + 12 * q - 4 = 48 + 12 * q by omega]
      have c4 := cfn0 (48 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 53 + 12 * q := ⟨(n - 53) / 12, by omega⟩
      have c0 := cfn5 (53 + 12 * q) (by omega) (by omega)
      rw [show 53 + 12 * q - 1 = 52 + 12 * q by omega]
      have c1 := cfn4 (52 + 12 * q) (by omega) (by omega)
      rw [show 53 + 12 * q - 3 = 50 + 12 * q by omega]
      have c3 := cfn2 (50 + 12 * q) (by omega) (by omega)
      rw [show 53 + 12 * q - 4 = 49 + 12 * q by omega]
      have c4 := cfn1 (49 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 54 + 12 * q := ⟨(n - 54) / 12, by omega⟩
      have c0 := cfn6 (54 + 12 * q) (by omega) (by omega)
      rw [show 54 + 12 * q - 1 = 53 + 12 * q by omega]
      have c1 := cfn5 (53 + 12 * q) (by omega) (by omega)
      rw [show 54 + 12 * q - 3 = 51 + 12 * q by omega]
      have c3 := cfn3 (51 + 12 * q) (by omega) (by omega)
      rw [show 54 + 12 * q - 4 = 50 + 12 * q by omega]
      have c4 := cfn2 (50 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 55 + 12 * q := ⟨(n - 55) / 12, by omega⟩
      have c0 := cfn7 (55 + 12 * q) (by omega) (by omega)
      rw [show 55 + 12 * q - 1 = 54 + 12 * q by omega]
      have c1 := cfn6 (54 + 12 * q) (by omega) (by omega)
      rw [show 55 + 12 * q - 3 = 52 + 12 * q by omega]
      have c3 := cfn4 (52 + 12 * q) (by omega) (by omega)
      rw [show 55 + 12 * q - 4 = 51 + 12 * q by omega]
      have c4 := cfn3 (51 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 44 + 12 * q := ⟨(n - 44) / 12, by omega⟩
      have c0 := cfn8 (44 + 12 * q) (by omega) (by omega)
      rw [show 44 + 12 * q - 1 = 43 + 12 * q by omega]
      have c1 := cfn7 (43 + 12 * q) (by omega) (by omega)
      rw [show 44 + 12 * q - 3 = 41 + 12 * q by omega]
      have c3 := cfn5 (41 + 12 * q) (by omega) (by omega)
      rw [show 44 + 12 * q - 4 = 40 + 12 * q by omega]
      have c4 := cfn4 (40 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 45 + 12 * q := ⟨(n - 45) / 12, by omega⟩
      have c0 := cfn9 (45 + 12 * q) (by omega) (by omega)
      rw [show 45 + 12 * q - 1 = 44 + 12 * q by omega]
      have c1 := cfn8 (44 + 12 * q) (by omega) (by omega)
      rw [show 45 + 12 * q - 3 = 42 + 12 * q by omega]
      have c3 := cfn6 (42 + 12 * q) (by omega) (by omega)
      rw [show 45 + 12 * q - 4 = 41 + 12 * q by omega]
      have c4 := cfn5 (41 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 46 + 12 * q := ⟨(n - 46) / 12, by omega⟩
      have c0 := cfn10 (46 + 12 * q) (by omega) (by omega)
      rw [show 46 + 12 * q - 1 = 45 + 12 * q by omega]
      have c1 := cfn9 (45 + 12 * q) (by omega) (by omega)
      rw [show 46 + 12 * q - 3 = 43 + 12 * q by omega]
      have c3 := cfn7 (43 + 12 * q) (by omega) (by omega)
      rw [show 46 + 12 * q - 4 = 42 + 12 * q by omega]
      have c4 := cfn6 (42 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 47 + 12 * q := ⟨(n - 47) / 12, by omega⟩
      have c0 := cfn11 (47 + 12 * q) (by omega) (by omega)
      rw [show 47 + 12 * q - 1 = 46 + 12 * q by omega]
      have c1 := cfn10 (46 + 12 * q) (by omega) (by omega)
      rw [show 47 + 12 * q - 3 = 44 + 12 * q by omega]
      have c3 := cfn8 (44 + 12 * q) (by omega) (by omega)
      rw [show 47 + 12 * q - 4 = 43 + 12 * q by omega]
      have c4 := cfn7 (43 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c4


lemma gfrec1 (n : ℕ) (hn : 4 ≤ n) : (ca n : ℚ) = ((10 : ℚ)) * (ca (n - 1) : ℚ) + ((1 : ℚ)) * (ca (n - 3) : ℚ) + ((-10 : ℚ)) * (ca (n - 4) : ℚ) := by
  rcases Nat.lt_or_ge n 44 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44] at *
  · rcases (by omega : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 5 ∨ n % 12 = 6 ∨ n % 12 = 7 ∨ n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11) with hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 48 + 12 * q := ⟨(n - 48) / 12, by omega⟩
      have c0 := cfn0 (48 + 12 * q) (by omega) (by omega)
      rw [show 48 + 12 * q - 1 = 47 + 12 * q by omega]
      have c1 := cfn11 (47 + 12 * q) (by omega) (by omega)
      rw [show 48 + 12 * q - 3 = 45 + 12 * q by omega]
      have c3 := cfn9 (45 + 12 * q) (by omega) (by omega)
      rw [show 48 + 12 * q - 4 = 44 + 12 * q by omega]
      have c4 := cfn8 (44 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 49 + 12 * q := ⟨(n - 49) / 12, by omega⟩
      have c0 := cfn1 (49 + 12 * q) (by omega) (by omega)
      rw [show 49 + 12 * q - 1 = 48 + 12 * q by omega]
      have c1 := cfn0 (48 + 12 * q) (by omega) (by omega)
      rw [show 49 + 12 * q - 3 = 46 + 12 * q by omega]
      have c3 := cfn10 (46 + 12 * q) (by omega) (by omega)
      rw [show 49 + 12 * q - 4 = 45 + 12 * q by omega]
      have c4 := cfn9 (45 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 50 + 12 * q := ⟨(n - 50) / 12, by omega⟩
      have c0 := cfn2 (50 + 12 * q) (by omega) (by omega)
      rw [show 50 + 12 * q - 1 = 49 + 12 * q by omega]
      have c1 := cfn1 (49 + 12 * q) (by omega) (by omega)
      rw [show 50 + 12 * q - 3 = 47 + 12 * q by omega]
      have c3 := cfn11 (47 + 12 * q) (by omega) (by omega)
      rw [show 50 + 12 * q - 4 = 46 + 12 * q by omega]
      have c4 := cfn10 (46 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 51 + 12 * q := ⟨(n - 51) / 12, by omega⟩
      have c0 := cfn3 (51 + 12 * q) (by omega) (by omega)
      rw [show 51 + 12 * q - 1 = 50 + 12 * q by omega]
      have c1 := cfn2 (50 + 12 * q) (by omega) (by omega)
      rw [show 51 + 12 * q - 3 = 48 + 12 * q by omega]
      have c3 := cfn0 (48 + 12 * q) (by omega) (by omega)
      rw [show 51 + 12 * q - 4 = 47 + 12 * q by omega]
      have c4 := cfn11 (47 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 52 + 12 * q := ⟨(n - 52) / 12, by omega⟩
      have c0 := cfn4 (52 + 12 * q) (by omega) (by omega)
      rw [show 52 + 12 * q - 1 = 51 + 12 * q by omega]
      have c1 := cfn3 (51 + 12 * q) (by omega) (by omega)
      rw [show 52 + 12 * q - 3 = 49 + 12 * q by omega]
      have c3 := cfn1 (49 + 12 * q) (by omega) (by omega)
      rw [show 52 + 12 * q - 4 = 48 + 12 * q by omega]
      have c4 := cfn0 (48 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 48 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 53 + 12 * q := ⟨(n - 53) / 12, by omega⟩
      have c0 := cfn5 (53 + 12 * q) (by omega) (by omega)
      rw [show 53 + 12 * q - 1 = 52 + 12 * q by omega]
      have c1 := cfn4 (52 + 12 * q) (by omega) (by omega)
      rw [show 53 + 12 * q - 3 = 50 + 12 * q by omega]
      have c3 := cfn2 (50 + 12 * q) (by omega) (by omega)
      rw [show 53 + 12 * q - 4 = 49 + 12 * q by omega]
      have c4 := cfn1 (49 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 49 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 54 + 12 * q := ⟨(n - 54) / 12, by omega⟩
      have c0 := cfn6 (54 + 12 * q) (by omega) (by omega)
      rw [show 54 + 12 * q - 1 = 53 + 12 * q by omega]
      have c1 := cfn5 (53 + 12 * q) (by omega) (by omega)
      rw [show 54 + 12 * q - 3 = 51 + 12 * q by omega]
      have c3 := cfn3 (51 + 12 * q) (by omega) (by omega)
      rw [show 54 + 12 * q - 4 = 50 + 12 * q by omega]
      have c4 := cfn2 (50 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 50 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 55 + 12 * q := ⟨(n - 55) / 12, by omega⟩
      have c0 := cfn7 (55 + 12 * q) (by omega) (by omega)
      rw [show 55 + 12 * q - 1 = 54 + 12 * q by omega]
      have c1 := cfn6 (54 + 12 * q) (by omega) (by omega)
      rw [show 55 + 12 * q - 3 = 52 + 12 * q by omega]
      have c3 := cfn4 (52 + 12 * q) (by omega) (by omega)
      rw [show 55 + 12 * q - 4 = 51 + 12 * q by omega]
      have c4 := cfn3 (51 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 51 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 44 + 12 * q := ⟨(n - 44) / 12, by omega⟩
      have c0 := cfn8 (44 + 12 * q) (by omega) (by omega)
      rw [show 44 + 12 * q - 1 = 43 + 12 * q by omega]
      have c1 := cfn7 (43 + 12 * q) (by omega) (by omega)
      rw [show 44 + 12 * q - 3 = 41 + 12 * q by omega]
      have c3 := cfn5 (41 + 12 * q) (by omega) (by omega)
      rw [show 44 + 12 * q - 4 = 40 + 12 * q by omega]
      have c4 := cfn4 (40 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 40 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 45 + 12 * q := ⟨(n - 45) / 12, by omega⟩
      have c0 := cfn9 (45 + 12 * q) (by omega) (by omega)
      rw [show 45 + 12 * q - 1 = 44 + 12 * q by omega]
      have c1 := cfn8 (44 + 12 * q) (by omega) (by omega)
      rw [show 45 + 12 * q - 3 = 42 + 12 * q by omega]
      have c3 := cfn6 (42 + 12 * q) (by omega) (by omega)
      rw [show 45 + 12 * q - 4 = 41 + 12 * q by omega]
      have c4 := cfn5 (41 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 41 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 46 + 12 * q := ⟨(n - 46) / 12, by omega⟩
      have c0 := cfn10 (46 + 12 * q) (by omega) (by omega)
      rw [show 46 + 12 * q - 1 = 45 + 12 * q by omega]
      have c1 := cfn9 (45 + 12 * q) (by omega) (by omega)
      rw [show 46 + 12 * q - 3 = 43 + 12 * q by omega]
      have c3 := cfn7 (43 + 12 * q) (by omega) (by omega)
      rw [show 46 + 12 * q - 4 = 42 + 12 * q by omega]
      have c4 := cfn6 (42 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 45 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 42 * ((10 : ℚ) ^ 12 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 47 + 12 * q := ⟨(n - 47) / 12, by omega⟩
      have c0 := cfn11 (47 + 12 * q) (by omega) (by omega)
      rw [show 47 + 12 * q - 1 = 46 + 12 * q by omega]
      have c1 := cfn10 (46 + 12 * q) (by omega) (by omega)
      rw [show 47 + 12 * q - 3 = 44 + 12 * q by omega]
      have c3 := cfn8 (44 + 12 * q) (by omega) (by omega)
      rw [show 47 + 12 * q - 4 = 43 + 12 * q by omega]
      have c4 := cfn7 (43 + 12 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (12 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c3 c4 ⊢
      push_cast at c0 c1 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 47 * ((10 : ℚ) ^ 12 - 1))) * c0 + (-((10 : ℚ)) / ((10 : ℚ) ^ 46 * ((10 : ℚ) ^ 12 - 1))) * c1 + (-((1 : ℚ)) / ((10 : ℚ) ^ 44 * ((10 : ℚ) ^ 12 - 1))) * c3 + (-((-10 : ℚ)) / ((10 : ℚ) ^ 43 * ((10 : ℚ) ^ 12 - 1))) * c4

open PowerSeries in
/-- G.f.: (1+x+x^2-x^3) / ((1-x)*(1-10*x)*(1+x+x^2)) -/
theorem gf1 : PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+X+X ^ 2-X ^ 3)) * (((1-X)*(1-10*X)*(1+X+X ^ 2)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1-X)*(1-10*X)*(1+X+X ^ 2))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X)*(1-10*X)*(1+X+X ^ 2))) = C ((1 : ℚ)) * G + C ((-10 : ℚ)) * (G * X ^ 1) + C ((-1 : ℚ)) * (G * X ^ 3) + C ((10 : ℚ)) * (G * X ^ 4) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1+X+X ^ 2-X ^ 3)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((1 : ℚ)) * X ^ 1 + C ((1 : ℚ)) * X ^ 2 + C ((-1 : ℚ)) * X ^ 3 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X)*(1-10*X)*(1+X+X ^ 2))) = (1+X+X ^ 2-X ^ 3) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec1 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 4 ≤ n → (ca n : ℤ) = ((((10 : ℤ) * (ca (n - 1) : ℤ)) + (ca (n - 3) : ℤ)) - ((10 : ℤ) * (ca (n - 4) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+X+X ^ 2-X ^ 3)) * (((1-X)*(1-10*X)*(1+X+X ^ 2)))⁻¹) :=
  ⟨recurrence0, gf1⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 109 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 109 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 109 (state 109 t) i
    rw [ih, rule_eq]
    rfl

theorem a_eq_ca : a = ca := by
  funext n
  rw [a, ca]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [c, ← cstate_eq]
  cases cstate k 0 <;> simp

theorem controls : ∀ n ≤ 68, a n = ([1, 11, 111, 1110, 11101, 111011, 1110110, 11101101, 111011011, 1110110110, 11101101101, 111011011011, 1110110110110, 11101101101101, 111011011011011, 1110110110110110, 11101101101101101, 111011011011011011, 1110110110110110110, 11101101101101101101, 111011011011011011011, 1110110110110110110110, 11101101101101101101101, 111011011011011011011011, 1110110110110110110110110, 11101101101101101101101101, 111011011011011011011011011, 1110110110110110110110110110, 11101101101101101101101101101, 111011011011011011011011011011, 1110110110110110110110110110110, 11101101101101101101101101101101, 111011011011011011011011011011011, 1110110110110110110110110110110110, 11101101101101101101101101101101101, 111011011011011011011011011011011011, 1110110110110110110110110110110110110, 11101101101101101101101101101101101101, 111011011011011011011011011011011011011, 1110110110110110110110110110110110110110, 11101101101101101101101101101101101101101, 111011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011011011, 1110110110110110110110110110110110110110110110110110110110110110110, 11101101101101101101101101101101101101101101101101101101101101101101, 111011011011011011011011011011011011011011011011011011011011011011011] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 3) - 10 * a (n - 4)) ∧
    A = (1 + X + X ^ 2 - X ^ 3) * ((1 - X) * (1 - 10 * X) * (1 + X + X ^ 2))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨fun n hn => (recurrence0 n (by omega)).trans (by ring),
    gf1⟩

end OMA.S_oeis_a267209

theorem OMA.solution : type_of% @OMA.S_oeis_a267209.main :=
  OMA.S_oeis_a267209.conj
