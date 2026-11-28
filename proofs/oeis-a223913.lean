import OMAStatements.S_oeis_a223913

namespace A223913
open OMA.S_oeis_a223913
open Classical

abbrev Row := Fin 3 → Fin 3
abbrev T := Fin 3 × Fin 3 × Fin 3

def toRow (t : T) : Row := ![t.1, t.2.1, t.2.2]
def ofRow (r : Row) : T := (r 0, r 1, r 2)

theorem toRow_ofRow (r : Row) : toRow (ofRow r) = r := by
  funext i
  fin_cases i <;> rfl

def rowEquiv : Row ≃ T where
  toFun := ofRow
  invFun := toRow
  left_inv := toRow_ofRow
  right_inv := fun _ => rfl

def lineB (t : T) : Bool := !(decide (t.2.1 < t.1) && decide (t.2.1 < t.2.2))

def okB (b : Bool) (v w : T) : Bool :=
  lineB w && (decide (v.1 ≤ w.1) && (decide (v.2.1 ≤ w.2.1) && (decide (v.2.2 ≤ w.2.2) &&
    !(b && decide (v.2.1 < w.1)))))

def flagB (v w : T) : Bool := decide (w.2.1 < v.2.2)

def allT : List T :=
  [(0, 0, 0), (1, 0, 0), (2, 0, 0), (0, 1, 0), (1, 1, 0), (2, 1, 0), (0, 2, 0), (1, 2, 0), (2, 2, 0),
   (0, 0, 1), (1, 0, 1), (2, 0, 1), (0, 1, 1), (1, 1, 1), (2, 1, 1), (0, 2, 1), (1, 2, 1), (2, 2, 1),
   (0, 0, 2), (1, 0, 2), (2, 0, 2), (0, 1, 2), (1, 1, 2), (2, 1, 2), (0, 2, 2), (1, 2, 2), (2, 2, 2)]

def cntT : ℕ → Bool → T → ℕ
  | 0, _, _ => 1
  | n + 1, b, v => (allT.map (fun w => if okB b v w then cntT n (flagB v w) w else 0)).sum

theorem sumT (g : T → ℕ) : ∑ t : T, g t = (allT.map g).sum := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, allT, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

instance lineDec : DecidablePred LineOK := fun u => by
  unfold LineOK
  infer_instance

theorem lineT : ∀ t : T, LineOK (toRow t) ↔ lineB t = true := by
  decide

theorem lineOK_iff (w : Row) : LineOK w ↔ lineB (ofRow w) = true := by
  have h := lineT (ofRow w)
  rw [toRow_ofRow] at h
  exact h

theorem blockOK_iff (v w : Row) : BlockOK v w ↔ v 0 ≤ w 0 ∧ v 1 ≤ w 1 ∧ v 2 ≤ w 2 := by
  unfold BlockOK
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2

theorem okB_iff (u v w : Row) :
    okB (decide (v 1 < u 2)) (ofRow v) (ofRow w) = true ↔ LineOK w ∧ BlockOK v w ∧ TriOK u v w := by
  rw [lineOK_iff, blockOK_iff]
  unfold okB TriOK
  simp only [ofRow, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, ⟨of_decide_eq_true h2, of_decide_eq_true h3, of_decide_eq_true h4⟩, ?_⟩
    rintro ⟨h6, h7⟩
    rcases h5 with h5 | h5
    · exact h5 h6
    · exact (of_decide_eq_false h5) h7
  · rintro ⟨h1, ⟨h2, h3, h4⟩, h5⟩
    refine ⟨h1, decide_eq_true h2, decide_eq_true h3, decide_eq_true h4, ?_⟩
    by_cases h6 : v 1 < u 2
    · right
      exact decide_eq_false (fun h7 => h5 ⟨h6, h7⟩)
    · left
      exact h6

/-- Prepending a row. -/
theorem good_cons0 {m : ℕ} (u : Row) (y : Fin m → Row) :
    Good (Fin.cons (α := fun _ => Row) u y) ↔
      LineOK u ∧ (∀ j : Fin m, (j : ℕ) = 0 → BlockOK u (y j)) ∧
        (∀ j l : Fin m, (j : ℕ) = 0 → (l : ℕ) = 1 → TriOK u (y j) (y l)) ∧ Good y := by
  constructor
  · rintro ⟨hl, hb, ht⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hl 0
    · intro j hj
      have h := hb 0 j.succ (by simp [hj])
      simpa using h
    · intro j l hj hl'
      have h := ht 0 j.succ l.succ (by simp [hj]) (by simp [hj, hl'])
      simpa using h
    · intro i
      simpa using hl i.succ
    · intro i j h
      have h' := hb i.succ j.succ (by simp [h])
      simpa using h'
    · intro i j l h1 h2
      have h' := ht i.succ j.succ l.succ (by simp [h1]) (by simp [h2])
      simpa using h'
  · rintro ⟨hu, hb0, ht0, hl, hb, ht⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using hu
      · simpa using hl i'
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro h
      · simp at h
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact hb0 j' (by simpa using h)
      · simp at h
      · simp only [Fin.cons_succ]
        exact hb i' j' (by simpa using h)
    · intro i j l
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        refine Fin.cases ?_ (fun l' => ?_) l <;> intro h1 h2
      · simp at h1
      · simp at h1
      · simp at h2
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact ht0 j' l' (by simpa using h1) (by simp at h1 h2; omega)
      · simp at h1
      · simp at h1
      · simp at h2
      · simp only [Fin.cons_succ]
        exact ht i' j' l' (by simpa using h1) (by simpa using h2)

def zr : Row := fun _ => 0

theorem line_zr : LineOK zr := by
  rw [lineOK_iff]
  rfl

theorem good_cons_z {n : ℕ} (x : Fin n → Row) :
    Good (Fin.cons (α := fun _ => Row) zr x) ↔ Good x := by
  rw [good_cons0]
  constructor
  · intro h
    exact h.2.2.2
  · intro h
    refine ⟨line_zr, ?_, ?_, h⟩
    · intro j _ k
      exact Fin.zero_le _
    · intro j l _ _ hcon
      exact absurd hcon.1 (Fin.not_lt_zero _)

def ext2 (u v : Row) {n : ℕ} (x : Fin n → Row) : Fin (n + 2) → Row :=
  Fin.cons (α := fun _ => Row) u (Fin.cons (α := fun _ => Row) v x)

theorem good_ext2_cons {n : ℕ} (u v w : Row) (x : Fin n → Row) :
    Good (ext2 u v (Fin.cons (α := fun _ => Row) w x)) ↔
      LineOK u ∧ BlockOK u v ∧ TriOK u v w ∧ Good (ext2 v w x) := by
  unfold ext2
  rw [good_cons0]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · simpa using h2 0 rfl
    · simpa using h3 0 1 rfl rfl
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · intro j hj
      have e : j = 0 := Fin.ext hj
      subst e
      simpa using h2
    · intro j l hj hl
      have e : j = 0 := Fin.ext hj
      have e' : l = 1 := Fin.ext hl
      subst e e'
      simpa using h3

theorem good_ext2_head {n : ℕ} (v w : Row) (x : Fin n → Row) (h : Good (ext2 v w x)) :
    LineOK w ∧ BlockOK v w := by
  unfold ext2 at h
  rw [good_cons0] at h
  obtain ⟨_, h2, _, h4⟩ := h
  rw [good_cons0] at h4
  refine ⟨h4.1, ?_⟩
  simpa using h2 0 rfl

theorem good_ext2_nil (u v : Row) (x : Fin 0 → Row) (hu : LineOK u) (hv : LineOK v)
    (hb : BlockOK u v) : Good (ext2 u v x) := by
  unfold ext2
  rw [good_cons0, good_cons0]
  refine ⟨hu, ?_, ?_, hv, ?_, ?_, ?_⟩
  · intro j hj
    have e : j = 0 := Fin.ext hj
    subst e
    simpa using hb
  · intro j l hj hl
    exfalso
    have := l.isLt
    omega
  · intro j
    exact j.elim0
  · intro j
    exact j.elim0
  · exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

def consE (n : ℕ) : (Fin (n + 1) → Row) ≃ Row × (Fin n → Row) where
  toFun x := (x 0, Fin.tail x)
  invFun p := Fin.cons (α := fun _ => Row) p.1 p.2
  left_inv x := Fin.cons_self_tail x
  right_inv p := by simp

theorem card_ext (n : ℕ) : ∀ (u v : Row), LineOK u → LineOK v → BlockOK u v →
    Fintype.card {x : Fin n → Row // Good (ext2 u v x)} =
      cntT n (decide (v 1 < u 2)) (ofRow v) := by
  induction n with
  | zero =>
    intro u v hu hv hb
    rw [cntT, Fintype.card_eq_one_iff]
    refine ⟨⟨fun i => i.elim0, good_ext2_nil u v _ hu hv hb⟩, ?_⟩
    rintro ⟨x, hx⟩
    apply Subtype.ext
    funext i
    exact i.elim0
  | succ n ih =>
    intro u v hu hv hb
    have e : {x : Fin (n + 1) → Row // Good (ext2 u v x)} ≃
        Σ w : Row, {x' : Fin n → Row // Good (ext2 u v (Fin.cons (α := fun _ => Row) w x'))} :=
      ((consE n).subtypeEquiv (q := fun p : Row × (Fin n → Row) =>
          Good (ext2 u v (Fin.cons (α := fun _ => Row) p.1 p.2)))
        (fun x => by
          show Good (ext2 u v x) ↔
            Good (ext2 u v (Fin.cons (α := fun _ => Row) (x 0) (Fin.tail x)))
          rw [Fin.cons_self_tail])).trans
        (Equiv.subtypeProdEquivSigmaSubtype
          (fun (w : Row) (x' : Fin n → Row) =>
            Good (ext2 u v (Fin.cons (α := fun _ => Row) w x'))))
    rw [Fintype.card_congr e, Fintype.card_sigma, cntT, ← sumT, ← Equiv.sum_comp rowEquiv]
    apply Finset.sum_congr rfl
    intro w _
    show _ = if okB (decide (v 1 < u 2)) (ofRow v) (ofRow w) then
      cntT n (flagB (ofRow v) (ofRow w)) (ofRow w) else 0
    by_cases hok : LineOK w ∧ BlockOK v w ∧ TriOK u v w
    · rw [if_pos ((okB_iff u v w).2 hok)]
      have e2 : {x' : Fin n → Row // Good (ext2 u v (Fin.cons (α := fun _ => Row) w x'))} ≃
          {x' : Fin n → Row // Good (ext2 v w x')} :=
        Equiv.subtypeEquivRight (fun x' => by
          rw [good_ext2_cons]
          exact ⟨fun h => h.2.2.2, fun h => ⟨hu, hb, hok.2.2, h⟩⟩)
      rw [Fintype.card_congr e2, ih v w hv hok.1 hok.2.1]
      rfl
    · rw [if_neg (fun h => hok ((okB_iff u v w).1 h))]
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun x' => ?_⟩
      have h := (good_ext2_cons u v w x'.1).1 x'.2
      have h2 := good_ext2_head v w x'.1 h.2.2.2
      exact hok ⟨h2.1, h2.2, h.2.2.1⟩

theorem a_eq (n : ℕ) : a n = cntT n false (0, 0, 0) := by
  unfold a
  have e : {x : Fin n → Fin 3 → Fin 3 // Good x} ≃ {x : Fin n → Row // Good (ext2 zr zr x)} :=
    Equiv.subtypeEquivRight (fun x => by
      unfold ext2
      rw [good_cons_z, good_cons_z])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card,
    card_ext n zr zr line_zr line_zr (fun j => le_refl _)]
  rfl

def code (t : T) : ℕ := t.1.val + 3 * t.2.1.val + 9 * t.2.2.val

def tab : List (List ℕ) :=
  [[22, 136, 372, 565, 490, 230, 46], [13, 53, 101, 101, 52, 11, 0], [6, 14, 16, 9, 2, 0, 0],
   [17, 81, 172, 188, 105, 24, 0], [11, 36, 51, 34, 9, 0, 0], [5, 9, 7, 2, 0, 0, 0],
   [9, 27, 37, 24, 6, 0, 0], [6, 12, 10, 3, 0, 0, 0], [3, 3, 1, 0, 0, 0, 0],
   [13, 43, 77, 80, 45, 11, 0], [], [],
   [11, 36, 49, 33, 9, 0, 0], [7, 15, 12, 4, 0, 0, 0], [3, 3, 1, 0, 0, 0, 0],
   [6, 12, 10, 3, 0, 0, 0], [4, 5, 2, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0],
   [6, 9, 11, 7, 2, 0, 0], [], [],
   [5, 7, 6, 2, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [],
   [3, 3, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
   [9, 83, 271, 464, 438, 219, 46], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0],
   [12, 72, 165, 186, 105, 24, 0], [6, 27, 44, 32, 9, 0, 0], [0, 0, 0, 0, 0, 0, 0],
   [9, 27, 37, 24, 6, 0, 0], [6, 12, 10, 3, 0, 0, 0], [3, 3, 1, 0, 0, 0, 0],
   [6, 28, 65, 76, 45, 11, 0], [], [],
   [8, 33, 48, 33, 9, 0, 0], [4, 12, 11, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0],
   [6, 12, 10, 3, 0, 0, 0], [4, 5, 2, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0],
   [3, 7, 10, 7, 2, 0, 0], [], [],
   [4, 7, 6, 2, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [],
   [3, 3, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]]

def c (k : ℕ) (b : Bool) (t : T) : ℕ := (tab.getD (cond b 27 0 + code t) []).getD k 0

set_option maxRecDepth 100000 in
theorem star : ∀ b : Bool, ∀ t : T, lineB t = true → ∀ k : Fin 7,
    (allT.map (fun w => if okB b t w then c k (flagB t w) w else 0)).sum =
      c k b t + c (k + 1) b t := by
  decide

set_option maxRecDepth 100000 in
theorem base : ∀ b : Bool, ∀ t : T, lineB t = true → cntT 1 b t = c 0 b t := by
  decide

theorem c7 : ∀ b : Bool, ∀ t : T, c 7 b t = 0 := by
  decide

theorem okB_line (b : Bool) (v w : T) (h : okB b v w = true) : lineB w = true := by
  unfold okB at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem lin7 (l : List T) (p : T → Bool) (f : ℕ → T → ℕ) (a1 a2 a3 a4 a5 a6 : ℕ) :
    (l.map (fun w => if p w then f 0 w + a1 * f 1 w + a2 * f 2 w + a3 * f 3 w + a4 * f 4 w
      + a5 * f 5 w + a6 * f 6 w else 0)).sum =
    (l.map (fun w => if p w then f 0 w else 0)).sum
      + a1 * (l.map (fun w => if p w then f 1 w else 0)).sum
      + a2 * (l.map (fun w => if p w then f 2 w else 0)).sum
      + a3 * (l.map (fun w => if p w then f 3 w else 0)).sum
      + a4 * (l.map (fun w => if p w then f 4 w else 0)).sum
      + a5 * (l.map (fun w => if p w then f 5 w else 0)).sum
      + a6 * (l.map (fun w => if p w then f 6 w else 0)).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    by_cases h : p w
    · simp only [h, if_true]
      ring
    · simp only [h]
      simp

theorem closed (n : ℕ) : ∀ (b : Bool) (t : T), lineB t = true →
    cntT (n + 1) b t = c 0 b t + n.choose 1 * c 1 b t + n.choose 2 * c 2 b t
      + n.choose 3 * c 3 b t + n.choose 4 * c 4 b t + n.choose 5 * c 5 b t
      + n.choose 6 * c 6 b t := by
  induction n with
  | zero =>
    intro b t ht
    rw [base b t ht]
    simp
  | succ n ih =>
    intro b t ht
    have h1 : cntT (n + 1 + 1) b t =
        (allT.map (fun w => if okB b t w then
          c 0 (flagB t w) w + n.choose 1 * c 1 (flagB t w) w + n.choose 2 * c 2 (flagB t w) w
          + n.choose 3 * c 3 (flagB t w) w + n.choose 4 * c 4 (flagB t w) w
          + n.choose 5 * c 5 (flagB t w) w + n.choose 6 * c 6 (flagB t w) w else 0)).sum := by
      rw [cntT]
      refine congrArg List.sum ?_
      apply List.map_congr_left
      intro w _
      by_cases h : okB b t w = true
      · rw [if_pos h, if_pos h]
        exact ih (flagB t w) w (okB_line b t w h)
      · rw [if_neg h, if_neg h]
    have h2 := lin7 allT (fun w => okB b t w) (fun k w => c k (flagB t w) w) (n.choose 1)
      (n.choose 2) (n.choose 3) (n.choose 4) (n.choose 5) (n.choose 6)
    beta_reduce at h2
    rw [h1, h2]
    have s0 : (allT.map (fun w => if okB b t w then c 0 (flagB t w) w else 0)).sum
      = c 0 b t + c 1 b t := star b t ht ⟨0, by norm_num⟩
    have s1 : (allT.map (fun w => if okB b t w then c 1 (flagB t w) w else 0)).sum
      = c 1 b t + c 2 b t := star b t ht ⟨1, by norm_num⟩
    have s2 : (allT.map (fun w => if okB b t w then c 2 (flagB t w) w else 0)).sum
      = c 2 b t + c 3 b t := star b t ht ⟨2, by norm_num⟩
    have s3 : (allT.map (fun w => if okB b t w then c 3 (flagB t w) w else 0)).sum
      = c 3 b t + c 4 b t := star b t ht ⟨3, by norm_num⟩
    have s4 : (allT.map (fun w => if okB b t w then c 4 (flagB t w) w else 0)).sum
      = c 4 b t + c 5 b t := star b t ht ⟨4, by norm_num⟩
    have s5 : (allT.map (fun w => if okB b t w then c 5 (flagB t w) w else 0)).sum
      = c 5 b t + c 6 b t := star b t ht ⟨5, by norm_num⟩
    have s6 : (allT.map (fun w => if okB b t w then c 6 (flagB t w) w else 0)).sum
      = c 6 b t + c 7 b t := star b t ht ⟨6, by norm_num⟩
    have e1 : (n + 1).choose 1 = n.choose 0 + n.choose 1 := Nat.choose_succ_succ' n 0
    have e2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    have e3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ' n 2
    have e4 : (n + 1).choose 4 = n.choose 3 + n.choose 4 := Nat.choose_succ_succ' n 3
    have e5 : (n + 1).choose 5 = n.choose 4 + n.choose 5 := Nat.choose_succ_succ' n 4
    have e6 : (n + 1).choose 6 = n.choose 5 + n.choose 6 := Nat.choose_succ_succ' n 5
    have e0 : n.choose 0 = 1 := Nat.choose_zero_right n
    have h7 := c7 b t
    rw [s0, s1, s2, s3, s4, s5, s6, h7, e1, e2, e3, e4, e5, e6, e0]
    ring

theorem a_succ (n : ℕ) : a (n + 1) = 22 + n.choose 1 * 136 + n.choose 2 * 372
    + n.choose 3 * 565 + n.choose 4 * 490 + n.choose 5 * 230 + n.choose 6 * 46 := by
  rw [a_eq, closed n false (0, 0, 0) rfl]
  rfl

end A223913

namespace A223913
open OMA.S_oeis_a223913

theorem ch1 (n : ℕ) : ((n.choose 1 : ℕ) : ℚ) = n := by simp

theorem ch2 (n : ℕ) : ((n.choose 2 : ℕ) : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    rw [e]
    push_cast
    rw [ih, ch1]
    ring

theorem ch3 (n : ℕ) : ((n.choose 3 : ℕ) : ℚ) = n * (n - 1) * (n - 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ' n 2
    rw [e]
    push_cast
    rw [ih, ch2]
    ring

theorem ch4 (n : ℕ) : ((n.choose 4 : ℕ) : ℚ) = n * (n - 1) * (n - 2) * (n - 3) / 24 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (n + 1).choose 4 = n.choose 3 + n.choose 4 := Nat.choose_succ_succ' n 3
    rw [e]
    push_cast
    rw [ih, ch3]
    ring

theorem ch5 (n : ℕ) :
    ((n.choose 5 : ℕ) : ℚ) = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (n + 1).choose 5 = n.choose 4 + n.choose 5 := Nat.choose_succ_succ' n 4
    rw [e]
    push_cast
    rw [ih, ch4]
    ring

theorem ch6 (n : ℕ) :
    ((n.choose 6 : ℕ) : ℚ) = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 720 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (n + 1).choose 6 = n.choose 5 + n.choose 6 := Nat.choose_succ_succ' n 5
    rw [e]
    push_cast
    rw [ih, ch5]
    ring

theorem a_poly (n : ℕ) : (a (n + 1) : ℚ) = (23 / 360) * ((n : ℚ) + 1) ^ 6
    + (23 / 40) * ((n : ℚ) + 1) ^ 5 + (205 / 72) * ((n : ℚ) + 1) ^ 4
    + (143 / 24) * ((n : ℚ) + 1) ^ 3 + (364 / 45) * ((n : ℚ) + 1) ^ 2
    + (82 / 15) * ((n : ℚ) + 1) - 1 := by
  rw [a_succ]
  push_cast
  rw [ch1, ch2, ch3, ch4, ch5, ch6]
  ring

theorem gf_aux (f : ℕ → ℚ) (h0 : f 0 = 0) (h1 : f 1 = 22) (h2 : f 2 = 158) (h3 : f 3 = 666)
    (h4 : f 4 = 2111) (h5 : f 5 = 5548) (h6 : f 6 = 12752) (h7 : f 7 = 26494)
    (hr : ∀ n, f (n + 8) = 7 * f (n + 7) - 21 * f (n + 6) + 35 * f (n + 5) - 35 * f (n + 4)
      + 21 * f (n + 3) - 7 * f (n + 2) + f (n + 1)) :
    PowerSeries.mk f * (1 - PowerSeries.X) ^ 7 =
      PowerSeries.X * (22 + 4 * PowerSeries.X + 22 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3
        - 3 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 - PowerSeries.X ^ 6) := by
  have c3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
  have c4 : (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = 4 := map_ofNat _ 4
  have c5 : (PowerSeries.C (5 : ℚ) : PowerSeries ℚ) = 5 := map_ofNat _ 5
  have c7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
  have c21 : (PowerSeries.C (21 : ℚ) : PowerSeries ℚ) = 21 := map_ofNat _ 21
  have c22 : (PowerSeries.C (22 : ℚ) : PowerSeries ℚ) = 22 := map_ofNat _ 22
  have c35 : (PowerSeries.C (35 : ℚ) : PowerSeries ℚ) = 35 := map_ofNat _ 35
  have e1 : PowerSeries.mk f * (1 - PowerSeries.X) ^ 7
      = PowerSeries.mk f - PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 1 * PowerSeries.mk f)
        + PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 2 * PowerSeries.mk f)
        - PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 3 * PowerSeries.mk f)
        + PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 4 * PowerSeries.mk f)
        - PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 5 * PowerSeries.mk f)
        + PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 6 * PowerSeries.mk f)
        - PowerSeries.X ^ 7 * PowerSeries.mk f := by
    rw [c7, c21, c35]
    ring
  have e2 : (PowerSeries.X : PowerSeries ℚ) * (22 + 4 * PowerSeries.X + 22 * PowerSeries.X ^ 2
        - 3 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5
        - PowerSeries.X ^ 6)
      = PowerSeries.C (22 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 2
        + PowerSeries.C (22 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 4
        - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 6
        - PowerSeries.X ^ 7 := by
    rw [c3, c4, c5, c22]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  · norm_num [h0]
  · norm_num [h0, h1]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2, h3]
  · norm_num [h0, h1, h2, h3, h4]
  · norm_num [h0, h1, h2, h3, h4, h5]
  · norm_num [h0, h1, h2, h3, h4, h5, h6]
  · norm_num [h0, h1, h2, h3, h4, h5, h6, h7]
  · have h := hr n
    simp
    linarith

end A223913

open OMA.S_oeis_a223913 A223913 in
theorem OMA.solution : type_of% @OMA.S_oeis_a223913.main := by
  have hp : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (23 / 360) * (n : ℚ) ^ 6 + (23 / 40) * (n : ℚ) ^ 5
      + (205 / 72) * (n : ℚ) ^ 4 + (143 / 24) * (n : ℚ) ^ 3 + (364 / 45) * (n : ℚ) ^ 2
      + (82 / 15) * (n : ℚ) - 1 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [a_poly m]
    push_cast
    ring
  have hrecQ : ∀ m : ℕ, (a (m + 8) : ℚ) = 7 * (a (m + 7) : ℚ) - 21 * (a (m + 6) : ℚ)
      + 35 * (a (m + 5) : ℚ) - 35 * (a (m + 4) : ℚ) + 21 * (a (m + 3) : ℚ)
      - 7 * (a (m + 2) : ℚ) + (a (m + 1) : ℚ) := by
    intro m
    rw [hp (m + 8) (by omega), hp (m + 7) (by omega), hp (m + 6) (by omega),
      hp (m + 5) (by omega), hp (m + 4) (by omega), hp (m + 3) (by omega),
      hp (m + 2) (by omega), hp (m + 1) (by omega)]
    push_cast
    ring
  have ha1 : a 1 = 22 := (a_succ 0).trans (by decide)
  have ha2 : a 2 = 158 := (a_succ 1).trans (by decide)
  have ha3 : a 3 = 666 := (a_succ 2).trans (by decide)
  have ha4 : a 4 = 2111 := (a_succ 3).trans (by decide)
  have ha5 : a 5 = 5548 := (a_succ 4).trans (by decide)
  have ha6 : a 6 = 12752 := (a_succ 5).trans (by decide)
  have ha7 : a 7 = 26494 := (a_succ 6).trans (by decide)
  refine ⟨?_, ?_, hp⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have h := hrecQ m
    have e1 : m + 8 - 1 = m + 7 := by omega
    have e2 : m + 8 - 2 = m + 6 := by omega
    have e3 : m + 8 - 3 = m + 5 := by omega
    have e4 : m + 8 - 4 = m + 4 := by omega
    have e5 : m + 8 - 5 = m + 3 := by omega
    have e6 : m + 8 - 6 = m + 2 := by omega
    have e7 : m + 8 - 7 = m + 1 := by omega
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact_mod_cast h
  · unfold G
    rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    apply gf_aux
    · simp
    · simp [ha1]
    · simp [ha2]
    · simp [ha3]
    · simp [ha4]
    · simp [ha5]
    · simp [ha6]
    · simp [ha7]
    · intro n
      simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, if_false, one_ne_zero]
      exact hrecQ n
