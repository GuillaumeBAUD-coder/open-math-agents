import OMAStatements.S_oeis_a207389

-- Problem: oeis-a207389
-- Transfer-matrix proof: rows are states, triples of consecutive rows are transitions;
-- the kernel checks the vector recurrence on the table of extension counts.

namespace OMA.Arr

section Gen
variable {α : Type} [Fintype α] [DecidableEq α]

def Valid (H : α → Prop) (V : α → α → α → Prop) (n : ℕ) (s : Fin n → α) : Prop :=
  (∀ i : Fin n, H (s i)) ∧
    ∀ (i : ℕ) (h : i + 1 + 1 < n),
      V (s ⟨i, by omega⟩) (s ⟨i + 1, by omega⟩) (s ⟨i + 1 + 1, h⟩)

theorem cons_mk_zero {n : ℕ} (a : α) (f : Fin n → α) (h : 0 < n + 1) :
    (Fin.cons a f : Fin (n + 1) → α) ⟨0, h⟩ = a := rfl

theorem cons_mk_succ {n : ℕ} (a : α) (f : Fin n → α) (i : ℕ) (h : i + 1 < n + 1) :
    (Fin.cons a f : Fin (n + 1) → α) ⟨i + 1, h⟩ = f ⟨i, by omega⟩ := rfl

theorem valid_two (H : α → Prop) (V : α → α → α → Prop) (u v : α) (t : Fin 0 → α) :
    Valid H V 2 (Fin.cons u (Fin.cons v t)) ↔ H u ∧ H v := by
  constructor
  · intro h
    exact ⟨h.1 0, h.1 1⟩
  · intro h
    refine ⟨fun i => ?_, fun i hi => absurd hi (by omega)⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h.1
    · have : j = 0 := Subsingleton.elim _ _
      subst this
      exact h.2

theorem valid_succ (H : α → Prop) (V : α → α → α → Prop) (m : ℕ) (u v w : α)
    (t : Fin m → α) :
    Valid H V (m + 3) (Fin.cons u (Fin.cons v (Fin.cons w t))) ↔
      H u ∧ V u v w ∧ Valid H V (m + 2) (Fin.cons v (Fin.cons w t)) := by
  constructor
  · intro h
    refine ⟨h.1 0, ?_, fun i => h.1 i.succ, fun i hi => ?_⟩
    · have h0 := h.2 0 (by omega)
      rw [cons_mk_zero, cons_mk_succ, cons_mk_succ, cons_mk_zero, cons_mk_succ, cons_mk_zero] at h0
      exact h0
    · have h1 := h.2 (i + 1) (by omega)
      rw [cons_mk_succ, cons_mk_succ, cons_mk_succ] at h1
      exact h1
  · intro h
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact h.1
      · exact h.2.2.1 j
    · cases i with
      | zero =>
        rw [cons_mk_zero, cons_mk_succ, cons_mk_succ, cons_mk_zero, cons_mk_succ, cons_mk_zero]
        exact h.2.1
      | succ i =>
        rw [cons_mk_succ, cons_mk_succ, cons_mk_succ]
        exact h.2.2.2 i (by omega)

variable (H : α → Prop) (V : α → α → α → Prop) [DecidablePred H]
  [∀ u v w, Decidable (V u v w)] [∀ (n : ℕ) (s : Fin n → α), Decidable (Valid H V n s)]

def F : ℕ → α → α → ℤ
  | 0, u, v => if H u ∧ H v then 1 else 0
  | m + 1, u, v => if H u then ∑ w, (if V u v w then F m v w else 0) else 0

theorem sum_valid : ∀ (m : ℕ) (u v : α),
    (∑ t : Fin m → α, if Valid H V (m + 2) (Fin.cons u (Fin.cons v t)) then (1 : ℤ) else 0)
      = F H V m u v := by
  intro m
  induction m with
  | zero =>
    intro u v
    simp only [F]
    rw [Fintype.sum_unique]
    exact if_congr (valid_two H V u v _) rfl rfl
  | succ m ih =>
    intro u v
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).sum_comp, Fintype.sum_prod_type]
    simp only [F]
    have key : ∀ (w : α) (t : Fin m → α),
        Valid H V (m + 1 + 2) (Fin.cons u (Fin.cons v
          ((Fin.consEquiv (fun _ : Fin (m + 1) => α)) (w, t)))) ↔
        H u ∧ V u v w ∧ Valid H V (m + 2) (Fin.cons v (Fin.cons w t)) :=
      fun w t => valid_succ H V m u v w t
    simp only [key]
    by_cases hu : H u
    · rw [if_pos hu]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hv : V u v w
      · rw [if_pos hv, ← ih v w]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp [hu, hv]
      · rw [if_neg hv]
        refine Finset.sum_eq_zero fun t _ => ?_
        simp [hv]
    · rw [if_neg hu]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun t _ => ?_
      simp [hu]

theorem card_valid (m : ℕ) :
    (((Finset.univ : Finset (Fin (m + 2) → α)).filter (fun s => Valid H V (m + 2) s)).card : ℤ)
      = ∑ u, ∑ v, F H V m u v := by
  rw [Finset.card_filter]
  push_cast
  rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => α)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← sum_valid H V m u v]
  rfl

def G (rows : List α) : ℕ → α → α → ℤ
  | 0, _, _ => 1
  | m + 1, u, v => (rows.map (fun w => if V u v w then G rows m v w else 0)).sum

theorem sum_rows (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) (f : α → ℤ) :
    (∑ w, if H w then f w else 0) = (rows.map f).sum := by
  rw [← List.sum_toFinset f hN, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext w
  simp [hH]

theorem F_eq (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) :
    ∀ (m : ℕ) (u v : α), F H V m u v = if H u ∧ H v then G V rows m u v else 0 := by
  intro m
  induction m with
  | zero => intro u v; simp [F, G]
  | succ m ih =>
    intro u v
    simp only [F, G]
    by_cases hu : H u
    · by_cases hv : H v
      · rw [if_pos hu, if_pos ⟨hu, hv⟩, ← sum_rows H rows hN hH]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [ih v w]
        by_cases hw : H w <;> simp [hv, hw]
      · rw [if_pos hu, if_neg (fun h => hv h.2)]
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [ih v w]
        simp [hv]
    · rw [if_neg hu, if_neg (fun h => hu h.1)]

def C (rows : List α) (m : ℕ) : ℤ :=
  (rows.map (fun u => (rows.map (fun v => G V rows m u v)).sum)).sum

theorem card_eq_C (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) (m : ℕ) :
    (((Finset.univ : Finset (Fin (m + 2) → α)).filter (fun s => Valid H V (m + 2) s)).card : ℤ)
      = C V rows m := by
  rw [card_valid, C, ← sum_rows H rows hN hH]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : H u
  · rw [if_pos hu, ← sum_rows H rows hN hH]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [F_eq H V rows hN hH]
    by_cases hv : H v <;> simp [hu, hv]
  · rw [if_neg hu]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [F_eq H V rows hN hH]
    simp [hu]

theorem card_one (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) :
    (((Finset.univ : Finset (Fin 1 → α)).filter (fun s => Valid H V 1 s)).card : ℤ)
      = rows.length := by
  rw [Finset.card_filter]
  push_cast
  rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
  have : ∀ u : α, Valid H V 1 ((Equiv.funUnique (Fin 1) α).symm u) ↔ H u := by
    intro u
    constructor
    · intro h; exact h.1 0
    · intro h; exact ⟨fun _ => h, fun i hi => absurd hi (by omega)⟩
  simp only [this]
  rw [sum_rows H rows hN hH]
  simp

end Gen
end OMA.Arr

namespace OMA.Arr

section Tab
variable {α : Type} (V : α → α → α → Prop) [∀ u v w, Decidable (V u v w)] (rows : List α)

theorem zipWith_map_self {β γ : Type} (f : α → β → γ) (g : α → β) (l : List α) :
    List.zipWith f l (l.map g) = l.map (fun a => f a (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem zipWith_map_map {β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map (fun a => f (g a) (h a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_lin (P : α → Prop) [DecidablePred P] (a : ℤ) (f g : α → ℤ) (l : List α) :
    (l.map (fun w => if P w then a * f w + g w else 0)).sum
      = a * (l.map (fun w => if P w then f w else 0)).sum
        + (l.map (fun w => if P w then g w else 0)).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    split_ifs <;> ring

theorem sum_lin2 (a : ℤ) (f g : α → ℤ) (l : List α) :
    (l.map (fun w => a * f w + g w)).sum = a * (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

def step (T : List (List ℤ)) : List (List ℤ) :=
  rows.map (fun u => List.zipWith
    (fun v gv => (List.zipWith (fun w x => if V u v w then x else 0) rows gv).sum) rows T)

def tab : ℕ → List (List ℤ)
  | 0 => rows.map (fun _ => rows.map (fun _ => 1))
  | m + 1 => step V rows (tab m)

theorem tab_eq : ∀ m : ℕ,
    tab V rows m = rows.map (fun u => rows.map (fun v => G V rows m u v)) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [tab, ih, step]
    refine List.map_congr_left fun u _ => ?_
    rw [zipWith_map_self]
    refine List.map_congr_left fun v _ => ?_
    rw [zipWith_map_self]
    rfl

theorem C_eq_tab (m : ℕ) : C V rows m = ((tab V rows m).map List.sum).sum := by
  rw [tab_eq, C, List.map_map]
  rfl

def comb : List ℤ → ℕ → α → α → ℤ
  | [], _, _, _ => 0
  | a :: q, m, u, v => a * G V rows m u v + comb q (m + 1) u v

theorem comb_succ : ∀ (q : List ℤ) (m : ℕ) (u v : α),
    comb V rows q (m + 1) u v
      = (rows.map (fun w => if V u v w then comb V rows q m v w else 0)).sum := by
  intro q
  induction q with
  | nil => intro m u v; simp [comb]
  | cons a q ih =>
    intro m u v
    simp only [comb]
    rw [sum_lin, ← ih (m + 1) u v]
    rfl

theorem comb_zero (q : List ℤ)
    (h0 : ∀ u ∈ rows, ∀ v ∈ rows, comb V rows q 0 u v = 0) :
    ∀ (m : ℕ), ∀ u ∈ rows, ∀ v ∈ rows, comb V rows q m u v = 0 := by
  intro m
  induction m with
  | zero => exact h0
  | succ m ih =>
    intro u _ v hv
    rw [comb_succ]
    refine List.sum_eq_zero ?_
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [ih v hv w hw]
    simp

def combC : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: q, m => a * C V rows m + combC q (m + 1)

theorem combC_eq : ∀ (q : List ℤ) (m : ℕ),
    combC V rows q m
      = (rows.map (fun u => (rows.map (fun v => comb V rows q m u v)).sum)).sum := by
  intro q
  induction q with
  | nil => intro m; simp [combC, comb]
  | cons a q ih =>
    intro m
    simp only [combC, comb, ih, C]
    rw [← sum_lin2]
    refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
    rw [sum_lin2]

def combT : List ℤ → List (List ℤ) → List (List ℤ)
  | [], _ => rows.map (fun _ => rows.map (fun _ => 0))
  | a :: q, T => List.zipWith (List.zipWith (fun x y => a * x + y)) T (combT q (step V rows T))

theorem combT_eq : ∀ (q : List ℤ) (m : ℕ),
    combT V rows q (tab V rows m)
      = rows.map (fun u => rows.map (fun v => comb V rows q m u v)) := by
  intro q
  induction q with
  | nil => intro m; rfl
  | cons a q ih =>
    intro m
    rw [combT, show step V rows (tab V rows m) = tab V rows (m + 1) from rfl, ih, tab_eq,
      zipWith_map_map]
    refine List.map_congr_left fun u _ => ?_
    rw [zipWith_map_map]
    rfl

theorem rec_C (q : List ℤ)
    (hchk : combT V rows q (tab V rows 0) = rows.map (fun _ => rows.map (fun _ => 0))) :
    ∀ m : ℕ, combC V rows q m = 0 := by
  have h0 : ∀ u ∈ rows, ∀ v ∈ rows, comb V rows q 0 u v = 0 := by
    rw [combT_eq] at hchk
    intro u hu v hv
    have h1 := List.map_inj_left.mp hchk u hu
    exact List.map_inj_left.mp h1 v hv
  intro m
  rw [combC_eq]
  refine List.sum_eq_zero ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  refine List.sum_eq_zero ?_
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact comb_zero V rows q h0 m u hu v hv

end Tab

section Bridge

def getG {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

theorem getG_eq {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) (hi : i < r) (hj : j < c) :
    getG x i j = (x ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := dif_pos ⟨hi, hj⟩

def mkRow (c : ℕ) (l : List (Fin 2)) : Fin c → Fin 2 := fun j => l.getD j.val 0

def Hrow (p1 p2 : ℕ × ℕ × ℕ) {c : ℕ} (u : Fin c → Fin 2) : Prop :=
  ∀ (j : ℕ) (h : j < c - 2),
    (((u ⟨j, by omega⟩ : Fin 2) : ℕ), ((u ⟨j + 1, by omega⟩ : Fin 2) : ℕ),
      ((u ⟨j + 2, by omega⟩ : Fin 2) : ℕ)) ≠ p1 ∧
    (((u ⟨j, by omega⟩ : Fin 2) : ℕ), ((u ⟨j + 1, by omega⟩ : Fin 2) : ℕ),
      ((u ⟨j + 2, by omega⟩ : Fin 2) : ℕ)) ≠ p2

def Vt (q1 q2 : ℕ × ℕ × ℕ) {c : ℕ} (u v w : Fin c → Fin 2) : Prop :=
  ∀ (j : ℕ) (h : j < c),
    (((u ⟨j, h⟩ : Fin 2) : ℕ), ((v ⟨j, h⟩ : Fin 2) : ℕ), ((w ⟨j, h⟩ : Fin 2) : ℕ)) ≠ q1 ∧
    (((u ⟨j, h⟩ : Fin 2) : ℕ), ((v ⟨j, h⟩ : Fin 2) : ℕ), ((w ⟨j, h⟩ : Fin 2) : ℕ)) ≠ q2

instance (p1 p2 : ℕ × ℕ × ℕ) {c : ℕ} (u : Fin c → Fin 2) : Decidable (Hrow p1 p2 u) :=
  Nat.decidableBallLT _ _

instance (q1 q2 : ℕ × ℕ × ℕ) {c : ℕ} (u v w : Fin c → Fin 2) : Decidable (Vt q1 q2 u v w) :=
  Nat.decidableBallLT _ _

theorem avoid_iff (p1 p2 q1 q2 : ℕ × ℕ × ℕ) {r c : ℕ} (x : Fin r → Fin c → Fin 2) :
    ((∀ i < r, ∀ j < c - 2,
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p1 ∧
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p2) ∧
      (∀ i < r - 2, ∀ j < c,
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q1 ∧
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q2))
      ↔ Valid (Hrow p1 p2) (Vt q1 q2) r x := by
  constructor
  · intro h
    refine ⟨fun i j hj => ?_, fun i hi j hj => ?_⟩
    · have h1 := h.1 i.val i.isLt j hj
      rw [getG_eq x i.val j i.isLt (by omega), getG_eq x i.val (j + 1) i.isLt (by omega),
        getG_eq x i.val (j + 2) i.isLt (by omega)] at h1
      exact h1
    · have h1 := h.2 i (by omega) j hj
      rw [getG_eq x i j (by omega) hj, getG_eq x (i + 1) j (by omega) hj,
        getG_eq x (i + 2) j (by omega) hj] at h1
      exact h1
  · intro h
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [getG_eq x i j hi (by omega), getG_eq x i (j + 1) hi (by omega),
        getG_eq x i (j + 2) hi (by omega)]
      exact h.1 ⟨i, hi⟩ j hj
    · rw [getG_eq x i j (by omega) hj, getG_eq x (i + 1) j (by omega) hj,
        getG_eq x (i + 2) j (by omega) hj]
      exact h.2 i (by omega) j hj

theorem avoid_iff_swap (p1 p2 q1 q2 : ℕ × ℕ × ℕ) {r c : ℕ} (x : Fin r → Fin c → Fin 2) :
    ((∀ i < r, ∀ j < c - 2,
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p1 ∧
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p2) ∧
      (∀ i < r - 2, ∀ j < c,
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q1 ∧
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q2))
      ↔ Valid (Hrow q1 q2) (Vt p1 p2) c (fun j i => x i j) := by
  constructor
  · intro h
    refine ⟨fun j i hi => ?_, fun j hj i hi => ?_⟩
    · have h1 := h.2 i hi j.val j.isLt
      rw [getG_eq x i j.val (by omega) j.isLt, getG_eq x (i + 1) j.val (by omega) j.isLt,
        getG_eq x (i + 2) j.val (by omega) j.isLt] at h1
      exact h1
    · have h1 := h.1 i hi j (by omega)
      rw [getG_eq x i j hi (by omega), getG_eq x i (j + 1) hi (by omega),
        getG_eq x i (j + 2) hi (by omega)] at h1
      exact h1
  · intro h
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [getG_eq x i j hi (by omega), getG_eq x i (j + 1) hi (by omega),
        getG_eq x i (j + 2) hi (by omega)]
      exact h.2 j (by omega) i hi
    · rw [getG_eq x i j (by omega) hj, getG_eq x (i + 1) j (by omega) hj,
        getG_eq x (i + 2) j (by omega) hj]
      exact h.1 ⟨j, hj⟩ i hi

end Bridge

end OMA.Arr

namespace OMA.Arr

section Fast
variable {α : Type} (V : α → α → α → Prop) [∀ u v w, Decidable (V u v w)] (rows : List α)

def rowTbl (u : α) : List (List Bool) :=
  rows.map (fun v => rows.map (fun w => decide (V u v w)))

def tblOf : List (List (List Bool)) := rows.map (rowTbl V rows)

def decRow (N : ℕ) (ru : List ℕ) : List (List Bool) :=
  ru.map (fun mask => (List.range N).map (fun i => mask.testBit i))

def dec (N : ℕ) (masks : List (List ℕ)) : List (List (List Bool)) := masks.map (decRow N)

def stepB (tbl : List (List (List Bool))) (T : List (List ℤ)) : List (List ℤ) :=
  tbl.map (fun tu => List.zipWith
    (fun tv gv => (List.zipWith (fun (b : Bool) x => if b then x else 0) tv gv).sum) tu T)

theorem step_eq (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl)
    (T : List (List ℤ)) : step V rows T = stepB tbl T := by
  subst htbl
  simp only [step, stepB, tblOf, rowTbl, List.map_map, List.zipWith_map_left]
  refine List.map_congr_left fun u _ => ?_
  simp only [Function.comp, rowTbl, List.zipWith_map_left, decide_eq_true_eq]

def iterB (tbl : List (List (List Bool))) : ℕ → List (List ℤ) → List (List ℤ)
  | 0, T => T
  | m + 1, T => stepB tbl (iterB tbl m T)

theorem tab_eqB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) :
    ∀ m : ℕ, tab V rows m = iterB tbl m (rows.map (fun _ => rows.map (fun _ => 1))) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [tab, ih, step_eq V rows tbl htbl]; rfl

def combTB (tbl : List (List (List Bool))) (Z : List (List ℤ)) :
    List ℤ → List (List ℤ) → List (List ℤ)
  | [], _ => Z
  | a :: q, T =>
    List.zipWith (List.zipWith (fun x y => a * x + y)) T (combTB tbl Z q (stepB tbl T))

theorem combT_eqB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) :
    ∀ (q : List ℤ) (T : List (List ℤ)),
      combT V rows q T = combTB tbl (rows.map (fun _ => rows.map (fun _ => 0))) q T := by
  intro q
  induction q with
  | nil => intro T; rfl
  | cons a q ih => intro T; rw [combT, combTB, step_eq V rows tbl htbl, ih]

theorem rec_CB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) (q : List ℤ)
    (hchk : combTB tbl (rows.map (fun _ => rows.map (fun _ => 0))) q
      (rows.map (fun _ => rows.map (fun _ => 1))) = rows.map (fun _ => rows.map (fun _ => 0))) :
    ∀ m : ℕ, combC V rows q m = 0 := by
  refine rec_C V rows q ?_
  rw [combT_eqB V rows tbl htbl]
  exact hchk

theorem C_eqB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) (m : ℕ) :
    C V rows m
      = ((iterB tbl m (rows.map (fun _ => rows.map (fun _ => 1)))).map List.sum).sum := by
  rw [C_eq_tab, tab_eqB V rows tbl htbl]

end Fast

end OMA.Arr

namespace OMA.P207389
open OMA.Arr OMA.S_oeis_a207389

def rows : List (Fin 6 → Fin 2) :=
  [(mkRow 6 [0, 0, 0, 0, 0, 0]), (mkRow 6 [0, 1, 1, 0, 0, 0]), (mkRow 6 [0, 1, 1, 0, 1, 1]), (mkRow 6 [0, 1, 1, 1, 0, 0]), (mkRow 6 [0, 1, 1, 1, 0, 1]), (mkRow 6 [0, 1, 1, 1, 1, 0]), (mkRow 6 [0, 1, 1, 1, 1, 1]), (mkRow 6 [1, 0, 0, 0, 0, 0]), (mkRow 6 [1, 0, 1, 1, 0, 0]), (mkRow 6 [1, 0, 1, 1, 0, 1]), (mkRow 6 [1, 0, 1, 1, 1, 0]), (mkRow 6 [1, 0, 1, 1, 1, 1]), (mkRow 6 [1, 1, 0, 0, 0, 0]), (mkRow 6 [1, 1, 0, 1, 1, 0]), (mkRow 6 [1, 1, 0, 1, 1, 1]), (mkRow 6 [1, 1, 1, 0, 0, 0]), (mkRow 6 [1, 1, 1, 0, 1, 1]), (mkRow 6 [1, 1, 1, 1, 0, 0]), (mkRow 6 [1, 1, 1, 1, 0, 1]), (mkRow 6 [1, 1, 1, 1, 1, 0]), (mkRow 6 [1, 1, 1, 1, 1, 1])]

theorem hN : rows.Nodup := by decide +kernel

theorem hH : ∀ u : Fin 6 → Fin 2, Hrow (0, 0, 1) (0, 1, 0) u ↔ u ∈ rows := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

def masks : List (List ℕ) :=
  [[1, 3, 7, 11, 27, 43, 127, 129, 385, 897, 1409, 3969, 4225, 12417, 28801, 36995, 102535, 168331, 431003, 701867, 2097151],
   [3, 2, 6, 10, 26, 42, 126, 36995, 164106, 426778, 689450, 2068350, 36866, 700458, 2093182, 32770, 98310, 163850, 426010, 688170, 2064510],
   [7, 6, 4, 126, 84, 100, 68, 102535, 2068350, 1378900, 1641572, 1116228, 102406, 1663076, 1130564, 98310, 65540, 2064510, 1376340, 1638500, 1114180],
   [11, 10, 126, 8, 24, 40, 120, 168331, 131336, 394008, 656680, 1970040, 167946, 663592, 1990776, 163850, 2064510, 131080, 393240, 655400, 1966200],
   [27, 26, 84, 24, 16, 120, 80, 431003, 394008, 262672, 1970040, 1313360, 430106, 1990776, 1327184, 426010, 1376340, 393240, 262160, 1966200, 1310800],
   [43, 42, 100, 40, 120, 32, 96, 701867, 656680, 1970040, 525344, 1576032, 700458, 532512, 1597536, 688170, 1638500, 655400, 1966200, 524320, 1572960],
   [127, 126, 68, 120, 80, 96, 64, 2097151, 1970040, 1313360, 1576032, 1050688, 2093182, 1597536, 1065024, 2064510, 1114180, 1966200, 1310800, 1572960, 1048640],
   [129, 36995, 102535, 168331, 431003, 701867, 2097151, 128, 384, 896, 1408, 3968, 4224, 12416, 28800, 36992, 102528, 168320, 430976, 701824, 2097024],
   [385, 164106, 2068350, 131336, 394008, 656680, 1970040, 384, 256, 768, 1280, 3840, 168320, 664832, 1994496, 164096, 2068224, 131328, 393984, 656640, 1969920],
   [897, 426778, 1378900, 394008, 262672, 1970040, 1313360, 896, 768, 512, 3840, 2560, 430976, 1994496, 1329664, 426752, 1378816, 393984, 262656, 1969920, 1313280],
   [1409, 689450, 1641572, 656680, 1970040, 525344, 1576032, 1408, 1280, 3840, 1024, 3072, 701824, 533504, 1600512, 689408, 1641472, 656640, 1969920, 525312, 1575936],
   [3969, 2068350, 1116228, 1970040, 1313360, 1576032, 1050688, 3968, 3840, 2560, 3072, 2048, 2097024, 1600512, 1067008, 2068224, 1116160, 1969920, 1313280, 1575936, 1050624],
   [4225, 36866, 102406, 167946, 430106, 700458, 2093182, 4224, 168320, 430976, 701824, 2097024, 4096, 12288, 28672, 36864, 102400, 167936, 430080, 700416, 2093056],
   [12417, 700458, 1663076, 663592, 1990776, 532512, 1597536, 12416, 664832, 1994496, 533504, 1600512, 12288, 8192, 24576, 700416, 1662976, 663552, 1990656, 532480, 1597440],
   [28801, 2093182, 1130564, 1990776, 1327184, 1597536, 1065024, 28800, 1994496, 1329664, 1600512, 1067008, 28672, 24576, 16384, 2093056, 1130496, 1990656, 1327104, 1597440, 1064960],
   [36995, 32770, 98310, 163850, 426010, 688170, 2064510, 36992, 164096, 426752, 689408, 2068224, 36864, 700416, 2093056, 32768, 98304, 163840, 425984, 688128, 2064384],
   [102535, 98310, 65540, 2064510, 1376340, 1638500, 1114180, 102528, 2068224, 1378816, 1641472, 1116160, 102400, 1662976, 1130496, 98304, 65536, 2064384, 1376256, 1638400, 1114112],
   [168331, 163850, 2064510, 131080, 393240, 655400, 1966200, 168320, 131328, 393984, 656640, 1969920, 167936, 663552, 1990656, 163840, 2064384, 131072, 393216, 655360, 1966080],
   [431003, 426010, 1376340, 393240, 262160, 1966200, 1310800, 430976, 393984, 262656, 1969920, 1313280, 430080, 1990656, 1327104, 425984, 1376256, 393216, 262144, 1966080, 1310720],
   [701867, 688170, 1638500, 655400, 1966200, 524320, 1572960, 701824, 656640, 1969920, 525312, 1575936, 700416, 532480, 1597440, 688128, 1638400, 655360, 1966080, 524288, 1572864],
   [2097151, 2064510, 1114180, 1966200, 1310800, 1572960, 1048640, 2097024, 1969920, 1313280, 1575936, 1050624, 2093056, 1597440, 1064960, 2064384, 1114112, 1966080, 1310720, 1572864, 1048576]]

theorem ht0 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [0, 0, 0, 0, 0, 0]) = decRow 21 [1, 3, 7, 11, 27, 43, 127, 129, 385, 897, 1409, 3969, 4225, 12417, 28801, 36995, 102535, 168331, 431003, 701867, 2097151] := by
  decide +kernel

theorem ht1 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [0, 1, 1, 0, 0, 0]) = decRow 21 [3, 2, 6, 10, 26, 42, 126, 36995, 164106, 426778, 689450, 2068350, 36866, 700458, 2093182, 32770, 98310, 163850, 426010, 688170, 2064510] := by
  decide +kernel

theorem ht2 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [0, 1, 1, 0, 1, 1]) = decRow 21 [7, 6, 4, 126, 84, 100, 68, 102535, 2068350, 1378900, 1641572, 1116228, 102406, 1663076, 1130564, 98310, 65540, 2064510, 1376340, 1638500, 1114180] := by
  decide +kernel

theorem ht3 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [0, 1, 1, 1, 0, 0]) = decRow 21 [11, 10, 126, 8, 24, 40, 120, 168331, 131336, 394008, 656680, 1970040, 167946, 663592, 1990776, 163850, 2064510, 131080, 393240, 655400, 1966200] := by
  decide +kernel

theorem ht4 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [0, 1, 1, 1, 0, 1]) = decRow 21 [27, 26, 84, 24, 16, 120, 80, 431003, 394008, 262672, 1970040, 1313360, 430106, 1990776, 1327184, 426010, 1376340, 393240, 262160, 1966200, 1310800] := by
  decide +kernel

theorem ht5 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [0, 1, 1, 1, 1, 0]) = decRow 21 [43, 42, 100, 40, 120, 32, 96, 701867, 656680, 1970040, 525344, 1576032, 700458, 532512, 1597536, 688170, 1638500, 655400, 1966200, 524320, 1572960] := by
  decide +kernel

theorem ht6 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [0, 1, 1, 1, 1, 1]) = decRow 21 [127, 126, 68, 120, 80, 96, 64, 2097151, 1970040, 1313360, 1576032, 1050688, 2093182, 1597536, 1065024, 2064510, 1114180, 1966200, 1310800, 1572960, 1048640] := by
  decide +kernel

theorem ht7 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 0, 0, 0, 0, 0]) = decRow 21 [129, 36995, 102535, 168331, 431003, 701867, 2097151, 128, 384, 896, 1408, 3968, 4224, 12416, 28800, 36992, 102528, 168320, 430976, 701824, 2097024] := by
  decide +kernel

theorem ht8 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 0, 1, 1, 0, 0]) = decRow 21 [385, 164106, 2068350, 131336, 394008, 656680, 1970040, 384, 256, 768, 1280, 3840, 168320, 664832, 1994496, 164096, 2068224, 131328, 393984, 656640, 1969920] := by
  decide +kernel

theorem ht9 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 0, 1, 1, 0, 1]) = decRow 21 [897, 426778, 1378900, 394008, 262672, 1970040, 1313360, 896, 768, 512, 3840, 2560, 430976, 1994496, 1329664, 426752, 1378816, 393984, 262656, 1969920, 1313280] := by
  decide +kernel

theorem ht10 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 0, 1, 1, 1, 0]) = decRow 21 [1409, 689450, 1641572, 656680, 1970040, 525344, 1576032, 1408, 1280, 3840, 1024, 3072, 701824, 533504, 1600512, 689408, 1641472, 656640, 1969920, 525312, 1575936] := by
  decide +kernel

theorem ht11 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 0, 1, 1, 1, 1]) = decRow 21 [3969, 2068350, 1116228, 1970040, 1313360, 1576032, 1050688, 3968, 3840, 2560, 3072, 2048, 2097024, 1600512, 1067008, 2068224, 1116160, 1969920, 1313280, 1575936, 1050624] := by
  decide +kernel

theorem ht12 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 0, 0, 0, 0]) = decRow 21 [4225, 36866, 102406, 167946, 430106, 700458, 2093182, 4224, 168320, 430976, 701824, 2097024, 4096, 12288, 28672, 36864, 102400, 167936, 430080, 700416, 2093056] := by
  decide +kernel

theorem ht13 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 0, 1, 1, 0]) = decRow 21 [12417, 700458, 1663076, 663592, 1990776, 532512, 1597536, 12416, 664832, 1994496, 533504, 1600512, 12288, 8192, 24576, 700416, 1662976, 663552, 1990656, 532480, 1597440] := by
  decide +kernel

theorem ht14 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 0, 1, 1, 1]) = decRow 21 [28801, 2093182, 1130564, 1990776, 1327184, 1597536, 1065024, 28800, 1994496, 1329664, 1600512, 1067008, 28672, 24576, 16384, 2093056, 1130496, 1990656, 1327104, 1597440, 1064960] := by
  decide +kernel

theorem ht15 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 1, 0, 0, 0]) = decRow 21 [36995, 32770, 98310, 163850, 426010, 688170, 2064510, 36992, 164096, 426752, 689408, 2068224, 36864, 700416, 2093056, 32768, 98304, 163840, 425984, 688128, 2064384] := by
  decide +kernel

theorem ht16 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 1, 0, 1, 1]) = decRow 21 [102535, 98310, 65540, 2064510, 1376340, 1638500, 1114180, 102528, 2068224, 1378816, 1641472, 1116160, 102400, 1662976, 1130496, 98304, 65536, 2064384, 1376256, 1638400, 1114112] := by
  decide +kernel

theorem ht17 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 1, 1, 0, 0]) = decRow 21 [168331, 163850, 2064510, 131080, 393240, 655400, 1966200, 168320, 131328, 393984, 656640, 1969920, 167936, 663552, 1990656, 163840, 2064384, 131072, 393216, 655360, 1966080] := by
  decide +kernel

theorem ht18 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 1, 1, 0, 1]) = decRow 21 [431003, 426010, 1376340, 393240, 262160, 1966200, 1310800, 430976, 393984, 262656, 1969920, 1313280, 430080, 1990656, 1327104, 425984, 1376256, 393216, 262144, 1966080, 1310720] := by
  decide +kernel

theorem ht19 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 1, 1, 1, 0]) = decRow 21 [701867, 688170, 1638500, 655400, 1966200, 524320, 1572960, 701824, 656640, 1969920, 525312, 1575936, 700416, 532480, 1597440, 688128, 1638400, 655360, 1966080, 524288, 1572864] := by
  decide +kernel

theorem ht20 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 6 [1, 1, 1, 1, 1, 1]) = decRow 21 [2097151, 2064510, 1114180, 1966200, 1310800, 1572960, 1048640, 2097024, 1969920, 1313280, 1575936, 1050624, 2093056, 1597440, 1064960, 2064384, 1114112, 1966080, 1310720, 1572864, 1048576] := by
  decide +kernel

theorem htbl : tblOf (Vt (0, 0, 1) (1, 1, 0)) rows = dec 21 masks := by
  show List.map (rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows) [(mkRow 6 [0, 0, 0, 0, 0, 0]), (mkRow 6 [0, 1, 1, 0, 0, 0]), (mkRow 6 [0, 1, 1, 0, 1, 1]), (mkRow 6 [0, 1, 1, 1, 0, 0]), (mkRow 6 [0, 1, 1, 1, 0, 1]), (mkRow 6 [0, 1, 1, 1, 1, 0]), (mkRow 6 [0, 1, 1, 1, 1, 1]), (mkRow 6 [1, 0, 0, 0, 0, 0]), (mkRow 6 [1, 0, 1, 1, 0, 0]), (mkRow 6 [1, 0, 1, 1, 0, 1]), (mkRow 6 [1, 0, 1, 1, 1, 0]), (mkRow 6 [1, 0, 1, 1, 1, 1]), (mkRow 6 [1, 1, 0, 0, 0, 0]), (mkRow 6 [1, 1, 0, 1, 1, 0]), (mkRow 6 [1, 1, 0, 1, 1, 1]), (mkRow 6 [1, 1, 1, 0, 0, 0]), (mkRow 6 [1, 1, 1, 0, 1, 1]), (mkRow 6 [1, 1, 1, 1, 0, 0]), (mkRow 6 [1, 1, 1, 1, 0, 1]), (mkRow 6 [1, 1, 1, 1, 1, 0]), (mkRow 6 [1, 1, 1, 1, 1, 1])]
    = List.map (decRow 21) [[1, 3, 7, 11, 27, 43, 127, 129, 385, 897, 1409, 3969, 4225, 12417, 28801, 36995, 102535, 168331, 431003, 701867, 2097151], [3, 2, 6, 10, 26, 42, 126, 36995, 164106, 426778, 689450, 2068350, 36866, 700458, 2093182, 32770, 98310, 163850, 426010, 688170, 2064510], [7, 6, 4, 126, 84, 100, 68, 102535, 2068350, 1378900, 1641572, 1116228, 102406, 1663076, 1130564, 98310, 65540, 2064510, 1376340, 1638500, 1114180], [11, 10, 126, 8, 24, 40, 120, 168331, 131336, 394008, 656680, 1970040, 167946, 663592, 1990776, 163850, 2064510, 131080, 393240, 655400, 1966200], [27, 26, 84, 24, 16, 120, 80, 431003, 394008, 262672, 1970040, 1313360, 430106, 1990776, 1327184, 426010, 1376340, 393240, 262160, 1966200, 1310800], [43, 42, 100, 40, 120, 32, 96, 701867, 656680, 1970040, 525344, 1576032, 700458, 532512, 1597536, 688170, 1638500, 655400, 1966200, 524320, 1572960], [127, 126, 68, 120, 80, 96, 64, 2097151, 1970040, 1313360, 1576032, 1050688, 2093182, 1597536, 1065024, 2064510, 1114180, 1966200, 1310800, 1572960, 1048640], [129, 36995, 102535, 168331, 431003, 701867, 2097151, 128, 384, 896, 1408, 3968, 4224, 12416, 28800, 36992, 102528, 168320, 430976, 701824, 2097024], [385, 164106, 2068350, 131336, 394008, 656680, 1970040, 384, 256, 768, 1280, 3840, 168320, 664832, 1994496, 164096, 2068224, 131328, 393984, 656640, 1969920], [897, 426778, 1378900, 394008, 262672, 1970040, 1313360, 896, 768, 512, 3840, 2560, 430976, 1994496, 1329664, 426752, 1378816, 393984, 262656, 1969920, 1313280], [1409, 689450, 1641572, 656680, 1970040, 525344, 1576032, 1408, 1280, 3840, 1024, 3072, 701824, 533504, 1600512, 689408, 1641472, 656640, 1969920, 525312, 1575936], [3969, 2068350, 1116228, 1970040, 1313360, 1576032, 1050688, 3968, 3840, 2560, 3072, 2048, 2097024, 1600512, 1067008, 2068224, 1116160, 1969920, 1313280, 1575936, 1050624], [4225, 36866, 102406, 167946, 430106, 700458, 2093182, 4224, 168320, 430976, 701824, 2097024, 4096, 12288, 28672, 36864, 102400, 167936, 430080, 700416, 2093056], [12417, 700458, 1663076, 663592, 1990776, 532512, 1597536, 12416, 664832, 1994496, 533504, 1600512, 12288, 8192, 24576, 700416, 1662976, 663552, 1990656, 532480, 1597440], [28801, 2093182, 1130564, 1990776, 1327184, 1597536, 1065024, 28800, 1994496, 1329664, 1600512, 1067008, 28672, 24576, 16384, 2093056, 1130496, 1990656, 1327104, 1597440, 1064960], [36995, 32770, 98310, 163850, 426010, 688170, 2064510, 36992, 164096, 426752, 689408, 2068224, 36864, 700416, 2093056, 32768, 98304, 163840, 425984, 688128, 2064384], [102535, 98310, 65540, 2064510, 1376340, 1638500, 1114180, 102528, 2068224, 1378816, 1641472, 1116160, 102400, 1662976, 1130496, 98304, 65536, 2064384, 1376256, 1638400, 1114112], [168331, 163850, 2064510, 131080, 393240, 655400, 1966200, 168320, 131328, 393984, 656640, 1969920, 167936, 663552, 1990656, 163840, 2064384, 131072, 393216, 655360, 1966080], [431003, 426010, 1376340, 393240, 262160, 1966200, 1310800, 430976, 393984, 262656, 1969920, 1313280, 430080, 1990656, 1327104, 425984, 1376256, 393216, 262144, 1966080, 1310720], [701867, 688170, 1638500, 655400, 1966200, 524320, 1572960, 701824, 656640, 1969920, 525312, 1575936, 700416, 532480, 1597440, 688128, 1638400, 655360, 1966080, 524288, 1572864], [2097151, 2064510, 1114180, 1966200, 1310800, 1572960, 1048640, 2097024, 1969920, 1313280, 1575936, 1050624, 2093056, 1597440, 1064960, 2064384, 1114112, 1966080, 1310720, 1572864, 1048576]]
  simp only [List.map_cons, List.map_nil, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12, ht13, ht14, ht15, ht16, ht17, ht18, ht19, ht20]

def T0 : List (List ℤ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

def T1 : List (List ℤ) :=
  [[1, 2, 3, 3, 4, 4, 7, 2, 3, 4, 4, 6, 3, 4, 5, 5, 7, 8, 11, 12, 21],
   [2, 1, 2, 2, 3, 3, 6, 5, 5, 8, 8, 16, 3, 8, 15, 2, 4, 4, 6, 6, 12],
   [3, 2, 1, 6, 3, 3, 2, 7, 16, 8, 8, 5, 5, 8, 5, 4, 2, 12, 6, 6, 4],
   [3, 2, 6, 1, 2, 2, 4, 8, 3, 6, 6, 12, 5, 5, 10, 4, 12, 2, 4, 4, 8],
   [4, 3, 3, 2, 1, 4, 2, 11, 6, 3, 12, 6, 7, 10, 5, 6, 6, 4, 2, 8, 4],
   [4, 3, 3, 2, 4, 1, 2, 12, 6, 12, 3, 6, 8, 3, 6, 6, 6, 4, 8, 2, 4],
   [7, 6, 2, 4, 2, 2, 1, 21, 12, 6, 6, 3, 15, 6, 3, 12, 4, 8, 4, 4, 2],
   [2, 5, 7, 8, 11, 12, 21, 1, 2, 3, 3, 5, 2, 3, 4, 3, 4, 5, 7, 8, 14],
   [3, 5, 16, 3, 6, 6, 12, 2, 1, 2, 2, 4, 5, 5, 10, 3, 10, 2, 4, 4, 8],
   [4, 8, 8, 6, 3, 12, 6, 3, 2, 1, 4, 2, 7, 10, 5, 5, 5, 4, 2, 8, 4],
   [4, 8, 8, 6, 12, 3, 6, 3, 2, 4, 1, 2, 8, 3, 6, 5, 5, 4, 8, 2, 4],
   [6, 16, 5, 12, 6, 6, 3, 5, 4, 2, 2, 1, 14, 6, 3, 10, 3, 8, 4, 4, 2],
   [3, 3, 5, 5, 7, 8, 15, 2, 5, 7, 8, 14, 1, 2, 3, 2, 3, 3, 4, 5, 9],
   [4, 8, 8, 5, 10, 3, 6, 3, 5, 10, 3, 6, 2, 1, 2, 5, 5, 3, 6, 2, 4],
   [5, 15, 5, 10, 5, 6, 3, 4, 10, 5, 6, 3, 3, 2, 1, 9, 3, 6, 3, 4, 2],
   [5, 2, 4, 4, 6, 6, 12, 3, 3, 5, 5, 10, 2, 5, 9, 1, 2, 2, 3, 3, 6],
   [7, 4, 2, 12, 6, 6, 4, 4, 10, 5, 5, 3, 3, 5, 3, 2, 1, 6, 3, 3, 2],
   [8, 4, 12, 2, 4, 4, 8, 5, 2, 4, 4, 8, 3, 3, 6, 2, 6, 1, 2, 2, 4],
   [11, 6, 6, 4, 2, 8, 4, 7, 4, 2, 8, 4, 4, 6, 3, 3, 3, 2, 1, 4, 2],
   [12, 6, 6, 4, 8, 2, 4, 8, 4, 8, 2, 4, 5, 2, 4, 3, 3, 2, 4, 1, 2],
   [21, 12, 4, 8, 4, 4, 2, 14, 8, 4, 4, 2, 9, 4, 2, 6, 2, 4, 2, 2, 1]]

def T2 : List (List ℤ) :=
  [[1, 3, 6, 6, 10, 10, 24, 3, 6, 10, 10, 20, 6, 10, 15, 13, 23, 27, 46, 51, 119],
   [3, 1, 3, 3, 6, 6, 17, 13, 14, 31, 31, 88, 6, 29, 77, 3, 9, 9, 18, 18, 51],
   [6, 3, 1, 17, 6, 6, 3, 24, 88, 31, 31, 14, 14, 31, 14, 9, 3, 51, 18, 18, 9],
   [6, 3, 17, 1, 3, 3, 9, 28, 6, 18, 18, 54, 14, 14, 42, 9, 51, 3, 9, 9, 27],
   [10, 6, 6, 3, 1, 9, 3, 49, 18, 6, 54, 18, 25, 42, 14, 18, 18, 9, 3, 27, 9],
   [10, 6, 6, 3, 9, 1, 3, 54, 18, 54, 6, 18, 29, 6, 18, 18, 18, 9, 27, 3, 9],
   [24, 17, 3, 9, 3, 3, 1, 130, 54, 18, 18, 6, 75, 18, 6, 51, 9, 27, 9, 9, 3],
   [3, 13, 24, 28, 49, 54, 130, 1, 3, 6, 6, 14, 3, 6, 10, 6, 10, 13, 23, 27, 64],
   [6, 14, 88, 6, 18, 18, 54, 3, 1, 3, 3, 9, 13, 14, 42, 6, 40, 3, 9, 9, 27],
   [10, 31, 31, 18, 6, 54, 18, 6, 3, 1, 9, 3, 24, 42, 14, 14, 14, 9, 3, 27, 9],
   [10, 31, 31, 18, 54, 6, 18, 6, 3, 9, 1, 3, 28, 6, 18, 14, 14, 9, 27, 3, 9],
   [20, 88, 14, 54, 18, 18, 6, 14, 9, 3, 3, 1, 68, 18, 6, 40, 6, 27, 9, 9, 3],
   [6, 6, 14, 14, 25, 29, 75, 3, 13, 24, 28, 68, 1, 3, 6, 3, 6, 6, 10, 13, 32],
   [10, 29, 31, 14, 42, 6, 18, 6, 14, 42, 6, 18, 3, 1, 3, 13, 14, 6, 18, 3, 9],
   [15, 77, 14, 42, 14, 18, 6, 10, 42, 14, 18, 6, 6, 3, 1, 33, 6, 18, 6, 9, 3],
   [13, 3, 9, 9, 18, 18, 51, 6, 6, 14, 14, 40, 3, 13, 33, 1, 3, 3, 6, 6, 17],
   [23, 9, 3, 51, 18, 18, 9, 10, 40, 14, 14, 6, 6, 14, 6, 3, 1, 17, 6, 6, 3],
   [27, 9, 51, 3, 9, 9, 27, 13, 3, 9, 9, 27, 6, 6, 18, 3, 17, 1, 3, 3, 9],
   [46, 18, 18, 9, 3, 27, 9, 23, 9, 3, 27, 9, 10, 18, 6, 6, 6, 3, 1, 9, 3],
   [51, 18, 18, 9, 27, 3, 9, 27, 9, 27, 3, 9, 13, 3, 9, 6, 6, 3, 9, 1, 3],
   [119, 51, 9, 27, 9, 9, 3, 64, 27, 9, 9, 3, 32, 9, 3, 17, 3, 9, 3, 3, 1]]

def T3 : List (List ℤ) :=
  [[1, 4, 10, 10, 20, 20, 60, 4, 10, 20, 20, 50, 10, 20, 35, 26, 55, 65, 131, 146, 419],
   [4, 1, 4, 4, 10, 10, 36, 26, 30, 85, 85, 308, 10, 75, 256, 4, 16, 16, 40, 40, 144],
   [10, 4, 1, 36, 10, 10, 4, 60, 308, 85, 85, 30, 30, 85, 30, 16, 4, 144, 40, 40, 16],
   [10, 4, 36, 1, 4, 4, 16, 70, 10, 40, 40, 160, 30, 30, 120, 16, 144, 4, 16, 16, 64],
   [20, 10, 10, 4, 1, 16, 4, 148, 40, 10, 160, 40, 65, 120, 30, 40, 40, 16, 4, 64, 16],
   [20, 10, 10, 4, 16, 1, 4, 163, 40, 160, 10, 40, 75, 10, 40, 40, 40, 16, 64, 4, 16],
   [60, 36, 4, 16, 4, 4, 1, 493, 160, 40, 40, 10, 243, 40, 10, 144, 16, 64, 16, 16, 4],
   [4, 26, 60, 70, 148, 163, 493, 1, 4, 10, 10, 30, 4, 10, 20, 10, 20, 26, 55, 65, 192],
   [10, 30, 308, 10, 40, 40, 160, 4, 1, 4, 4, 16, 26, 30, 120, 10, 110, 4, 16, 16, 64],
   [20, 85, 85, 40, 10, 160, 40, 10, 4, 1, 16, 4, 60, 120, 30, 30, 30, 16, 4, 64, 16],
   [20, 85, 85, 40, 160, 10, 40, 10, 4, 16, 1, 4, 70, 10, 40, 30, 30, 16, 64, 4, 16],
   [50, 308, 30, 160, 40, 40, 10, 30, 16, 4, 4, 1, 216, 40, 10, 110, 10, 64, 16, 16, 4],
   [10, 10, 30, 30, 65, 75, 243, 4, 26, 60, 70, 216, 1, 4, 10, 4, 10, 10, 20, 26, 80],
   [20, 75, 85, 30, 120, 10, 40, 10, 30, 120, 10, 40, 4, 1, 4, 26, 30, 10, 40, 4, 16],
   [35, 256, 30, 120, 30, 40, 10, 20, 120, 30, 40, 10, 10, 4, 1, 85, 10, 40, 10, 16, 4],
   [26, 4, 16, 16, 40, 40, 144, 10, 10, 30, 30, 110, 4, 26, 85, 1, 4, 4, 10, 10, 36],
   [55, 16, 4, 144, 40, 40, 16, 20, 110, 30, 30, 10, 10, 30, 10, 4, 1, 36, 10, 10, 4],
   [65, 16, 144, 4, 16, 16, 64, 26, 4, 16, 16, 64, 10, 10, 40, 4, 36, 1, 4, 4, 16],
   [131, 40, 40, 16, 4, 64, 16, 55, 16, 4, 64, 16, 20, 40, 10, 10, 10, 4, 1, 16, 4],
   [146, 40, 40, 16, 64, 4, 16, 65, 16, 64, 4, 16, 26, 4, 16, 10, 10, 4, 16, 1, 4],
   [419, 144, 16, 64, 16, 16, 4, 192, 64, 16, 16, 4, 80, 16, 4, 36, 4, 16, 4, 4, 1]]

def T4 : List (List ℤ) :=
  [[1, 5, 15, 15, 35, 35, 125, 5, 15, 35, 35, 105, 15, 35, 70, 45, 110, 130, 301, 336, 1136],
   [5, 1, 5, 5, 15, 15, 65, 45, 55, 190, 190, 833, 15, 160, 666, 5, 25, 25, 75, 75, 325],
   [15, 5, 1, 65, 15, 15, 5, 125, 833, 190, 190, 55, 55, 190, 55, 25, 5, 325, 75, 75, 25],
   [15, 5, 65, 1, 5, 5, 25, 145, 15, 75, 75, 375, 55, 55, 275, 25, 325, 5, 25, 25, 125],
   [35, 15, 15, 5, 1, 25, 5, 358, 75, 15, 375, 75, 140, 275, 55, 75, 75, 25, 5, 125, 25],
   [35, 15, 15, 5, 25, 1, 5, 393, 75, 375, 15, 75, 160, 15, 75, 75, 75, 25, 125, 5, 25],
   [125, 65, 5, 25, 5, 5, 1, 1421, 375, 75, 75, 15, 618, 75, 15, 325, 25, 125, 25, 25, 5],
   [5, 45, 125, 145, 358, 393, 1421, 1, 5, 15, 15, 55, 5, 15, 35, 15, 35, 45, 110, 130, 457],
   [15, 55, 833, 15, 75, 75, 375, 5, 1, 5, 5, 25, 45, 55, 275, 15, 245, 5, 25, 25, 125],
   [35, 190, 190, 75, 15, 375, 75, 15, 5, 1, 25, 5, 125, 275, 55, 55, 55, 25, 5, 125, 25],
   [35, 190, 190, 75, 375, 15, 75, 15, 5, 25, 1, 5, 145, 15, 75, 55, 55, 25, 125, 5, 25],
   [105, 833, 55, 375, 75, 75, 15, 55, 25, 5, 5, 1, 541, 75, 15, 245, 15, 125, 25, 25, 5],
   [15, 15, 55, 55, 140, 160, 618, 5, 45, 125, 145, 541, 1, 5, 15, 5, 15, 15, 35, 45, 165],
   [35, 160, 190, 55, 275, 15, 75, 15, 55, 275, 15, 75, 5, 1, 5, 45, 55, 15, 75, 5, 25],
   [70, 666, 55, 275, 55, 75, 15, 35, 275, 55, 75, 15, 15, 5, 1, 180, 15, 75, 15, 25, 5],
   [45, 5, 25, 25, 75, 75, 325, 15, 15, 55, 55, 245, 5, 45, 180, 1, 5, 5, 15, 15, 65],
   [110, 25, 5, 325, 75, 75, 25, 35, 245, 55, 55, 15, 15, 55, 15, 5, 1, 65, 15, 15, 5],
   [130, 25, 325, 5, 25, 25, 125, 45, 5, 25, 25, 125, 15, 15, 75, 5, 65, 1, 5, 5, 25],
   [301, 75, 75, 25, 5, 125, 25, 110, 25, 5, 125, 25, 35, 75, 15, 15, 15, 5, 1, 25, 5],
   [336, 75, 75, 25, 125, 5, 25, 130, 25, 125, 5, 25, 45, 5, 25, 15, 15, 5, 25, 1, 5],
   [1136, 325, 25, 125, 25, 25, 5, 457, 125, 25, 25, 5, 165, 25, 5, 65, 5, 25, 5, 5, 1]]

def T5 : List (List ℤ) :=
  [[1, 6, 21, 21, 56, 56, 231, 6, 21, 56, 56, 196, 21, 56, 126, 71, 196, 231, 602, 672, 2604],
   [6, 1, 6, 6, 21, 21, 106, 71, 91, 371, 371, 1904, 21, 301, 1477, 6, 36, 36, 126, 126, 636],
   [21, 6, 1, 106, 21, 21, 6, 231, 1904, 371, 371, 91, 91, 371, 91, 36, 6, 636, 126, 126, 36],
   [21, 6, 106, 1, 6, 6, 36, 266, 21, 126, 126, 756, 91, 91, 546, 36, 636, 6, 36, 36, 216],
   [56, 21, 21, 6, 1, 36, 6, 749, 126, 21, 756, 126, 266, 546, 91, 126, 126, 36, 6, 216, 36],
   [56, 21, 21, 6, 36, 1, 6, 819, 126, 756, 21, 126, 301, 21, 126, 126, 126, 36, 216, 6, 36],
   [231, 106, 6, 36, 6, 6, 1, 3430, 756, 126, 126, 21, 1344, 126, 21, 636, 36, 216, 36, 36, 6],
   [6, 71, 231, 266, 749, 819, 3430, 1, 6, 21, 21, 91, 6, 21, 56, 21, 56, 71, 196, 231, 938],
   [21, 91, 1904, 21, 126, 126, 756, 6, 1, 6, 6, 36, 71, 91, 546, 21, 476, 6, 36, 36, 216],
   [56, 371, 371, 126, 21, 756, 126, 21, 6, 1, 36, 6, 231, 546, 91, 91, 91, 36, 6, 216, 36],
   [56, 371, 371, 126, 756, 21, 126, 21, 6, 36, 1, 6, 266, 21, 126, 91, 91, 36, 216, 6, 36],
   [196, 1904, 91, 756, 126, 126, 21, 91, 36, 6, 6, 1, 1162, 126, 21, 476, 21, 216, 36, 36, 6],
   [21, 21, 91, 91, 266, 301, 1344, 6, 71, 231, 266, 1162, 1, 6, 21, 6, 21, 21, 56, 71, 301],
   [56, 301, 371, 91, 546, 21, 126, 21, 91, 546, 21, 126, 6, 1, 6, 71, 91, 21, 126, 6, 36],
   [126, 1477, 91, 546, 91, 126, 21, 56, 546, 91, 126, 21, 21, 6, 1, 336, 21, 126, 21, 36, 6],
   [71, 6, 36, 36, 126, 126, 636, 21, 21, 91, 91, 476, 6, 71, 336, 1, 6, 6, 21, 21, 106],
   [196, 36, 6, 636, 126, 126, 36, 56, 476, 91, 91, 21, 21, 91, 21, 6, 1, 106, 21, 21, 6],
   [231, 36, 636, 6, 36, 36, 216, 71, 6, 36, 36, 216, 21, 21, 126, 6, 106, 1, 6, 6, 36],
   [602, 126, 126, 36, 6, 216, 36, 196, 36, 6, 216, 36, 56, 126, 21, 21, 21, 6, 1, 36, 6],
   [672, 126, 126, 36, 216, 6, 36, 231, 36, 216, 6, 36, 71, 6, 36, 21, 21, 6, 36, 1, 6],
   [2604, 636, 36, 216, 36, 36, 6, 938, 216, 36, 36, 6, 301, 36, 6, 106, 6, 36, 6, 6, 1]]

def T6 : List (List ℤ) :=
  [[1, 7, 28, 28, 84, 84, 392, 7, 28, 84, 84, 336, 28, 84, 210, 105, 322, 378, 1092, 1218, 5306],
   [7, 1, 7, 7, 28, 28, 161, 105, 140, 658, 658, 3864, 28, 518, 2926, 7, 49, 49, 196, 196, 1127],
   [28, 7, 1, 161, 28, 28, 7, 392, 3864, 658, 658, 140, 140, 658, 140, 49, 7, 1127, 196, 196, 49],
   [28, 7, 161, 1, 7, 7, 49, 448, 28, 196, 196, 1372, 140, 140, 980, 49, 1127, 7, 49, 49, 343],
   [84, 28, 28, 7, 1, 49, 7, 1414, 196, 28, 1372, 196, 462, 980, 140, 196, 196, 49, 7, 343, 49],
   [84, 28, 28, 7, 49, 1, 7, 1540, 196, 1372, 28, 196, 518, 28, 196, 196, 196, 49, 343, 7, 49],
   [392, 161, 7, 49, 7, 7, 1, 7308, 1372, 196, 196, 28, 2618, 196, 28, 1127, 49, 343, 49, 49, 7],
   [7, 105, 392, 448, 1414, 1540, 7308, 1, 7, 28, 28, 140, 7, 28, 84, 28, 84, 105, 322, 378, 1736],
   [28, 140, 3864, 28, 196, 196, 1372, 7, 1, 7, 7, 49, 105, 140, 980, 28, 840, 7, 49, 49, 343],
   [84, 658, 658, 196, 28, 1372, 196, 28, 7, 1, 49, 7, 392, 980, 140, 140, 140, 49, 7, 343, 49],
   [84, 658, 658, 196, 1372, 28, 196, 28, 7, 49, 1, 7, 448, 28, 196, 140, 140, 49, 343, 7, 49],
   [336, 3864, 140, 1372, 196, 196, 28, 140, 49, 7, 7, 1, 2240, 196, 28, 840, 28, 343, 49, 49, 7],
   [28, 28, 140, 140, 462, 518, 2618, 7, 105, 392, 448, 2240, 1, 7, 28, 7, 28, 28, 84, 105, 504],
   [84, 518, 658, 140, 980, 28, 196, 28, 140, 980, 28, 196, 7, 1, 7, 105, 140, 28, 196, 7, 49],
   [210, 2926, 140, 980, 140, 196, 28, 84, 980, 140, 196, 28, 28, 7, 1, 574, 28, 196, 28, 49, 7],
   [105, 7, 49, 49, 196, 196, 1127, 28, 28, 140, 140, 840, 7, 105, 574, 1, 7, 7, 28, 28, 161],
   [322, 49, 7, 1127, 196, 196, 49, 84, 840, 140, 140, 28, 28, 140, 28, 7, 1, 161, 28, 28, 7],
   [378, 49, 1127, 7, 49, 49, 343, 105, 7, 49, 49, 343, 28, 28, 196, 7, 161, 1, 7, 7, 49],
   [1092, 196, 196, 49, 7, 343, 49, 322, 49, 7, 343, 49, 84, 196, 28, 28, 28, 7, 1, 49, 7],
   [1218, 196, 196, 49, 343, 7, 49, 378, 49, 343, 7, 49, 105, 7, 49, 28, 28, 7, 49, 1, 7],
   [5306, 1127, 49, 343, 49, 49, 7, 1736, 343, 49, 49, 7, 504, 49, 7, 161, 7, 49, 7, 7, 1]]

def T7 : List (List ℤ) :=
  [[1, 8, 36, 36, 120, 120, 624, 8, 36, 120, 120, 540, 36, 120, 330, 148, 498, 582, 1842, 2052, 9906],
   [8, 1, 8, 8, 36, 36, 232, 148, 204, 1086, 1086, 7176, 36, 834, 5328, 8, 64, 64, 288, 288, 1856],
   [36, 8, 1, 232, 36, 36, 8, 624, 7176, 1086, 1086, 204, 204, 1086, 204, 64, 8, 1856, 288, 288, 64],
   [36, 8, 232, 1, 8, 8, 64, 708, 36, 288, 288, 2304, 204, 204, 1632, 64, 1856, 8, 64, 64, 512],
   [120, 36, 36, 8, 1, 64, 8, 2472, 288, 36, 2304, 288, 750, 1632, 204, 288, 288, 64, 8, 512, 64],
   [120, 36, 36, 8, 64, 1, 8, 2682, 288, 2304, 36, 288, 834, 36, 288, 288, 288, 64, 512, 8, 64],
   [624, 232, 8, 64, 8, 8, 1, 14190, 2304, 288, 288, 36, 4698, 288, 36, 1856, 64, 512, 64, 64, 8],
   [8, 148, 624, 708, 2472, 2682, 14190, 1, 8, 36, 36, 204, 8, 36, 120, 36, 120, 148, 498, 582, 2976],
   [36, 204, 7176, 36, 288, 288, 2304, 8, 1, 8, 8, 64, 148, 204, 1632, 36, 1380, 8, 64, 64, 512],
   [120, 1086, 1086, 288, 36, 2304, 288, 36, 8, 1, 64, 8, 624, 1632, 204, 204, 204, 64, 8, 512, 64],
   [120, 1086, 1086, 288, 2304, 36, 288, 36, 8, 64, 1, 8, 708, 36, 288, 204, 204, 64, 512, 8, 64],
   [540, 7176, 204, 2304, 288, 288, 36, 204, 64, 8, 8, 1, 3984, 288, 36, 1380, 36, 512, 64, 64, 8],
   [36, 36, 204, 204, 750, 834, 4698, 8, 148, 624, 708, 3984, 1, 8, 36, 8, 36, 36, 120, 148, 792],
   [120, 834, 1086, 204, 1632, 36, 288, 36, 204, 1632, 36, 288, 8, 1, 8, 148, 204, 36, 288, 8, 64],
   [330, 5328, 204, 1632, 204, 288, 36, 120, 1632, 204, 288, 36, 36, 8, 1, 918, 36, 288, 36, 64, 8],
   [148, 8, 64, 64, 288, 288, 1856, 36, 36, 204, 204, 1380, 8, 148, 918, 1, 8, 8, 36, 36, 232],
   [498, 64, 8, 1856, 288, 288, 64, 120, 1380, 204, 204, 36, 36, 204, 36, 8, 1, 232, 36, 36, 8],
   [582, 64, 1856, 8, 64, 64, 512, 148, 8, 64, 64, 512, 36, 36, 288, 8, 232, 1, 8, 8, 64],
   [1842, 288, 288, 64, 8, 512, 64, 498, 64, 8, 512, 64, 120, 288, 36, 36, 36, 8, 1, 64, 8],
   [2052, 288, 288, 64, 512, 8, 64, 582, 64, 512, 8, 64, 148, 8, 64, 36, 36, 8, 64, 1, 8],
   [9906, 1856, 64, 512, 64, 64, 8, 2976, 512, 64, 64, 8, 792, 64, 8, 232, 8, 64, 8, 8, 1]]

theorem hT0 : rows.map (fun _ => rows.map (fun _ => (1 : ℤ))) = T0 := by decide +kernel

theorem hT1 : stepB (dec 21 masks) T0 = T1 := by decide +kernel

theorem hT2 : stepB (dec 21 masks) T1 = T2 := by decide +kernel

theorem hT3 : stepB (dec 21 masks) T2 = T3 := by decide +kernel

theorem hT4 : stepB (dec 21 masks) T3 = T4 := by decide +kernel

theorem hT5 : stepB (dec 21 masks) T4 = T5 := by decide +kernel

theorem hT6 : stepB (dec 21 masks) T5 = T6 := by decide +kernel

theorem hT7 : stepB (dec 21 masks) T6 = T7 := by decide +kernel

theorem hchk : combTB (dec 21 masks) (rows.map (fun _ => rows.map (fun _ => 0))) [-1, 7, -21, 35, -35, 21, -7, 1]
    (rows.map (fun _ => rows.map (fun _ => 1))) = rows.map (fun _ => rows.map (fun _ => 0)) := by
  simp only [combTB, hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7]
  decide +kernel

theorem val0 : C (Vt (0, 0, 1) (1, 1, 0)) rows 0 = 441 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl]
  simp only [iterB, hT0]
  decide +kernel

theorem val1 : C (Vt (0, 0, 1) (1, 1, 0)) rows 1 = 2307 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl]
  simp only [iterB, hT0, hT1]
  decide +kernel

theorem val2 : C (Vt (0, 0, 1) (1, 1, 0)) rows 2 = 7561 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl]
  simp only [iterB, hT0, hT1, hT2]
  decide +kernel

theorem val3 : C (Vt (0, 0, 1) (1, 1, 0)) rows 3 = 19319 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3]
  decide +kernel

theorem val4 : C (Vt (0, 0, 1) (1, 1, 0)) rows 4 = 42167 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3, hT4]
  decide +kernel

theorem val5 : C (Vt (0, 0, 1) (1, 1, 0)) rows 5 = 82477 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3, hT4, hT5]
  decide +kernel

theorem val6 : C (Vt (0, 0, 1) (1, 1, 0)) rows 6 = 148743 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3, hT4, hT5, hT6]
  decide +kernel

theorem vals : C (Vt (0, 0, 1) (1, 1, 0)) rows 0 = 441 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 1 = 2307 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 2 = 7561 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 3 = 19319 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 4 = 42167 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 5 = 82477 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 6 = 148743 :=
  ⟨val0, val1, val2, val3, val4, val5, val6⟩

theorem a_C (m : ℕ) : a (m + 2) = C (Vt (0, 0, 1) (1, 1, 0)) rows m := by
  classical
  rw [← card_eq_C (Hrow (0, 0, 1) (0, 1, 0)) (Vt (0, 0, 1) (1, 1, 0)) rows hN hH m]
  unfold a
  refine congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun x _ => ?_))
  simp only [avoids, decide_eq_true_eq]
  exact avoid_iff _ _ _ _ x

theorem a_1 : a 1 = 21 := by
  classical
  have h := card_one (Hrow (0, 0, 1) (0, 1, 0)) (Vt (0, 0, 1) (1, 1, 0)) rows hN hH
  rw [show ((rows.length : ℕ) : ℤ) = 21 from rfl] at h
  rw [← h]
  unfold a
  refine congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun x _ => ?_))
  simp only [avoids, decide_eq_true_eq]
  exact avoid_iff _ _ _ _ x

theorem recZ (m : ℕ) : -a (m + 2) + 7 * a (m + 3) - 21 * a (m + 4) + 35 * a (m + 5) - 35 * a (m + 6) + 21 * a (m + 7) - 7 * a (m + 8) + a (m + 9) = 0 := by
  have h := rec_CB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 21 masks) htbl [-1, 7, -21, 35, -35, 21, -7, 1] hchk m
  simp only [combC] at h
  rw [a_C, a_C, a_C, a_C, a_C, a_C, a_C, a_C]
  linarith

end OMA.P207389

theorem OMA.solution : type_of% @OMA.S_oeis_a207389.main := by
  have A1 : (OMA.S_oeis_a207389.a 1 : ℚ) = 21 := by exact_mod_cast OMA.P207389.a_1
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := OMA.P207389.vals
  have A2 : (OMA.S_oeis_a207389.a 2 : ℚ) = 441 := by
    have h := OMA.P207389.a_C 0
    rw [v0] at h
    exact_mod_cast h
  have A3 : (OMA.S_oeis_a207389.a 3 : ℚ) = 2307 := by
    have h := OMA.P207389.a_C 1
    rw [v1] at h
    exact_mod_cast h
  have A4 : (OMA.S_oeis_a207389.a 4 : ℚ) = 7561 := by
    have h := OMA.P207389.a_C 2
    rw [v2] at h
    exact_mod_cast h
  have A5 : (OMA.S_oeis_a207389.a 5 : ℚ) = 19319 := by
    have h := OMA.P207389.a_C 3
    rw [v3] at h
    exact_mod_cast h
  have A6 : (OMA.S_oeis_a207389.a 6 : ℚ) = 42167 := by
    have h := OMA.P207389.a_C 4
    rw [v4] at h
    exact_mod_cast h
  have A7 : (OMA.S_oeis_a207389.a 7 : ℚ) = 82477 := by
    have h := OMA.P207389.a_C 5
    rw [v5] at h
    exact_mod_cast h
  have A8 : (OMA.S_oeis_a207389.a 8 : ℚ) = 148743 := by
    have h := OMA.P207389.a_C 6
    rw [v6] at h
    exact_mod_cast h
  have hrec : ∀ m : ℕ, (OMA.S_oeis_a207389.a (m + 9) : ℚ) = OMA.S_oeis_a207389.a (m + 2) - 7 * OMA.S_oeis_a207389.a (m + 3) + 21 * OMA.S_oeis_a207389.a (m + 4) - 35 * OMA.S_oeis_a207389.a (m + 5) + 35 * OMA.S_oeis_a207389.a (m + 6) - 21 * OMA.S_oeis_a207389.a (m + 7) + 7 * OMA.S_oeis_a207389.a (m + 8) := by
    intro m
    have h := OMA.P207389.recZ m
    have h' : (-(OMA.S_oeis_a207389.a (m + 2) : ℚ) + 7 * (OMA.S_oeis_a207389.a (m + 3) : ℚ) - 21 * (OMA.S_oeis_a207389.a (m + 4) : ℚ) + 35 * (OMA.S_oeis_a207389.a (m + 5) : ℚ) - 35 * (OMA.S_oeis_a207389.a (m + 6) : ℚ) + 21 * (OMA.S_oeis_a207389.a (m + 7) : ℚ) - 7 * (OMA.S_oeis_a207389.a (m + 8) : ℚ) + (OMA.S_oeis_a207389.a (m + 9) : ℚ) : ℚ) = 0 := by exact_mod_cast h
    linarith
  refine ⟨?_, ?_⟩
  · have hD : (((1 - PowerSeries.X) ^ 7) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (21 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-35 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (35 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-21 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 7 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have hNum : ((PowerSeries.X * (21 + 294 * PowerSeries.X - 339 * PowerSeries.X ^ 2 - 62 * PowerSeries.X ^ 3 + 139 * PowerSeries.X ^ 4 - 36 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6)) : PowerSeries ℚ)
        = PowerSeries.C (0 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (21 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (294 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-339 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-62 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (139 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (-36 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 7 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have key : ∀ F : PowerSeries ℚ, F * (PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (21 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-35 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (35 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-21 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 7)
        = PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 0) + PowerSeries.C (-7 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (21 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (-35 : ℚ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (35 : ℚ) * (F * PowerSeries.X ^ 4) + PowerSeries.C (-21 : ℚ) * (F * PowerSeries.X ^ 5) + PowerSeries.C (7 : ℚ) * (F * PowerSeries.X ^ 6) + PowerSeries.C (-1 : ℚ) * (F * PowerSeries.X ^ 7) := by
      intro F; ring
    rw [hD, hNum, key]
    ext n
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | m
    · norm_num
    · norm_num [A1]
    · norm_num [A1, A2]
    · norm_num [A1, A2, A3]
    · norm_num [A1, A2, A3, A4]
    · norm_num [A1, A2, A3, A4, A5]
    · norm_num [A1, A2, A3, A4, A5, A6]
    · norm_num [A1, A2, A3, A4, A5, A6, A7]
    · norm_num [A1, A2, A3, A4, A5, A6, A7, A8]
    · rw [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 9 from rfl]
      have h := hrec m
      simp only [show 0 ≤ m + 9 from by omega,
        show m + 9 - 0 = m + 9 from rfl,
        show ¬ (m + 9 < 1) from by omega,
        show 1 ≤ m + 9 from by omega,
        show m + 9 - 1 = m + 8 from rfl,
        show ¬ (m + 8 < 1) from by omega,
        show 2 ≤ m + 9 from by omega,
        show m + 9 - 2 = m + 7 from rfl,
        show ¬ (m + 7 < 1) from by omega,
        show 3 ≤ m + 9 from by omega,
        show m + 9 - 3 = m + 6 from rfl,
        show ¬ (m + 6 < 1) from by omega,
        show 4 ≤ m + 9 from by omega,
        show m + 9 - 4 = m + 5 from rfl,
        show ¬ (m + 5 < 1) from by omega,
        show 5 ≤ m + 9 from by omega,
        show m + 9 - 5 = m + 4 from rfl,
        show ¬ (m + 4 < 1) from by omega,
        show 6 ≤ m + 9 from by omega,
        show m + 9 - 6 = m + 3 from rfl,
        show ¬ (m + 3 < 1) from by omega,
        show 7 ≤ m + 9 from by omega,
        show m + 9 - 7 = m + 2 from rfl,
        show ¬ (m + 2 < 1) from by omega,
        show ¬ (m + 9 = 0) from by omega,
        show ¬ (m + 8 = 0) from by omega,
        show ¬ (m + 7 = 0) from by omega,
        show ¬ (m + 6 = 0) from by omega,
        show ¬ (m + 5 = 0) from by omega,
        show ¬ (m + 4 = 0) from by omega,
        show ¬ (m + 3 = 0) from by omega,
        show ¬ (m + 2 = 0) from by omega,
        if_true, if_false]
      rw [h]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 9 with h | h
    · interval_cases n <;> norm_num [A1, A2, A3, A4, A5, A6, A7, A8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have h := hrec m
      simp only [show m + 9 - 1 = m + 8 from rfl, show m + 9 - 2 = m + 7 from rfl, show m + 9 - 3 = m + 6 from rfl, show m + 9 - 4 = m + 5 from rfl, show m + 9 - 5 = m + 4 from rfl, show m + 9 - 6 = m + 3 from rfl, show m + 9 - 7 = m + 2 from rfl]
      rw [h]
      ring
