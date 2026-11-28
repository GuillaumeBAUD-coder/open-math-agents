import OMAStatements.S_oeis_a207390

-- Problem: oeis-a207390
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

namespace OMA.P207390
open OMA.Arr OMA.S_oeis_a207390

def rows : List (Fin 7 → Fin 2) :=
  [(mkRow 7 [0, 0, 0, 0, 0, 0, 0]), (mkRow 7 [0, 1, 1, 0, 0, 0, 0]), (mkRow 7 [0, 1, 1, 0, 1, 1, 0]), (mkRow 7 [0, 1, 1, 0, 1, 1, 1]), (mkRow 7 [0, 1, 1, 1, 0, 0, 0]), (mkRow 7 [0, 1, 1, 1, 0, 1, 1]), (mkRow 7 [0, 1, 1, 1, 1, 0, 0]), (mkRow 7 [0, 1, 1, 1, 1, 0, 1]), (mkRow 7 [0, 1, 1, 1, 1, 1, 0]), (mkRow 7 [0, 1, 1, 1, 1, 1, 1]), (mkRow 7 [1, 0, 0, 0, 0, 0, 0]), (mkRow 7 [1, 0, 1, 1, 0, 0, 0]), (mkRow 7 [1, 0, 1, 1, 0, 1, 1]), (mkRow 7 [1, 0, 1, 1, 1, 0, 0]), (mkRow 7 [1, 0, 1, 1, 1, 0, 1]), (mkRow 7 [1, 0, 1, 1, 1, 1, 0]), (mkRow 7 [1, 0, 1, 1, 1, 1, 1]), (mkRow 7 [1, 1, 0, 0, 0, 0, 0]), (mkRow 7 [1, 1, 0, 1, 1, 0, 0]), (mkRow 7 [1, 1, 0, 1, 1, 0, 1]), (mkRow 7 [1, 1, 0, 1, 1, 1, 0]), (mkRow 7 [1, 1, 0, 1, 1, 1, 1]), (mkRow 7 [1, 1, 1, 0, 0, 0, 0]), (mkRow 7 [1, 1, 1, 0, 1, 1, 0]), (mkRow 7 [1, 1, 1, 0, 1, 1, 1]), (mkRow 7 [1, 1, 1, 1, 0, 0, 0]), (mkRow 7 [1, 1, 1, 1, 0, 1, 1]), (mkRow 7 [1, 1, 1, 1, 1, 0, 0]), (mkRow 7 [1, 1, 1, 1, 1, 0, 1]), (mkRow 7 [1, 1, 1, 1, 1, 1, 0]), (mkRow 7 [1, 1, 1, 1, 1, 1, 1])]

theorem hN : rows.Nodup := by decide +kernel

theorem hH : ∀ u : Fin 7 → Fin 2, Hrow (0, 0, 1) (0, 1, 0) u ↔ u ∈ rows := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

def masks : List (List ℕ) :=
  [[1, 3, 7, 15, 19, 51, 83, 211, 343, 1023, 1025, 3073, 7169, 11265, 27649, 44033, 130049, 132097, 394241, 918529, 1442817, 4064257, 4326403, 12715015, 29492239, 37882899, 104995891, 172371027, 441347283, 718712151, 2147483647],
   [3, 2, 6, 14, 18, 50, 82, 210, 342, 1022, 4326403, 37750802, 104863794, 171976786, 440428754, 717269334, 2143419390, 4325378, 172359762, 441319634, 718668118, 2147353598, 4194306, 12582918, 29360142, 37748754, 104857650, 171966546, 440402130, 717226326, 2143290366],
   [7, 6, 4, 12, 342, 812, 324, 972, 260, 780, 12715015, 717269334, 1702990636, 679518532, 2038555596, 545292548, 1635877644, 12713990, 680788292, 2042364876, 546308356, 1638925068, 12582918, 8388612, 25165836, 717226326, 1702888236, 679477572, 2038432716, 545259780, 1635779340],
   [15, 14, 12, 8, 1022, 552, 972, 648, 780, 520, 29492239, 2143419390, 1157698088, 2038555596, 1359037064, 1635877644, 1090585096, 29491214, 2042364876, 1361576584, 1638925068, 1092616712, 29360142, 25165836, 16777224, 2143290366, 1157628456, 2038432716, 1358955144, 1635779340, 1090519560],
   [19, 18, 342, 1022, 16, 48, 80, 208, 336, 1008, 37882899, 33556496, 100669488, 167782480, 436234448, 704686416, 2114059248, 37879826, 168034384, 436994256, 705954128, 2117862384, 37748754, 717226326, 2143290366, 33554448, 100663344, 167772240, 436207824, 704643408, 2113930224],
   [51, 50, 812, 552, 48, 32, 1008, 672, 800, 544, 104995891, 100669488, 67112992, 2114059248, 1409372832, 1677824800, 1140920864, 104988722, 2117862384, 1411908256, 1680868128, 1142948384, 104857650, 1702888236, 1157628456, 100663344, 67108896, 2113930224, 1409286816, 1677722400, 1140851232],
   [83, 82, 324, 972, 80, 1008, 64, 192, 320, 960, 172371027, 167782480, 2114059248, 134225984, 402677952, 671129920, 2013389760, 172359762, 134479936, 403439808, 672399680, 2017199040, 171966546, 679477572, 2038432716, 167772240, 2113930224, 134217792, 402653376, 671088960, 2013266880],
   [211, 210, 972, 648, 208, 672, 192, 128, 960, 640, 441347283, 436234448, 1409372832, 402677952, 268451968, 2013389760, 1342259840, 441319634, 403439808, 268959872, 2017199040, 1344799360, 440402130, 2038432716, 1358955144, 436207824, 1409286816, 402653376, 268435584, 2013266880, 1342177920],
   [343, 342, 260, 780, 336, 800, 320, 960, 256, 768, 718712151, 704686416, 1677824800, 671129920, 2013389760, 536903936, 1610711808, 718668118, 672399680, 2017199040, 537919744, 1613759232, 717226326, 545259780, 1635779340, 704643408, 1677722400, 671088960, 2013266880, 536871168, 1610613504],
   [1023, 1022, 780, 520, 1008, 544, 960, 640, 768, 512, 2147483647, 2114059248, 1140920864, 2013389760, 1342259840, 1610711808, 1073807872, 2147353598, 2017199040, 1344799360, 1613759232, 1075839488, 2143290366, 1635779340, 1090519560, 2113930224, 1140851232, 2013266880, 1342177920, 1610613504, 1073742336],
   [1025, 4326403, 12715015, 29492239, 37882899, 104995891, 172371027, 441347283, 718712151, 2147483647, 1024, 3072, 7168, 11264, 27648, 44032, 130048, 132096, 394240, 918528, 1442816, 4064256, 4326400, 12715008, 29492224, 37882880, 104995840, 172370944, 441347072, 718711808, 2147482624],
   [3073, 37750802, 717269334, 2143419390, 33556496, 100669488, 167782480, 436234448, 704686416, 2114059248, 3072, 2048, 6144, 10240, 26624, 43008, 129024, 37882880, 168044544, 437020672, 705996800, 2117990400, 37750784, 717268992, 2143418368, 33556480, 100669440, 167782400, 436234240, 704686080, 2114058240],
   [7169, 104863794, 1702990636, 1157698088, 100669488, 67112992, 2114059248, 1409372832, 1677824800, 1140920864, 7168, 6144, 4096, 129024, 86016, 102400, 69632, 104995840, 2117990400, 1411993600, 1680969728, 1143017472, 104863744, 1702989824, 1157697536, 100669440, 67112960, 2114058240, 1409372160, 1677824000, 1140920320],
   [11265, 171976786, 679518532, 2038555596, 167782480, 2114059248, 134225984, 402677952, 671129920, 2013389760, 11264, 10240, 129024, 8192, 24576, 40960, 122880, 172370944, 134488064, 403464192, 672440320, 2017320960, 171976704, 679518208, 2038554624, 167782400, 2114058240, 134225920, 402677760, 671129600, 2013388800],
   [27649, 440428754, 2038555596, 1359037064, 436234448, 1409372832, 402677952, 268451968, 2013389760, 1342259840, 27648, 26624, 86016, 24576, 16384, 122880, 81920, 441347072, 403464192, 268976128, 2017320960, 1344880640, 440428544, 2038554624, 1359036416, 436234240, 1409372160, 402677760, 268451840, 2013388800, 1342259200],
   [44033, 717269334, 545292548, 1635877644, 704686416, 1677824800, 671129920, 2013389760, 536903936, 1610711808, 44032, 43008, 102400, 40960, 122880, 32768, 98304, 718711808, 672440320, 2017320960, 537952256, 1613856768, 717268992, 545292288, 1635876864, 704686080, 1677824000, 671129600, 2013388800, 536903680, 1610711040],
   [130049, 2143419390, 1635877644, 1090585096, 2114059248, 1140920864, 2013389760, 1342259840, 1610711808, 1073807872, 130048, 129024, 69632, 122880, 81920, 98304, 65536, 2147482624, 2017320960, 1344880640, 1613856768, 1075904512, 2143418368, 1635876864, 1090584576, 2114058240, 1140920320, 2013388800, 1342259200, 1610711040, 1073807360],
   [132097, 4325378, 12713990, 29491214, 37879826, 104988722, 172359762, 441319634, 718668118, 2147353598, 132096, 37882880, 104995840, 172370944, 441347072, 718711808, 2147482624, 131072, 393216, 917504, 1441792, 4063232, 4325376, 12713984, 29491200, 37879808, 104988672, 172359680, 441319424, 718667776, 2147352576],
   [394241, 172359762, 680788292, 2042364876, 168034384, 2117862384, 134479936, 403439808, 672399680, 2017199040, 394240, 168044544, 2117990400, 134488064, 403464192, 672440320, 2017320960, 393216, 262144, 786432, 1310720, 3932160, 172359680, 680787968, 2042363904, 168034304, 2117861376, 134479872, 403439616, 672399360, 2017198080],
   [918529, 441319634, 2042364876, 1361576584, 436994256, 1411908256, 403439808, 268959872, 2017199040, 1344799360, 918528, 437020672, 1411993600, 403464192, 268976128, 2017320960, 1344880640, 917504, 786432, 524288, 3932160, 2621440, 441319424, 2042363904, 1361575936, 436994048, 1411907584, 403439616, 268959744, 2017198080, 1344798720],
   [1442817, 718668118, 546308356, 1638925068, 705954128, 1680868128, 672399680, 2017199040, 537919744, 1613759232, 1442816, 705996800, 1680969728, 672440320, 2017320960, 537952256, 1613856768, 1441792, 1310720, 3932160, 1048576, 3145728, 718667776, 546308096, 1638924288, 705953792, 1680867328, 672399360, 2017198080, 537919488, 1613758464],
   [4064257, 2147353598, 1638925068, 1092616712, 2117862384, 1142948384, 2017199040, 1344799360, 1613759232, 1075839488, 4064256, 2117990400, 1143017472, 2017320960, 1344880640, 1613856768, 1075904512, 4063232, 3932160, 2621440, 3145728, 2097152, 2147352576, 1638924288, 1092616192, 2117861376, 1142947840, 2017198080, 1344798720, 1613758464, 1075838976],
   [4326403, 4194306, 12582918, 29360142, 37748754, 104857650, 171966546, 440402130, 717226326, 2143290366, 4326400, 37750784, 104863744, 171976704, 440428544, 717268992, 2143418368, 4325376, 172359680, 441319424, 718667776, 2147352576, 4194304, 12582912, 29360128, 37748736, 104857600, 171966464, 440401920, 717225984, 2143289344],
   [12715015, 12582918, 8388612, 25165836, 717226326, 1702888236, 679477572, 2038432716, 545259780, 1635779340, 12715008, 717268992, 1702989824, 679518208, 2038554624, 545292288, 1635876864, 12713984, 680787968, 2042363904, 546308096, 1638924288, 12582912, 8388608, 25165824, 717225984, 1702887424, 679477248, 2038431744, 545259520, 1635778560],
   [29492239, 29360142, 25165836, 16777224, 2143290366, 1157628456, 2038432716, 1358955144, 1635779340, 1090519560, 29492224, 2143418368, 1157697536, 2038554624, 1359036416, 1635876864, 1090584576, 29491200, 2042363904, 1361575936, 1638924288, 1092616192, 29360128, 25165824, 16777216, 2143289344, 1157627904, 2038431744, 1358954496, 1635778560, 1090519040],
   [37882899, 37748754, 717226326, 2143290366, 33554448, 100663344, 167772240, 436207824, 704643408, 2113930224, 37882880, 33556480, 100669440, 167782400, 436234240, 704686080, 2114058240, 37879808, 168034304, 436994048, 705953792, 2117861376, 37748736, 717225984, 2143289344, 33554432, 100663296, 167772160, 436207616, 704643072, 2113929216],
   [104995891, 104857650, 1702888236, 1157628456, 100663344, 67108896, 2113930224, 1409286816, 1677722400, 1140851232, 104995840, 100669440, 67112960, 2114058240, 1409372160, 1677824000, 1140920320, 104988672, 2117861376, 1411907584, 1680867328, 1142947840, 104857600, 1702887424, 1157627904, 100663296, 67108864, 2113929216, 1409286144, 1677721600, 1140850688],
   [172371027, 171966546, 679477572, 2038432716, 167772240, 2113930224, 134217792, 402653376, 671088960, 2013266880, 172370944, 167782400, 2114058240, 134225920, 402677760, 671129600, 2013388800, 172359680, 134479872, 403439616, 672399360, 2017198080, 171966464, 679477248, 2038431744, 167772160, 2113929216, 134217728, 402653184, 671088640, 2013265920],
   [441347283, 440402130, 2038432716, 1358955144, 436207824, 1409286816, 402653376, 268435584, 2013266880, 1342177920, 441347072, 436234240, 1409372160, 402677760, 268451840, 2013388800, 1342259200, 441319424, 403439616, 268959744, 2017198080, 1344798720, 440401920, 2038431744, 1358954496, 436207616, 1409286144, 402653184, 268435456, 2013265920, 1342177280],
   [718712151, 717226326, 545259780, 1635779340, 704643408, 1677722400, 671088960, 2013266880, 536871168, 1610613504, 718711808, 704686080, 1677824000, 671129600, 2013388800, 536903680, 1610711040, 718667776, 672399360, 2017198080, 537919488, 1613758464, 717225984, 545259520, 1635778560, 704643072, 1677721600, 671088640, 2013265920, 536870912, 1610612736],
   [2147483647, 2143290366, 1635779340, 1090519560, 2113930224, 1140851232, 2013266880, 1342177920, 1610613504, 1073742336, 2147482624, 2114058240, 1140920320, 2013388800, 1342259200, 1610711040, 1073807360, 2147352576, 2017198080, 1344798720, 1613758464, 1075838976, 2143289344, 1635778560, 1090519040, 2113929216, 1140850688, 2013265920, 1342177280, 1610612736, 1073741824]]

theorem ht0 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 0, 0, 0, 0, 0, 0]) = decRow 31 [1, 3, 7, 15, 19, 51, 83, 211, 343, 1023, 1025, 3073, 7169, 11265, 27649, 44033, 130049, 132097, 394241, 918529, 1442817, 4064257, 4326403, 12715015, 29492239, 37882899, 104995891, 172371027, 441347283, 718712151, 2147483647] := by
  decide +kernel

theorem ht1 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 0, 0, 0, 0]) = decRow 31 [3, 2, 6, 14, 18, 50, 82, 210, 342, 1022, 4326403, 37750802, 104863794, 171976786, 440428754, 717269334, 2143419390, 4325378, 172359762, 441319634, 718668118, 2147353598, 4194306, 12582918, 29360142, 37748754, 104857650, 171966546, 440402130, 717226326, 2143290366] := by
  decide +kernel

theorem ht2 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 0, 1, 1, 0]) = decRow 31 [7, 6, 4, 12, 342, 812, 324, 972, 260, 780, 12715015, 717269334, 1702990636, 679518532, 2038555596, 545292548, 1635877644, 12713990, 680788292, 2042364876, 546308356, 1638925068, 12582918, 8388612, 25165836, 717226326, 1702888236, 679477572, 2038432716, 545259780, 1635779340] := by
  decide +kernel

theorem ht3 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 0, 1, 1, 1]) = decRow 31 [15, 14, 12, 8, 1022, 552, 972, 648, 780, 520, 29492239, 2143419390, 1157698088, 2038555596, 1359037064, 1635877644, 1090585096, 29491214, 2042364876, 1361576584, 1638925068, 1092616712, 29360142, 25165836, 16777224, 2143290366, 1157628456, 2038432716, 1358955144, 1635779340, 1090519560] := by
  decide +kernel

theorem ht4 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 1, 0, 0, 0]) = decRow 31 [19, 18, 342, 1022, 16, 48, 80, 208, 336, 1008, 37882899, 33556496, 100669488, 167782480, 436234448, 704686416, 2114059248, 37879826, 168034384, 436994256, 705954128, 2117862384, 37748754, 717226326, 2143290366, 33554448, 100663344, 167772240, 436207824, 704643408, 2113930224] := by
  decide +kernel

theorem ht5 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 1, 0, 1, 1]) = decRow 31 [51, 50, 812, 552, 48, 32, 1008, 672, 800, 544, 104995891, 100669488, 67112992, 2114059248, 1409372832, 1677824800, 1140920864, 104988722, 2117862384, 1411908256, 1680868128, 1142948384, 104857650, 1702888236, 1157628456, 100663344, 67108896, 2113930224, 1409286816, 1677722400, 1140851232] := by
  decide +kernel

theorem ht6 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 1, 1, 0, 0]) = decRow 31 [83, 82, 324, 972, 80, 1008, 64, 192, 320, 960, 172371027, 167782480, 2114059248, 134225984, 402677952, 671129920, 2013389760, 172359762, 134479936, 403439808, 672399680, 2017199040, 171966546, 679477572, 2038432716, 167772240, 2113930224, 134217792, 402653376, 671088960, 2013266880] := by
  decide +kernel

theorem ht7 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 1, 1, 0, 1]) = decRow 31 [211, 210, 972, 648, 208, 672, 192, 128, 960, 640, 441347283, 436234448, 1409372832, 402677952, 268451968, 2013389760, 1342259840, 441319634, 403439808, 268959872, 2017199040, 1344799360, 440402130, 2038432716, 1358955144, 436207824, 1409286816, 402653376, 268435584, 2013266880, 1342177920] := by
  decide +kernel

theorem ht8 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 1, 1, 1, 0]) = decRow 31 [343, 342, 260, 780, 336, 800, 320, 960, 256, 768, 718712151, 704686416, 1677824800, 671129920, 2013389760, 536903936, 1610711808, 718668118, 672399680, 2017199040, 537919744, 1613759232, 717226326, 545259780, 1635779340, 704643408, 1677722400, 671088960, 2013266880, 536871168, 1610613504] := by
  decide +kernel

theorem ht9 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [0, 1, 1, 1, 1, 1, 1]) = decRow 31 [1023, 1022, 780, 520, 1008, 544, 960, 640, 768, 512, 2147483647, 2114059248, 1140920864, 2013389760, 1342259840, 1610711808, 1073807872, 2147353598, 2017199040, 1344799360, 1613759232, 1075839488, 2143290366, 1635779340, 1090519560, 2113930224, 1140851232, 2013266880, 1342177920, 1610613504, 1073742336] := by
  decide +kernel

theorem ht10 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 0, 0, 0, 0, 0, 0]) = decRow 31 [1025, 4326403, 12715015, 29492239, 37882899, 104995891, 172371027, 441347283, 718712151, 2147483647, 1024, 3072, 7168, 11264, 27648, 44032, 130048, 132096, 394240, 918528, 1442816, 4064256, 4326400, 12715008, 29492224, 37882880, 104995840, 172370944, 441347072, 718711808, 2147482624] := by
  decide +kernel

theorem ht11 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 0, 1, 1, 0, 0, 0]) = decRow 31 [3073, 37750802, 717269334, 2143419390, 33556496, 100669488, 167782480, 436234448, 704686416, 2114059248, 3072, 2048, 6144, 10240, 26624, 43008, 129024, 37882880, 168044544, 437020672, 705996800, 2117990400, 37750784, 717268992, 2143418368, 33556480, 100669440, 167782400, 436234240, 704686080, 2114058240] := by
  decide +kernel

theorem ht12 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 0, 1, 1, 0, 1, 1]) = decRow 31 [7169, 104863794, 1702990636, 1157698088, 100669488, 67112992, 2114059248, 1409372832, 1677824800, 1140920864, 7168, 6144, 4096, 129024, 86016, 102400, 69632, 104995840, 2117990400, 1411993600, 1680969728, 1143017472, 104863744, 1702989824, 1157697536, 100669440, 67112960, 2114058240, 1409372160, 1677824000, 1140920320] := by
  decide +kernel

theorem ht13 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 0, 1, 1, 1, 0, 0]) = decRow 31 [11265, 171976786, 679518532, 2038555596, 167782480, 2114059248, 134225984, 402677952, 671129920, 2013389760, 11264, 10240, 129024, 8192, 24576, 40960, 122880, 172370944, 134488064, 403464192, 672440320, 2017320960, 171976704, 679518208, 2038554624, 167782400, 2114058240, 134225920, 402677760, 671129600, 2013388800] := by
  decide +kernel

theorem ht14 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 0, 1, 1, 1, 0, 1]) = decRow 31 [27649, 440428754, 2038555596, 1359037064, 436234448, 1409372832, 402677952, 268451968, 2013389760, 1342259840, 27648, 26624, 86016, 24576, 16384, 122880, 81920, 441347072, 403464192, 268976128, 2017320960, 1344880640, 440428544, 2038554624, 1359036416, 436234240, 1409372160, 402677760, 268451840, 2013388800, 1342259200] := by
  decide +kernel

theorem ht15 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 0, 1, 1, 1, 1, 0]) = decRow 31 [44033, 717269334, 545292548, 1635877644, 704686416, 1677824800, 671129920, 2013389760, 536903936, 1610711808, 44032, 43008, 102400, 40960, 122880, 32768, 98304, 718711808, 672440320, 2017320960, 537952256, 1613856768, 717268992, 545292288, 1635876864, 704686080, 1677824000, 671129600, 2013388800, 536903680, 1610711040] := by
  decide +kernel

theorem ht16 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 0, 1, 1, 1, 1, 1]) = decRow 31 [130049, 2143419390, 1635877644, 1090585096, 2114059248, 1140920864, 2013389760, 1342259840, 1610711808, 1073807872, 130048, 129024, 69632, 122880, 81920, 98304, 65536, 2147482624, 2017320960, 1344880640, 1613856768, 1075904512, 2143418368, 1635876864, 1090584576, 2114058240, 1140920320, 2013388800, 1342259200, 1610711040, 1073807360] := by
  decide +kernel

theorem ht17 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 0, 0, 0, 0, 0]) = decRow 31 [132097, 4325378, 12713990, 29491214, 37879826, 104988722, 172359762, 441319634, 718668118, 2147353598, 132096, 37882880, 104995840, 172370944, 441347072, 718711808, 2147482624, 131072, 393216, 917504, 1441792, 4063232, 4325376, 12713984, 29491200, 37879808, 104988672, 172359680, 441319424, 718667776, 2147352576] := by
  decide +kernel

theorem ht18 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 0, 1, 1, 0, 0]) = decRow 31 [394241, 172359762, 680788292, 2042364876, 168034384, 2117862384, 134479936, 403439808, 672399680, 2017199040, 394240, 168044544, 2117990400, 134488064, 403464192, 672440320, 2017320960, 393216, 262144, 786432, 1310720, 3932160, 172359680, 680787968, 2042363904, 168034304, 2117861376, 134479872, 403439616, 672399360, 2017198080] := by
  decide +kernel

theorem ht19 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 0, 1, 1, 0, 1]) = decRow 31 [918529, 441319634, 2042364876, 1361576584, 436994256, 1411908256, 403439808, 268959872, 2017199040, 1344799360, 918528, 437020672, 1411993600, 403464192, 268976128, 2017320960, 1344880640, 917504, 786432, 524288, 3932160, 2621440, 441319424, 2042363904, 1361575936, 436994048, 1411907584, 403439616, 268959744, 2017198080, 1344798720] := by
  decide +kernel

theorem ht20 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 0, 1, 1, 1, 0]) = decRow 31 [1442817, 718668118, 546308356, 1638925068, 705954128, 1680868128, 672399680, 2017199040, 537919744, 1613759232, 1442816, 705996800, 1680969728, 672440320, 2017320960, 537952256, 1613856768, 1441792, 1310720, 3932160, 1048576, 3145728, 718667776, 546308096, 1638924288, 705953792, 1680867328, 672399360, 2017198080, 537919488, 1613758464] := by
  decide +kernel

theorem ht21 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 0, 1, 1, 1, 1]) = decRow 31 [4064257, 2147353598, 1638925068, 1092616712, 2117862384, 1142948384, 2017199040, 1344799360, 1613759232, 1075839488, 4064256, 2117990400, 1143017472, 2017320960, 1344880640, 1613856768, 1075904512, 4063232, 3932160, 2621440, 3145728, 2097152, 2147352576, 1638924288, 1092616192, 2117861376, 1142947840, 2017198080, 1344798720, 1613758464, 1075838976] := by
  decide +kernel

theorem ht22 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 0, 0, 0, 0]) = decRow 31 [4326403, 4194306, 12582918, 29360142, 37748754, 104857650, 171966546, 440402130, 717226326, 2143290366, 4326400, 37750784, 104863744, 171976704, 440428544, 717268992, 2143418368, 4325376, 172359680, 441319424, 718667776, 2147352576, 4194304, 12582912, 29360128, 37748736, 104857600, 171966464, 440401920, 717225984, 2143289344] := by
  decide +kernel

theorem ht23 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 0, 1, 1, 0]) = decRow 31 [12715015, 12582918, 8388612, 25165836, 717226326, 1702888236, 679477572, 2038432716, 545259780, 1635779340, 12715008, 717268992, 1702989824, 679518208, 2038554624, 545292288, 1635876864, 12713984, 680787968, 2042363904, 546308096, 1638924288, 12582912, 8388608, 25165824, 717225984, 1702887424, 679477248, 2038431744, 545259520, 1635778560] := by
  decide +kernel

theorem ht24 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 0, 1, 1, 1]) = decRow 31 [29492239, 29360142, 25165836, 16777224, 2143290366, 1157628456, 2038432716, 1358955144, 1635779340, 1090519560, 29492224, 2143418368, 1157697536, 2038554624, 1359036416, 1635876864, 1090584576, 29491200, 2042363904, 1361575936, 1638924288, 1092616192, 29360128, 25165824, 16777216, 2143289344, 1157627904, 2038431744, 1358954496, 1635778560, 1090519040] := by
  decide +kernel

theorem ht25 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 1, 0, 0, 0]) = decRow 31 [37882899, 37748754, 717226326, 2143290366, 33554448, 100663344, 167772240, 436207824, 704643408, 2113930224, 37882880, 33556480, 100669440, 167782400, 436234240, 704686080, 2114058240, 37879808, 168034304, 436994048, 705953792, 2117861376, 37748736, 717225984, 2143289344, 33554432, 100663296, 167772160, 436207616, 704643072, 2113929216] := by
  decide +kernel

theorem ht26 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 1, 0, 1, 1]) = decRow 31 [104995891, 104857650, 1702888236, 1157628456, 100663344, 67108896, 2113930224, 1409286816, 1677722400, 1140851232, 104995840, 100669440, 67112960, 2114058240, 1409372160, 1677824000, 1140920320, 104988672, 2117861376, 1411907584, 1680867328, 1142947840, 104857600, 1702887424, 1157627904, 100663296, 67108864, 2113929216, 1409286144, 1677721600, 1140850688] := by
  decide +kernel

theorem ht27 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 1, 1, 0, 0]) = decRow 31 [172371027, 171966546, 679477572, 2038432716, 167772240, 2113930224, 134217792, 402653376, 671088960, 2013266880, 172370944, 167782400, 2114058240, 134225920, 402677760, 671129600, 2013388800, 172359680, 134479872, 403439616, 672399360, 2017198080, 171966464, 679477248, 2038431744, 167772160, 2113929216, 134217728, 402653184, 671088640, 2013265920] := by
  decide +kernel

theorem ht28 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 1, 1, 0, 1]) = decRow 31 [441347283, 440402130, 2038432716, 1358955144, 436207824, 1409286816, 402653376, 268435584, 2013266880, 1342177920, 441347072, 436234240, 1409372160, 402677760, 268451840, 2013388800, 1342259200, 441319424, 403439616, 268959744, 2017198080, 1344798720, 440401920, 2038431744, 1358954496, 436207616, 1409286144, 402653184, 268435456, 2013265920, 1342177280] := by
  decide +kernel

theorem ht29 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 1, 1, 1, 0]) = decRow 31 [718712151, 717226326, 545259780, 1635779340, 704643408, 1677722400, 671088960, 2013266880, 536871168, 1610613504, 718711808, 704686080, 1677824000, 671129600, 2013388800, 536903680, 1610711040, 718667776, 672399360, 2017198080, 537919488, 1613758464, 717225984, 545259520, 1635778560, 704643072, 1677721600, 671088640, 2013265920, 536870912, 1610612736] := by
  decide +kernel

theorem ht30 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows (mkRow 7 [1, 1, 1, 1, 1, 1, 1]) = decRow 31 [2147483647, 2143290366, 1635779340, 1090519560, 2113930224, 1140851232, 2013266880, 1342177920, 1610613504, 1073742336, 2147482624, 2114058240, 1140920320, 2013388800, 1342259200, 1610711040, 1073807360, 2147352576, 2017198080, 1344798720, 1613758464, 1075838976, 2143289344, 1635778560, 1090519040, 2113929216, 1140850688, 2013265920, 1342177280, 1610612736, 1073741824] := by
  decide +kernel

theorem htbl : tblOf (Vt (0, 0, 1) (1, 1, 0)) rows = dec 31 masks := by
  show List.map (rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows) [(mkRow 7 [0, 0, 0, 0, 0, 0, 0]), (mkRow 7 [0, 1, 1, 0, 0, 0, 0]), (mkRow 7 [0, 1, 1, 0, 1, 1, 0]), (mkRow 7 [0, 1, 1, 0, 1, 1, 1]), (mkRow 7 [0, 1, 1, 1, 0, 0, 0]), (mkRow 7 [0, 1, 1, 1, 0, 1, 1]), (mkRow 7 [0, 1, 1, 1, 1, 0, 0]), (mkRow 7 [0, 1, 1, 1, 1, 0, 1]), (mkRow 7 [0, 1, 1, 1, 1, 1, 0]), (mkRow 7 [0, 1, 1, 1, 1, 1, 1]), (mkRow 7 [1, 0, 0, 0, 0, 0, 0]), (mkRow 7 [1, 0, 1, 1, 0, 0, 0]), (mkRow 7 [1, 0, 1, 1, 0, 1, 1]), (mkRow 7 [1, 0, 1, 1, 1, 0, 0]), (mkRow 7 [1, 0, 1, 1, 1, 0, 1]), (mkRow 7 [1, 0, 1, 1, 1, 1, 0]), (mkRow 7 [1, 0, 1, 1, 1, 1, 1]), (mkRow 7 [1, 1, 0, 0, 0, 0, 0]), (mkRow 7 [1, 1, 0, 1, 1, 0, 0]), (mkRow 7 [1, 1, 0, 1, 1, 0, 1]), (mkRow 7 [1, 1, 0, 1, 1, 1, 0]), (mkRow 7 [1, 1, 0, 1, 1, 1, 1]), (mkRow 7 [1, 1, 1, 0, 0, 0, 0]), (mkRow 7 [1, 1, 1, 0, 1, 1, 0]), (mkRow 7 [1, 1, 1, 0, 1, 1, 1]), (mkRow 7 [1, 1, 1, 1, 0, 0, 0]), (mkRow 7 [1, 1, 1, 1, 0, 1, 1]), (mkRow 7 [1, 1, 1, 1, 1, 0, 0]), (mkRow 7 [1, 1, 1, 1, 1, 0, 1]), (mkRow 7 [1, 1, 1, 1, 1, 1, 0]), (mkRow 7 [1, 1, 1, 1, 1, 1, 1])]
    = List.map (decRow 31) [[1, 3, 7, 15, 19, 51, 83, 211, 343, 1023, 1025, 3073, 7169, 11265, 27649, 44033, 130049, 132097, 394241, 918529, 1442817, 4064257, 4326403, 12715015, 29492239, 37882899, 104995891, 172371027, 441347283, 718712151, 2147483647], [3, 2, 6, 14, 18, 50, 82, 210, 342, 1022, 4326403, 37750802, 104863794, 171976786, 440428754, 717269334, 2143419390, 4325378, 172359762, 441319634, 718668118, 2147353598, 4194306, 12582918, 29360142, 37748754, 104857650, 171966546, 440402130, 717226326, 2143290366], [7, 6, 4, 12, 342, 812, 324, 972, 260, 780, 12715015, 717269334, 1702990636, 679518532, 2038555596, 545292548, 1635877644, 12713990, 680788292, 2042364876, 546308356, 1638925068, 12582918, 8388612, 25165836, 717226326, 1702888236, 679477572, 2038432716, 545259780, 1635779340], [15, 14, 12, 8, 1022, 552, 972, 648, 780, 520, 29492239, 2143419390, 1157698088, 2038555596, 1359037064, 1635877644, 1090585096, 29491214, 2042364876, 1361576584, 1638925068, 1092616712, 29360142, 25165836, 16777224, 2143290366, 1157628456, 2038432716, 1358955144, 1635779340, 1090519560], [19, 18, 342, 1022, 16, 48, 80, 208, 336, 1008, 37882899, 33556496, 100669488, 167782480, 436234448, 704686416, 2114059248, 37879826, 168034384, 436994256, 705954128, 2117862384, 37748754, 717226326, 2143290366, 33554448, 100663344, 167772240, 436207824, 704643408, 2113930224], [51, 50, 812, 552, 48, 32, 1008, 672, 800, 544, 104995891, 100669488, 67112992, 2114059248, 1409372832, 1677824800, 1140920864, 104988722, 2117862384, 1411908256, 1680868128, 1142948384, 104857650, 1702888236, 1157628456, 100663344, 67108896, 2113930224, 1409286816, 1677722400, 1140851232], [83, 82, 324, 972, 80, 1008, 64, 192, 320, 960, 172371027, 167782480, 2114059248, 134225984, 402677952, 671129920, 2013389760, 172359762, 134479936, 403439808, 672399680, 2017199040, 171966546, 679477572, 2038432716, 167772240, 2113930224, 134217792, 402653376, 671088960, 2013266880], [211, 210, 972, 648, 208, 672, 192, 128, 960, 640, 441347283, 436234448, 1409372832, 402677952, 268451968, 2013389760, 1342259840, 441319634, 403439808, 268959872, 2017199040, 1344799360, 440402130, 2038432716, 1358955144, 436207824, 1409286816, 402653376, 268435584, 2013266880, 1342177920], [343, 342, 260, 780, 336, 800, 320, 960, 256, 768, 718712151, 704686416, 1677824800, 671129920, 2013389760, 536903936, 1610711808, 718668118, 672399680, 2017199040, 537919744, 1613759232, 717226326, 545259780, 1635779340, 704643408, 1677722400, 671088960, 2013266880, 536871168, 1610613504], [1023, 1022, 780, 520, 1008, 544, 960, 640, 768, 512, 2147483647, 2114059248, 1140920864, 2013389760, 1342259840, 1610711808, 1073807872, 2147353598, 2017199040, 1344799360, 1613759232, 1075839488, 2143290366, 1635779340, 1090519560, 2113930224, 1140851232, 2013266880, 1342177920, 1610613504, 1073742336], [1025, 4326403, 12715015, 29492239, 37882899, 104995891, 172371027, 441347283, 718712151, 2147483647, 1024, 3072, 7168, 11264, 27648, 44032, 130048, 132096, 394240, 918528, 1442816, 4064256, 4326400, 12715008, 29492224, 37882880, 104995840, 172370944, 441347072, 718711808, 2147482624], [3073, 37750802, 717269334, 2143419390, 33556496, 100669488, 167782480, 436234448, 704686416, 2114059248, 3072, 2048, 6144, 10240, 26624, 43008, 129024, 37882880, 168044544, 437020672, 705996800, 2117990400, 37750784, 717268992, 2143418368, 33556480, 100669440, 167782400, 436234240, 704686080, 2114058240], [7169, 104863794, 1702990636, 1157698088, 100669488, 67112992, 2114059248, 1409372832, 1677824800, 1140920864, 7168, 6144, 4096, 129024, 86016, 102400, 69632, 104995840, 2117990400, 1411993600, 1680969728, 1143017472, 104863744, 1702989824, 1157697536, 100669440, 67112960, 2114058240, 1409372160, 1677824000, 1140920320], [11265, 171976786, 679518532, 2038555596, 167782480, 2114059248, 134225984, 402677952, 671129920, 2013389760, 11264, 10240, 129024, 8192, 24576, 40960, 122880, 172370944, 134488064, 403464192, 672440320, 2017320960, 171976704, 679518208, 2038554624, 167782400, 2114058240, 134225920, 402677760, 671129600, 2013388800], [27649, 440428754, 2038555596, 1359037064, 436234448, 1409372832, 402677952, 268451968, 2013389760, 1342259840, 27648, 26624, 86016, 24576, 16384, 122880, 81920, 441347072, 403464192, 268976128, 2017320960, 1344880640, 440428544, 2038554624, 1359036416, 436234240, 1409372160, 402677760, 268451840, 2013388800, 1342259200], [44033, 717269334, 545292548, 1635877644, 704686416, 1677824800, 671129920, 2013389760, 536903936, 1610711808, 44032, 43008, 102400, 40960, 122880, 32768, 98304, 718711808, 672440320, 2017320960, 537952256, 1613856768, 717268992, 545292288, 1635876864, 704686080, 1677824000, 671129600, 2013388800, 536903680, 1610711040], [130049, 2143419390, 1635877644, 1090585096, 2114059248, 1140920864, 2013389760, 1342259840, 1610711808, 1073807872, 130048, 129024, 69632, 122880, 81920, 98304, 65536, 2147482624, 2017320960, 1344880640, 1613856768, 1075904512, 2143418368, 1635876864, 1090584576, 2114058240, 1140920320, 2013388800, 1342259200, 1610711040, 1073807360], [132097, 4325378, 12713990, 29491214, 37879826, 104988722, 172359762, 441319634, 718668118, 2147353598, 132096, 37882880, 104995840, 172370944, 441347072, 718711808, 2147482624, 131072, 393216, 917504, 1441792, 4063232, 4325376, 12713984, 29491200, 37879808, 104988672, 172359680, 441319424, 718667776, 2147352576], [394241, 172359762, 680788292, 2042364876, 168034384, 2117862384, 134479936, 403439808, 672399680, 2017199040, 394240, 168044544, 2117990400, 134488064, 403464192, 672440320, 2017320960, 393216, 262144, 786432, 1310720, 3932160, 172359680, 680787968, 2042363904, 168034304, 2117861376, 134479872, 403439616, 672399360, 2017198080], [918529, 441319634, 2042364876, 1361576584, 436994256, 1411908256, 403439808, 268959872, 2017199040, 1344799360, 918528, 437020672, 1411993600, 403464192, 268976128, 2017320960, 1344880640, 917504, 786432, 524288, 3932160, 2621440, 441319424, 2042363904, 1361575936, 436994048, 1411907584, 403439616, 268959744, 2017198080, 1344798720], [1442817, 718668118, 546308356, 1638925068, 705954128, 1680868128, 672399680, 2017199040, 537919744, 1613759232, 1442816, 705996800, 1680969728, 672440320, 2017320960, 537952256, 1613856768, 1441792, 1310720, 3932160, 1048576, 3145728, 718667776, 546308096, 1638924288, 705953792, 1680867328, 672399360, 2017198080, 537919488, 1613758464], [4064257, 2147353598, 1638925068, 1092616712, 2117862384, 1142948384, 2017199040, 1344799360, 1613759232, 1075839488, 4064256, 2117990400, 1143017472, 2017320960, 1344880640, 1613856768, 1075904512, 4063232, 3932160, 2621440, 3145728, 2097152, 2147352576, 1638924288, 1092616192, 2117861376, 1142947840, 2017198080, 1344798720, 1613758464, 1075838976], [4326403, 4194306, 12582918, 29360142, 37748754, 104857650, 171966546, 440402130, 717226326, 2143290366, 4326400, 37750784, 104863744, 171976704, 440428544, 717268992, 2143418368, 4325376, 172359680, 441319424, 718667776, 2147352576, 4194304, 12582912, 29360128, 37748736, 104857600, 171966464, 440401920, 717225984, 2143289344], [12715015, 12582918, 8388612, 25165836, 717226326, 1702888236, 679477572, 2038432716, 545259780, 1635779340, 12715008, 717268992, 1702989824, 679518208, 2038554624, 545292288, 1635876864, 12713984, 680787968, 2042363904, 546308096, 1638924288, 12582912, 8388608, 25165824, 717225984, 1702887424, 679477248, 2038431744, 545259520, 1635778560], [29492239, 29360142, 25165836, 16777224, 2143290366, 1157628456, 2038432716, 1358955144, 1635779340, 1090519560, 29492224, 2143418368, 1157697536, 2038554624, 1359036416, 1635876864, 1090584576, 29491200, 2042363904, 1361575936, 1638924288, 1092616192, 29360128, 25165824, 16777216, 2143289344, 1157627904, 2038431744, 1358954496, 1635778560, 1090519040], [37882899, 37748754, 717226326, 2143290366, 33554448, 100663344, 167772240, 436207824, 704643408, 2113930224, 37882880, 33556480, 100669440, 167782400, 436234240, 704686080, 2114058240, 37879808, 168034304, 436994048, 705953792, 2117861376, 37748736, 717225984, 2143289344, 33554432, 100663296, 167772160, 436207616, 704643072, 2113929216], [104995891, 104857650, 1702888236, 1157628456, 100663344, 67108896, 2113930224, 1409286816, 1677722400, 1140851232, 104995840, 100669440, 67112960, 2114058240, 1409372160, 1677824000, 1140920320, 104988672, 2117861376, 1411907584, 1680867328, 1142947840, 104857600, 1702887424, 1157627904, 100663296, 67108864, 2113929216, 1409286144, 1677721600, 1140850688], [172371027, 171966546, 679477572, 2038432716, 167772240, 2113930224, 134217792, 402653376, 671088960, 2013266880, 172370944, 167782400, 2114058240, 134225920, 402677760, 671129600, 2013388800, 172359680, 134479872, 403439616, 672399360, 2017198080, 171966464, 679477248, 2038431744, 167772160, 2113929216, 134217728, 402653184, 671088640, 2013265920], [441347283, 440402130, 2038432716, 1358955144, 436207824, 1409286816, 402653376, 268435584, 2013266880, 1342177920, 441347072, 436234240, 1409372160, 402677760, 268451840, 2013388800, 1342259200, 441319424, 403439616, 268959744, 2017198080, 1344798720, 440401920, 2038431744, 1358954496, 436207616, 1409286144, 402653184, 268435456, 2013265920, 1342177280], [718712151, 717226326, 545259780, 1635779340, 704643408, 1677722400, 671088960, 2013266880, 536871168, 1610613504, 718711808, 704686080, 1677824000, 671129600, 2013388800, 536903680, 1610711040, 718667776, 672399360, 2017198080, 537919488, 1613758464, 717225984, 545259520, 1635778560, 704643072, 1677721600, 671088640, 2013265920, 536870912, 1610612736], [2147483647, 2143290366, 1635779340, 1090519560, 2113930224, 1140851232, 2013266880, 1342177920, 1610613504, 1073742336, 2147482624, 2114058240, 1140920320, 2013388800, 1342259200, 1610711040, 1073807360, 2147352576, 2017198080, 1344798720, 1613758464, 1075838976, 2143289344, 1635778560, 1090519040, 2113929216, 1140850688, 2013265920, 1342177280, 1610612736, 1073741824]]
  simp only [List.map_cons, List.map_nil, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12, ht13, ht14, ht15, ht16, ht17, ht18, ht19, ht20, ht21, ht22, ht23, ht24, ht25, ht26, ht27, ht28, ht29, ht30]

def T0 : List (List ℤ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

def T1 : List (List ℤ) :=
  [[1, 2, 3, 4, 3, 4, 4, 5, 6, 10, 2, 3, 4, 4, 5, 5, 8, 3, 4, 5, 5, 7, 5, 7, 9, 8, 11, 12, 16, 18, 31],
   [2, 1, 2, 3, 2, 3, 3, 4, 5, 9, 5, 5, 8, 8, 11, 13, 24, 3, 8, 11, 13, 23, 2, 4, 6, 4, 6, 6, 8, 10, 18],
   [3, 2, 1, 2, 5, 5, 3, 6, 2, 4, 7, 13, 13, 8, 16, 5, 10, 5, 8, 16, 5, 10, 4, 2, 4, 10, 10, 6, 12, 4, 8],
   [4, 3, 2, 1, 9, 3, 6, 3, 4, 2, 9, 24, 8, 16, 8, 10, 5, 7, 16, 8, 10, 5, 6, 4, 2, 18, 6, 12, 6, 8, 4],
   [3, 2, 5, 9, 1, 2, 2, 3, 3, 6, 8, 3, 6, 6, 9, 9, 18, 5, 5, 8, 8, 16, 4, 10, 18, 2, 4, 4, 6, 6, 12],
   [4, 3, 5, 3, 2, 1, 6, 3, 3, 2, 11, 6, 3, 18, 9, 9, 6, 7, 16, 8, 8, 5, 6, 10, 6, 4, 2, 12, 6, 6, 4],
   [4, 3, 3, 6, 2, 6, 1, 2, 2, 4, 12, 6, 18, 3, 6, 6, 12, 8, 3, 6, 6, 12, 6, 6, 12, 4, 12, 2, 4, 4, 8],
   [5, 4, 6, 3, 3, 3, 2, 1, 4, 2, 16, 9, 9, 6, 3, 12, 6, 11, 6, 3, 12, 6, 8, 12, 6, 6, 6, 4, 2, 8, 4],
   [6, 5, 2, 4, 3, 3, 2, 4, 1, 2, 18, 9, 9, 6, 12, 3, 6, 13, 6, 12, 3, 6, 10, 4, 8, 6, 6, 4, 8, 2, 4],
   [10, 9, 4, 2, 6, 2, 4, 2, 2, 1, 31, 18, 6, 12, 6, 6, 3, 23, 12, 6, 6, 3, 18, 8, 4, 12, 4, 8, 4, 4, 2],
   [2, 5, 7, 9, 8, 11, 12, 16, 18, 31, 1, 2, 3, 3, 4, 4, 7, 2, 3, 4, 4, 6, 3, 4, 5, 5, 7, 8, 11, 12, 21],
   [3, 5, 13, 24, 3, 6, 6, 9, 9, 18, 2, 1, 2, 2, 3, 3, 6, 5, 5, 8, 8, 16, 3, 8, 15, 2, 4, 4, 6, 6, 12],
   [4, 8, 13, 8, 6, 3, 18, 9, 9, 6, 3, 2, 1, 6, 3, 3, 2, 7, 16, 8, 8, 5, 5, 8, 5, 4, 2, 12, 6, 6, 4],
   [4, 8, 8, 16, 6, 18, 3, 6, 6, 12, 3, 2, 6, 1, 2, 2, 4, 8, 3, 6, 6, 12, 5, 5, 10, 4, 12, 2, 4, 4, 8],
   [5, 11, 16, 8, 9, 9, 6, 3, 12, 6, 4, 3, 3, 2, 1, 4, 2, 11, 6, 3, 12, 6, 7, 10, 5, 6, 6, 4, 2, 8, 4],
   [5, 13, 5, 10, 9, 9, 6, 12, 3, 6, 4, 3, 3, 2, 4, 1, 2, 12, 6, 12, 3, 6, 8, 3, 6, 6, 6, 4, 8, 2, 4],
   [8, 24, 10, 5, 18, 6, 12, 6, 6, 3, 7, 6, 2, 4, 2, 2, 1, 21, 12, 6, 6, 3, 15, 6, 3, 12, 4, 8, 4, 4, 2],
   [3, 3, 5, 7, 5, 7, 8, 11, 13, 23, 2, 5, 7, 8, 11, 12, 21, 1, 2, 3, 3, 5, 2, 3, 4, 3, 4, 5, 7, 8, 14],
   [4, 8, 8, 16, 5, 16, 3, 6, 6, 12, 3, 5, 16, 3, 6, 6, 12, 2, 1, 2, 2, 4, 5, 5, 10, 3, 10, 2, 4, 4, 8],
   [5, 11, 16, 8, 8, 8, 6, 3, 12, 6, 4, 8, 8, 6, 3, 12, 6, 3, 2, 1, 4, 2, 7, 10, 5, 5, 5, 4, 2, 8, 4],
   [5, 13, 5, 10, 8, 8, 6, 12, 3, 6, 4, 8, 8, 6, 12, 3, 6, 3, 2, 4, 1, 2, 8, 3, 6, 5, 5, 4, 8, 2, 4],
   [7, 23, 10, 5, 16, 5, 12, 6, 6, 3, 6, 16, 5, 12, 6, 6, 3, 5, 4, 2, 2, 1, 14, 6, 3, 10, 3, 8, 4, 4, 2],
   [5, 2, 4, 6, 4, 6, 6, 8, 10, 18, 3, 3, 5, 5, 7, 8, 15, 2, 5, 7, 8, 14, 1, 2, 3, 2, 3, 3, 4, 5, 9],
   [7, 4, 2, 4, 10, 10, 6, 12, 4, 8, 4, 8, 8, 5, 10, 3, 6, 3, 5, 10, 3, 6, 2, 1, 2, 5, 5, 3, 6, 2, 4],
   [9, 6, 4, 2, 18, 6, 12, 6, 8, 4, 5, 15, 5, 10, 5, 6, 3, 4, 10, 5, 6, 3, 3, 2, 1, 9, 3, 6, 3, 4, 2],
   [8, 4, 10, 18, 2, 4, 4, 6, 6, 12, 5, 2, 4, 4, 6, 6, 12, 3, 3, 5, 5, 10, 2, 5, 9, 1, 2, 2, 3, 3, 6],
   [11, 6, 10, 6, 4, 2, 12, 6, 6, 4, 7, 4, 2, 12, 6, 6, 4, 4, 10, 5, 5, 3, 3, 5, 3, 2, 1, 6, 3, 3, 2],
   [12, 6, 6, 12, 4, 12, 2, 4, 4, 8, 8, 4, 12, 2, 4, 4, 8, 5, 2, 4, 4, 8, 3, 3, 6, 2, 6, 1, 2, 2, 4],
   [16, 8, 12, 6, 6, 6, 4, 2, 8, 4, 11, 6, 6, 4, 2, 8, 4, 7, 4, 2, 8, 4, 4, 6, 3, 3, 3, 2, 1, 4, 2],
   [18, 10, 4, 8, 6, 6, 4, 8, 2, 4, 12, 6, 6, 4, 8, 2, 4, 8, 4, 8, 2, 4, 5, 2, 4, 3, 3, 2, 4, 1, 2],
   [31, 18, 8, 4, 12, 4, 8, 4, 4, 2, 21, 12, 4, 8, 4, 4, 2, 14, 8, 4, 4, 2, 9, 4, 2, 6, 2, 4, 2, 2, 1]]

def T2 : List (List ℤ) :=
  [[1, 3, 6, 10, 6, 10, 10, 15, 19, 42, 3, 6, 10, 10, 15, 15, 32, 6, 10, 15, 15, 27, 13, 23, 36, 27, 46, 51, 82, 95, 214],
   [3, 1, 3, 6, 3, 6, 6, 10, 13, 32, 13, 14, 31, 31, 54, 65, 165, 6, 29, 52, 63, 154, 3, 9, 18, 9, 18, 18, 30, 39, 96],
   [6, 3, 1, 3, 13, 14, 6, 18, 3, 9, 24, 65, 70, 31, 93, 14, 42, 14, 31, 93, 14, 42, 9, 3, 9, 39, 42, 18, 54, 9, 27],
   [10, 6, 3, 1, 33, 6, 18, 6, 9, 3, 38, 170, 31, 93, 31, 42, 14, 25, 93, 31, 42, 14, 18, 9, 3, 99, 18, 54, 18, 27, 9],
   [6, 3, 13, 33, 1, 3, 3, 6, 6, 17, 28, 6, 18, 18, 36, 36, 102, 14, 14, 31, 31, 88, 9, 39, 99, 3, 9, 9, 18, 18, 51],
   [10, 6, 14, 6, 3, 1, 17, 6, 6, 3, 49, 18, 6, 102, 36, 36, 18, 25, 88, 31, 31, 14, 18, 42, 18, 9, 3, 51, 18, 18, 9],
   [10, 6, 6, 18, 3, 17, 1, 3, 3, 9, 54, 18, 102, 6, 18, 18, 54, 29, 6, 18, 18, 54, 18, 18, 54, 9, 51, 3, 9, 9, 27],
   [15, 10, 18, 6, 6, 6, 3, 1, 9, 3, 89, 36, 36, 18, 6, 54, 18, 50, 18, 6, 54, 18, 30, 54, 18, 18, 18, 9, 3, 27, 9],
   [19, 13, 3, 9, 6, 6, 3, 9, 1, 3, 103, 36, 36, 18, 54, 6, 18, 61, 18, 54, 6, 18, 39, 9, 27, 18, 18, 9, 27, 3, 9],
   [42, 32, 9, 3, 17, 3, 9, 3, 3, 1, 238, 102, 18, 54, 18, 18, 6, 146, 54, 18, 18, 6, 96, 27, 9, 51, 9, 27, 9, 9, 3],
   [3, 13, 24, 38, 28, 49, 54, 89, 103, 238, 1, 3, 6, 6, 10, 10, 24, 3, 6, 10, 10, 20, 6, 10, 15, 13, 23, 27, 46, 51, 119],
   [6, 14, 65, 170, 6, 18, 18, 36, 36, 102, 3, 1, 3, 3, 6, 6, 17, 13, 14, 31, 31, 88, 6, 29, 77, 3, 9, 9, 18, 18, 51],
   [10, 31, 70, 31, 18, 6, 102, 36, 36, 18, 6, 3, 1, 17, 6, 6, 3, 24, 88, 31, 31, 14, 14, 31, 14, 9, 3, 51, 18, 18, 9],
   [10, 31, 31, 93, 18, 102, 6, 18, 18, 54, 6, 3, 17, 1, 3, 3, 9, 28, 6, 18, 18, 54, 14, 14, 42, 9, 51, 3, 9, 9, 27],
   [15, 54, 93, 31, 36, 36, 18, 6, 54, 18, 10, 6, 6, 3, 1, 9, 3, 49, 18, 6, 54, 18, 25, 42, 14, 18, 18, 9, 3, 27, 9],
   [15, 65, 14, 42, 36, 36, 18, 54, 6, 18, 10, 6, 6, 3, 9, 1, 3, 54, 18, 54, 6, 18, 29, 6, 18, 18, 18, 9, 27, 3, 9],
   [32, 165, 42, 14, 102, 18, 54, 18, 18, 6, 24, 17, 3, 9, 3, 3, 1, 130, 54, 18, 18, 6, 75, 18, 6, 51, 9, 27, 9, 9, 3],
   [6, 6, 14, 25, 14, 25, 29, 50, 61, 146, 3, 13, 24, 28, 49, 54, 130, 1, 3, 6, 6, 14, 3, 6, 10, 6, 10, 13, 23, 27, 64],
   [10, 29, 31, 93, 14, 88, 6, 18, 18, 54, 6, 14, 88, 6, 18, 18, 54, 3, 1, 3, 3, 9, 13, 14, 42, 6, 40, 3, 9, 9, 27],
   [15, 52, 93, 31, 31, 31, 18, 6, 54, 18, 10, 31, 31, 18, 6, 54, 18, 6, 3, 1, 9, 3, 24, 42, 14, 14, 14, 9, 3, 27, 9],
   [15, 63, 14, 42, 31, 31, 18, 54, 6, 18, 10, 31, 31, 18, 54, 6, 18, 6, 3, 9, 1, 3, 28, 6, 18, 14, 14, 9, 27, 3, 9],
   [27, 154, 42, 14, 88, 14, 54, 18, 18, 6, 20, 88, 14, 54, 18, 18, 6, 14, 9, 3, 3, 1, 68, 18, 6, 40, 6, 27, 9, 9, 3],
   [13, 3, 9, 18, 9, 18, 18, 30, 39, 96, 6, 6, 14, 14, 25, 29, 75, 3, 13, 24, 28, 68, 1, 3, 6, 3, 6, 6, 10, 13, 32],
   [23, 9, 3, 9, 39, 42, 18, 54, 9, 27, 10, 29, 31, 14, 42, 6, 18, 6, 14, 42, 6, 18, 3, 1, 3, 13, 14, 6, 18, 3, 9],
   [36, 18, 9, 3, 99, 18, 54, 18, 27, 9, 15, 77, 14, 42, 14, 18, 6, 10, 42, 14, 18, 6, 6, 3, 1, 33, 6, 18, 6, 9, 3],
   [27, 9, 39, 99, 3, 9, 9, 18, 18, 51, 13, 3, 9, 9, 18, 18, 51, 6, 6, 14, 14, 40, 3, 13, 33, 1, 3, 3, 6, 6, 17],
   [46, 18, 42, 18, 9, 3, 51, 18, 18, 9, 23, 9, 3, 51, 18, 18, 9, 10, 40, 14, 14, 6, 6, 14, 6, 3, 1, 17, 6, 6, 3],
   [51, 18, 18, 54, 9, 51, 3, 9, 9, 27, 27, 9, 51, 3, 9, 9, 27, 13, 3, 9, 9, 27, 6, 6, 18, 3, 17, 1, 3, 3, 9],
   [82, 30, 54, 18, 18, 18, 9, 3, 27, 9, 46, 18, 18, 9, 3, 27, 9, 23, 9, 3, 27, 9, 10, 18, 6, 6, 6, 3, 1, 9, 3],
   [95, 39, 9, 27, 18, 18, 9, 27, 3, 9, 51, 18, 18, 9, 27, 3, 9, 27, 9, 27, 3, 9, 13, 3, 9, 6, 6, 3, 9, 1, 3],
   [214, 96, 27, 9, 51, 9, 27, 9, 9, 3, 119, 51, 9, 27, 9, 9, 3, 64, 27, 9, 9, 3, 32, 9, 3, 17, 3, 9, 3, 3, 1]]

def T3 : List (List ℤ) :=
  [[1, 4, 10, 20, 10, 20, 20, 35, 45, 122, 4, 10, 20, 20, 35, 35, 92, 10, 20, 35, 35, 77, 26, 55, 101, 65, 131, 146, 273, 319, 873],
   [4, 1, 4, 10, 4, 10, 10, 20, 26, 80, 26, 30, 85, 85, 179, 214, 680, 10, 75, 167, 202, 624, 4, 16, 40, 16, 40, 40, 80, 104, 320],
   [10, 4, 1, 4, 26, 30, 10, 40, 4, 16, 60, 214, 246, 85, 340, 30, 120, 30, 85, 340, 30, 120, 16, 4, 16, 104, 120, 40, 160, 16, 64],
   [20, 10, 4, 1, 85, 10, 40, 10, 16, 4, 113, 721, 85, 340, 85, 120, 30, 65, 340, 85, 120, 30, 40, 16, 4, 340, 40, 160, 40, 64, 16],
   [10, 4, 26, 85, 1, 4, 4, 10, 10, 36, 70, 10, 40, 40, 100, 100, 360, 30, 30, 85, 85, 308, 16, 104, 340, 4, 16, 16, 40, 40, 144],
   [20, 10, 30, 10, 4, 1, 36, 10, 10, 4, 148, 40, 10, 360, 100, 100, 40, 65, 308, 85, 85, 30, 40, 120, 40, 16, 4, 144, 40, 40, 16],
   [20, 10, 10, 40, 4, 36, 1, 4, 4, 16, 163, 40, 360, 10, 40, 40, 160, 75, 10, 40, 40, 160, 40, 40, 160, 16, 144, 4, 16, 16, 64],
   [35, 20, 40, 10, 10, 10, 4, 1, 16, 4, 318, 100, 100, 40, 10, 160, 40, 154, 40, 10, 160, 40, 80, 160, 40, 40, 40, 16, 4, 64, 16],
   [45, 26, 4, 16, 10, 10, 4, 16, 1, 4, 371, 100, 100, 40, 160, 10, 40, 189, 40, 160, 10, 40, 104, 16, 64, 40, 40, 16, 64, 4, 16],
   [122, 80, 16, 4, 36, 4, 16, 4, 4, 1, 1058, 360, 40, 160, 40, 40, 10, 562, 160, 40, 40, 10, 320, 64, 16, 144, 16, 64, 16, 16, 4],
   [4, 26, 60, 113, 70, 148, 163, 318, 371, 1058, 1, 4, 10, 10, 20, 20, 60, 4, 10, 20, 20, 50, 10, 20, 35, 26, 55, 65, 131, 146, 419],
   [10, 30, 214, 721, 10, 40, 40, 100, 100, 360, 4, 1, 4, 4, 10, 10, 36, 26, 30, 85, 85, 308, 10, 75, 256, 4, 16, 16, 40, 40, 144],
   [20, 85, 246, 85, 40, 10, 360, 100, 100, 40, 10, 4, 1, 36, 10, 10, 4, 60, 308, 85, 85, 30, 30, 85, 30, 16, 4, 144, 40, 40, 16],
   [20, 85, 85, 340, 40, 360, 10, 40, 40, 160, 10, 4, 36, 1, 4, 4, 16, 70, 10, 40, 40, 160, 30, 30, 120, 16, 144, 4, 16, 16, 64],
   [35, 179, 340, 85, 100, 100, 40, 10, 160, 40, 20, 10, 10, 4, 1, 16, 4, 148, 40, 10, 160, 40, 65, 120, 30, 40, 40, 16, 4, 64, 16],
   [35, 214, 30, 120, 100, 100, 40, 160, 10, 40, 20, 10, 10, 4, 16, 1, 4, 163, 40, 160, 10, 40, 75, 10, 40, 40, 40, 16, 64, 4, 16],
   [92, 680, 120, 30, 360, 40, 160, 40, 40, 10, 60, 36, 4, 16, 4, 4, 1, 493, 160, 40, 40, 10, 243, 40, 10, 144, 16, 64, 16, 16, 4],
   [10, 10, 30, 65, 30, 65, 75, 154, 189, 562, 4, 26, 60, 70, 148, 163, 493, 1, 4, 10, 10, 30, 4, 10, 20, 10, 20, 26, 55, 65, 192],
   [20, 75, 85, 340, 30, 308, 10, 40, 40, 160, 10, 30, 308, 10, 40, 40, 160, 4, 1, 4, 4, 16, 26, 30, 120, 10, 110, 4, 16, 16, 64],
   [35, 167, 340, 85, 85, 85, 40, 10, 160, 40, 20, 85, 85, 40, 10, 160, 40, 10, 4, 1, 16, 4, 60, 120, 30, 30, 30, 16, 4, 64, 16],
   [35, 202, 30, 120, 85, 85, 40, 160, 10, 40, 20, 85, 85, 40, 160, 10, 40, 10, 4, 16, 1, 4, 70, 10, 40, 30, 30, 16, 64, 4, 16],
   [77, 624, 120, 30, 308, 30, 160, 40, 40, 10, 50, 308, 30, 160, 40, 40, 10, 30, 16, 4, 4, 1, 216, 40, 10, 110, 10, 64, 16, 16, 4],
   [26, 4, 16, 40, 16, 40, 40, 80, 104, 320, 10, 10, 30, 30, 65, 75, 243, 4, 26, 60, 70, 216, 1, 4, 10, 4, 10, 10, 20, 26, 80],
   [55, 16, 4, 16, 104, 120, 40, 160, 16, 64, 20, 75, 85, 30, 120, 10, 40, 10, 30, 120, 10, 40, 4, 1, 4, 26, 30, 10, 40, 4, 16],
   [101, 40, 16, 4, 340, 40, 160, 40, 64, 16, 35, 256, 30, 120, 30, 40, 10, 20, 120, 30, 40, 10, 10, 4, 1, 85, 10, 40, 10, 16, 4],
   [65, 16, 104, 340, 4, 16, 16, 40, 40, 144, 26, 4, 16, 16, 40, 40, 144, 10, 10, 30, 30, 110, 4, 26, 85, 1, 4, 4, 10, 10, 36],
   [131, 40, 120, 40, 16, 4, 144, 40, 40, 16, 55, 16, 4, 144, 40, 40, 16, 20, 110, 30, 30, 10, 10, 30, 10, 4, 1, 36, 10, 10, 4],
   [146, 40, 40, 160, 16, 144, 4, 16, 16, 64, 65, 16, 144, 4, 16, 16, 64, 26, 4, 16, 16, 64, 10, 10, 40, 4, 36, 1, 4, 4, 16],
   [273, 80, 160, 40, 40, 40, 16, 4, 64, 16, 131, 40, 40, 16, 4, 64, 16, 55, 16, 4, 64, 16, 20, 40, 10, 10, 10, 4, 1, 16, 4],
   [319, 104, 16, 64, 40, 40, 16, 64, 4, 16, 146, 40, 40, 16, 64, 4, 16, 65, 16, 64, 4, 16, 26, 4, 16, 10, 10, 4, 16, 1, 4],
   [873, 320, 64, 16, 144, 16, 64, 16, 16, 4, 419, 144, 16, 64, 16, 16, 4, 192, 64, 16, 16, 4, 80, 16, 4, 36, 4, 16, 4, 4, 1]]

def T4 : List (List ℤ) :=
  [[1, 5, 15, 35, 15, 35, 35, 70, 90, 287, 5, 15, 35, 35, 70, 70, 217, 15, 35, 70, 70, 182, 45, 110, 231, 130, 301, 336, 714, 835, 2669],
   [5, 1, 5, 15, 5, 15, 15, 35, 45, 165, 45, 55, 190, 190, 469, 554, 2098, 15, 160, 427, 512, 1903, 5, 25, 75, 25, 75, 75, 175, 225, 825],
   [15, 5, 1, 5, 45, 55, 15, 75, 5, 25, 125, 554, 671, 190, 950, 55, 275, 55, 190, 950, 55, 275, 25, 5, 25, 225, 275, 75, 375, 25, 125],
   [35, 15, 5, 1, 180, 15, 75, 15, 25, 5, 273, 2281, 190, 950, 190, 275, 55, 140, 950, 190, 275, 55, 75, 25, 5, 900, 75, 375, 75, 125, 25],
   [15, 5, 45, 180, 1, 5, 5, 15, 15, 65, 145, 15, 75, 75, 225, 225, 975, 55, 55, 190, 190, 833, 25, 225, 900, 5, 25, 25, 75, 75, 325],
   [35, 15, 55, 15, 5, 1, 65, 15, 15, 5, 358, 75, 15, 975, 225, 225, 75, 140, 833, 190, 190, 55, 75, 275, 75, 25, 5, 325, 75, 75, 25],
   [35, 15, 15, 75, 5, 65, 1, 5, 5, 25, 393, 75, 975, 15, 75, 75, 375, 160, 15, 75, 75, 375, 75, 75, 375, 25, 325, 5, 25, 25, 125],
   [70, 35, 75, 15, 15, 15, 5, 1, 25, 5, 882, 225, 225, 75, 15, 375, 75, 379, 75, 15, 375, 75, 175, 375, 75, 75, 75, 25, 5, 125, 25],
   [90, 45, 5, 25, 15, 15, 5, 25, 1, 5, 1030, 225, 225, 75, 375, 15, 75, 464, 75, 375, 15, 75, 225, 25, 125, 75, 75, 25, 125, 5, 25],
   [287, 165, 25, 5, 65, 5, 25, 5, 5, 1, 3467, 975, 75, 375, 75, 75, 15, 1637, 375, 75, 75, 15, 825, 125, 25, 325, 25, 125, 25, 25, 5],
   [5, 45, 125, 273, 145, 358, 393, 882, 1030, 3467, 1, 5, 15, 15, 35, 35, 125, 5, 15, 35, 35, 105, 15, 35, 70, 45, 110, 130, 301, 336, 1136],
   [15, 55, 554, 2281, 15, 75, 75, 225, 225, 975, 5, 1, 5, 5, 15, 15, 65, 45, 55, 190, 190, 833, 15, 160, 666, 5, 25, 25, 75, 75, 325],
   [35, 190, 671, 190, 75, 15, 975, 225, 225, 75, 15, 5, 1, 65, 15, 15, 5, 125, 833, 190, 190, 55, 55, 190, 55, 25, 5, 325, 75, 75, 25],
   [35, 190, 190, 950, 75, 975, 15, 75, 75, 375, 15, 5, 65, 1, 5, 5, 25, 145, 15, 75, 75, 375, 55, 55, 275, 25, 325, 5, 25, 25, 125],
   [70, 469, 950, 190, 225, 225, 75, 15, 375, 75, 35, 15, 15, 5, 1, 25, 5, 358, 75, 15, 375, 75, 140, 275, 55, 75, 75, 25, 5, 125, 25],
   [70, 554, 55, 275, 225, 225, 75, 375, 15, 75, 35, 15, 15, 5, 25, 1, 5, 393, 75, 375, 15, 75, 160, 15, 75, 75, 75, 25, 125, 5, 25],
   [217, 2098, 275, 55, 975, 75, 375, 75, 75, 15, 125, 65, 5, 25, 5, 5, 1, 1421, 375, 75, 75, 15, 618, 75, 15, 325, 25, 125, 25, 25, 5],
   [15, 15, 55, 140, 55, 140, 160, 379, 464, 1637, 5, 45, 125, 145, 358, 393, 1421, 1, 5, 15, 15, 55, 5, 15, 35, 15, 35, 45, 110, 130, 457],
   [35, 160, 190, 950, 55, 833, 15, 75, 75, 375, 15, 55, 833, 15, 75, 75, 375, 5, 1, 5, 5, 25, 45, 55, 275, 15, 245, 5, 25, 25, 125],
   [70, 427, 950, 190, 190, 190, 75, 15, 375, 75, 35, 190, 190, 75, 15, 375, 75, 15, 5, 1, 25, 5, 125, 275, 55, 55, 55, 25, 5, 125, 25],
   [70, 512, 55, 275, 190, 190, 75, 375, 15, 75, 35, 190, 190, 75, 375, 15, 75, 15, 5, 25, 1, 5, 145, 15, 75, 55, 55, 25, 125, 5, 25],
   [182, 1903, 275, 55, 833, 55, 375, 75, 75, 15, 105, 833, 55, 375, 75, 75, 15, 55, 25, 5, 5, 1, 541, 75, 15, 245, 15, 125, 25, 25, 5],
   [45, 5, 25, 75, 25, 75, 75, 175, 225, 825, 15, 15, 55, 55, 140, 160, 618, 5, 45, 125, 145, 541, 1, 5, 15, 5, 15, 15, 35, 45, 165],
   [110, 25, 5, 25, 225, 275, 75, 375, 25, 125, 35, 160, 190, 55, 275, 15, 75, 15, 55, 275, 15, 75, 5, 1, 5, 45, 55, 15, 75, 5, 25],
   [231, 75, 25, 5, 900, 75, 375, 75, 125, 25, 70, 666, 55, 275, 55, 75, 15, 35, 275, 55, 75, 15, 15, 5, 1, 180, 15, 75, 15, 25, 5],
   [130, 25, 225, 900, 5, 25, 25, 75, 75, 325, 45, 5, 25, 25, 75, 75, 325, 15, 15, 55, 55, 245, 5, 45, 180, 1, 5, 5, 15, 15, 65],
   [301, 75, 275, 75, 25, 5, 325, 75, 75, 25, 110, 25, 5, 325, 75, 75, 25, 35, 245, 55, 55, 15, 15, 55, 15, 5, 1, 65, 15, 15, 5],
   [336, 75, 75, 375, 25, 325, 5, 25, 25, 125, 130, 25, 325, 5, 25, 25, 125, 45, 5, 25, 25, 125, 15, 15, 75, 5, 65, 1, 5, 5, 25],
   [714, 175, 375, 75, 75, 75, 25, 5, 125, 25, 301, 75, 75, 25, 5, 125, 25, 110, 25, 5, 125, 25, 35, 75, 15, 15, 15, 5, 1, 25, 5],
   [835, 225, 25, 125, 75, 75, 25, 125, 5, 25, 336, 75, 75, 25, 125, 5, 25, 130, 25, 125, 5, 25, 45, 5, 25, 15, 15, 5, 25, 1, 5],
   [2669, 825, 125, 25, 325, 25, 125, 25, 25, 5, 1136, 325, 25, 125, 25, 25, 5, 457, 125, 25, 25, 5, 165, 25, 5, 65, 5, 25, 5, 5, 1]]

def T5 : List (List ℤ) :=
  [[1, 6, 21, 56, 21, 56, 56, 126, 161, 588, 6, 21, 56, 56, 126, 126, 448, 21, 56, 126, 126, 378, 71, 196, 462, 231, 602, 672, 1596, 1862, 6778],
   [6, 1, 6, 21, 6, 21, 21, 56, 71, 301, 71, 91, 371, 371, 1050, 1225, 5362, 21, 301, 938, 1113, 4823, 6, 36, 126, 36, 126, 126, 336, 426, 1806],
   [21, 6, 1, 6, 71, 91, 21, 126, 6, 36, 231, 1225, 1547, 371, 2226, 91, 546, 91, 371, 2226, 91, 546, 36, 6, 36, 426, 546, 126, 756, 36, 216],
   [56, 21, 6, 1, 336, 21, 126, 21, 36, 6, 574, 5957, 371, 2226, 371, 546, 91, 266, 2226, 371, 546, 91, 126, 36, 6, 2016, 126, 756, 126, 216, 36],
   [21, 6, 71, 336, 1, 6, 6, 21, 21, 106, 266, 21, 126, 126, 441, 441, 2226, 91, 91, 371, 371, 1904, 36, 426, 2016, 6, 36, 36, 126, 126, 636],
   [56, 21, 91, 21, 6, 1, 106, 21, 21, 6, 749, 126, 21, 2226, 441, 441, 126, 266, 1904, 371, 371, 91, 126, 546, 126, 36, 6, 636, 126, 126, 36],
   [56, 21, 21, 126, 6, 106, 1, 6, 6, 36, 819, 126, 2226, 21, 126, 126, 756, 301, 21, 126, 126, 756, 126, 126, 756, 36, 636, 6, 36, 36, 216],
   [126, 56, 126, 21, 21, 21, 6, 1, 36, 6, 2072, 441, 441, 126, 21, 756, 126, 805, 126, 21, 756, 126, 336, 756, 126, 126, 126, 36, 6, 216, 36],
   [161, 71, 6, 36, 21, 21, 6, 36, 1, 6, 2415, 441, 441, 126, 756, 21, 126, 980, 126, 756, 21, 126, 426, 36, 216, 126, 126, 36, 216, 6, 36],
   [588, 301, 36, 6, 106, 6, 36, 6, 6, 1, 9327, 2226, 126, 756, 126, 126, 21, 3983, 756, 126, 126, 21, 1806, 216, 36, 636, 36, 216, 36, 36, 6],
   [6, 71, 231, 574, 266, 749, 819, 2072, 2415, 9327, 1, 6, 21, 21, 56, 56, 231, 6, 21, 56, 56, 196, 21, 56, 126, 71, 196, 231, 602, 672, 2604],
   [21, 91, 1225, 5957, 21, 126, 126, 441, 441, 2226, 6, 1, 6, 6, 21, 21, 106, 71, 91, 371, 371, 1904, 21, 301, 1477, 6, 36, 36, 126, 126, 636],
   [56, 371, 1547, 371, 126, 21, 2226, 441, 441, 126, 21, 6, 1, 106, 21, 21, 6, 231, 1904, 371, 371, 91, 91, 371, 91, 36, 6, 636, 126, 126, 36],
   [56, 371, 371, 2226, 126, 2226, 21, 126, 126, 756, 21, 6, 106, 1, 6, 6, 36, 266, 21, 126, 126, 756, 91, 91, 546, 36, 636, 6, 36, 36, 216],
   [126, 1050, 2226, 371, 441, 441, 126, 21, 756, 126, 56, 21, 21, 6, 1, 36, 6, 749, 126, 21, 756, 126, 266, 546, 91, 126, 126, 36, 6, 216, 36],
   [126, 1225, 91, 546, 441, 441, 126, 756, 21, 126, 56, 21, 21, 6, 36, 1, 6, 819, 126, 756, 21, 126, 301, 21, 126, 126, 126, 36, 216, 6, 36],
   [448, 5362, 546, 91, 2226, 126, 756, 126, 126, 21, 231, 106, 6, 36, 6, 6, 1, 3430, 756, 126, 126, 21, 1344, 126, 21, 636, 36, 216, 36, 36, 6],
   [21, 21, 91, 266, 91, 266, 301, 805, 980, 3983, 6, 71, 231, 266, 749, 819, 3430, 1, 6, 21, 21, 91, 6, 21, 56, 21, 56, 71, 196, 231, 938],
   [56, 301, 371, 2226, 91, 1904, 21, 126, 126, 756, 21, 91, 1904, 21, 126, 126, 756, 6, 1, 6, 6, 36, 71, 91, 546, 21, 476, 6, 36, 36, 216],
   [126, 938, 2226, 371, 371, 371, 126, 21, 756, 126, 56, 371, 371, 126, 21, 756, 126, 21, 6, 1, 36, 6, 231, 546, 91, 91, 91, 36, 6, 216, 36],
   [126, 1113, 91, 546, 371, 371, 126, 756, 21, 126, 56, 371, 371, 126, 756, 21, 126, 21, 6, 36, 1, 6, 266, 21, 126, 91, 91, 36, 216, 6, 36],
   [378, 4823, 546, 91, 1904, 91, 756, 126, 126, 21, 196, 1904, 91, 756, 126, 126, 21, 91, 36, 6, 6, 1, 1162, 126, 21, 476, 21, 216, 36, 36, 6],
   [71, 6, 36, 126, 36, 126, 126, 336, 426, 1806, 21, 21, 91, 91, 266, 301, 1344, 6, 71, 231, 266, 1162, 1, 6, 21, 6, 21, 21, 56, 71, 301],
   [196, 36, 6, 36, 426, 546, 126, 756, 36, 216, 56, 301, 371, 91, 546, 21, 126, 21, 91, 546, 21, 126, 6, 1, 6, 71, 91, 21, 126, 6, 36],
   [462, 126, 36, 6, 2016, 126, 756, 126, 216, 36, 126, 1477, 91, 546, 91, 126, 21, 56, 546, 91, 126, 21, 21, 6, 1, 336, 21, 126, 21, 36, 6],
   [231, 36, 426, 2016, 6, 36, 36, 126, 126, 636, 71, 6, 36, 36, 126, 126, 636, 21, 21, 91, 91, 476, 6, 71, 336, 1, 6, 6, 21, 21, 106],
   [602, 126, 546, 126, 36, 6, 636, 126, 126, 36, 196, 36, 6, 636, 126, 126, 36, 56, 476, 91, 91, 21, 21, 91, 21, 6, 1, 106, 21, 21, 6],
   [672, 126, 126, 756, 36, 636, 6, 36, 36, 216, 231, 36, 636, 6, 36, 36, 216, 71, 6, 36, 36, 216, 21, 21, 126, 6, 106, 1, 6, 6, 36],
   [1596, 336, 756, 126, 126, 126, 36, 6, 216, 36, 602, 126, 126, 36, 6, 216, 36, 196, 36, 6, 216, 36, 56, 126, 21, 21, 21, 6, 1, 36, 6],
   [1862, 426, 36, 216, 126, 126, 36, 216, 6, 36, 672, 126, 126, 36, 216, 6, 36, 231, 36, 216, 6, 36, 71, 6, 36, 21, 21, 6, 36, 1, 6],
   [6778, 1806, 216, 36, 636, 36, 216, 36, 36, 6, 2604, 636, 36, 216, 36, 36, 6, 938, 216, 36, 36, 6, 301, 36, 6, 106, 6, 36, 6, 6, 1]]

def T6 : List (List ℤ) :=
  [[1, 7, 28, 84, 28, 84, 84, 210, 266, 1092, 7, 28, 84, 84, 210, 210, 840, 28, 84, 210, 210, 714, 105, 322, 840, 378, 1092, 1218, 3192, 3710, 15108],
   [7, 1, 7, 28, 7, 28, 28, 84, 105, 504, 105, 140, 658, 658, 2100, 2422, 11998, 28, 518, 1848, 2170, 10724, 7, 49, 196, 49, 196, 196, 588, 735, 3528],
   [28, 7, 1, 7, 105, 140, 28, 196, 7, 49, 392, 2422, 3164, 658, 4606, 140, 980, 140, 658, 4606, 140, 980, 49, 7, 49, 735, 980, 196, 1372, 49, 343],
   [84, 28, 7, 1, 574, 28, 196, 28, 49, 7, 1092, 13580, 658, 4606, 658, 980, 140, 462, 4606, 658, 980, 140, 196, 49, 7, 4018, 196, 1372, 196, 343, 49],
   [28, 7, 105, 574, 1, 7, 7, 28, 28, 161, 448, 28, 196, 196, 784, 784, 4508, 140, 140, 658, 658, 3864, 49, 735, 4018, 7, 49, 49, 196, 196, 1127],
   [84, 28, 140, 28, 7, 1, 161, 28, 28, 7, 1414, 196, 28, 4508, 784, 784, 196, 462, 3864, 658, 658, 140, 196, 980, 196, 49, 7, 1127, 196, 196, 49],
   [84, 28, 28, 196, 7, 161, 1, 7, 7, 49, 1540, 196, 4508, 28, 196, 196, 1372, 518, 28, 196, 196, 1372, 196, 196, 1372, 49, 1127, 7, 49, 49, 343],
   [210, 84, 196, 28, 28, 28, 7, 1, 49, 7, 4326, 784, 784, 196, 28, 1372, 196, 1540, 196, 28, 1372, 196, 588, 1372, 196, 196, 196, 49, 7, 343, 49],
   [266, 105, 7, 49, 28, 28, 7, 49, 1, 7, 5026, 784, 784, 196, 1372, 28, 196, 1862, 196, 1372, 28, 196, 735, 49, 343, 196, 196, 49, 343, 7, 49],
   [1092, 504, 49, 7, 161, 7, 49, 7, 7, 1, 21836, 4508, 196, 1372, 196, 196, 28, 8540, 1372, 196, 196, 28, 3528, 343, 49, 1127, 49, 343, 49, 49, 7],
   [7, 105, 392, 1092, 448, 1414, 1540, 4326, 5026, 21836, 1, 7, 28, 28, 84, 84, 392, 7, 28, 84, 84, 336, 28, 84, 210, 105, 322, 378, 1092, 1218, 5306],
   [28, 140, 2422, 13580, 28, 196, 196, 784, 784, 4508, 7, 1, 7, 7, 28, 28, 161, 105, 140, 658, 658, 3864, 28, 518, 2926, 7, 49, 49, 196, 196, 1127],
   [84, 658, 3164, 658, 196, 28, 4508, 784, 784, 196, 28, 7, 1, 161, 28, 28, 7, 392, 3864, 658, 658, 140, 140, 658, 140, 49, 7, 1127, 196, 196, 49],
   [84, 658, 658, 4606, 196, 4508, 28, 196, 196, 1372, 28, 7, 161, 1, 7, 7, 49, 448, 28, 196, 196, 1372, 140, 140, 980, 49, 1127, 7, 49, 49, 343],
   [210, 2100, 4606, 658, 784, 784, 196, 28, 1372, 196, 84, 28, 28, 7, 1, 49, 7, 1414, 196, 28, 1372, 196, 462, 980, 140, 196, 196, 49, 7, 343, 49],
   [210, 2422, 140, 980, 784, 784, 196, 1372, 28, 196, 84, 28, 28, 7, 49, 1, 7, 1540, 196, 1372, 28, 196, 518, 28, 196, 196, 196, 49, 343, 7, 49],
   [840, 11998, 980, 140, 4508, 196, 1372, 196, 196, 28, 392, 161, 7, 49, 7, 7, 1, 7308, 1372, 196, 196, 28, 2618, 196, 28, 1127, 49, 343, 49, 49, 7],
   [28, 28, 140, 462, 140, 462, 518, 1540, 1862, 8540, 7, 105, 392, 448, 1414, 1540, 7308, 1, 7, 28, 28, 140, 7, 28, 84, 28, 84, 105, 322, 378, 1736],
   [84, 518, 658, 4606, 140, 3864, 28, 196, 196, 1372, 28, 140, 3864, 28, 196, 196, 1372, 7, 1, 7, 7, 49, 105, 140, 980, 28, 840, 7, 49, 49, 343],
   [210, 1848, 4606, 658, 658, 658, 196, 28, 1372, 196, 84, 658, 658, 196, 28, 1372, 196, 28, 7, 1, 49, 7, 392, 980, 140, 140, 140, 49, 7, 343, 49],
   [210, 2170, 140, 980, 658, 658, 196, 1372, 28, 196, 84, 658, 658, 196, 1372, 28, 196, 28, 7, 49, 1, 7, 448, 28, 196, 140, 140, 49, 343, 7, 49],
   [714, 10724, 980, 140, 3864, 140, 1372, 196, 196, 28, 336, 3864, 140, 1372, 196, 196, 28, 140, 49, 7, 7, 1, 2240, 196, 28, 840, 28, 343, 49, 49, 7],
   [105, 7, 49, 196, 49, 196, 196, 588, 735, 3528, 28, 28, 140, 140, 462, 518, 2618, 7, 105, 392, 448, 2240, 1, 7, 28, 7, 28, 28, 84, 105, 504],
   [322, 49, 7, 49, 735, 980, 196, 1372, 49, 343, 84, 518, 658, 140, 980, 28, 196, 28, 140, 980, 28, 196, 7, 1, 7, 105, 140, 28, 196, 7, 49],
   [840, 196, 49, 7, 4018, 196, 1372, 196, 343, 49, 210, 2926, 140, 980, 140, 196, 28, 84, 980, 140, 196, 28, 28, 7, 1, 574, 28, 196, 28, 49, 7],
   [378, 49, 735, 4018, 7, 49, 49, 196, 196, 1127, 105, 7, 49, 49, 196, 196, 1127, 28, 28, 140, 140, 840, 7, 105, 574, 1, 7, 7, 28, 28, 161],
   [1092, 196, 980, 196, 49, 7, 1127, 196, 196, 49, 322, 49, 7, 1127, 196, 196, 49, 84, 840, 140, 140, 28, 28, 140, 28, 7, 1, 161, 28, 28, 7],
   [1218, 196, 196, 1372, 49, 1127, 7, 49, 49, 343, 378, 49, 1127, 7, 49, 49, 343, 105, 7, 49, 49, 343, 28, 28, 196, 7, 161, 1, 7, 7, 49],
   [3192, 588, 1372, 196, 196, 196, 49, 7, 343, 49, 1092, 196, 196, 49, 7, 343, 49, 322, 49, 7, 343, 49, 84, 196, 28, 28, 28, 7, 1, 49, 7],
   [3710, 735, 49, 343, 196, 196, 49, 343, 7, 49, 1218, 196, 196, 49, 343, 7, 49, 378, 49, 343, 7, 49, 105, 7, 49, 28, 28, 7, 49, 1, 7],
   [15108, 3528, 343, 49, 1127, 49, 343, 49, 49, 7, 5306, 1127, 49, 343, 49, 49, 7, 1736, 343, 49, 49, 7, 504, 49, 7, 161, 7, 49, 7, 7, 1]]

def T7 : List (List ℤ) :=
  [[1, 8, 36, 120, 36, 120, 120, 330, 414, 1884, 8, 36, 120, 120, 330, 330, 1464, 36, 120, 330, 330, 1254, 148, 498, 1422, 582, 1842, 2052, 5874, 6798, 30558],
   [8, 1, 8, 36, 8, 36, 36, 120, 148, 792, 148, 204, 1086, 1086, 3858, 4404, 24312, 36, 834, 3354, 3900, 21624, 8, 64, 288, 64, 288, 288, 960, 1184, 6336],
   [36, 8, 1, 8, 148, 204, 36, 288, 8, 64, 624, 4404, 5916, 1086, 8688, 204, 1632, 204, 1086, 8688, 204, 1632, 64, 8, 64, 1184, 1632, 288, 2304, 64, 512],
   [120, 36, 8, 1, 918, 36, 288, 36, 64, 8, 1926, 27966, 1086, 8688, 1086, 1632, 204, 750, 8688, 1086, 1632, 204, 288, 64, 8, 7344, 288, 2304, 288, 512, 64],
   [36, 8, 148, 918, 1, 8, 8, 36, 36, 232, 708, 36, 288, 288, 1296, 1296, 8352, 204, 204, 1086, 1086, 7176, 64, 1184, 7344, 8, 64, 64, 288, 288, 1856],
   [120, 36, 204, 36, 8, 1, 232, 36, 36, 8, 2472, 288, 36, 8352, 1296, 1296, 288, 750, 7176, 1086, 1086, 204, 288, 1632, 288, 64, 8, 1856, 288, 288, 64],
   [120, 36, 36, 288, 8, 232, 1, 8, 8, 64, 2682, 288, 8352, 36, 288, 288, 2304, 834, 36, 288, 288, 2304, 288, 288, 2304, 64, 1856, 8, 64, 64, 512],
   [330, 120, 288, 36, 36, 36, 8, 1, 64, 8, 8268, 1296, 1296, 288, 36, 2304, 288, 2724, 288, 36, 2304, 288, 960, 2304, 288, 288, 288, 64, 8, 512, 64],
   [414, 148, 8, 64, 36, 36, 8, 64, 1, 8, 9570, 1296, 1296, 288, 2304, 36, 288, 3270, 288, 2304, 36, 288, 1184, 64, 512, 288, 288, 64, 512, 8, 64],
   [1884, 792, 64, 8, 232, 8, 64, 8, 8, 1, 46092, 8352, 288, 2304, 288, 288, 36, 16668, 2304, 288, 288, 36, 6336, 512, 64, 1856, 64, 512, 64, 64, 8],
   [8, 148, 624, 1926, 708, 2472, 2682, 8268, 9570, 46092, 1, 8, 36, 36, 120, 120, 624, 8, 36, 120, 120, 540, 36, 120, 330, 148, 498, 582, 1842, 2052, 9906],
   [36, 204, 4404, 27966, 36, 288, 288, 1296, 1296, 8352, 8, 1, 8, 8, 36, 36, 232, 148, 204, 1086, 1086, 7176, 36, 834, 5328, 8, 64, 64, 288, 288, 1856],
   [120, 1086, 5916, 1086, 288, 36, 8352, 1296, 1296, 288, 36, 8, 1, 232, 36, 36, 8, 624, 7176, 1086, 1086, 204, 204, 1086, 204, 64, 8, 1856, 288, 288, 64],
   [120, 1086, 1086, 8688, 288, 8352, 36, 288, 288, 2304, 36, 8, 232, 1, 8, 8, 64, 708, 36, 288, 288, 2304, 204, 204, 1632, 64, 1856, 8, 64, 64, 512],
   [330, 3858, 8688, 1086, 1296, 1296, 288, 36, 2304, 288, 120, 36, 36, 8, 1, 64, 8, 2472, 288, 36, 2304, 288, 750, 1632, 204, 288, 288, 64, 8, 512, 64],
   [330, 4404, 204, 1632, 1296, 1296, 288, 2304, 36, 288, 120, 36, 36, 8, 64, 1, 8, 2682, 288, 2304, 36, 288, 834, 36, 288, 288, 288, 64, 512, 8, 64],
   [1464, 24312, 1632, 204, 8352, 288, 2304, 288, 288, 36, 624, 232, 8, 64, 8, 8, 1, 14190, 2304, 288, 288, 36, 4698, 288, 36, 1856, 64, 512, 64, 64, 8],
   [36, 36, 204, 750, 204, 750, 834, 2724, 3270, 16668, 8, 148, 624, 708, 2472, 2682, 14190, 1, 8, 36, 36, 204, 8, 36, 120, 36, 120, 148, 498, 582, 2976],
   [120, 834, 1086, 8688, 204, 7176, 36, 288, 288, 2304, 36, 204, 7176, 36, 288, 288, 2304, 8, 1, 8, 8, 64, 148, 204, 1632, 36, 1380, 8, 64, 64, 512],
   [330, 3354, 8688, 1086, 1086, 1086, 288, 36, 2304, 288, 120, 1086, 1086, 288, 36, 2304, 288, 36, 8, 1, 64, 8, 624, 1632, 204, 204, 204, 64, 8, 512, 64],
   [330, 3900, 204, 1632, 1086, 1086, 288, 2304, 36, 288, 120, 1086, 1086, 288, 2304, 36, 288, 36, 8, 64, 1, 8, 708, 36, 288, 204, 204, 64, 512, 8, 64],
   [1254, 21624, 1632, 204, 7176, 204, 2304, 288, 288, 36, 540, 7176, 204, 2304, 288, 288, 36, 204, 64, 8, 8, 1, 3984, 288, 36, 1380, 36, 512, 64, 64, 8],
   [148, 8, 64, 288, 64, 288, 288, 960, 1184, 6336, 36, 36, 204, 204, 750, 834, 4698, 8, 148, 624, 708, 3984, 1, 8, 36, 8, 36, 36, 120, 148, 792],
   [498, 64, 8, 64, 1184, 1632, 288, 2304, 64, 512, 120, 834, 1086, 204, 1632, 36, 288, 36, 204, 1632, 36, 288, 8, 1, 8, 148, 204, 36, 288, 8, 64],
   [1422, 288, 64, 8, 7344, 288, 2304, 288, 512, 64, 330, 5328, 204, 1632, 204, 288, 36, 120, 1632, 204, 288, 36, 36, 8, 1, 918, 36, 288, 36, 64, 8],
   [582, 64, 1184, 7344, 8, 64, 64, 288, 288, 1856, 148, 8, 64, 64, 288, 288, 1856, 36, 36, 204, 204, 1380, 8, 148, 918, 1, 8, 8, 36, 36, 232],
   [1842, 288, 1632, 288, 64, 8, 1856, 288, 288, 64, 498, 64, 8, 1856, 288, 288, 64, 120, 1380, 204, 204, 36, 36, 204, 36, 8, 1, 232, 36, 36, 8],
   [2052, 288, 288, 2304, 64, 1856, 8, 64, 64, 512, 582, 64, 1856, 8, 64, 64, 512, 148, 8, 64, 64, 512, 36, 36, 288, 8, 232, 1, 8, 8, 64],
   [5874, 960, 2304, 288, 288, 288, 64, 8, 512, 64, 1842, 288, 288, 64, 8, 512, 64, 498, 64, 8, 512, 64, 120, 288, 36, 36, 36, 8, 1, 64, 8],
   [6798, 1184, 64, 512, 288, 288, 64, 512, 8, 64, 2052, 288, 288, 64, 512, 8, 64, 582, 64, 512, 8, 64, 148, 8, 64, 36, 36, 8, 64, 1, 8],
   [30558, 6336, 512, 64, 1856, 64, 512, 64, 64, 8, 9906, 1856, 64, 512, 64, 64, 8, 2976, 512, 64, 64, 8, 792, 64, 8, 232, 8, 64, 8, 8, 1]]

def T8 : List (List ℤ) :=
  [[1, 9, 45, 165, 45, 165, 165, 495, 615, 3069, 9, 45, 165, 165, 495, 495, 2409, 45, 165, 495, 495, 2079, 201, 735, 2277, 855, 2937, 3267, 10131, 11673, 57321],
   [9, 1, 9, 45, 9, 45, 45, 165, 201, 1185, 201, 285, 1695, 1695, 6633, 7503, 45615, 45, 1275, 5709, 6579, 40413, 9, 81, 405, 81, 405, 405, 1485, 1809, 10665],
   [45, 9, 1, 9, 201, 285, 45, 405, 9, 81, 945, 7503, 10317, 1695, 15255, 285, 2565, 285, 1695, 15255, 285, 2565, 81, 9, 81, 1809, 2565, 405, 3645, 81, 729],
   [165, 45, 9, 1, 1395, 45, 405, 45, 81, 9, 3201, 53217, 1695, 15255, 1695, 2565, 285, 1155, 15255, 1695, 2565, 285, 405, 81, 9, 12555, 405, 3645, 405, 729, 81],
   [45, 9, 201, 1395, 1, 9, 9, 45, 45, 321, 1065, 45, 405, 405, 2025, 2025, 14445, 285, 285, 1695, 1695, 12441, 81, 1809, 12555, 9, 81, 81, 405, 405, 2889],
   [165, 45, 285, 45, 9, 1, 321, 45, 45, 9, 4071, 405, 45, 14445, 2025, 2025, 405, 1155, 12441, 1695, 1695, 285, 405, 2565, 405, 81, 9, 2889, 405, 405, 81],
   [165, 45, 45, 405, 9, 321, 1, 9, 9, 81, 4401, 405, 14445, 45, 405, 405, 3645, 1275, 45, 405, 405, 3645, 405, 405, 3645, 81, 2889, 9, 81, 81, 729],
   [495, 165, 405, 45, 45, 45, 9, 1, 81, 9, 14751, 2025, 2025, 405, 45, 3645, 405, 4533, 405, 45, 3645, 405, 1485, 3645, 405, 405, 405, 81, 9, 729, 81],
   [615, 201, 9, 81, 45, 45, 9, 81, 1, 9, 17007, 2025, 2025, 405, 3645, 45, 405, 5403, 405, 3645, 45, 405, 1809, 81, 729, 405, 405, 81, 729, 9, 81],
   [3069, 1185, 81, 9, 321, 9, 81, 9, 9, 1, 89781, 14445, 405, 3645, 405, 405, 45, 30249, 3645, 405, 405, 45, 10665, 729, 81, 2889, 81, 729, 81, 81, 9],
   [9, 201, 945, 3201, 1065, 4071, 4401, 14751, 17007, 89781, 1, 9, 45, 45, 165, 165, 945, 9, 45, 165, 165, 825, 45, 165, 495, 201, 735, 855, 2937, 3267, 17283],
   [45, 285, 7503, 53217, 45, 405, 405, 2025, 2025, 14445, 9, 1, 9, 9, 45, 45, 321, 201, 285, 1695, 1695, 12441, 45, 1275, 9087, 9, 81, 81, 405, 405, 2889],
   [165, 1695, 10317, 1695, 405, 45, 14445, 2025, 2025, 405, 45, 9, 1, 321, 45, 45, 9, 945, 12441, 1695, 1695, 285, 285, 1695, 285, 81, 9, 2889, 405, 405, 81],
   [165, 1695, 1695, 15255, 405, 14445, 45, 405, 405, 3645, 45, 9, 321, 1, 9, 9, 81, 1065, 45, 405, 405, 3645, 285, 285, 2565, 81, 2889, 9, 81, 81, 729],
   [495, 6633, 15255, 1695, 2025, 2025, 405, 45, 3645, 405, 165, 45, 45, 9, 1, 81, 9, 4071, 405, 45, 3645, 405, 1155, 2565, 285, 405, 405, 81, 9, 729, 81],
   [495, 7503, 285, 2565, 2025, 2025, 405, 3645, 45, 405, 165, 45, 45, 9, 81, 1, 9, 4401, 405, 3645, 45, 405, 1275, 45, 405, 405, 405, 81, 729, 9, 81],
   [2409, 45615, 2565, 285, 14445, 405, 3645, 405, 405, 45, 945, 321, 9, 81, 9, 9, 1, 25641, 3645, 405, 405, 45, 7911, 405, 45, 2889, 81, 729, 81, 81, 9],
   [45, 45, 285, 1155, 285, 1155, 1275, 4533, 5403, 30249, 9, 201, 945, 1065, 4071, 4401, 25641, 1, 9, 45, 45, 285, 9, 45, 165, 45, 165, 201, 735, 855, 4809],
   [165, 1275, 1695, 15255, 285, 12441, 45, 405, 405, 3645, 45, 285, 12441, 45, 405, 405, 3645, 9, 1, 9, 9, 81, 201, 285, 2565, 45, 2145, 9, 81, 81, 729],
   [495, 5709, 15255, 1695, 1695, 1695, 405, 45, 3645, 405, 165, 1695, 1695, 405, 45, 3645, 405, 45, 9, 1, 81, 9, 945, 2565, 285, 285, 285, 81, 9, 729, 81],
   [495, 6579, 285, 2565, 1695, 1695, 405, 3645, 45, 405, 165, 1695, 1695, 405, 3645, 45, 405, 45, 9, 81, 1, 9, 1065, 45, 405, 285, 285, 81, 729, 9, 81],
   [2079, 40413, 2565, 285, 12441, 285, 3645, 405, 405, 45, 825, 12441, 285, 3645, 405, 405, 45, 285, 81, 9, 9, 1, 6657, 405, 45, 2145, 45, 729, 81, 81, 9],
   [201, 9, 81, 405, 81, 405, 405, 1485, 1809, 10665, 45, 45, 285, 285, 1155, 1275, 7911, 9, 201, 945, 1065, 6657, 1, 9, 45, 9, 45, 45, 165, 201, 1185],
   [735, 81, 9, 81, 1809, 2565, 405, 3645, 81, 729, 165, 1275, 1695, 285, 2565, 45, 405, 45, 285, 2565, 45, 405, 9, 1, 9, 201, 285, 45, 405, 9, 81],
   [2277, 405, 81, 9, 12555, 405, 3645, 405, 729, 81, 495, 9087, 285, 2565, 285, 405, 45, 165, 2565, 285, 405, 45, 45, 9, 1, 1395, 45, 405, 45, 81, 9],
   [855, 81, 1809, 12555, 9, 81, 81, 405, 405, 2889, 201, 9, 81, 81, 405, 405, 2889, 45, 45, 285, 285, 2145, 9, 201, 1395, 1, 9, 9, 45, 45, 321],
   [2937, 405, 2565, 405, 81, 9, 2889, 405, 405, 81, 735, 81, 9, 2889, 405, 405, 81, 165, 2145, 285, 285, 45, 45, 285, 45, 9, 1, 321, 45, 45, 9],
   [3267, 405, 405, 3645, 81, 2889, 9, 81, 81, 729, 855, 81, 2889, 9, 81, 81, 729, 201, 9, 81, 81, 729, 45, 45, 405, 9, 321, 1, 9, 9, 81],
   [10131, 1485, 3645, 405, 405, 405, 81, 9, 729, 81, 2937, 405, 405, 81, 9, 729, 81, 735, 81, 9, 729, 81, 165, 405, 45, 45, 45, 9, 1, 81, 9],
   [11673, 1809, 81, 729, 405, 405, 81, 729, 9, 81, 3267, 405, 405, 81, 729, 9, 81, 855, 81, 729, 9, 81, 201, 9, 81, 45, 45, 9, 81, 1, 9],
   [57321, 10665, 729, 81, 2889, 81, 729, 81, 81, 9, 17283, 2889, 81, 729, 81, 81, 9, 4809, 729, 81, 81, 9, 1185, 81, 9, 321, 9, 81, 9, 9, 1]]

theorem hT0 : rows.map (fun _ => rows.map (fun _ => (1 : ℤ))) = T0 := by decide +kernel

theorem hT1 : stepB (dec 31 masks) T0 = T1 := by decide +kernel

theorem hT2 : stepB (dec 31 masks) T1 = T2 := by decide +kernel

theorem hT3 : stepB (dec 31 masks) T2 = T3 := by decide +kernel

theorem hT4 : stepB (dec 31 masks) T3 = T4 := by decide +kernel

theorem hT5 : stepB (dec 31 masks) T4 = T5 := by decide +kernel

theorem hT6 : stepB (dec 31 masks) T5 = T6 := by decide +kernel

theorem hT7 : stepB (dec 31 masks) T6 = T7 := by decide +kernel

theorem hT8 : stepB (dec 31 masks) T7 = T8 := by decide +kernel

theorem hchk : combTB (dec 31 masks) (rows.map (fun _ => rows.map (fun _ => 0))) [1, -8, 28, -56, 70, -56, 28, -8, 1]
    (rows.map (fun _ => rows.map (fun _ => 1))) = rows.map (fun _ => rows.map (fun _ => 0)) := by
  simp only [combTB, hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8]
  decide +kernel

theorem val0 : C (Vt (0, 0, 1) (1, 1, 0)) rows 0 = 961 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0]
  decide +kernel

theorem val1 : C (Vt (0, 0, 1) (1, 1, 0)) rows 1 = 6115 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0, hT1]
  decide +kernel

theorem val2 : C (Vt (0, 0, 1) (1, 1, 0)) rows 2 = 23071 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0, hT1, hT2]
  decide +kernel

theorem val3 : C (Vt (0, 0, 1) (1, 1, 0)) rows 3 = 65955 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3]
  decide +kernel

theorem val4 : C (Vt (0, 0, 1) (1, 1, 0)) rows 4 = 158217 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3, hT4]
  decide +kernel

theorem val5 : C (Vt (0, 0, 1) (1, 1, 0)) rows 5 = 335915 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3, hT4, hT5]
  decide +kernel

theorem val6 : C (Vt (0, 0, 1) (1, 1, 0)) rows 6 = 651531 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3, hT4, hT5, hT6]
  decide +kernel

theorem val7 : C (Vt (0, 0, 1) (1, 1, 0)) rows 7 = 1178343 := by
  rw [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl]
  simp only [iterB, hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7]
  decide +kernel

theorem vals : C (Vt (0, 0, 1) (1, 1, 0)) rows 0 = 961 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 1 = 6115 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 2 = 23071 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 3 = 65955 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 4 = 158217 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 5 = 335915 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 6 = 651531 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 7 = 1178343 :=
  ⟨val0, val1, val2, val3, val4, val5, val6, val7⟩

theorem a_C (m : ℕ) : a (m + 2) = C (Vt (0, 0, 1) (1, 1, 0)) rows m := by
  classical
  rw [← card_eq_C (Hrow (0, 0, 1) (0, 1, 0)) (Vt (0, 0, 1) (1, 1, 0)) rows hN hH m]
  unfold a
  refine congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun x _ => ?_))
  simp only [avoids, decide_eq_true_eq]
  exact avoid_iff _ _ _ _ x

theorem a_1 : a 1 = 31 := by
  classical
  have h := card_one (Hrow (0, 0, 1) (0, 1, 0)) (Vt (0, 0, 1) (1, 1, 0)) rows hN hH
  rw [show ((rows.length : ℕ) : ℤ) = 31 from rfl] at h
  rw [← h]
  unfold a
  refine congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun x _ => ?_))
  simp only [avoids, decide_eq_true_eq]
  exact avoid_iff _ _ _ _ x

theorem recZ (m : ℕ) : a (m + 2) - 8 * a (m + 3) + 28 * a (m + 4) - 56 * a (m + 5) + 70 * a (m + 6) - 56 * a (m + 7) + 28 * a (m + 8) - 8 * a (m + 9) + a (m + 10) = 0 := by
  have h := rec_CB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 31 masks) htbl [1, -8, 28, -56, 70, -56, 28, -8, 1] hchk m
  simp only [combC] at h
  rw [a_C, a_C, a_C, a_C, a_C, a_C, a_C, a_C, a_C]
  linarith

end OMA.P207390

theorem OMA.solution : type_of% @OMA.S_oeis_a207390.main := by
  have A1 : (OMA.S_oeis_a207390.a 1 : ℚ) = 31 := by exact_mod_cast OMA.P207390.a_1
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := OMA.P207390.vals
  have A2 : (OMA.S_oeis_a207390.a 2 : ℚ) = 961 := by
    have h := OMA.P207390.a_C 0
    rw [v0] at h
    exact_mod_cast h
  have A3 : (OMA.S_oeis_a207390.a 3 : ℚ) = 6115 := by
    have h := OMA.P207390.a_C 1
    rw [v1] at h
    exact_mod_cast h
  have A4 : (OMA.S_oeis_a207390.a 4 : ℚ) = 23071 := by
    have h := OMA.P207390.a_C 2
    rw [v2] at h
    exact_mod_cast h
  have A5 : (OMA.S_oeis_a207390.a 5 : ℚ) = 65955 := by
    have h := OMA.P207390.a_C 3
    rw [v3] at h
    exact_mod_cast h
  have A6 : (OMA.S_oeis_a207390.a 6 : ℚ) = 158217 := by
    have h := OMA.P207390.a_C 4
    rw [v4] at h
    exact_mod_cast h
  have A7 : (OMA.S_oeis_a207390.a 7 : ℚ) = 335915 := by
    have h := OMA.P207390.a_C 5
    rw [v5] at h
    exact_mod_cast h
  have A8 : (OMA.S_oeis_a207390.a 8 : ℚ) = 651531 := by
    have h := OMA.P207390.a_C 6
    rw [v6] at h
    exact_mod_cast h
  have A9 : (OMA.S_oeis_a207390.a 9 : ℚ) = 1178343 := by
    have h := OMA.P207390.a_C 7
    rw [v7] at h
    exact_mod_cast h
  have hrec : ∀ m : ℕ, (OMA.S_oeis_a207390.a (m + 10) : ℚ) = -OMA.S_oeis_a207390.a (m + 2) + 8 * OMA.S_oeis_a207390.a (m + 3) - 28 * OMA.S_oeis_a207390.a (m + 4) + 56 * OMA.S_oeis_a207390.a (m + 5) - 70 * OMA.S_oeis_a207390.a (m + 6) + 56 * OMA.S_oeis_a207390.a (m + 7) - 28 * OMA.S_oeis_a207390.a (m + 8) + 8 * OMA.S_oeis_a207390.a (m + 9) := by
    intro m
    have h := OMA.P207390.recZ m
    have h' : ((OMA.S_oeis_a207390.a (m + 2) : ℚ) - 8 * (OMA.S_oeis_a207390.a (m + 3) : ℚ) + 28 * (OMA.S_oeis_a207390.a (m + 4) : ℚ) - 56 * (OMA.S_oeis_a207390.a (m + 5) : ℚ) + 70 * (OMA.S_oeis_a207390.a (m + 6) : ℚ) - 56 * (OMA.S_oeis_a207390.a (m + 7) : ℚ) + 28 * (OMA.S_oeis_a207390.a (m + 8) : ℚ) - 8 * (OMA.S_oeis_a207390.a (m + 9) : ℚ) + (OMA.S_oeis_a207390.a (m + 10) : ℚ) : ℚ) = 0 := by exact_mod_cast h
    linarith
  refine ⟨?_, ?_⟩
  · have hD : (((1 - PowerSeries.X) ^ 8) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-8 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (28 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-56 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (70 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-56 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (28 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (-8 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 8 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have hNum : ((PowerSeries.X * (31 + 713 * PowerSeries.X - 705 * PowerSeries.X ^ 2 - 677 * PowerSeries.X ^ 3 + 961 * PowerSeries.X ^ 4 - 341 * PowerSeries.X ^ 5 + 45 * PowerSeries.X ^ 6 - 3 * PowerSeries.X ^ 7)) : PowerSeries ℚ)
        = PowerSeries.C (0 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (31 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (713 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-705 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-677 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (961 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (-341 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (45 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ 8 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have key : ∀ F : PowerSeries ℚ, F * (PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-8 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (28 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-56 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (70 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-56 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (28 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (-8 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 8)
        = PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 0) + PowerSeries.C (-8 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (28 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (-56 : ℚ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (70 : ℚ) * (F * PowerSeries.X ^ 4) + PowerSeries.C (-56 : ℚ) * (F * PowerSeries.X ^ 5) + PowerSeries.C (28 : ℚ) * (F * PowerSeries.X ^ 6) + PowerSeries.C (-8 : ℚ) * (F * PowerSeries.X ^ 7) + PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 8) := by
      intro F; ring
    rw [hD, hNum, key]
    ext n
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
    · norm_num
    · norm_num [A1]
    · norm_num [A1, A2]
    · norm_num [A1, A2, A3]
    · norm_num [A1, A2, A3, A4]
    · norm_num [A1, A2, A3, A4, A5]
    · norm_num [A1, A2, A3, A4, A5, A6]
    · norm_num [A1, A2, A3, A4, A5, A6, A7]
    · norm_num [A1, A2, A3, A4, A5, A6, A7, A8]
    · norm_num [A1, A2, A3, A4, A5, A6, A7, A8, A9]
    · rw [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 10 from rfl]
      have h := hrec m
      simp only [show 0 ≤ m + 10 from by omega,
        show m + 10 - 0 = m + 10 from rfl,
        show ¬ (m + 10 < 1) from by omega,
        show 1 ≤ m + 10 from by omega,
        show m + 10 - 1 = m + 9 from rfl,
        show ¬ (m + 9 < 1) from by omega,
        show 2 ≤ m + 10 from by omega,
        show m + 10 - 2 = m + 8 from rfl,
        show ¬ (m + 8 < 1) from by omega,
        show 3 ≤ m + 10 from by omega,
        show m + 10 - 3 = m + 7 from rfl,
        show ¬ (m + 7 < 1) from by omega,
        show 4 ≤ m + 10 from by omega,
        show m + 10 - 4 = m + 6 from rfl,
        show ¬ (m + 6 < 1) from by omega,
        show 5 ≤ m + 10 from by omega,
        show m + 10 - 5 = m + 5 from rfl,
        show ¬ (m + 5 < 1) from by omega,
        show 6 ≤ m + 10 from by omega,
        show m + 10 - 6 = m + 4 from rfl,
        show ¬ (m + 4 < 1) from by omega,
        show 7 ≤ m + 10 from by omega,
        show m + 10 - 7 = m + 3 from rfl,
        show ¬ (m + 3 < 1) from by omega,
        show 8 ≤ m + 10 from by omega,
        show m + 10 - 8 = m + 2 from rfl,
        show ¬ (m + 2 < 1) from by omega,
        show ¬ (m + 10 = 0) from by omega,
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
    rcases Nat.lt_or_ge n 10 with h | h
    · interval_cases n <;> norm_num [A1, A2, A3, A4, A5, A6, A7, A8, A9]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      have h := hrec m
      simp only [show m + 10 - 1 = m + 9 from rfl, show m + 10 - 2 = m + 8 from rfl, show m + 10 - 3 = m + 7 from rfl, show m + 10 - 4 = m + 6 from rfl, show m + 10 - 5 = m + 5 from rfl, show m + 10 - 6 = m + 4 from rfl, show m + 10 - 7 = m + 3 from rfl, show m + 10 - 8 = m + 2 from rfl]
      rw [h]
      ring
