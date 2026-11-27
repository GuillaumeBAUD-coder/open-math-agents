import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1

namespace OMA.BB4H1

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev State := Fin 4
abbrev Key := State × Symbol
abbrev Machine4 := Machine Symbol State

structure Move where
  state : State
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Table where
  t00 : Option Move
  t01 : Option Move
  t10 : Option Move
  t11 : Option Move
  t20 : Option Move
  t21 : Option Move
  t30 : Option Move
  t31 : Option Move

def Table.empty : Table := ⟨none, none, none, none, none, none, none, none⟩

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val, a.val with
  | 0, 0 => tb.t00
  | 0, _ => tb.t01
  | 1, 0 => tb.t10
  | 1, _ => tb.t11
  | 2, 0 => tb.t20
  | 2, _ => tb.t21
  | _, 0 => tb.t30
  | _, _ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val, a.val with
  | 0, 0 => { tb with t00 := some m }
  | 0, _ => { tb with t01 := some m }
  | 1, 0 => { tb with t10 := some m }
  | 1, _ => { tb with t11 := some m }
  | 2, 0 => { tb with t20 := some m }
  | 2, _ => { tb with t21 := some m }
  | _, 0 => { tb with t30 := some m }
  | _, _ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip, tb.t01.map Move.flip,
   tb.t10.map Move.flip, tb.t11.map Move.flip,
   tb.t20.map Move.flip, tb.t21.map Move.flip,
   tb.t30.map Move.flip, tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q', a') ≠ (q, a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
  fin_cases q <;> fin_cases a <;> fin_cases q' <;> fin_cases a' <;>
    first | rfl | exact absurd rfl h

theorem Table.get_flip (tb : Table) (q : State) (a : Symbol) :
    tb.flip.get q a = (tb.get q a).map Move.flip := by
  fin_cases q <;> fin_cases a <;> rfl

structure Position where
  state : State
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def startPos : Position := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val, xs with
  | 0, [] => []
  | _, xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def listEq : List Symbol → List Symbol → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x.val y.val && listEq xs ys
  | _, _ => false

theorem listEq_eq_true {xs ys : List Symbol} (h : listEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [listEq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [listEq] at h
    | cons y ys =>
      simp only [listEq, Bool.and_eq_true] at h
      rw [Fin.ext (Nat.eq_of_beq_eq_true h.1), ih h.2]

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state, c.ls.tail, symHead c.ls, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, symHead c.rs, c.rs.tail⟩

def Position.flip (c : Position) : Position := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position) (m : Move) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  fin_cases a
  · cases xs with
    | nil => exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
    | cons x xs => exact (ListBlank.cons_mk 0 (x :: xs)).symm
  · exact (ListBlank.cons_mk 1 xs).symm

def Position.view (c : Position) : Cfg Symbol State :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m, tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    rw [Table.get_set_self] at hh
    exact (Option.some.inj hh) ▸ h
  · rw [Table.get_set_ne tb m e] at hh
    exact hm q' a' m' hh

theorem step_move {M : Machine4} {tb : Table} (hm : Matches M tb) (c : Position) (m : Move)
    (h : tb.get c.state c.head = some m) :
    M.step c.view = some (c.move m).view := by
  have he := hm c.state c.head m h
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push, symHead_eq_headI]

theorem multi_succ_front (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    M.multiStep c (k + 1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

-- ============================================================
-- Guarded repeatable-segment checker
-- ============================================================

def takePad : ℕ → List Symbol → List Symbol
  | 0, _ => []
  | k + 1, [] => 0 :: takePad k []
  | k + 1, x :: xs => x :: takePad k xs

theorem takePad_foldr_drop (k : ℕ) (xs : List Symbol) :
    (takePad k xs).foldr ListBlank.cons (ListBlank.mk (xs.drop k)) = ListBlank.mk xs := by
  induction k generalizing xs with
  | zero => simp [takePad]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [takePad, List.foldr_cons, List.drop_nil]
      have h0 := ih []
      simp only [List.drop_nil] at h0
      rw [h0]
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons x xs =>
      simp only [takePad, List.foldr_cons, List.drop_succ_cons]
      rw [ih xs, ListBlank.cons_mk]

def runGuardedLeft (tb : Table) : ℕ → State → Symbol → List Symbol → List Symbol →
    Option (State × Symbol × List Symbol × List Symbol)
  | 0, q, a, near, rs => some (q, a, near, rs)
  | k + 1, q, a, near, rs =>
    match tb.get q a with
    | none => none
    | some m =>
      if m.left then
        match near with
        | [] => none
        | a' :: near' => runGuardedLeft tb k m.state a' near' (push m.write rs)
      else
        runGuardedLeft tb k m.state (symHead rs) (m.write :: near) rs.tail

def checkGuardedLeft (tb : Table) (p : ℕ) (q : State) (a : Symbol)
    (near rs : List Symbol) : Bool :=
  match runGuardedLeft tb p q a near rs with
  | none => false
  | some (q', a', near', rs') =>
    Nat.beq q'.val q.val && Nat.beq a'.val a.val && listEq rs' rs &&
      listEq (near'.take near.length) near && Nat.ble near.length near'.length

theorem runGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near rs : List Symbol)
    {q' : State} {a' : Symbol} {near' rs' : List Symbol}
    (h : runGuardedLeft tb p q a near rs = some (q', a', near', rs'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q', ⟨a', near'.foldr ListBlank.cons tail, ListBlank.mk rs'⟩⟩ := by
  induction p generalizing q a near rs with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | true =>
        simp only [hd, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, (x :: xs).foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
              some ⟨some m.state, ⟨x, xs.foldr ListBlank.cons tail, ListBlank.mk (push m.write rs)⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write rs) h
      | false =>
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
            some ⟨some m.state, ⟨symHead rs, (m.write :: near).foldr ListBlank.cons tail, ListBlank.mk rs.tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead rs) (m.write :: near) rs.tail h

theorem runGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near ls : List Symbol)
    {q' : State} {a' : Symbol} {near' ls' : List Symbol}
    (h : runGuardedLeft tb.flip p q a near ls = some (q', a', near', ls'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q', ⟨a', ListBlank.mk ls', near'.foldr ListBlank.cons tail⟩⟩ := by
  induction p generalizing q a near ls with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    rw [Table.get_flip] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht, Option.map_some] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | false =>
        simp only [Move.flip, hd, Bool.not_false, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, (x :: xs).foldr ListBlank.cons tail⟩⟩ =
              some ⟨some m.state, ⟨x, ListBlank.mk (push m.write ls), xs.foldr ListBlank.cons tail⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write ls) h
      | true =>
        simp only [Move.flip, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ =
            some ⟨some m.state, ⟨symHead ls, ListBlank.mk ls.tail, (m.write :: near).foldr ListBlank.cons tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead ls) (m.write :: near) ls.tail h

theorem foldr_append (xs ys : List Symbol) (tail : ListBlank Symbol) :
    (xs ++ ys).foldr ListBlank.cons tail = xs.foldr ListBlank.cons (ys.foldr ListBlank.cons tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem checkGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near rs : List Symbol}
    (h : checkGuardedLeft tb p q a near rs = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q, ⟨a, near.foldr ListBlank.cons tail', ListBlank.mk rs⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb p q a near rs with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', rs'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hrs⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hrs' : rs' = rs := listEq_eq_true hrs
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hrs'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedLeft_sound hm p q' a' near rs' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

theorem checkGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near ls : List Symbol}
    (h : checkGuardedLeft tb.flip p q a near ls = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail'⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb.flip p q a near ls with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', ls'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hls⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hls' : ls' = ls := listEq_eq_true hls
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hls'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedRight_sound hm p q' a' near ls' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

structure HistItem where
  step : ℕ
  pos : ℕ
  c : Position

def findRepAux (tb : Table) (cur : HistItem) (minp maxp : ℕ) : List HistItem → Bool
  | [] => false
  | hi :: rest =>
    let minp' := if Nat.ble minp hi.pos then minp else hi.pos
    let maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    let ok :=
      if Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val then
        let p := cur.step - hi.step
        let leftOk :=
          if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
            let dL := hi.pos - minp'
            let near := takePad dL hi.c.ls
            if listEq (takePad dL cur.c.ls) near then
              checkGuardedLeft tb p hi.c.state hi.c.head near hi.c.rs
            else false
          else false
        if leftOk then true
        else if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
          let dR := maxp' - hi.pos
          let near := takePad dR hi.c.rs
          if listEq (takePad dR cur.c.rs) near then
            checkGuardedLeft tb.flip p hi.c.state hi.c.head near hi.c.ls
          else false
        else false
      else false
    if ok then true else findRepAux tb cur minp' maxp' rest

def findRep (tb : Table) (cur : HistItem) (prev : List HistItem) : Bool :=
  findRepAux tb cur 1000 0 prev

def HistValid (M : Machine4) (hist : List HistItem) : Prop :=
  ∀ h ∈ hist, h.step ≤ 107 ∧ M.multiStep (Machine.init []) h.step = some h.c.view

def NoRepeatHyp (M : Machine4) : Prop :=
  ∀ (i p : ℕ) (q : State) (a : Symbol) (side : Bool)
      (near : List Symbol) (fixed : ListBlank Symbol), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank Symbol =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg Symbol State)
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')

theorem findRepAux_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem}
    (hcur : cur.step ≤ 107) (hvalid : HistValid M prev)
    {minp maxp : ℕ} (h : findRepAux tb cur minp maxp prev = true) : False := by
  induction prev generalizing minp maxp with
  | nil => simp [findRepAux] at h
  | cons hi rest ih =>
    unfold findRepAux at h
    dsimp only at h
    set minp' := if Nat.ble minp hi.pos then minp else hi.pos
    set maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    by_cases hcond : (Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val) = true
    · simp only [hcond, ↓reduceIte] at h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq_true_eq] at hcond
      have ⟨hstep_hi, hrun_hi⟩ := hvalid hi (List.mem_cons_self ..)
      have hp_pos : 0 < cur.step - hi.step := by omega
      have hp_le : hi.step + (cur.step - hi.step) ≤ 107 := by omega
      by_cases hleft : (if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
          if listEq (takePad (hi.pos - minp') cur.c.ls) (takePad (hi.pos - minp') hi.c.ls) then
            checkGuardedLeft tb (cur.step - hi.step) hi.c.state hi.c.head (takePad (hi.pos - minp') hi.c.ls) hi.c.rs
          else false else false) = true
      · split at hleft
        · split at hleft
          · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head true
              (takePad (hi.pos - minp') hi.c.ls) (ListBlank.mk hi.c.rs)
              hp_pos hp_le
              ⟨ListBlank.mk (hi.c.ls.drop (hi.pos - minp')), by
                simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
              (checkGuardedLeft_sound hm hleft)
          · contradiction
        · contradiction
      · simp only [hleft, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hright : (if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
            if listEq (takePad (maxp' - hi.pos) cur.c.rs) (takePad (maxp' - hi.pos) hi.c.rs) then
              checkGuardedLeft tb.flip (cur.step - hi.step) hi.c.state hi.c.head (takePad (maxp' - hi.pos) hi.c.rs) hi.c.ls
            else false else false) = true
        · split at hright
          · split at hright
            · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head false
                (takePad (maxp' - hi.pos) hi.c.rs) (ListBlank.mk hi.c.ls)
                hp_pos hp_le
                ⟨ListBlank.mk (hi.c.rs.drop (maxp' - hi.pos)), by
                  simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
                (checkGuardedRight_sound hm hright)
            · contradiction
          · contradiction
        · simp only [hright, Bool.false_eq_true, ↓reduceIte] at h
          exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h

-- ============================================================
-- FAR (Finite Automata Reduction) certificate verifier
-- ============================================================

inductive CanStop (tb : Table) : Position → Prop
  | missing {c} : tb.get c.state c.head = none → CanStop tb c
  | move {c m} : tb.get c.state c.head = some m → CanStop tb (c.move m) → CanStop tb c

theorem canStop_flip {tb : Table} {c : Position} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, Table.get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get c.state c.head = some m.flip
      simp [Table.get_flip, h]
    · rwa [← flip_move]

theorem cannot_stop_run {M : Machine4} {tb : Table}
    (hm : Matches M tb) (c : Position) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get c.state c.head with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move hm c m h, Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  fin_cases a
  · cases xs with
    | nil => exact D.blank.symm
    | cons x xs => rfl
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

structure Certificate where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate) := Option (State × Fin cert.dfa.size)

def nodeId (cert : Certificate) : Node cert → ℕ
  | none => 4 * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edgeRow (cert : Certificate) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (4 * cert.dfa.size)
  | some _ => (cert.edges / 2 ^ ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) %
      2 ^ (4 * cert.dfa.size + 1)

def Certificate.edge (cert : Certificate) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  (cert.edgeRow p a).testBit (nodeId cert q)

theorem edge_none (cert : Certificate) (a : Symbol) (q : Node cert) :
    cert.edge none a q = q.isNone := by
  unfold Certificate.edge Certificate.edgeRow
  simp only [Nat.testBit_two_pow]
  rcases q with _ | ⟨q, l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hl : l.val < cert.dfa.size := l.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId, hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := val / 2 % 16
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 32 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 32 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (nodes cert).all fun q => !row.testBit (nodeId cert q) || cert.onBlank q
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state, l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              (nodes cert).all fun t => !swRow.testBit (nodeId cert t) || pRow.testBit (nodeId cert t)
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state, cert.dfa.next m.write l)))

def checkMachine (tb : Table) (cert : Certificate) : Bool :=
  (List.finRange 4).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

theorem Reads.push {cert : Certificate} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, by simp [edge_none], .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

theorem no_read_blank {cert : Certificate} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0, 0)) (ListBlank.mk []) := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart, hsink⟩, hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp, if_true] at ht
      have hn := allNodes ht q
      have he0 : (cert.edgeRow p 0).testBit (nodeId cert q) = true := he
      simp [he0] at hn
      exact ih rfl hn
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Table} {cert : Certificate} (hchk : checkMachine tb cert = true)
    {c : Position} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    exact Reads.push (show cert.edge (some (c.state, cert.dfa.read c.ls)) c.head none = true from h) (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd, Certificate.edge] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, symHead_eq_headI, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push, symHead_eq_headI] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      have hbeq : Nat.beq (cert.dfa.next c.ls.headI (cert.dfa.read c.ls.tail)).val (cert.dfa.read c.ls).val = true := by
        simp [TapeDFA.read_pop]
      simp only [hbeq, if_true] at h'
      have h'' := allNodes h' s
      have he' : (cert.edgeRow (some (m.state, cert.dfa.read c.ls.tail)) c.ls.headI).testBit (nodeId cert s) = true := he
      simp only [he', if_true] at h''
      have h''' := allNodes h'' t
      have hf' : (cert.edgeRow s m.write).testBit (nodeId cert t) = true := hf
      simp [hf'] at h'''
      exact Reads.push h''' ht

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := unpack val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound {tb : Table} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb startPos := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, startPos, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [startPos, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

-- ============================================================
-- Symmetry: swapping states 2 and 3
-- ============================================================

def swap23 : Equiv.Perm State := Equiv.swap (2 : State) (3 : State)

theorem swap23_0 : swap23 0 = 0 := by decide
theorem swap23_1 : swap23 1 = 1 := by decide
theorem swap23_2 : swap23 2 = 3 := by decide
theorem swap23_3 : swap23 3 = 2 := by decide
theorem swap23_inv (q : State) : swap23.symm q = swap23 q := by fin_cases q <;> decide

def reindex23 (M : Machine4) : Machine4 :=
  fun q a => (M (swap23 q) a).map fun (s, b) => (s.map swap23, b)

def mapCfg23 (c : Cfg Symbol State) : Cfg Symbol State :=
  ⟨c.q.map swap23, c.tape⟩

theorem reindex23_step (M : Machine4) (c : Cfg Symbol State) :
    (reindex23 M).step (mapCfg23 c) = (M.step c).map mapCfg23 := by
  obtain ⟨q, t⟩ := c
  cases q with
  | none => rfl
  | some q =>
    simp only [Machine.step, mapCfg23, Option.map_some, reindex23]
    have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
    rw [hinv]
    cases M q t.head with
    | none => rfl
    | some entry => rfl

theorem reindex23_multi (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    (reindex23 M).multiStep (mapCfg23 c) k = (M.multiStep c k).map mapCfg23 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases M.multiStep c k with
    | none => rfl
    | some c' => exact reindex23_step M c'

theorem mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
  simp [mapCfg23, Machine.init, swap23_0]

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨swap23 q0, t0, ?_⟩
    rw [← mapCfg23_init, reindex23_multi, hRun]; rfl
  · intro q a
    rcases hForm (swap23 q) a with h | ⟨q', z, h⟩
    · left; simp [reindex23, h]
    · right; exact ⟨swap23 q', z, by simp [reindex23, h]⟩
  · exact ⟨swap23 qm, am, by
      have : swap23 (swap23 qm) = qm := by fin_cases qm <;> decide
      simp [reindex23, this, hMiss]⟩
  · intro i p q a side near fixed hp hle cfg hEnter hCycle
    let cfgM : ListBlank Symbol → Cfg Symbol State := fun tail =>
      let free := near.foldr ListBlank.cons tail
      ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
    have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
      intro tail
      have : swap23 (swap23 q) = q := by fin_cases q <;> decide
      simp [mapCfg23, cfgM, cfg, this]
    apply hLoop i p (swap23 q) a side near fixed hp hle
    · obtain ⟨tail, ht⟩ := hEnter
      rw [← mapCfg23_init, reindex23_multi] at ht
      cases hMi : M.multiStep (Machine.init []) i with
      | none => simp [hMi] at ht
      | some c' =>
        simp only [hMi, Option.map_some, Option.some.injEq] at ht
        refine ⟨tail, ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht
        rcases ht with ⟨hq', ht'⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht']
    · intro tail
      obtain ⟨tail', ht'⟩ := hCycle tail
      rw [← hmap tail, reindex23_multi] at ht'
      cases hMp : M.multiStep (cfgM tail) p with
      | none => simp [hMp] at ht'
      | some c' =>
        simp only [hMp, Option.map_some, Option.some.injEq] at ht'
        refine ⟨tail', ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht'
        rcases ht' with ⟨hq', ht''⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht'']
  · obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl

def UsesOnly01 (tb : Table) : Prop :=
  tb.t20 = none ∧ tb.t21 = none ∧ tb.t30 = none ∧ tb.t31 = none ∧
  (∀ q a m, tb.get q a = some m → m.state = 0 ∨ m.state = 1)

theorem matches_reindex23 {M : Machine4} {tb : Table}
    (hm : Matches M tb) (h01 : UsesOnly01 tb) : Matches (reindex23 M) tb := by
  intro q a m hget
  have hms := h01.2.2.2.2 q a m hget
  have hq : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · fin_cases a <;> simp [Table.get, h01.1, h01.2.1] at hget
    · fin_cases a <;> simp [Table.get, h01.2.2.1, h01.2.2.2.1] at hget
  have hsq : swap23 q = q := by rcases hq with rfl | rfl <;> decide
  have hsm : swap23 m.state = m.state := by rcases hms with h | h <;> rw [h] <;> decide
  simp only [reindex23, hsq, hm q a m hget, Move.command, Option.map_some, hsm]

theorem histValid_reindex23 {M : Machine4} {hist : List HistItem}
    (hv : HistValid M hist)
    (h01 : ∀ h ∈ hist, h.c.state = 0 ∨ h.c.state = 1) :
    HistValid (reindex23 M) hist := by
  intro h hh
  have ⟨hle, hrun⟩ := hv h hh
  refine ⟨hle, ?_⟩
  rw [← mapCfg23_init, reindex23_multi, hrun]
  have hs : swap23 h.c.state = h.c.state := by
    rcases h01 h hh with hs | hs <;> rw [hs] <;> decide
  simp [mapCfg23, Position.view, hs]

-- ============================================================
-- Stateful DFS Tree Verifier
-- ============================================================

def holes (tb : Table) : Finset Key :=
  Finset.univ.filter fun k => tb.get k.1 k.2 = none

theorem holes_set (tb : Table) (q : State) (a : Symbol) (m : Move) :
    holes (tb.set q a m) = (holes tb).erase (q, a) := by
  ext ⟨q', a'⟩
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    simp [Table.get_set_self]
  · simp [Table.get_set_ne tb m e, e]

def moves12 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩]

def moves16 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩,
   ⟨3, 0, false⟩, ⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 1, true⟩]

def movesAllowed (used2 : Bool) : List Move :=
  if used2 then moves16 else moves12

theorem mem_movesAllowed (used2 : Bool) (m : Move) (h : used2 = false → m.state ≠ 3) :
    m ∈ movesAllowed used2 := by
  obtain ⟨q, a, d⟩ := m
  cases used2
  · have h3 := h rfl
    fin_cases q <;> fin_cases a <;> cases d <;> simp_all [movesAllowed, moves12]
  · fin_cases q <;> fin_cases a <;> cases d <;> simp [movesAllowed, moves16]

inductive StepResult where
  | rep
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : HistItem) (prev : List HistItem)

def stepLoop (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0, _, _ => .done
  | rem + 1, cur, prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep, npos, nc⟩
      let nprev := cur :: prev
      if (Nat.beq nstep 6 || Nat.beq nstep 12 || Nat.beq nstep 24 || Nat.beq nstep 48 || Nat.beq nstep 107) &&
          findRep tb ncur nprev then
        .rep
      else
        stepLoop tb rem ncur nprev

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | holesLeft + 1, used2, tb, rem, cur, prev, certs =>
    match stepLoop tb rem cur prev with
    | .rep => some certs
    | .done =>
      match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some rest else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some certs
      else
        checkMoves (fun m rest =>
          checkTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) certs

theorem checkMoves_each {f : Move → List ℕ → Option (List ℕ)} {ms : List Move}
    {a b : List ℕ} (h : checkMoves f ms a = some b) {m : Move} (hm : m ∈ ms) :
    ∃ x y, f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a, mid, hh⟩
      · exact ih h ht

theorem stepLoop_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match stepLoop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only [ht]
      have ⟨hcur_le, hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1, if m.left then cur.pos - 1 else cur.pos + 1, cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ, hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega, hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev, h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u, hprev01⟩ := h01 hu
        refine ⟨u, fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur, Position.move, hd] using hms
        · exact hprev01 h hh'
      by_cases hrep : ((Nat.beq (cur.step + 1) 6 || Nat.beq (cur.step + 1) 12 || Nat.beq (cur.step + 1) 24 ||
          Nat.beq (cur.step + 1) 48 || Nat.beq (cur.step + 1) 107) && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01

theorem usesOnly01_set {tb : Table} (h01 : UsesOnly01 tb) {q : State} {a : Symbol} {m : Move}
    (hq : q = 0 ∨ q = 1) (hm : m.state = 0 ∨ m.state = 1) :
    UsesOnly01 (tb.set q a m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.2.1
  · intro q' a' m' hh
    by_cases e : (q', a') = (q, a)
    · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
      rw [Table.get_set_self] at hh
      exact (Option.some.inj hh) ▸ hm
    · rw [Table.get_set_ne tb m e] at hh
      exact h01.2.2.2.2 q' a' m' hh

theorem checkTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : checkTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm hG hsum hv hu
    cases hsl : stepLoop tb rem cur prev with
    | rep => rw [hsl] at hstep; exact hstep
    | done =>
      simp only [hsl] at hCheck
      cases a with
      | nil => simp at hCheck
      | cons v rest =>
        simp only at hCheck
        split at hCheck
        · rename_i hcert
          have hns := certificate_sound hcert
          obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2
          exact cannot_stop_run hm startPos hns (k + 1) hk
        · simp at hCheck
    | missing q a rem' cur' prev' =>
      simp only [hsl] at hCheck hstep
      obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
      have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
      -- M must define (q, a) as some (some q', z) since cur'.step < 107 and M runs past 107
      have hM_def : ∃ q' z, M q a = some (some q', z) := by
        rcases hG.2.1 q a with hMnone | hMsome
        · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
            rw [Machine.multiStep_succ, hcur'_run]
            simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
          have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
          obtain ⟨q0, t0, hrun107⟩ := hG.1
          rw [h107] at hrun107
          contradiction
        · exact hMsome
      obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
      split at hCheck
      · -- holesLeft == 0: (holes tb).card ≤ 1 and (q, a) ∈ holes tb, so M has no none!
        rename_i h0
        have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
        have hmem : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard1 : (holes tb).card = 1 :=
          le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hmem⟩)
        obtain ⟨qm, am, hMmiss⟩ := hG.2.2.1
        have hqm_mem : (qm, am) ∈ holes tb := by
          simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hget : tb.get qm am with
          | none => rfl
          | some m =>
            have := hm qm am m hget
            rw [hMmiss] at this
            simp [Move.command] at this
        have heq_key : (qm, am) = (q, a) := by
          have hsub : ({(q, a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
          have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
          rw [← hEq, Finset.mem_singleton] at hqm_mem
          exact hqm_mem
        rcases Prod.mk.inj heq_key with ⟨rfl, rfl⟩
        rw [hMmiss] at hMqa
        contradiction
      · -- Branch on movesAllowed used2
        let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
        have hm_cmd : M q a = m.command := by
          cases d <;> simpa [m, Move.command] using hMqa
        have hmem_hole : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
          rw [holes_set, Finset.card_erase_of_mem hmem_hole]
          omega
        by_cases hswap : used2 = false ∧ q' = 3
        · rcases hswap with ⟨hu2, rfl⟩
          have ⟨h01, hprev01⟩ := hu' hu2
          let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
          have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m2
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
          have hM2qa : (reindex23 M) q a = m2.command := by
            cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
          have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
            rw [holes_set, Finset.card_erase_of_mem hmem_hole]
            omega
          exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
            (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
            (histValid_reindex23 hv' hprev01) (by simp [m2])
        · have hmem_m : m ∈ movesAllowed used2 :=
            mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m
          refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
          intro hnext_u2
          simp only [Bool.or_eq_false_iff] at hnext_u2
          have ⟨h01, hprev01⟩ := hu' hnext_u2.1
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hm01 : m.state = 0 ∨ m.state = 1 := by
            have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
            have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
            fin_cases q' <;> simp_all [m]
          exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

def TreeValid (tb : Table) (used2 : Bool) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : Prop :=
  ∀ M : Machine4, GoodMachine M → Matches M tb →
    cur.step + rem = 107 →
    HistValid M (cur :: prev) →
    (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
    False

theorem branch_one {tb : Table} {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    {q : State} {a : Symbol} {rem' : ℕ} {cur' : HistItem} {prev' : List HistItem}
    (hsl : stepLoop tb rem cur prev = .missing q a rem' cur' prev')
    (hChildren : ∀ m ∈ movesAllowed used2,
      TreeValid (tb.set q a m) (used2 || Nat.beq m.state.val 2) rem' cur' prev') :
    TreeValid tb used2 rem cur prev := by
  intro M hG hm hsum hv hu
  have hstep := stepLoop_sound hm hG hsum hv hu
  simp only [hsl] at hstep
  obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
  have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
  have hM_def : ∃ q' z, M q a = some (some q', z) := by
    rcases hG.2.1 q a with hMnone | hMsome
    · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
        rw [Machine.multiStep_succ, hcur'_run]
        simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
      have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
      obtain ⟨q0, t0, hrun107⟩ := hG.1
      rw [h107] at hrun107
      contradiction
    · exact hMsome
  obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M q a = m.command := by cases d <;> simpa [m, Move.command] using hMqa
  by_cases hswap : used2 = false ∧ q' = 3
  · rcases hswap with ⟨hu2, rfl⟩
    have ⟨h01, hprev01⟩ := hu' hu2
    let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
    have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
    have hM2qa : (reindex23 M) q a = m2.command := by
      cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
    exact hChildren m2 hmem_m2 (reindex23 M) (goodMachine_reindex23 hG)
      (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
      (histValid_reindex23 hv' hprev01) (by simp [m2])
  · have hmem_m : m ∈ movesAllowed used2 :=
      mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
    refine hChildren m hmem_m M hG (matches_set hm hm_cmd) hsum' hv' ?_
    intro hnext_u2
    simp only [Bool.or_eq_false_iff] at hnext_u2
    have ⟨h01, hprev01⟩ := hu' hnext_u2.1
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hm01 : m.state = 0 ∨ m.state = 1 := by
      have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
      have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
      fin_cases q' <;> simp_all [m]
    exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩



def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩
def h2 : HistItem := ⟨2, 128, (startPos.move ⟨1, 0, false⟩).move ⟨2, 1, true⟩⟩

private theorem mk_base_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 0 Dir.right)) :
    Matches M baseTable ∧ HistValid M [h1, h0] := by
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 0, false⟩ rfl
  refine ⟨hm0, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨by decide, hrun1⟩
  · exact ⟨by decide, rfl⟩

private theorem mk_step2_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 0 Dir.right))
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left)) :
    Matches M (baseTable.set 1 0 ⟨2, 1, true⟩) ∧ HistValid M [h2, h1, h0] := by
  obtain ⟨hm0, hv1⟩ := mk_base_hm_hv hFirst
  have hm1 : Matches M (baseTable.set 1 0 ⟨2, 1, true⟩) := matches_set hm0 hM10
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := (hv1 h1 (by simp)).2
  have hrun2 : M.multiStep (Machine.init []) 2 = some h2.c.view := by
    change M.multiStep (Machine.init []) (1 + 1) = some h2.c.view
    rw [Machine.multiStep_succ, hrun1, Option.bind_some]
    exact step_move hm1 h1.c ⟨2, 1, true⟩ rfl
  refine ⟨hm1, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact ⟨by decide, hrun2⟩
  · exact hv1 h1 (by simp)
  · exact hv1 h0 (by simp)

private theorem tv_b11_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580612001957984, 580577642219616, 580612001957984, 580612001957984, 88236951144544, 88236951144544, 
    1461596415838943819066141803272144828631953722786, 36833677312033, 580612001957984, 14272531372903084953836162937035596384640175522, 580646329190496, 169241061330642844097831491589819926591938434911455703199782504276684730634331902834566379442526164164, 
    2108619733444055736040516974455955545361557547850711074147200127984256281026626218759683525346268356, 169241061330642844097831491589819926591938434911455703199782504276684730634331902834566379442526164164, 16641875742412316784232257566029626371375643636297592541635400495133515354707770948498688220822967492, 580612001957984, 14272531372903084953836162937035596384640175522, 88236951144544, 
    565430503020769, 567627311485089, 564325454709793, 567627311485089, 1464361708243561616335624400007535491143191514530, 1461596415838943819066073970941727094316449942946, 
    565219046984032, 259775868603384269922685981980179434430755927206987759693095226922730014082603537482679015459246436, 283950497139040, 73117594685601, 73117594685601, 265783439004225734624146363603288008423510853539136781768284152145582552341306118535602767749997211332, 
    36834985903137, 73121889587361, 1461596415838943819066073971495707003184241741218, 1461596415838943819066073970942304680972955192738, 565219046984032, 37694253304160, 
    283950497139040, 37933188939809, 1461596426727979560536104801770292118789537959330, 268346440765117631283758124814127022345128734839012224742345670040950418581141374730956925012657793605, 73121889587361, 45761303733508096284159240621020199999413168547, 
    265783407324242938773040517788746352726518614462695014733373971528285669464926031930727151741236325220, 290547566905696, 308182880614109742061827413289012068044934707198677604865781843379179088472241007526973892669910724, 290547566905696, 45390834698592, 45639669130529, 
    564188116419617, 564188116419617, 564085171422241, 36834986165281, 563087531048993, 567489872531617, 
    567489872531617, 1461596415838943819066141803272144828631953722786, 480481077099545422682419265944113133141282504613097243343720657884441890750682224023574175446043707614527355213940466720739218457808234589192612970365518864775426831841803942599215845812486547254500257655332576193422060072385734248346733119530796474903314466107022760, 265783423164234690750004324612180051388730070258309611647188224306268488718040014684243390126677387300, 265783407324242938773040517788746352726518614462695014733376617563951175498281100102989468976508135460, 265783407324242938773040517788746352726518614462695014733376617563951175498281100102989468976508135460, 
    265783407324242938773040517788746352726518614462695014733376617563951175498281100102989468976508135460, 567489872531617]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580578715961440, 567485577560097, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 565219913107552, 565219913107552, 565219913107552, 565219913107552, 565219913107552, 
    580578715961440, 158467252027425, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 
    580613076158560, 580613076158560, 88238025345120, 72844862556256, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 72638704126048, 283744936659040, 72638704126048, 79510651799648, 
    88238024886368, 88238024886368, 88238024886368, 72844862556256, 730764756684369903962391543591264917804296569251, 730775907099504627398975418616329149663840306083, 
    72844862556256, 72844862556256, 72844862556256, 72844862556256, 72844862556256, 71748842689697, 
    142113359004705, 142113359004705, 282850713142305, 71748842689697, 142113359004705, 142113359004705, 
    282850713142305, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 143007448303712, 72638704126048, 72638704126048, 72638704126048, 
    74837727381600, 74837727381600, 72638704126048, 143007448303712, 72638704126048, 72638704126048, 
    72638704126048, 79235773892704, 79235773892704, 565220120988000, 72638911744352, 72638911744352, 
    283951302707552, 72638911744352, 72638911744352, 36834986165281, 36834986165281, 36833677312033, 
    36833677312033, 36834986165281, 1461551814348214975630118361056176158382355940642, 1461551814348214975630118361056176158382355940642, 1461551814348215056759756775662862287402244277538, 1461551814348214975630118361056180591621829068066, 
    354388768459104, 72913791748448, 354388768459104, 283951302707552, 354388768459104, 284020022184288, 
    81709884770656, 81709884770656, 79235981511008, 81709884770656, 290548372474208, 79235981511008, 
    81709884770656, 290548372474208, 81709884770656, 290548372474208, 81709884770656, 81709884770656, 
    81709884770656, 283951302707552]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580615223183456, 580615223183456, 580615223183456, 580615223183456, 88034014136416, 88034014136416, 
    88034014136416, 228908945639648, 88034014136416, 290550519957856, 290550519957856, 564325454480417, 
    564325823677473, 265783439004225734624146370479393073482713426520553944321377951062398286185558108421523209513670356676, 2125093301300450100468358697445578821046335593247926585678523813163758314649594863508015754252037828, 290550788131168, 732180864850979437470565335558054178544102704546, 265783439004225734624145923961796311422433966033303569026171190688902569886287075280948685287575972740, 
    281754426935648, 72847018428768, 495059621906912, 154211216525792, 290550519957856, 81643379886432, 
    564325689361441, 142113359004705, 142113359004705, 282850713142305, 72640851609696, 72640851609696, 
    72640851609696, 72640851609696, 213378339965024, 72640851609696, 72640851609696, 213584712305120, 
    145140367231072]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [88003949168736, 88038308907104, 88038308907104, 88038308907104, 88038308907104, 88003949168736, 
    88038308907104, 88038308907104, 88038308907104, 88038308907104, 36421461606433, 36421461606433, 
    39719996489761, 39719996489761, 1464356317830597444122860028369261287131264322978, 88244467337312, 88244467337312, 88244467337312, 
    37456481620129, 37525268205729, 37456481620129, 37456481620129, 44263971234081, 37456548728993, 
    88003949168736, 88038308907104, 88038308907104, 88038308907104, 88038308907104, 88003949168736, 
    88038308907104, 88038308907104, 88038308907104, 88038308907104, 88244668663904, 88244668663904, 
    88072636172384, 88072636139616, 88072636172384, 88038308874336, 2108619733444055736040626940042907433620073815289424947370696049047182806073723338637167832349217988, 88072636139616, 
    88072636172384, 2108619733444055736040517028019115064901420614545944225989845504011443736604979863938638915494417604, 141974577872929, 141974577872929, 72645146576992, 72920234199392, 
    86251682662880, 81716327221600, 72645146576992, 81716327221600, 79448844535904, 88038309103712, 
    88038309365856, 72920234199392, 81716327221600, 81716327221600, 81716327221600, 72645146576992, 
    86251682662880, 86251682662880, 81716327221600, 79517094250592, 79517303966048, 72851506333792, 
    1237089517601, 143426220198368, 143426421524960, 154215503104480, 141974577872929, 141974577872929, 
    142113359004705, 354395210910048, 72645146576992, 354395210910048, 72645146576992, 354395210910048, 
    72645146576992, 72851506333792, 16662150931854847291602735010499995435936558194535665299057769048228636246695806735369687908028849860, 71541342081185, 141978805735585, 71541342081185, 
    141974577872929, 61855273627806509114174205571252528999090903663295901043542356721576360289495786963711336457524271198336304842643368573436591862571044913229718840698853085673185103584405286, 16662150931431873879036211471346842833887687070030227342804624814545521634348174583160528272137985732, 16662150931431873879036211471346842833887687070030227342804624814545521634348174583160528272137985732, 156208168700384, 16658095893966341188868078299457483443111617403079724688143683607006492953514740834806443440633355972, 
    149542310250976, 185542899677648490886248036530871555253860853154, 16609688878692677949138540929357652285385570642293446444969101643764740444056179566847471860558267588, 16609688878692677949138338279066710463816504754277876983814299294819352053965739391078516227883074756, 143426220198368, 143426421524960, 
    147412283296224, 107825192243361, 16658412693801380727257013511749920061628984300903048823262674422955877650949962018622239028974264004, 154352950446560, 156620359731680, 149817188157920, 
    149817188157920, 154215503104480, 154215503104480, 146278537365984, 147412006472160, 154352614902240, 
    145282105346528, 141910086258849, 1237089517601, 284026265405792, 283751586728288, 284026265405792, 
    284026464635232, 283125355676705, 268378675140597766436307679246101858268862437160241843330867168230360159129676564603915547486458031812, 283125590787105, 282713139971105, 72645146576992, 
    354395210910048, 36838005837985, 36834985935905, 290555082901856, 290555082901856, 290555082901856, 
    72022377959585, 732180864861621090476662535260372308920214521250, 36833677312033, 36838005837985, 36833777975329, 36833677312033, 
    45694401242704623446606986885238876622701994403, 107206716493985, 107206716493985, 72022377959585, 353498629739681, 732180864850987225945563698742344412029872801186, 
    732180864850987225945563698742346100886175516066, 732180864850987225945563698742346100886175516066, 283125590787105, 283125355906081, 290554613598560, 73121890046113, 
    290554680707424, 290554680707424, 290554680707424, 730842809579771226543529861293919154549513817506, 283958013135200, 283958013135200, 
    365422798761882351792454754708936659053612401954, 365422798761882351792454754708941092284495594786, 283751586728288, 284026265405792, 283751586728288, 283751586728288, 
    283751586728288, 283957745158496, 283957610940768, 283957745158496, 284026265405792, 284026533841248, 
    284026464635232, 284026464635232, 283958013593952, 284026464635232, 45761303733511990506735441748270352777038799267, 37937483911329, 
    37937483911329, 37937483911329, 292822358428000, 292753636854112, 73121890046113, 290554680707424, 
    290554680707424, 290554814925152, 290554814925152, 290554680707424, 290554814925152, 290554814925152, 
    290554814925152, 290348656494944, 281758721902944, 732180859395918567746098956340897167716395812258, 290314564929888, 290555083098464, 
    290555082901856, 290555083098464, 290555083098464, 290555083098464, 290348656494944, 290348656494944, 
    290348656494944, 290554814925152, 290554680707424, 290554814925152, 290554814925152, 290554814925152, 
    290555083360608, 290555083360608, 283125590557729, 290829688185121, 282713139971105, 282713139971105, 
    730775907099504627398975418616329149663840306083, 282850713142305, 72645146576992, 72645146576992, 72851305007200, 72645146576992, 
    72645146576992, 72645146576992, 72851305007200, 72645146576992, 72851305007200, 283751586728288, 
    284026464635232]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [265750982861125756828414396982106008458777873180850958754718975889452488361516235511033550102486673444, 282033595359521, 1978884747337952134529170910556397484519752008648674045508824395945504120816365275663467456008695506022277275063175711830965955414864109386550046571580147178288400839330489126, 2040475814111039689397857420643758795689708851591337060684747891134538663367397210361611930915421217662980132632774311894968685133962083744452719974848688875556930929643479846, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511033550102486673444, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511033550102486673444, 
    290829721706785, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511031413695559329828, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511031413695559329828, 567494167306657, 571789033906465, 571789033906465, 
    571789033906465, 571789168222497, 571789168222497, 1461507212517379170121915390068049675977473671587, 571789033906465, 571789033906465, 
    576187147563425, 571789168222497, 571789168222497, 1464361707903954088321324674728018087323545649571, 71612211136736, 1464361707905283321387731334400740310732272320931, 
    71745350928480, 71745350928480, 1978884747337952134529170910556397484519729297711208179822545758877931602696980553007513116903549313454443773739118959241060389663820978553296044477546101226311940952676098854, 141976725358816, 44539083530529, 282033595359521, 
    265750982861125756828414396982106008458777873183757464598898590493719165215735818536021787106150017060, 265750982861125756828414396982106008458777873183757464598898590493719165215735818536021787106150017060, 290829453500705, 290829453500705, 1978884747222783456185379191100483388765130552673384691772630548306025393764125279657824255934840393847572399016206808781252703828965304693007359874129675595153885396933259046, 290829688381729, 
    2076195269844596962910139223763065850744109725584943466560754848046564765094632692049846078913455684, 1978884747222783456185379191100483388765130552673384691772630548306025393764125279657824255934840393847572399016206808781252703828965304693007359874129675595153885396933259046, 265750998701117921836539516306935753456928530646428830703484854628345961701913507803790040728961611716, 265750998701117921836539522317749557401096751331072458106674895727511920858083703382176648900609636292, 265750982861125933832504980636721537844497694058277556915268938197950403390073909998588467665065645893, 212349699492064, 
    36354820409440, 36354820409440, 141907936675936, 71612211136736, 36354820409440, 36354820409440, 
    14272520570942007187085344688278493201298375587, 71539192498272, 71539192498272, 141907936675936, 71745350928480, 71612276148448, 
    212349764503776, 141976725358816, 2040475813996767279036676692917856389751479123634140620313394207462623933389239616034597158977855431627120060865865699373362957442625243017725818490352169228563438871390433062, 212418486077664, 212349764503776, 71680997722336, 
    71612276148448, 5954006363464895581091524976614863824486294635390292553502705106580754364486906074020514240682148079373731314775599232741753208208171908724591985657057527929702542421900194096160097844098341856906511104504298741227068526423831555153404523694844511877068294606724672512504778764360099082687069569956887702426133730840504228613863724431209775981782374329130958849118356524448022796100264489976016100769843873615169863698180781274617919516757924158169571395007926814152413468234088656411534605099166754329156405557256499026611713309312720842793140545804855533783382737166435223716735061228855894898726060261441834502974683967819191200914741403997148906356516485821143463936684334635022299697497603523556661761768802735136231740647448744329034192309774253670009662399436422334247169375392047970501035338003898512602111675783942893460997978900473574992637280642235276327736441912129000880308601888437028530436935572446151730685048626996302881572728339336603825743225514502843503711273904430293940092473136844579230946244444607026782399057508790363173173572582691378236804168652456853535639037607748179632153609067172140165425042931100665243807951316882163674297841733428003052875185223052849753406639646137014429442831149247541, 141976725358816, 2040475813996767279036676692917856389751479123634140620313394207462623933389239616034597158977855431627120060865865699373362957442625243017725818490352169228563438871390433062, 290829554164001, 290829554164001, 
    11440325949328145383785318393828641928123000226, 290829554164001, 290829554164001, 36842535691553, 45638628975905, 480489325051325295666342253388956945115538779346589577666126262277530851069531532253996457279965911310956058043481948408454164119039791090533652941115611996734693721037541189401037413136867936007439963636124989518399427254476259569127239058774758052149084170248495560, 
    1932269682998647193295653558742663277806926810021254210167560034023342270890865364066740258923838535814834888621729035119342167469007031358925618020046478264131907613383718, 71822870055264, 71822870055264, 265750998701117870204043743557483350953351739257964208172433925645167675870571059310822500504287717412, 36842535691553, 291929233335585, 
    22858351047118790312341079409050203005825582498, 71539192498272, 71539192498272, 71539192498272, 71539192498272, 36842502137121, 
    290829688381729, 291929199781153, 290829688185121, 36842267255073, 75371410127349642867478165369235408653623609024435525404206700266401347092714145110882298537827160604074152155683263248183736007635644641036008567900048740483208979730420420934607882311016211835333328380004606369719921187854463817489634758730428064605128310625111347930492857156191142857782455107780201818890256393775507950212249874895031394387050484970965882623727816041214118205477869635480577703080652092046123965816013807479539390366636819572291569688128276903414480429876012763600164915902571291624346357351570972911383132377502296167872461877468847340500281524274374400992681148173197784605723234660192549050871180994599301575409251377586524079902111166474862178650825072459651727735537800596521752147339619582699256895806332931675421508502486696187559591264066501131189984132118936490843963428153323742741370722855846753329959870444613040727759084887776214681639838319166341030402768687771264882351149754992862034717066337123999404156909593608718080468060419504286144340733501549130574872921489347440498451186750451825759750784174578213138319061758075936953572476427092249342624016735415059291860951497813917373000390655994462656033163028872173913139570590266485220048923234216469473450489911820288693871751820107744105524, 71822870055264, 
    71822870055264, 36842267255073, 36842502137121, 290829688381729, 81922479172065, 81922479172065, 
    290829688381729, 290829688381729, 2077188920579703643766219717397407380534037619405772766119846853600807156347919310448346753804274739532972793270167807356565344765926315963108458556058264996729963426549332774, 45638595421473, 290829688381729, 81922479172065, 
    1978899843072482742350788208465535590217910939314355370475667720102535332362005618195296992077932086558921639287796887540371663167411549801826051800136853259443823218291355430, 318317512664353, 318317512631585, 318317512664353, 1984455115761929009283051194308495906516972684524245350247757179599294811383073020542579828672054957207950789811494342135243846093164170883655963609846590428464319887904324390, 1978899843072482742350788208465535590217910939314355370475667720102535332362005618195296992077932086558921639287796887540371663167411549801826051800136853259443823218291355430, 
    283133106988321, 1461529513347648292475291541652165976196921705379, 564092452512033, 564092519657889, 564092586828065, 11441676173819026464746650483538885233451484067, 
    282858229343521, 730775907099514687512514971062706216022359163811, 142120875205921, 282858229343521, 282858229343521, 282858229343521, 
    3887181297622863362303984241384831197859476471368066140163586366524902017664164223400343048011083749639867543292348567406640941256640845152432416208779169913885693521674022, 36842535691553, 36842267255073, 318317512664353, 318317512402209, 36842267255073, 
    318317512664353, 318317512631585, 72603738867808, 72603738867808, 1461529513347648292475291541652165976196921705379, 22925601965970581122164799689713642900864636834, 
    72608038127840, 564092452512033, 566291542913505, 568490633339297, 72643070396640, 213380558751968, 
    72710042945760, 143078384470240, 143078384470240, 143078384470240, 72709573183712, 143078384470240, 
    143078384470240, 143078384470240, 143078384470240, 72844862556256, 72844862556256, 72844862556256, 
    72844862556256, 72638704126048, 72638704126048, 143078384470240, 143078384470240, 39653355292768, 
    39653355292768, 39653355292768, 39653355292768, 145273515149536, 145273246976224, 215579582007520, 
    215579582007520, 145273515411680, 145273515411680, 245307557627514211885146954933307963719983428943077129254285080044323386236951623068924337352457697551555202762598915823893504245810671907182332864868650879741305561244454, 245307557627514211885146954933307963719983428943077129254357227272465918562322785986269631378934996658780976258891696896970799969435842193203298791205505505004154200744742, 44126632943905, 
    79519451449696, 79244363827296, 9080097802336, 9080097736800, 137871290263649813197002402691657551399067633803624007420983356540881497662689549597464117243094596, 249081520045470955577462486712308026749408244218304520642429108172418059973170201220093216616669303935224035100003489731365624775961105447967414253862496707105767713332390, 
    249081520045470955577462486712308026749408244217309466790989295251409800512571787933964589124414276237623633524220571212090531787052159883964607282475684001840738167872678, 11596431741283241455626853187251969298263986595, 11774837702871486440759138933433437666362282403, 290829688152353, 290829688250657, 290829688381729, 
    79450522257504, 79244363827296, 79450522257504, 79519241734240, 79519174625376, 79317449574880, 
    290314292568353, 79386169051616, 79248730098144, 79661055347168, 79317449574880, 79661055347168, 
    290829688643873, 290829688643873, 9079628499040, 9079561390176, 2092399566058740735068295192402456358315855740965094978183680438452173285870948034354084194010993764, 79244363827296, 
    79519241734240, 79519451449696, 79519241734240, 79244363827296, 79450522257504, 9079829825632, 
    9079561390176, 9079829825632, 24266090926142509238219088944453964782698497442, 325534942234976, 9080097998944, 44059957135456, 
    44059957135456, 9079829825632, 44059957135456, 9080098261088]) (b := []) (by decide) ?_
  decide +kernel


private theorem solve_canon {M : Machine4} (hG : GoodMachine M)
    (hFirst : M 0 0 = some (some 1, Stmt.write 0 Dir.right))
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left))
    {r : Fin 4} {d : Dir} (hM20 : M 2 0 = some (some r, Stmt.write 0 d)) : False := by
  obtain ⟨hm1, hv⟩ := mk_step2_hm_hv hFirst hM10
  let m : Move := ⟨r, 0, match d with | .left => true | .right => false⟩
  have hm_cmd : M 2 0 = m.command := by cases d <;> simpa [m, Move.command] using hM20
  have hm2 : Matches M ((baseTable.set 1 0 ⟨2, 1, true⟩).set 2 0 m) := matches_set hm1 hm_cmd
  fin_cases r <;> cases d
  · exact tv_b11_1 M hG hm2 rfl hv (by simp)
  · exact tv_b11_0 M hG hm2 rfl hv (by simp)
  · exact tv_b11_5 M hG hm2 rfl hv (by simp)
  · exact tv_b11_4 M hG hm2 rfl hv (by simp)
  · exact tv_b11_9 M hG hm2 rfl hv (by simp)
  · exact tv_b11_8 M hG hm2 rfl hv (by simp)
  · exact tv_b11_13 M hG hm2 rfl hv (by simp)
  · exact tv_b11_12 M hG hm2 rfl hv (by simp)

theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H2 := by
  intro M hFirst ⟨q, hq23, hM10, r, d, hMq0⟩ hRun _hUsed hForm hMissing hLoop hHalts
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts⟩
  rcases hq23 with rfl | rfl
  · exact solve_canon hG hFirst hM10 hMq0
  · have hG' := goodMachine_reindex23 hG
    have hFirst' : reindex23 M 0 0 = some (some 1, Stmt.write 0 Dir.right) := by
      simp [reindex23, swap23_0, hFirst, swap23_1]
    have hM10' : reindex23 M 1 0 = some (some 2, Stmt.write 1 Dir.left) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    have hM20' : reindex23 M 2 0 = some (some (swap23 r), Stmt.write 0 d) := by
      have hswap2 : swap23 2 = 3 := by decide
      simp [reindex23, hswap2, hMq0]
    exact solve_canon hG' hFirst' hM10' hM20'

end OMA.BB4H1

-- Step BusyBeaver.BB_4.R2.H1.R1.H4.R1.H2
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H2 := OMA.BB4H1.step_proof
