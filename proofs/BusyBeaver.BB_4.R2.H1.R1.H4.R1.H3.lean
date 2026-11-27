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

private theorem tv_b11_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580612001957984, 580577642219616, 580612001957984, 580680725629152, 580612001957984, 88236951144544, 
    88236951144544, 1464356230722953767981429428604622335286845115810, 88236951144544, 551485161054599252787988895017918044733462245858815589912980910746174105318112906017684354607936516, 16641875742412316784231367965586808976709091425926981789136221745565389600382828527746122385388270596, 53052580104288, 
    88236951144544, 88236951144544, 158605699516640, 268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 291962732323023105016161381018474482305508768725846788929609031616708031115628198849315309206434820, 2108619733444055736040073891616489864368968325111015578584936645033550915604687535029340383113180164, 
    268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 580680790706400, 581093107467297, 580612073392352, 580680790706400, 48526606668269102587545057650434698277275838370, 
    268897676423098020835752910817277330914779316246829700504291708656512897315263140810134224468999682629, 94198707059431611313507970450807273965348206498, 185542907841756770742224858991028576161439950754, 8337157961126915040399697926093429867676917339950111405565199488100261075607936967580425491974212708, 36834751054881, 36834751054881, 
    731110419564175286665820176719609388776009803682, 564600567268385, 1461596415840937830925850615735519189187623921570, 36834985935905, 1070530010783380518061108374468429168074762601874704643645948715347802131957314092800724998615485540, 2108619710240942818105729504726730330420949364844807885078727694022144476941968104298302564686966084, 
    7507745940037755093449473433490120066569316925435963047549644266088334985627070674018392591318553281965412518238046823966505954660635160975758646078666864166795874663849014460459941522784628373444363207791253599120778328821482730227738950138433887862259978249938760, 94198707059431611313585341998410515416177194914, 30931396034738014376190465486022130231392233066662287727986142085845502645105290083969916831113652393928535040318878703072571130762908244190892245462824040894441730991793958, 185542907841756770742302230538631817612268939170, 185542907841756770742302230538631817612268939170, 185542907841756770742302230538631817612268939170, 
    83827770757906992197027132560565223727344151818176841190108093235568687796968320851787392748709577092, 36834751054881, 36834751054881, 36834751054881, 731110419564175286665897548267212630226838792098, 564188250407969, 
    564085171192865, 564085171192865, 564085171192865, 142388102202401, 36834985935905, 1461551824907269542626679691847602394153183872418, 
    580646329190496, 580612001957984, 580749512214752, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 25690556470693892142321573237587390457493065122, 
    185542907839929074642041993834789134438127636386, 7560670634477546039554829970952216529291147244499708391564956530749636980267856197212295711345661052441883610296435374791084934987324536281450616384569574533844712175087069066643469565471625823492928040373201925559843339817232355508944610847034492059674247998760, 2108619710240942818105621310079871561278143002039008692250637211138592345828763223419839621856570692, 61847696221575429410295888569120643854407946574120795219496089964728619452921077268574564204384700432377775789552897002435665529646469769162777131212681466899557500409846822, 14272531372903247213731962170041678100100025762, 94198707057437761713859239642861664601851301282, 
    580646329190496, 580612001957984, 580749512214752, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 25690556470693892142321573237587390457493065122, 
    185542907839929074642041993834789134438127636386, 1978658307756457001175676491339305053670083847336631991890751242200445304622619723136463140379294878323507745156405545394747867640609410686176502672026272454447458402431489831, 2108619710240942818105621310079871561278143002039008692250637211138592345828763223419839621856570692, 61847696221575429410295888569120643854407946574120795219496089964728619452921077268574564204384700432377775789552897002435665529646469769162777131212681466899557500409846822, 14272531372903247213731962170041678100100025762, 94198707057437761713859239642861664601851301282, 
    123421290727520, 88236951144544, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351526178370926382825721534092318953103670718174424119329185788576830694338878844557781286032910710689422553902452623873990057666526701974999530886347673382191768792548486618074901339582464486231871538912960222515656341996994752960799037203108568009715665921153204216701908497077194728422621327257706615989181783185410547749396684621433172105626132111176179217887604293375585249575061890587333070652089718419241680632333119825792068387873447150074385988539986849667476727416845296400413797898030, 3879633372745541415433854513852050427088000117636720104180501520882363705875575086950881571382111014117885115789965009470225529863325236900046457883608445097515589106114343, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 
    268897676423098020835754222784629449697508914397199707173454007144514416875423302826728710623033634116, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 268897676423098020835754222784629449697508914397199707173454007144514416875423302826728710623033634116, 580577642219616, 580612001957984, 
    88236951144544, 291962732323023090610657254772178293171664489403645248142160383110305540511948644479431920431738180, 8563518833978308804298379707902786119182461347, 269416721272826801985775785432765670043568572725798129600296712030446645944750525532875624888011926852, 580612001957984, 580612001957984, 
    1461864025142214023833124976117491504732488864163, 1464406309568469972113685397546951697302909617570, 1464361708078072910867402326110406400579897656738, 1461529513368741919844010188983178934685372791203, 1461551825077410726087148923579325797035099555234, 268897676423098020835752910830301249840124854773556135300744547796085902187742673734700779388487559749, 
    290829688185121, 290829688185121, 290829688185121, 294849918909537079143611153333285870490155820079071965399734158208058396504680399731268051561222203973, 2108619710240942818105842851499629993332460792546121325184346295138245333466923179694351232165555524, 568487512773793, 
    1461551814188374984617118092751338359201336919458, 1461551825077410726087148923579325797017919686050, 580612001957984, 580612001957984, 1464356230722953767981497128708739072386530805154, 568487512773793, 
    88237152471136, 88237152471136, 158605898811616, 265751980780613625436517173604054780705892322982543114378925411945865652551958083734664420928430172261, 265751980780613625436517173604054780705892322982543114378925412571682808317443788163698077847886391397, 368229994557999773226442495693887441112220059042, 
    274055744047704776410971997714469678247690206935746917202959971698474688800576362478529295353633777573, 265751026452044276166602415778491193089281909885187164068933757170738837318497420092549764309637605285, 8304780986568768591145375763158153178624701317834816914121106810927441374050098545772864071651239845, 2855889187304084711713420837306850823379633570, 368231298520029814262634629016377605737362769314, 368231298520029814262634629016377605737362769314, 
    565253276699104, 565219046984032, 241563079273537770287932958213530655028630354742917182953448563258685873933604237710258905173768425625088709446213866076548443345365114992217434444926813439562102869045030, 283950497139040, 368231301242288749630142336723374465191508460962, 368231301242288749630142336723374465191508460962, 
    368231301242288749630142336723374465191508460962, 368231301242288749630142336723374465191508460962, 368231301247605681895691603866660117379881125282, 5798215880631800410887509447884956026183788963, 182777604896386634544130681761837398258129873315, 366090429719180606605203162546239534537992848802, 
    290547566905696, 290547566905696, 36843609662753, 45639702684961, 37943121292769, 45639702684961, 
    125665047919343617216252820948522021537792395170, 242005340505767904011487671634643433504737492155277540854817659156418760284083539250883594019534248943194269591323450128441857752838164609771224652997163691932660042562599, 217009248701668776644989052375788530758570215330, 34610801486660014261534719139200947406573667746, 45639702684961, 234839012131501401984529677125161640868286971066506092906173614941987112300637658334319072332966851951856592571976177619657059476285360865382242941748921385367480977640730283563607510772615291597911566352553207775176758638527158372739003740724802313256962123098760, 
    283133106988321, 283132972769569, 290829554164001, 22925253537925832852677935695346407836603647394, 145274589710560, 286431507653025, 
    145274589710560, 36833912161313, 283132972769569, 265751026428841163594421611852727993497435433042382902114557289600231982615179209489328552577548176485, 8304780963365655673211246048196591111122040374848601116406117348572512697936314897029611674013813861, 45716702072969851720940281905737890841555380643, 
    1461596415838943981325969770728713084899701591458, 1461596415838943981325969770175310762688415042978, 565219046984032, 37694253304160, 143350451931616, 283950497139040, 
    37934262682657, 37934262682657, 37934262682657, 1461596426727979722796000601003298200504997809570, 268865485614847297792796352618851042197989992187417771103196579790859561048805964678854012970336342373, 45761303733508096427692585073970491280451447203, 
    1461551824907269542626679691848757567449014502818, 37694253304160, 144449963559392, 283950497139040, 45390834698592, 154345568209376, 
    290547566905696, 45390834698592, 154345568209376, 290547566905696, 318318418601249, 1070533963046947539657058221526342712726549979971262112255902338339607315857488093891029168167079012, 
    14272531374897096891332229679021916181357659043, 4184803061419635131295651447518274647129661373965263450336255496782421733566623013410378740736740452, 480730579174438581968289717475574934246283507193188650921838329547458500783809725172236344242044307581129060692063852570225903715140935782121298180541471278171308631651145319229195394362812112943829387097248372370167317197779482519332162032111174243005235202123098760, 8337161859249885253480418372252480585866386038977688922054852126185349722143133516704324194581630052, 45639669130529, 17729763672097, 
    318318586373409, 318318586373409, 158471546998945, 155307641014752, 3354202804493645814748870298199752719705254241588016358342634337923820016949415689613989862007182004054652638919985186226517921330431788446400121691678523596789852730623100325340585383832176406099910314106850710421447909948480166577943632920701216204163062820829662668955604314465325617829930536024367105732699202548987036064846141556154960963356693042176603859279278253577273898, 158405042116833, 
    158405042116833, 158471546998945, 158405042116833, 158471546998945, 158471546998945, 282033461141793, 
    45716702072969851720940281905740001911933774243, 730842809590311953894439635834997302461081357730, 45761303733508096427692585221546555215384160675, 45761303733508096427692585073972602350829840803, 730753606439376647941404261230219405299173328290, 290307048737120, 
    290547566905696, 283132972769569, 290829554164001, 145274588760288, 286431507653025, 145274588760288]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580613075765344, 88238024951904, 14272531382872495289618653550577857764354425763, 3879633488283271308237127022445478069148563303144059817457111187435128332419296479853459130020922157195460269839746976012994841792372220327809646156328562092116858722998054, 565219913107552, 567419005569248, 
    88031866652768, 158400680036576, 580578715961440, 567489872531617, 580613075699808, 580613075699808, 
    565219913107552, 565219913107552, 565219913107552, 565219913107552, 580578715961440, 158471546998945, 
    580613075699808, 580613075699808, 580613075699808, 88031866652768, 88031866652768, 88031866652768, 
    88031866652768, 88031866652768, 580613076158560, 88238025345120, 72844862556256, 37454332037216, 
    72638704126048, 74837727381600, 74837727381600, 79510651799648, 283744936659040, 71539192498272, 
    74837727381600, 282858229343521, 72638704126048, 72638704126048, 74837727381600, 72638704126048, 
    88238024886368, 88238024886368, 730764756684390510969158046183037295667714228643, 730775907099525072145846121975095445811797984163, 72844862556256, 72844862556256, 
    72844862556256, 72844862556256, 291962732323023090610653820755226275218338619010369664010978989490203098856654128942559288312802628, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 8563518833978308640271324502589899695048501667, 
    291962732323023105016161381752216401732287115977390200477850003430571063239184130926755080711762948, 2108619733444055736040073892350231783795746672362558990133177616847413947728243467106780154618508292, 1978658307750130403652078844387023550925337189955691787029207652894257074690548685097681052620524591009714317233839875294203864895868392266665764371597575545326035966550955814, 2108619733444055736040073892350231783795746672362558990133177616847414474162253017692717846372873220, 1984455114034234518000883447562533043956712728316072082953094598375293920300786394631407365641680283939554883781690996261135909942638124884223925211815345933074805822923447334, 143007448303712, 
    72638704126048, 268897676423098020835753791724149516861767552324333036874781215910617558970699990928363931610965421380, 282858229343521, 282858229343521, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 565361783347425, 88173736892641, 580613145364704, 424688661039584, 
    564332970909985, 564335252416993, 564332970909985, 564332970909985, 567631606718881, 149879465183456, 
    217911749249248, 158606838270176, 424688661039584, 567631606260129, 220110772504800, 72844862556256, 
    72844862556256, 154209069042144, 290548372474208, 580750586087648, 228906865264864, 14272531377555562984456514080591337358092403619, 
    14272531377555562984456514080591337358092403619, 141908005882080, 145206540765408, 141908005882080, 142120606769441, 141908005882080, 
    142120606769441, 145206540765408, 145206540765408, 145206540765408, 149879465183456, 149879465183456, 
    212414191110368, 215712725993696, 213513702738144, 215712725993696, 213444981164256, 213444981164256, 
    37458763323617, 70439888488800, 70439888488800, 281752279452000, 281752279452000, 37525268205729, 
    37525268205729, 281752279452000, 281752279452000, 281752279452000, 565220120988000, 72638911744352, 
    283951302707552, 11440328570565367743033308425719527867049853859, 72913791748448, 284020022184288, 284020022184288, 72638911744352, 
    37525268205729, 290548372474208, 145206679177696, 290548372474208, 290548372474208, 39724291461281, 
    290548372474208, 290548372474208, 290548372474208, 286150325963232, 145206679177696, 79235981511008, 
    366090429719181580164345843301466300491149886882, 7136265707388342634524319919982323222617139619, 366090429719181580164345843301466300491149886882, 366090429719181580164345843301467426395351696802, 81709884770656, 81435004766560, 
    290548372474208, 290548372474208, 22858351047119439351919440637755609306152568226, 22858351047119439351919440637755609306152568226, 71539192498272, 185542907839182355235406472487471489145278827938, 
    185542907839763894701950923581263853753754717602, 15473245943568763756317697198856288555756411648462535514092352657905584472081764052843226046144860436390577905821329231195889201160587423491565172070603099765569535661987622, 141907936675936, 141907936675936, 185542907839763894701950923581268216632536731042, 283744936659040, 
    286081537280224, 11429175534194233246646589481466198968246994338, 11440325949328794423334665273524349077971010978, 22858351047119439351919440637755609306152568226, 22858351047119439351919440637755609306152568226, 22858351047119439351919440637755609323064001954, 
    1461596420943180458699566872517709444016308260258, 24263303354074147614771733514997364886413542818, 732180859417094133187327619702831531053103482274, 354388768459104, 72913791748448, 283951302707552, 
    81709884770656, 74837935000032, 75112815004128, 81709884770656, 81709884770656, 290548372474208, 
    75112815004128, 145550280755680, 286150325963232, 75112815004128, 79235981511008, 81709884770656, 
    154346373777888, 290548372474208, 81709884770656, 156614118607328, 14272531372904220773106757568078168392859127202, 14272531372904220773106757568078168392859127202, 
    25698832137525425619092898954269284462387275171, 74837727381600, 217843027675360, 497256766114272, 730753611724388173306269333733382035916720735650, 283951302707552, 
    286356692011488, 290548372474208, 286150325963232, 290342214044000, 290548372474208, 11429175534194233246644171620585583274533324706, 
    11440325949328794423332247412643733384257341346, 22858351047119439351924276341070096619870356898, 74837727381600]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [564085171192865, 145140366706784, 580615223183456, 564085171192865, 580615223314528, 5887419191224840058862115485528911268961866147, 
    365555209771630155308815894093576160389393043875, 183045214848961549958066283142791848103441335714, 88034014136416, 228908945639648, 88034014136416, 365555209771640539902532963748834347286261715363, 
    145139830360160, 145208619042912, 217776386476128, 145208619042912, 580649550415968, 268897676423098020835752910830301249840124854727006583246943173723451120789069063540535865114826336837, 
    71541339981920, 71541339981920, 145139964577888, 145139964577888, 145139964577888, 79513076107616, 
    281754426935648, 145139830360160, 281754426935648, 290550519957856, 290550788131168, 290550788131168, 
    290550788131168, 53052547564577, 1983307829457088769429797309470913580882050960887440899865002156957561731920466005503410358557293810274860453993952538476905323485159347189985463333480849107182478756448042022, 71541339981920, 71816427604320, 79512807672160, 
    79513008998752, 11429175513262706688850182165612667843293742498, 11440325928397267865538257957670817953017759138, 72572130035808, 732180864850982033628898123286151485985017857442, 145415123503584, 
    281754426935648, 281754426935648, 72847018428768, 495059621906912, 290550519957856, 86041560615392, 
    290550654175584, 45394055924064, 291962732323023105016161387622151757146513893989737492863777777941475320227631587546273252754387972, 2108619733444055736040073898220167139209973450374906282519105391358318204716690923726298326661133316, 1978658307750130403652078844387023550925337189956326400759394049072504593922926367543609712806304396321153991484115303066920890831045568538989774845941721600485865004005414694, 2108619733444055736040073898220167139209973450374906282519105391358318731150700474312236018415498244, 
    1978658307750130403652075570996415654783467132403914467227204079175831604568797629269248410659442788918925818380082052272657990333466825259038119381228906008515376028678969126, 81712032254304, 177301095713248, 177301095713248, 213378339965024, 213584712305120, 
    282858095124769, 282858229343521, 145140367231072, 145140367231072, 281754426935648, 290550519957856, 
    290550385740128, 36323076376672, 36323076376672, 282858229343521, 72640851609696, 72640851609696]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 36834851718177, 36834985935905, 9080097802336, 9080097802336, 
    732180864850997610578894849654733641819303216546, 5753614230702594312420318140803585265730857379, 283958013200736, 5798215891240839019172621309036185704626923939, 281758989945184, 290555082967392, 
    45639702684961, 45639702684961, 22925253537946277599546221193286166653685990818]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88038308907104, 88003949168736, 88038308907104, 88038308907104, 88244467337312, 2108619733444055736040073945179649982523787674473684621606527587445552260624270576682443703002133508, 
    36834851718177, 36834985935905, 88038308907104, 88038308907104, 88038308907104, 1432828334178097069929407614776357822635967906, 
    2108619733444055736040073945179649982523787674473684621606527587445552787058280127268381394756498436, 88038309103712, 36842368147745, 45639669130529, 45639534912801]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 88038308907104, 88038309103712, 9079628499040, 22858351036505046087704026701463228968681382819, 
    72645146576992, 495270008195552, 290554680707424, 281758587685216, 290554680707424, 354395210910048, 
    81924626655713, 81924626655713, 1984440489929837483293235241291086758375741837860202614833627185401425533326208190765865034442555685500416473033491816736567212240531016896023039557550153891441492212176648998]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 294849918909537079143611153333285870490155819706675548969323165626980068907155268111914444870606875205, 88038308907104, 88072636139616, 88038308907104, 2108619710240942818105126759540034372597267683280560935644183952026953949156605679393023547884514628, 
    2108619710240942818105621363643031080818009042086879280656051476713042161879809224100738728112237892, 3879633372942368893933662488472374990280982834119452482988331851785776201820863331890703335598394804820014736778666464327288578917016497952935506509888895225151265786820902, 2078206925601301951481966219823460129171699391076949008810496939888034363125669094049311381916822852, 2092399558263944989199394209130074898575743497171668906384750099236691785738398286330559558238416196, 88003949168736, 88038308907104, 
    88003915614304, 88038308907104, 88244668663904, 75256901929440, 79517371074912, 81716327221600, 
    72920234199392, 81716327221600, 81716327221600, 81716327221600, 71545634949216, 47099348434805540314425534894308233901624528290, 
    86251682662880, 72645146576992, 75188249561568, 79448844535904, 86251682662880, 81716327221600, 
    88072636172384, 88072636106848, 88072636172384, 88038308874336, 88038308907104, 981230230566952290560025527830757515871604043744272048388963252183562419046457259960424288245957115758348763288178619919250999435054589855218693365722972545842048571954982, 
    88072636106848, 88072636139616, 48526606665797166247944886385720693071601471394, 88072636106848, 88038308972640, 88038309103712, 
    88038309365856, 2108619710240942818105126759540034372597267683280560935644183952026963500173636937647310110550207812, 81716327221600, 81716327221600, 81716327221600, 2108619710240942818105621363643031080818009042086879280656051476713051712896840482355025290777931076, 
    71545634949216, 72645146576992, 72782656834016, 72920234199392, 81716327221600, 75119047739488, 
    75119047739488, 79517094250592, 72851506333792]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [123257008228448, 123257008228448, 123257008228448, 123428806920288, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351717142984214254662347383686083590644867514403640469517019407014118370049617879117055983964809807886972864025622581570419213603682712442395599112349605641516208329741783448167392099499040473080079728415519920417388674947597616311532368730176083550323265613926877108787448443396460552997483026703540052458472036787201631336472754167448202837960499327191419378093946161178641950460701706036238144440645692730114056418587382450856814804232882843262651519955831306953229231819553510355256549562158, 88003949168736, 
    88038308907104, 88038308907104, 88003949168736, 88038308907104, 88038308907104, 88038309103712, 
    497400244865504, 79448374773856, 88038309365856, 88244467796064, 72645146576992, 72645146576992, 
    215581796600288, 9079829825632, 266140254622296127312129299213221869627250625909798475537396539540831788541009512089385598645109364772, 81924626655713, 81924626655713, 74844169832544]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [182699551980117837340611440749834229193342723491, 182699551982448538466540463099196666210047500707, 182699551980117837340611440749838662424225916323, 145419543841248, 182699551980117837343087320828405060112153585059, 182699551982448538469016343177767497128858362275, 
    154353084533216, 91522607424831215789295322887996872250614125986, 154078197975520, 145419544037856, 182710702395252398517299516541892379303066740131, 182710702395252398519775396620463210221877601699, 
    182710702397583099645704418969825647238582378915, 91522617634299148217239147694625392063429514658, 91522607445766636584605418961174153757219919266, 91522607445766636584605418961174153757219919266, 91522608126331370426501688774824178982389847458, 91522607445766636584895561157881664759149401506, 
    182733003225355042218518944632370882091092812707, 149817322375648, 149679883422176, 154352614902240, 149817456593376, 149679749204448, 
    149679749204448, 61857131127637483263755009076775401996465851725186789839515489699136229627862977748692393910118788487737424678568120878452245891749452156503334872552486461830498486422847270, 143426220198368, 143426622851552, 143426220198368, 143426622851552, 
    143289114692064, 143426622851552, 182777604885893286925271247800603482529988879267, 154352950446560, 156620359731680, 154352950446560, 
    145281702693344, 145281702693344, 145281971128800, 5280026789543376283667659932019425984407506103603905942303596721776440011921292092560552725314331830863924708895930913205534653805505777613732711935507532796483233667006948613984246313940111459652418517429078326951635450021502118448224767438226572386570312668674072008052527024990600323271998482772785352385089021010705782297417669946364477942006233696035070558451760202054246699, 147412283296224, 147412283296224, 
    145281836911072, 154352950446560, 145281836911072, 145281836911072, 154352950446560, 154215503104480, 
    182866808206969776337537914097783303132881888163, 182866808207136254990932577630710914086997599651, 183045214849122755164547126770713704888466154403, 183045214849122755164619662596591743744591799203, 183045214849289233817941790303641315842581865891, 145419544300000]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [25696044544229575384828505936284314909561849250, 25696044544229575384828496491551278801527244194, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269518246845658697122, 290417514383840, 
    435553049250272, 36567889741920, 72851506333792]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [16644916896595362606194719733137530198452223968205265722021357604898191729631200863325446124574727780, 154353084533216, 8340199424715012154549699770557994538954024863845222243612596443653748321047420327311608465526948260, 149679749204448, 149817456593376, 149817456593376, 
    149817188157920, 149817322375648, 16609688693064942194413866485572845602054608574280450093608263118845854563723652457336820354294891844, 143220118391264, 143288980474336, 145281702693344, 
    154352950446560, 154215503104480, 149817188157920, 141021095135712, 141021095135712, 145419141646816, 
    154353084533216, 154215234669024]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 88038308907104, 88038309103712, 88038309103712, 9080097867872, 
    9079695607904, 9080098261088, 9080098261088, 149679749204448, 145281702693344, 36361228257376, 
    36361228257376, 36361228257376, 61832602211931006545952620795707570920629961556582665318838464320757278005018180782647807751939661129647415584881517083439809957099473292603705926824644700917782604733726503, 36327371343968, 36327371343968, 182710702405574075087992431570052414887610581923, 
    72645146576992, 72645146576992, 72645146576992, 143082679437792]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [368231298514733347026056182693119085570651866530, 368231298520050259009195846184734313811773244834, 36834985935905, 11440325949328794423484043742211855044299467171, 11440325949332688660983225334358238429414695331, 36833912161313, 
    368231298514816403810605272530975465712095085986, 368231298520050259009505332375142916719127315874, 989336701756513946551633305859901898115939610101432257544833080886329657572483162615939414065826290204338389686058779831571048314798289717672398024251824231730676669569019686, 281552563472736, 281552563472736, 8304780986568768591145375763158153178624701317834816914121106810927450699452556803786760229645133733, 
    290554680707424, 368231298520050259009505332375147279597909329314, 284026334611936, 283751586728288, 284026464635232, 284026464635232, 
    281758989879648, 91522433200238746533710073470342660892449184035, 281758721902944, 281758587685216, 281758453467488, 281758721902944, 
    281758721902944, 281758453467488, 281758721902944, 281758990338400]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72645146576992]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [36834751054881, 36834784613537, 36834851718177, 36834985935905, 72020230478049, 290555082901856, 
    290555082901856, 72020230478049, 290555083098464, 36834751054881, 36834784613537, 36834851718177, 
    36834751054881, 72020230478049, 45694401242700729209107805293092915451662444963, 72020230478049, 732180864850997610578894849654733641819303216546, 732180864850997610578894849654735330675605931426, 
    283133106988321, 283133140542753, 732180854653160467481549638968011160332096013730, 732180855333725201323445908781661185557265941922, 108305154378977, 290554613598560, 
    73119742564577, 281758721902944, 281758721902944, 281758721902944, 281758721902944, 730842809579781611176861012206308384338944232866, 
    283958013135200, 283751586728288, 284026265405792, 283751586728288, 283751586728288, 283751586728288, 
    283957745158496, 283957610940768, 283957745158496, 283958013593952, 284026464635232, 45761303733508096269236260193017880028296260003, 
    37934262682657, 292822358428000, 292753636854112, 73119742564577, 290554680707424, 290554680707424, 
    290554680707424, 290554814925152, 290554814925152, 290554814925152, 281758989879648, 281483843996000, 
    290348656494944, 281758721902944, 281758587685216, 281758721902944, 281758721902944, 281758990338400, 
    732180859395928952379430107253286397505826227618, 290314564929888, 290555082901856, 290555083098464, 132932252556490215032027325598086552396264520638511020757157739547965310120690464655434109864344677700, 290348656494944, 
    290348656494944, 290554814925152, 290348656494944, 290554814925152, 290554680707424, 290554814925152, 
    290555083360608]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [11429175534213704434447147910865753620647249826, 1038097623321096073894050850658663711185768498961356785832629030709583160251095483018018375990351908, 177064863992288, 11440325949348265611135223702923903730371266466, 291930273522977, 290829554164001, 
    290829688381729, 290829688381729, 290829688185121, 290829688185121, 102784483166724243191840649282227841814600652706, 141983570069984, 
    36567889512544, 177064863992288, 141983570069984, 423595994122720, 141983570069984, 283132872106273, 
    283133106988321, 730775907091549633261815119149685599387806368675, 730775907099525072225074284489359783405341934499, 730775907099525031660255077186018935510839362467, 283132972769569, 290829688381729, 
    290829688381729, 72713870248416, 72645146576992, 72645146576992, 72851305007200, 72645146576992, 
    143082679437792, 290829554426145, 213382706235872, 143082679437792, 11507206662084149730893739539316263617015842722, 11507228440155632670956610125722439897783469986, 
    11507228440155632670956610116499067860928694178, 72645146576992, 72851305007200, 72645146576992, 72851305007200, 732180853993946377667833355031080832218314080675, 
    283751586728288, 283957745158496, 39625906227296, 39625906227296, 22880651856306457963897681911005703819691034018, 39625906227296, 
    39625906227296, 11774838382283606478691962704686952809786509218, 74844169832544]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_14_0
  · exact tv_b11_14_1
  · exact tv_b11_14_2
  · exact tv_b11_14_3
  · exact tv_b11_14_4
  · exact tv_b11_14_5
  · exact tv_b11_14_6
  · exact tv_b11_14_7
  · exact tv_b11_14_8
  · exact tv_b11_14_9
  · exact tv_b11_14_10
  · exact tv_b11_14_11
  · exact tv_b11_14_12
  · exact tv_b11_14_13
  · exact tv_b11_14_14
  · exact tv_b11_14_15


private theorem solve_canon {M : Machine4} (hG : GoodMachine M)
    (hFirst : M 0 0 = some (some 1, Stmt.write 0 Dir.right))
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left))
    {r : Fin 4} (hM20 : M 2 0 = some (some r, Stmt.write 1 Dir.right)) : False := by
  obtain ⟨hm1, hv⟩ := mk_step2_hm_hv hFirst hM10
  have hm2 : Matches M ((baseTable.set 1 0 ⟨2, 1, true⟩).set 2 0 ⟨r, 1, false⟩) := matches_set hm1 hM20
  fin_cases r
  · exact tv_b11_2 M hG hm2 rfl hv (by simp)
  · exact tv_b11_6 M hG hm2 rfl hv (by simp)
  · exact tv_b11_10 M hG hm2 rfl hv (by simp)
  · exact tv_b11_14 M hG hm2 rfl hv (by simp)

theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H3 := by
  intro M hFirst ⟨q, hq23, hM10, r, hMq0⟩ hRun _hUsed hForm hMissing hLoop hHalts
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts⟩
  rcases hq23 with rfl | rfl
  · exact solve_canon hG hFirst hM10 hMq0
  · have hG' := goodMachine_reindex23 hG
    have hFirst' : reindex23 M 0 0 = some (some 1, Stmt.write 0 Dir.right) := by
      simp [reindex23, swap23_0, hFirst, swap23_1]
    have hM10' : reindex23 M 1 0 = some (some 2, Stmt.write 1 Dir.left) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    have hM20' : reindex23 M 2 0 = some (some (swap23 r), Stmt.write 1 Dir.right) := by
      have hswap2 : swap23 2 = 3 := by decide
      simp [reindex23, hswap2, hMq0]
    exact solve_canon hG' hFirst' hM10' hM20'

end OMA.BB4H1

-- Step BusyBeaver.BB_4.R2.H1.R1.H4.R1.H3
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H3 := OMA.BB4H1.step_proof
