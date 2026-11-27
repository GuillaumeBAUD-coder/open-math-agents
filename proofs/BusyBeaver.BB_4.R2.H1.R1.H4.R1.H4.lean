import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1

-- Checker and branch certificates from @hyprspacecoyote, PR 4446.
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
  | some _ => (cert.edges >>> ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) &&&
      ((1 <<< (4 * cert.dfa.size + 1)) - 1)

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
  let extra := (val >>> 1) &&& 15
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := (val >>> 5) / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val.testBit 0, ⟨extra, (val >>> 5) % dfaBase⟩, payload >>> width, payload &&& (initialBase - 1)⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

-- A single inclusion check verifies every target in an automaton edge row.
theorem included_bit {x y : ℕ} (h : Nat.beq (x &&& y) x = true) (k : ℕ)
    (bit : x.testBit k = true) : y.testBit k = true := by
  have e := congrArg (fun n : ℕ => n.testBit k) (Nat.eq_of_beq_eq_true h)
  simpa [Nat.testBit_and, bit] using e

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        Nat.beq (row &&& cert.blankReach) row
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
              Nat.beq (swRow &&& pRow) swRow
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
      exact ih rfl (included_bit ht (nodeId cert q) he)
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
      exact Reads.push (included_bit h'' (nodeId cert t) hf) ht

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

def limitedStep (stop : ℕ) (tb : Table) : ℕ → HistItem → List HistItem → StepResult
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
      if Nat.beq nstep stop &&
          findRep tb ncur nprev then
        .rep
      else
        limitedStep stop tb rem ncur nprev

theorem limitedStep_sound (stop : ℕ) {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match limitedStep stop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [limitedStep]
  | succ rem ih =>
    unfold limitedStep
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
      by_cases hrep : (Nat.beq (cur.step + 1) stop && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01


-- Each three-bit tag selects a recurrence time, a certificate, or traversal to the next missing transition.
-- The soundness theorem below applies to arbitrary tags.
def runPos (tb : Table) : ℕ → Position → Option Position
  | 0, c => some c
  | k + 1, c =>
    match tb.get c.state c.head with
    | none => none
    | some m => runPos tb k (c.move m)

theorem runPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (k : ℕ) (c : Position) {c' : Position} (h : runPos tb k c = some c') :
    M.multiStep c.view k = some c'.view := by
  induction k generalizing c with
  | zero =>
    simp only [runPos, Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    simp only [runPos] at h
    cases ht : tb.get c.state c.head with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      rw [multi_succ_front, step_move hm c m ht, Option.bind_some]
      exact ih (c.move m) h

theorem run_add (M : Machine4) (x : Cfg Symbol State) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp


def witnessPos (tb : Table) (i : ℕ) (cur : HistItem) (prev : List HistItem) : Option Position :=
  if cur.step ≤ i then runPos tb (i - cur.step) cur.c
  else
    match prev[cur.step - i - 1]? with
    | some h => if h.step = i then some h.c else none
    | none => none

theorem witnessPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {i : ℕ} {cur : HistItem} {prev : List HistItem} (hv : HistValid M (cur :: prev))
    {c : Position} (ok : witnessPos tb i cur prev = some c) :
    M.multiStep (Machine.init []) i = some c.view := by
  unfold witnessPos at ok
  split at ok
  · rename_i le
    have live := (hv cur (List.mem_cons_self ..)).2
    have eq : cur.step + (i - cur.step) = i := by omega
    exact eq ▸ (show M.multiStep (Machine.init []) (cur.step + (i - cur.step)) = some c.view by
      rw [run_add, live, Option.bind_some]
      exact runPos_sound hm _ _ ok)
  · cases mem : prev[cur.step - i - 1]? with
    | none => simp [mem] at ok
    | some h =>
      simp only [mem] at ok
      split at ok
      · rename_i time
        have eq := Option.some.inj ok
        have live := (hv h (List.mem_cons_of_mem _ (List.mem_of_getElem? mem))).2
        simpa only [time, eq] using live
      · contradiction

-- A recurrence witness gives a reachable starting configuration, a period,
-- a guarded tape width, and a choice of side. Both the run into the cycle
-- and the guarded period itself are checked by the kernel.
def checkWitness (tb : Table) (cur : HistItem) (prev : List HistItem) (i p width : ℕ) (mirror : Bool) : Bool :=
  if 0 < p ∧ i + p ≤ 107 then
    match witnessPos tb i cur prev with
    | none => false
    | some c =>
      if mirror then
        checkGuardedLeft tb.flip p c.state c.head (takePad width c.rs) c.ls
      else
        checkGuardedLeft tb p c.state c.head (takePad width c.ls) c.rs
  else false

theorem checkWitness_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem} (hv : HistValid M (cur :: prev)) {i p width : ℕ} {mirror : Bool}
    (h : checkWitness tb cur prev i p width mirror = true) : False := by
  unfold checkWitness at h
  split at h
  · rename_i bounds
    cases hr : witnessPos tb i cur prev with
    | none => simp [hr] at h
    | some c =>
      have live : M.multiStep (Machine.init []) i = some c.view := witnessPos_sound hm hv hr
      cases mirror
      · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
        exact hLoop i p c.state c.head true (takePad width c.ls) (ListBlank.mk c.rs)
          bounds.1 bounds.2 ⟨ListBlank.mk (c.ls.drop width), by
            simpa [Position.view, takePad_foldr_drop] using live⟩ (checkGuardedLeft_sound hm h)
      · simp only [hr, ↓reduceIte] at h
        exact hLoop i p c.state c.head false (takePad width c.rs) (ListBlank.mk c.ls)
          bounds.1 bounds.2 ⟨ListBlank.mk (c.rs.drop width), by
            simpa [Position.view, takePad_foldr_drop] using live⟩ (checkGuardedRight_sound hm h)
  · contradiction

def witnessTable : ℕ := 0x200a010002de085960008680441b812a100431780244400612001c58004230010460c50a00205c00c040220220041480106400b1a81163e086960118420078f013e00008128036260460e802a1c0082c0021080081483140e08a0203103e0118580183800a15823c0600f16032600006170018600071b800a6a0118701300c0071702120a0c70382143a0041882300a04e8180367a0c9058024540d286001c4604593801e4a04897801e4c04492041e040898a01125010b01021264044ba81144400984020a5e0c80100206e0068f801c780419300284a1090684344609900804b0e04d040428060080e83b41005283801e2c08c81801f000c4888424200870401127600c46001056008a0052e0600d08801c5a08989002a120088803202a00a9802381008b000124140029a01185c1058b013a1000c06011a240c58a822e0c0c6838025360841382102200811800a4c0c7030022340079703260600e23010c3a0080480126200b86821a1e0880381241e00908802a180478900165600846003098045988344020009d000a5800d1103240a00985820c3601285800c4404a0180066000f0a80074800792801e1c0079a010e5408e0102400600d97802a9c0080d026614056880020cc0070e001cdc0079c001a6004392801aa00880b80165e0059e00202a005a08016aa005a400502600b3001203c08b8702084400a8b000e540088706b8060121906900604e0582302e00901802c0604a850002c60c48e0460041950181221c0cb01814c140009f00027a006898116320069581484a04a8181361408982812e040051303145409500023c0008e8080320604c8b842a0c1120102360608589010e400468e01040800699010c3e00b1380143404f0b832c0e04419000884002128222120051a811c34001a70006500449002080a00b118018700c40b820e3e043980290020d480001c60091060004581058900284604b0784300204e07802a2a00a09841c0208e82820c320830e821e360439e8238020480d035016042958010540088484340004e13800a5e0cc0082161c0c50a8028360078982360608c010330260079801204c08c0202340a0429904360804807822a080ca85051e1e10483013a14010040034100490c011c240538283101a10b060118440031882320608f06821c2404d848026640459101045008c018316060068c832a060478a0002d204888820c1400413859c0004510021c3a0458b012434000b5811a3811c01012a1a04591824a0a0009c811a4a08609801c6c08587000c4c0069300501a008940024620860d00285c0440f8018240041a82181c04214011634045a001166804592802a3e0019380204a0498980083a002118008420449b81183c0088a0026280c78002182e005170230100861200342c0c6058016240009b81303a00217805492000a38116560061e801c8a0093402300e04b848220260050a02381a007090410180821280026000c020002e000a0201480804e0281381808a8600343c08e00801c5e006268014a215f000104660868981301808488001a3a0039302200800696032c000ca0002280208804011a420c38981342c0421602184600615022c160c38b812e000850d821c1600d81823e1c08d040002820cc8c86544600aa581249a00c4f8038cc00e838210520440e02086e04f1d0226300498d80230e09e01842a3601e1b0124380198300c00c0c80601162409104003a1c000b600460c08c05014a000148304281c08d01032a1808784800a7408a8281222c0d185800c6000722001c9800735810c340080f80185a0878400067404118801c660052e802caa008328018ca16300000c8216f000024160058d0016640031585a40208a0e010c5608c0000424e014210016440c60c83180e0838b803efe0009982204600d0e80224408a0403301008b0401105600805803a160c4070014a00850c032c90098820330980098c00262e004a08012a20049e801a4208983810e5c04a87810e760439583141c0071a801672005a6811e1a0c6848110460c38f8016940498601321a0c48703520004e06014c200478e8334a804f82800e9008312022c0e08882000c4a04918821a1208991023e080839080303808a058012a60099b02401405180023c0e00c0b0018501050d0016581040d041c360051400203a00983001e2404b07031834005940022180c90900163c00e850034140840d00321404c840038140098582201a04180801c500088800301400889000a6e000818234020440c81401e045908138320cd07021e16047020126200051501162c04f008004420c582831e0a00109802e120010d0310301060f020c440490700202c00c0a003a32086030030000c60304241400a0e80025a005968122100838f812a3204a11002678007880212341100082220e0429781224204809012e200480d82181000998002a1c0448d01163e0c8040312180011a00265804908002e2800810001c280c50402087004c0c02203004f0e030e1600423801ca60062700164208499814c100498c002c2000a0b836a000820f002c240ca028030e6083978366020d380820e3208789811e2200a8482242e0c48a021a18088868136540c408011422084038226100c680821030104898022060480281244204b0080246404b03020a30108010028100c3030134000c489010c340c4038218220058f011e2a0c501842c020418f810c3e00316820a3e0050c820c3c0d201820c280091182162c00982002c1800197001842089028134140011700064a0848b8210360488501144c0c51303280408b818316240478801063800196000a5e0080d810e4e0080c81064004785801c2e0c58383300c10488820c4a0068a030e2010588012e020848a80183e0858800241e043168108000848903121c0090f01102608903801c2a0870701182e00707811e340830d030c3e0868b0108460071381280e047058220140c5038002080820e011c1e04803801a6000633841602086850116520468980029c04e008108260039580104c0440b00242c044100018460488902204200895001a680500201044a004248024880478b8004040cd018014080488d001e3a0060d03200800592010e380c410812c220448b02181a04782811e1c000988234120840e001e3c0091303141c0830e030c2c00787013208002188020260c70403241808682801cb00058d02241a0009b0220120029b0218220069d0322020049601083c00294801a5a005908016620059a0208360058c8002c80460d80025004f06010a4800497800e620039e822a0200c0381125e08f04801266004a180241204903801a9c0011381123e0068e020c3c0c508011c280840e82221c0470800064c00986021a2600799001450049068012720049281221a0450c80025e0051080241e0078a800a5a08507011a1c0450e801a4c0480681163a0480482304604a040218280858a820c200450c02241c0840c0008540078a02220c0070b002a280438d031e0c0090282142400705022414048050014380060e8012500c407802c840070c0234020460681182608504822c020418d802a300029800124800a88000a4c0c48581082800980002e0c0c40503101000410001a4000687030e240458e030c180009c00243200711821816005910136380060c02280a0438e8342020838a000e6000399820e420d68003240c0c5058312180078b001a2e0080a001c4204906810c2e0c601801a2e04588022a020448c0116280448e810e3200312800a4a0080683200210583800a5408a83000a4a0c681011a280049981300600708021c1804784001e0a0440b8012320058e030c4000214810c400888101242a008078008360040f83100a0088580026a0060a83180a04704011e0e089800124060080881201808702000c3a0019281181e0460c8010380c3080314180009a0136000019800123a0058881320404a0382320008409002c0e0071000143404282801c3c08b01820c2e0878280143e00592041c180448b001c3604706811c440c606012e0808a0380261204c09801e46005950318200850900281404b0601261004b0200201804b86001a240c40a80083000397820a2e08404011c1a08586811246046910014420438b820e360010e0214280c50c82121800a83010e2c0c90500025808c0081220c00808811026045098316160450b800a520418c030c1004c80030e1a0049a001c2408783811a2000394801494048080014320888000125604490010a4008902021e1a08a8680248c00191030e1e00083031a0600102031e0400295022200083898106440448c8010360c48303161e08b81821e0c0058e822806009068328000850880024c08c0602220a00410000c400860502241004903820c260c383833c0004c020110300860981201604a83801652088028228000040d02120200490813c0e046868012460448d83121600783011e1804884012a100c510001a340488680145600a05810a4a04508801a2004210011838001950318280c70a83140a0050b030c1c089000320140068a00103c0860200262204489022a04086848212200450a03121000807801a1600513020e20085840012460c70280181000989831e020009281141e0c701010a340c501810c32001918224000878081260c0050f82122604312810a3e0450a01122a003910228040020f822c04003110114260478502200e08981801c180040e800e4804a8280221a0049f02240c00112002014006868012921068002161a0058b8116280850700025e049048018220c600020c300030f001e3008705810a4e04589800e2c04489010c320438d01083a0c482800c3c0440a002424007080008400c3848322000049300182c00102800e3e0c500820a2a0078600280c0490481163404686800a460039c031006006830208320448e02102c000990224040c30c801c100078502121e0020b0014440488880064204687811e120840601181e082898020060428e011a2204505020a2c0c30501220e0440a8014240088380164c0411000025608901022604084858010440870380024604684000e4e08485820e3a0c388821a0c0438c030e040c801012a00089800324060c88180102e04605801a1c0028e0018580418d810c260030e0024100830b031c0608a81812406003940128100088580280e04b018002560048d80124e0058a011632088810130000019082140e0048b0012360078501044c04685810a440058c021a140470300183400589821c0c0040b020e1c0011180141e08585002a00001148014380c4060014480078402181e009058014220438f0310380430b811a1600705000c3408805011c1608505830e0a04981820e100820b01162004507011e0600310001828082890018240410f8220040040c020a280488100162c045878010300009280160a0048a831c020cd00832c020060701063200390800e5a00497011c10007868212120448a821c10084080120100080481161c0068801044608306800a4204800011820085040006080029180042c00392801e100428e821a08003900024000468302121804181800608049820214160049580200e0048e0124080420c010e280420d811a0a085840018200050a820c1e0030b00123c0010f01280a0068680043208389800e30084028122040488200161e0018e03180604703001c1808801021a0e0420802082a0438a02160c0418b010a2e0048f00122e0010a801a120848701200e006060002520028f8128060430a001a160c680001c1e0030d80080e0428d0014260010402120c0098300240e0c9000028000009381081a083888118100039100202608407020a220040a0118180428981121c08506000c320420780063c0038c000e380860301161804488821c0a08583810a300048c0216000c581011a10002908210140010381062c0028f0016280018e021812045068116120c682800c300850200083804505801026043080212100830a012c000050b800e3404980811222087808218080480180060604783801e060418a800a3a08284020e180060700122a0070101160e048018008280018f00200c0820901240204306000e3c04388021a000430a0004400410302101a00587820e1800507800c2a000900116160880082120c0070281101a0428a821e0604586801c0c088008012260028d80180e04780810a2c08383820e1404389801020005860110200840781102200584001e0c00880011e0a0058501280204603821c06083878012080c481800e38046040118160038a020c2204503800a3208381801814000918008240010e00200a08288810e240018d01220008405011c040428c001024002008108160828580121c007038110140020d80023e0c48000082c08286000e3400489810c0e04683011c0800588020a1c084030116120430701043a00505020c0808700800c220460201160a004840120080428a001614006848012200048802140c04485811410007040218000060581161400508001a0a00106820a1e0418302100000606821a020038902082008781020e16086018014120050680161a0020801082c046818006360008402081e08286020c2600108820c0a0840001062808701810a2600583020e100040a82160604486000c2e0c58001082a0040701121c08281000e2c0020c82100404309000a32044040104340850081060a04189010a1e0868102081a00483800a2e04204810a0608501800a2a04485811c02084818216080868101120800683810a220870002080c04504810a02043888006320440381160804308021604000908012180030a800c240028d800e20045060010200420181160c0018c001e00044070118080028a01062604483011a080830582140a047010108080008f81121208383811e060040280140c04603010e1e0418800023a001070002100830701043000487020c1200307011018082050016120420280121604304010e1604407810e1a0040502101208402811a000448401042c0028b80023404382000e240820401120e004048218020068101140a0008e00141a0040301200200207810e1c042880112180038a020a160850082120a0020201140e0020600181004209800e1c0010d00101c0828480062e08580010622001830008280010c00160e0468180101a0828200180e08283000c240830381140a002828118020430500062c04405020c180038780081400486820e020448280062800183800a240410400080a042868008060028800140c00582800c0c0028000200000505810c000008d021804083010012160038201042804187011c0004780010c0004208010e1a00304010a1800307810e0e04187001c000028981061000602800c1604384810a1c00209811602002048118040038800101404402010c1c08401800a1c085010014100438400062a0038480062400288000c2200385800e1a04385800c1a0008c000216083820004120038300042c00406000c18043068018040440301101000483001210004820014080848181061800189810a16042838002160430101042400287010a040008c010e020018881140600286000e1404581811604043838016040038680022c04601800c080428501081c0010a810a120018780022804184000a1a08480010c140068000022e00184000610002080006200420381061404680800a140040200080e0050101061400282010c0a04402800a1000404010c0e04500010a0c00305020e040020701140400403010c100458080021804284010414041860104200460001081800285000c100010581120600185000e10001878006180448100042400383800a0e043820002280448081100604381800a0604480810c0a00089000c0000283810a08003820018000030201081404500810e000410781100000206000422004810104180018500061a00088000218042040002240430101100200087801004003030016000010600041c0438100081000205000a100440100021e0030100022000500000e020038100100000480


def witnessAt (tag : ℕ) : ℕ := (witnessTable >>> (22 * (tag - 2))) &&& 0x3fffff

def checkTag (tb : Table) (cur : HistItem) (prev : List HistItem) (tag : ℕ) : Bool :=
  let v := witnessAt tag
  checkWitness tb cur prev (v &&& 127) ((v >>> 7) &&& 127) ((v >>> 14) &&& 127) (v.testBit 21)


def readTag (code : ℕ) : ℕ :=
  let low := code &&& 15
  if low < 3 then low else if low < 15 then 3 + 16 * (low - 3) + ((code >>> 4) &&& 15)
  else (code >>> 4) &&& 4095

-- Each word ends with a sentinel; the next word and the automaton data
-- occur in exactly the order in which the traversal consumes them.
def advance (code : ℕ) (rest : List ℕ) : List ℕ :=
  let low := code &&& 15
  let next := code >>> (if low < 3 then 4 else if low < 15 then 8 else 16)
  if next = 1 then rest else next :: rest

def advisedStep (tag : ℕ) (tb : Table) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : StepResult :=
  if tag = 0 then limitedStep 0 tb rem cur prev
  else if tag = 1 then .done
  else if checkTag tb cur prev tag then .rep else .done

theorem advisedStep_sound (tag : ℕ) {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match advisedStep tag tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  by_cases hz : tag = 0
  · simpa only [advisedStep, if_pos hz] using limitedStep_sound 0 hm hG hsum hv h01
  · by_cases ho : tag = 1
    · simp [advisedStep, hz, ho]
    · by_cases hw : checkTag tb cur prev tag = true
      · simp only [advisedStep, if_neg hz, if_neg ho, if_pos hw]
        exact checkWitness_sound hm hG.2.2.2.1 hv hw
      · simp [advisedStep, hz, ho, hw]

def guidedTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, [] => none
  | holesLeft + 1, used2, tb, rem, cur, prev, code :: certs =>
    match advisedStep (readTag code) tb rem cur prev with
    | .rep => some (advance code certs)
    | .done =>
      match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some (advance code rest) else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some (advance code certs)
      else
        checkMoves (fun m rest =>
          guidedTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) (advance code certs)

theorem guidedTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : guidedTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [guidedTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    cases a with
    | nil => simp [guidedTree] at hCheck
    | cons code a =>
      unfold guidedTree at hCheck
      have hstep := advisedStep_sound (readTag code) hm hG hsum hv hu
      cases hsl : advisedStep (readTag code) tb rem cur prev with
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


-- A subtree starts from a partial transition table and an already verified history.
-- Each group of successor moves is checked by separate kernel computations.
structure SearchNode where
  tb : Table
  used : Bool
  rem : ℕ
  cur : HistItem
  prev : List HistItem

namespace SearchNode

def Valid (n : SearchNode) : Prop :=
  TreeValid n.tb n.used n.rem n.cur n.prev

def result (n : SearchNode) : StepResult := stepLoop n.tb n.rem n.cur n.prev

def branches (n : SearchNode) : Bool :=
  match n.result with
  | .missing .. => true
  | _ => false

def child (n : SearchNode) (m : Move) : SearchNode :=
  match n.result with
  | .missing q a r c p => ⟨n.tb.set q a m, n.used || Nat.beq m.state.val 2, r, c, p⟩
  | _ => n

def atMove (n : SearchNode) (i : ℕ) : SearchNode :=
  n.child ⟨⟨i / 4 % 4, Nat.mod_lt _ (by decide)⟩, ⟨i / 2 % 2, Nat.mod_lt _ (by decide)⟩, i % 2 == 1⟩

theorem check (n : SearchNode) (fuel : ℕ) (certs : List ℕ) (hCount : (holes n.tb).card ≤ fuel)
    (ok : guidedTree fuel n.used n.tb n.rem n.cur n.prev certs = some []) : n.Valid :=
  guidedTree_sound hCount ok

theorem split (n : SearchNode) (h : n.branches = true)
    (children : ∀ m ∈ movesAllowed n.used, (n.child m).Valid) : n.Valid := by
  cases hs : n.result with
  | rep => simp [branches, hs] at h
  | done => simp [branches, hs] at h
  | missing q a r c p =>
    unfold Valid
    apply branch_one (q := q) (a := a) (rem' := r) (cur' := c) (prev' := p) hs
    intro m hm
    simpa only [child, hs, Valid] using children m hm

theorem cover12 (n : SearchNode) (branching : n.branches = true) (used : n.used = false)
    (h0 : (n.atMove 0).Valid)
    (h1 : (n.atMove 1).Valid)
    (h2 : (n.atMove 2).Valid)
    (h3 : (n.atMove 3).Valid)
    (h4 : (n.atMove 4).Valid)
    (h5 : (n.atMove 5).Valid)
    (h6 : (n.atMove 6).Valid)
    (h7 : (n.atMove 7).Valid)
    (h8 : (n.atMove 8).Valid)
    (h9 : (n.atMove 9).Valid)
    (h10 : (n.atMove 10).Valid)
    (h11 : (n.atMove 11).Valid)
    : n.Valid := by
  apply n.split branching
  intro m hm
  simp only [movesAllowed, used, moves12, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11

theorem cover16 (n : SearchNode) (branching : n.branches = true) (used : n.used = true)
    (h0 : (n.atMove 0).Valid)
    (h1 : (n.atMove 1).Valid)
    (h2 : (n.atMove 2).Valid)
    (h3 : (n.atMove 3).Valid)
    (h4 : (n.atMove 4).Valid)
    (h5 : (n.atMove 5).Valid)
    (h6 : (n.atMove 6).Valid)
    (h7 : (n.atMove 7).Valid)
    (h8 : (n.atMove 8).Valid)
    (h9 : (n.atMove 9).Valid)
    (h10 : (n.atMove 10).Valid)
    (h11 : (n.atMove 11).Valid)
    (h12 : (n.atMove 12).Valid)
    (h13 : (n.atMove 13).Valid)
    (h14 : (n.atMove 14).Valid)
    (h15 : (n.atMove 15).Valid)
    : n.Valid := by
  apply n.split branching
  intro m hm
  simp only [movesAllowed, used, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

end SearchNode

private def nb11_3 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_3_14 : SearchNode := nb11_3.atMove 14

private def nb11_15 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_15_2 : SearchNode := nb11_15.atMove 2

private def nb11_15_6 : SearchNode := nb11_15.atMove 6

private def nb11_15_10 : SearchNode := nb11_15.atMove 10

private structure BranchChecks1 : Prop where
  vb11_3_0 : (nb11_3.atMove 0).Valid
  vb11_3_1 : (nb11_3.atMove 1).Valid
  vb11_3_2 : (nb11_3.atMove 2).Valid
  vb11_3_3 : (nb11_3.atMove 3).Valid
  vb11_3_4 : (nb11_3.atMove 4).Valid
  vb11_3_5 : (nb11_3.atMove 5).Valid
  vb11_3_6 : (nb11_3.atMove 6).Valid
  vb11_3_7 : (nb11_3.atMove 7).Valid
  vb11_3_8 : (nb11_3.atMove 8).Valid
  vb11_3_9 : (nb11_3.atMove 9).Valid
  vb11_3_10 : (nb11_3.atMove 10).Valid
  vb11_3_11 : (nb11_3.atMove 11).Valid
  vb11_3_12 : (nb11_3.atMove 12).Valid
  vb11_3_13 : (nb11_3.atMove 13).Valid
  vb11_3_14_0 : (nb11_3_14.atMove 0).Valid
  vb11_3_14_1 : (nb11_3_14.atMove 1).Valid
  vb11_3_14_2 : (nb11_3_14.atMove 2).Valid
  vb11_3_14_3 : (nb11_3_14.atMove 3).Valid
  vb11_3_14_4 : (nb11_3_14.atMove 4).Valid
  vb11_3_14_5 : (nb11_3_14.atMove 5).Valid
  vb11_3_14_6 : (nb11_3_14.atMove 6).Valid
  vb11_3_14_7 : (nb11_3_14.atMove 7).Valid
  vb11_3_14_8 : (nb11_3_14.atMove 8).Valid
  vb11_3_14_9 : (nb11_3_14.atMove 9).Valid
  vb11_3_14_10 : (nb11_3_14.atMove 10).Valid
  vb11_3_14_11 : (nb11_3_14.atMove 11).Valid
  vb11_3_14_12 : (nb11_3_14.atMove 12).Valid
  vb11_3_14_13 : (nb11_3_14.atMove 13).Valid
  vb11_3_14_14 : (nb11_3_14.atMove 14).Valid
  vb11_3_14_15 : (nb11_3_14.atMove 15).Valid
  vb11_3_15 : (nb11_3.atMove 15).Valid
  tv_b11_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  vb11_15_0 : (nb11_15.atMove 0).Valid
  vb11_15_1 : (nb11_15.atMove 1).Valid
  vb11_15_2_0 : (nb11_15_2.atMove 0).Valid
  vb11_15_2_1 : (nb11_15_2.atMove 1).Valid
  vb11_15_2_2 : (nb11_15_2.atMove 2).Valid
  vb11_15_2_3 : (nb11_15_2.atMove 3).Valid
  vb11_15_2_4 : (nb11_15_2.atMove 4).Valid
  vb11_15_2_5 : (nb11_15_2.atMove 5).Valid
  vb11_15_2_6 : (nb11_15_2.atMove 6).Valid
  vb11_15_2_7 : (nb11_15_2.atMove 7).Valid
  vb11_15_2_8 : (nb11_15_2.atMove 8).Valid
  vb11_15_2_9 : (nb11_15_2.atMove 9).Valid
  vb11_15_2_10 : (nb11_15_2.atMove 10).Valid
  vb11_15_2_11 : (nb11_15_2.atMove 11).Valid
  vb11_15_2_12 : (nb11_15_2.atMove 12).Valid
  vb11_15_2_13 : (nb11_15_2.atMove 13).Valid
  vb11_15_2_14 : (nb11_15_2.atMove 14).Valid
  vb11_15_2_15 : (nb11_15_2.atMove 15).Valid
  vb11_15_3 : (nb11_15.atMove 3).Valid
  vb11_15_4 : (nb11_15.atMove 4).Valid
  vb11_15_5 : (nb11_15.atMove 5).Valid
  vb11_15_6_0 : (nb11_15_6.atMove 0).Valid
  vb11_15_6_1 : (nb11_15_6.atMove 1).Valid
  vb11_15_6_2 : (nb11_15_6.atMove 2).Valid
  vb11_15_6_3 : (nb11_15_6.atMove 3).Valid
  vb11_15_6_4 : (nb11_15_6.atMove 4).Valid
  vb11_15_6_5 : (nb11_15_6.atMove 5).Valid
  vb11_15_6_6 : (nb11_15_6.atMove 6).Valid
  vb11_15_6_7 : (nb11_15_6.atMove 7).Valid
  vb11_15_6_8 : (nb11_15_6.atMove 8).Valid
  vb11_15_6_9 : (nb11_15_6.atMove 9).Valid
  vb11_15_6_10 : (nb11_15_6.atMove 10).Valid
  vb11_15_6_11 : (nb11_15_6.atMove 11).Valid
  vb11_15_6_12 : (nb11_15_6.atMove 12).Valid
  vb11_15_6_13 : (nb11_15_6.atMove 13).Valid
  vb11_15_6_14 : (nb11_15_6.atMove 14).Valid
  vb11_15_6_15 : (nb11_15_6.atMove 15).Valid
  vb11_15_7 : (nb11_15.atMove 7).Valid
  vb11_15_8 : (nb11_15.atMove 8).Valid
  vb11_15_9 : (nb11_15.atMove 9).Valid
  vb11_15_10_0 : (nb11_15_10.atMove 0).Valid
  vb11_15_10_1 : (nb11_15_10.atMove 1).Valid
  vb11_15_10_2 : (nb11_15_10.atMove 2).Valid
  vb11_15_10_3 : (nb11_15_10.atMove 3).Valid
  vb11_15_10_4 : (nb11_15_10.atMove 4).Valid
  vb11_15_10_5 : (nb11_15_10.atMove 5).Valid
  vb11_15_10_6 : (nb11_15_10.atMove 6).Valid
  vb11_15_10_7 : (nb11_15_10.atMove 7).Valid
  vb11_15_10_8 : (nb11_15_10.atMove 8).Valid
  vb11_15_10_9 : (nb11_15_10.atMove 9).Valid
  vb11_15_10_10 : (nb11_15_10.atMove 10).Valid
  vb11_15_10_11 : (nb11_15_10.atMove 11).Valid
  vb11_15_10_12 : (nb11_15_10.atMove 12).Valid
  vb11_15_10_13 : (nb11_15_10.atMove 13).Valid
  vb11_15_10_14 : (nb11_15_10.atMove 14).Valid
  vb11_15_10_15 : (nb11_15_10.atMove 15).Valid
  vb11_15_11 : (nb11_15.atMove 11).Valid
  vb11_15_12 : (nb11_15.atMove 12).Valid
  vb11_15_13 : (nb11_15.atMove 13).Valid
  vb11_15_14 : (nb11_15.atMove 14).Valid
  vb11_15_15 : (nb11_15.atMove 15).Valid

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem checkedBranches1 : BranchChecks1 := by
  constructor
  · exact SearchNode.check _ 4 [0x11f5d5f575949e940c5168f24b78e8e0, 0x2101842310860, 0x1f6f6f69e171d1d576bf5f5098f698f6, 0x110af4e9f66e59e985739570000010af, 0x1831715f7576b93f507407401c86631f, 0x1f4632f83e583985715700000c3f60f6,
      0x2014042440421, 0x115aec3ee93f50f5f5c574074010107f, 0x204404a440421, 0x1e6e6980003bf600150120f1798f683f6, 0x198980fdf0a63bf61fff151500440440, 0x10440e6c498c60570760d615000003de6,
      0x1079e00fdf57a65736d61dcfd60044, 0x11987b4a214f4a08a8a012df0000120f, 0x280002200200002800800020000400028000400420000000180000001a00000001000140000000250000002400040002100010000008020000010200000100200000102829ea726, 0x1fefef519bff99ef91d7f01bff0218f98, 0x1980c602b000ae980150fff15f3930930, 0x10dbf0fff0fff120f00c3f0c3f9e098,
      0x1f60c6f1515015156c14af6c3e9f19ff, 0x14764424f0d4d4d43dbe98981cbf03b3b, 0x1150415f30b525053fef57b058a04764, 0x147646596160f1553002b01601a2f9804, 0x10000119f989e98994aee4a0b68a04764, 0x10f683015aec3ee93f501ecff926fff9,
      0x100ecf6aef646b7aeb70120f1798f6076, 0x115f615093f693024194fbb1d5f0c3f00, 0x157057d5a71502424015e80000000980, 0x1579ec40c6fd61501a2fa4193ff628057, 0x1f5d5f5759409400d4155fd40be098c60, 0x1292f0d5a7154d2424064001c00098f60,
      0x1f57594283f9406474a4747428765757, 0x1b525005270741774950098038cff5d5, 0x12b198ff61aaf1601a2f004150415f3f4, 0x105757135713a7150242405324532468, 0x1a357f510ef96096240193fd3f6f6f628, 0x1013a7150f0f24240650000160193f57,
      0x19610df9624047d3434343280575713, 0x1472b43444300057a30f510ef] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1149f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x16b119f6b839419406a8368b7058e0, 0x2101842310860, 0x12a1d119f6b6bf5010f3f4eaf0f3f119f, 0x2101842310860, 0x1119f39119f00000860f3f0f3f0f3f117, 0x704042310860,
      0x16b93f5000001c86010af10e534ff392f, 0x4000212220000000100000000800000000000010020000000000000008800000000000200020000000000000800800000000000010020000000000000008800000004000272a0000001010000000000000040000004000000000090000000000000010000001000000001000000002000000004000004000000000090000000000000001000000202000119500000008000000400000000012000000000000002000004000000000200000008000000000800000010000000012000000000000000200000200000020000000100000000800000004000000001000000080000000200000004000000020000000020000000080000004000000001000000100000000020000000080000013487ffd6bfc7d72e, 0x1119f00000c30f3f00f3f8317ecf7119f, 0x100001f425df03e4f83e583392f119f1, 0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44, 0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44,
      0x11f4f0fbf30df8c18c0e7fee3b6fee00c, 0x21018c25208e0, 0x1174f174f0eff164f9e9e032df224f, 0x10eff10eff00000131f00fbf0fbf01c0f, 0x2014042408421, 0x100000117ff25ef131f633f01399f1f4f,
      0x202405e439ce1, 0x204405a4294a1, 0x1000fbf119f1c0f5d2b1f0164f0c6f9e, 0x1119f3b7f253f634f253f000000f0f, 0x11058a0000030df01161f4a7f119f635f, 0x204405a4294a1,
      0x2100842210860, 0x11b6f0e3f2424065111b6f532f5f53fe1, 0x2100842210860, 0x21018c2318860, 0x21021c27388e0, 0x12cafe42401463146328111d9f13013a7,
      0x100024000840011000402800080804020100805a2, 0x1e600f379803cde60079bcc26076cc001f530007988a3ae0222c0003d398c570798f3007983cc1e709b84, 0x1124014631463a51361f1136613131, 0x2014058420421, 0x2014058420421, 0x100804002040011000440101404010090400413a3,
      0x100004000080012000402800080000020100805a2, 0x10e2f96e4100630630cbd31a301111cdf, 0x100014000480012000402800080402020100807a2, 0x100024000880012000402800080804020100805a2, 0x100024020880012000402800080804020100805a2, 0x1e600f379800f4e6003cfcc2da023000204600079889fe20222c0003cfcca71079879807983cc1e690384,
      0x2014058420421, 0x1179fc3ee93f50140140a501a4130131, 0x2014058420421, 0x20440584214a1, 0x13b0001500fdf171e7f198f83140f1bbf, 0x1425f344f212f1500440440e6e60000,
      0x10760d615000000e6026cfc60204f2cbf, 0x11dcfd6322fd600440440e6c40c600, 0x1682705280000000700a919af019af, 0x1242406549426f2a0f530f3f5329bf, 0x10000028012a0f138413a7427f2c2f, 0x100800120040011000402020080804020100805a2,
      0x1140a51827bf2813661313419f0e4427f, 0x11600000d3001a38411161cdf16240140, 0x504042210860, 0x504042210860, 0x10800420080402000402080082010020400817a2, 0x108a0140140a501a413013540e2f96e4,
      0x20440584214a1, 0x1ae428f0356f002d2a2d7b115f2cbfae, 0x1002d12d7b4a2cbf4a0636f196f189f, 0x80440002200000002002000020000400028000402220000000280000000a00000002000460020000440000004400000004400040000020020000010200000100200000102029fa726, 0x1ee3b6fee019bff9136ff9428f0356f, 0x1224f1f4f0fbf32df01f4f008c18c0e7f,
      0x80444022200000002002000008000400028000402220000000280000000a00000002000460020000440000004400000004400040000020020000010200000100200000102029fa726, 0x1930a60a60000000e50f3250fc0fe3b7f, 0x100083e58300000c600000000000f3930, 0x10e1f00e1f0e3f0c6f4adf0c6f0000000, 0x1151500101f1abf101f4a8f0190f00, 0x101b7f369f3dbe216f000a63b1b6f21cf,
      0x1d4d43dbe216f00003b1b6f0c6f151501, 0xc0044020200000040a00040000000400408000600220000000280000000a00000002000460020000440000004400000004400040000020020000010200000100200000102028fa726, 0x10356f002da62d36b92cbf103f00d4, 0x11d14ef196f39f5064000f7f103f1dcf, 0x14ebf5706495f495951cc8278f000e5, 0x11b95e929cf0637f0083e583314f1f1f,
      0x1ac114f2cbf102a117b105f7b0058a095, 0x1018050440421, 0x1018050440421, 0x1028050440ce1, 0x1110e7f14cf0e7f0e9249fe930ef12ff, 0x218052440421,
      0x218052440421, 0x1110bf14ef211f0edf638f251f100e6f, 0x228052440ce1, 0x298052442521, 0x1165d00042f5f040f325b50053fe10bf, 0x1001d3f3b8f1b6f0e3f10e3f053084084,
      0x10030400500014000402800080402020180807a2, 0x11e4f126f0102f0102f01147f240f27ff, 0x2b9b9d6b1fffb00159fd8acfeeb9b9d6af77405cfec000acfeeb3fb0000567f60159fd80ad0173fb0000002becaec000000afb2bb0000000360f9c000000afb2bb0000000614f4c0000000f3a22b6b1fffb567f6000acfec567f60002b405e6e75ac7ffec00567f60567f759fd8000ad0019fd815cdcebae256000000164cd6c000002b554fd80000016f9d580002b3fb2b3fb00000159fd8103782cfeb, 0x1147f240f27bf206f0206f206f1639f, 0x818058440421, 0x1b411b6fd71b6f0102f0102f279f27bf,
      0x20010800500014000402800080402020100807a2, 0x12424065950954e187916af3db40b4, 0x114631463281e114f013013a71b6f0cbf, 0x163a51e114f241f1301313163afe4240, 0x1018050440421, 0x1d3630000a300e6f111cdfd7240146314,
      0x1018050440421, 0x1018050440421, 0x1a4a5000134ecf1310e2f96e41508463, 0x1018050440421, 0x1119f2d136f2d994aee4a0b68a0146614, 0x1179fc3ee93f501c9ff9215ff90000,
      0x1b700fdf171e7f198f076008301bbf, 0x10c3f0000ec120f1dcf120f46b71dcf, 0x13e0eff3eeb4d1f4f4d0179fbb15cf, 0x10093093063bf11bf1ebf179f00000f3f, 0x10e1f0f0f0c6f00c6f0e800000000000, 0x12400101f279f101f0000194f0e1f13bf,
      0x1c40c6fd61500a4000000a3000000ecf, 0x109409400d4159fd40be00c60170f218f, 0x11cbff44d0ecf24064000000000000, 0x1942c5f9406495a495e907600a3013bf, 0x1b5f4009517951f2f0000863e136f3ef4, 0x1057415741516000042f5f0429aff325,
      0x10f3f10f3f29bf194f63cf10df06827, 0x85670020004040080002200100000800108000000220000000280000001200000002f567020004404020000220100040000200400042b3840000202200000110400000040123fbd27, 0x10530f3f533cec3cec63ef04edf063df, 0x12b4f00000280001319af13a7002424, 0x10642f10000641f0640f1419f063ff, 0x818058440421,
      0x818058440421, 0x10001615df00a319af0001cdf02404eef, 0x104eff00fbf01d1d2a0f1deff5f5065d3, 0x101313426f643fe4161f07443744310af, 0x1db490d6f25f50149a1406a5002813, 0x10e2f96e4c308443c3430cb00830101f,
      0x1146614a4a5000130cef1354] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1228f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1168f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11501f6218fb71172a1dd68c3b9ff500, 0x2100884210860, 0x2100884210860, 0x10105f1500440443d04a4a0e603bb7015, 0x1150044044151f0574ac6e612ef0218f, 0x1d6000070044044760574ac6e6d6000c4,
      0x136af39194f00000157644f5786d612ef, 0x100104004020010080420100804080012000403a3, 0x13600f601ca9429f10af29df1e522ef1, 0x2101084210860, 0x2101084210860, 0x1a6a6000f8f00950950000571b9a6194f,
      0x100044001001010040421100044100010800403a3, 0x1086b91000c4f60950950110f7a0000, 0x100024000801010040401100044100010040403a3, 0x17900ecf00ba603baf000700000100ecf, 0x100104004001010040401100044100010040403a3, 0x10e3fb7831793f718c0ecff509509500,
      0x2100884210860, 0x100440440004a0e6e63bb700150c311ef, 0x11500000151f004ac6e612ef000e3f015, 0x1d600700004404476004ac6e6d6000c4, 0x18318c2a7f57000001208f0086d612ef, 0x20800820020012000420100804080012000403a3,
      0x2101084210860, 0x11b9a60cbf3601001f41361aff83e5, 0x2101084210860, 0x2101084210860, 0x10080022000804020100804020104002100080da2, 0x501084240860,
      0x1000a600360f8f360000010dbf10e3f, 0x501084240860, 0x501084240860, 0x186b910cbfc40000950950110f7a645f, 0x501084240860, 0x100790000a60000070000010dbf10e3f,
      0x501084240860, 0x501084240860, 0x11140f252ff600ccfb783946a9495095, 0x21020846108e0, 0x1bbbb143f4d01f60bac81c8f7b70d8fb7, 0x21021846308e0,
      0x10080022002004080100810020104002100082da2, 0x1310f004d04d000001133f646fee0d8f, 0xd021846408e0, 0x14a19bf9900f600000100103f169f0d8f, 0x20800820020011000420100804040011000403a3, 0x1f7169ff70ce0000000ba133fd8eef7bb,
      0x11164f3b9f9e0f5010000125fba0baec, 0x2102048480421, 0x504084210860, 0x1164f648f9e0000112d09e647f6b6d6b, 0x504084210860, 0x10080022004004100100804020104002100080da2,
      0x1d60000649f3e03e2ccf6b14ef6b119f, 0x1296a2c6f77140f64aff60b71172a1d, 0x8800220020014000420100804100014000403a3, 0x177140f0f600002f4f64bf02c6f0391f, 0x12a8f9800c80c80000125fb764cfb7, 0x11515001011a9019ff275f866a861164f,
      0x504084210860, 0x504084210860, 0x504084240860, 0x504084240860, 0x101501f2f4410bf443d04a4a0e603bb70, 0x10e944e944151f034bf4ac6e612ef000,
      0x100000c844c444760ee4ac6e6d6000015, 0x1fd00e90edfe9071034bfee86d612efd6, 0x80102004020010080420100804100014000403a3, 0x1135f42af0edf15cf194f31effd337f, 0x10fd03910bf0fff10bf0fff249f03bbf, 0x100000102f6f135f201f1b6f2e6f00fd,
      0xf30079f9801e7e600798f300088b0001f5300088b0079bcc01e6f30079f9800097e0079f980007a79745, 0x103bbf000edf0e6f031ef0e7f14cf0e7f, 0x1164ef64df2e5f010bf010bf14ef211f, 0x1023000408c001023000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x17b0e50336f0336f110064ff22ef122ef, 0x3ca765455e90077b43ced4000059682fee6b2f7359401ded0f3b577359400079126a500002540be400077acc994000eee25d940015239eb1ecc39401dcd82cf41d650773594000ef59939f35940ee6b29dd4f9ec6d187b5a2f599504d6500773772b32650001dcda0d666a928734e9,
      0x1023000408c001023000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x77536165001dd4d8594007753616500077acc99400079126a5ee9d7a0f5b94d4704862f41b92800ee6b2bb9aca3c8967729a8dcd6c75367ae534fdcd65ee6b9f35947735a2ee276b94d46e6b45dc4ed729b5e6b287735cf9aca3b9ad8ea6cf5ca6aae6b36e6b28ee6b6b83703e8, 0x112ff013ff1338fac2a10d1f7b105f, 0x1014050480421, 0x1014050480421, 0x1339f0212f317f010af29dfe91e930ef,
      0x1084050482521, 0x128bf02f7f28bf650f147f12ef42bf, 0x16a861164f2a8f980102f2d3f102f29cf, 0x1e6f30079bcc00f3f3000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x13600001c01c0f01c0f1a900275f86, 0x4004000004010000020040000040100008040402020001000000100008200000020004040200004000400020400000040004080400020000800080800000040008000100028fbc26,
      0x110950995090013ff19df1b9a6194f, 0x2a04080104001100046010100410005400042ba3, 0x40801000040011000440101004100004000403a3, 0x1110f013ff142cf15efa6a6173f00f8f, 0x1014050480421, 0x119df86b90e6f00000095142f950c4f,
      0x10ba613baf01000dbf09c40912ff01f3f, 0x1014050480421, 0x1014050480421, 0x10e1f0ecf150f50957a950717913ff11, 0x1024050480ce1, 0x1014050480421,
      0x10440504814a1, 0x119e0000ecf0151f004ac6e612ef6b77, 0x3040c4318860, 0x100e7f0208f3e03e119f6b651f6b1164f, 0x304084310860, 0x14a100086d612efd610e1f0ecf57011ff,
      0x504084210860, 0x504084210860, 0x14decba0baecf70f3ff71179f1ae00070, 0x504084210860, 0x504084210860, 0x10464d864eb70000570b7831793ec4d1,
      0x1023000f6cc00102301e6003cfccf301e6003cc1f530003cc7981e608118001e60f31ed98001e611c64, 0x1b70b71140f252ff602e2f062e2f0697, 0x9040846108e0, 0x104a0e6e63bb700150c3bac80c80000f7, 0x12a2a188f0105ff604bbf441b3f4400, 0x1150e909e90912ff021bf428f39df0d1f,
      0x1110100c844c444760ca4ac6e6d60000, 0x8000a00028001400048010200410000c000403a3, 0x80012000480014000480102004100014000403a3, 0x80002000480014000480102004100004000403a3, 0x1652f5700e9ace9ce1ad21bf200f112a, 0x1084050482521,
      0x1024050480ce1, 0x10440504814a1, 0x12a7f3bcf00570571fd001b9a60360e1f, 0x88b000222c0002d907b2d194a1e608132943cc3db652840994a1e608132947980f31e607981e612d44, 0xc0002001f0000000440000001500000800000048000000440000002040000002010000403fe1e0400000082001000002000080000200801000f04004000004000008000495727, 0x1570002a7f001042df1104f0f1653f,
      0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x1ecb4307983cc00102307b2d194a1e608118003cc3db6528408c001e608132947980f31e607981e612d44, 0x3db3000f6cc003db3000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x11d5f0c40000fd0086b90010e1f0ecf, 0x88b000222c0004bf000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404,
      0x10232f11003dff0faf10faf136af654f, 0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x80004000201e100000018400000041000000504000201e100f00040000c200000020000800040008100f00040400000040009000080010201e0004080000010001200010004895726, 0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x80004000201e100000008400000041000000104000201e100f000400004200000020000800040008100f00040400000040008000080010201e0004080000010001000010004895726, 0x1ca275f866a86000001aff83e58302b4f,
      0x11656f0655f0069369f69369f1a913ff, 0x201008840800120004a0102004100114000423a3, 0x814058480421, 0x113df658f16af2f7f161f657f4f1f12ef, 0x1143f2ccf0f6f601f4102f17df102f, 0x1e6f3001e9cc00f3f303cc000f6cc00111600092a78f303cc0f33cc079f983cd8ae0f307980003cc3a45,
      0x109e909103f0276f312f0f3f119f143f, 0x142cf3a1fa636bf659f360f8f360e9, 0x10000f6095355f9512cf110f013ff65af, 0x11001b09990915df09d312ff70d9f115f, 0x1014050480421, 0x1957a950717913ff4611a6110,
      0x1014050480421, 0x1014050480421, 0x1084050482521, 0x1024050480ce1, 0x10440504814a1] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x12a5f3bdfc61c60e3fbb42eff608e8e0, 0x21009c87388e0, 0x136cf0dbf2e4f0dbf7700000f0fee2dbf, 0x117a0000156f0077177000000b7135fb7, 0x1e61045a5800097e0001e622714b079bcc00f3f31e70452de9cc0079802682967b660007983cc1e616b84, 0x80004222200000002800040002000000020004422200010010000040040000040100040042220020000020200400000200000284440020200000010800000100008000100029fe726,
      0x1138fb700dbf103f0dbf460000690690, 0x18469069000000000000ca000000b7, 0x113efc8d5c8753e1f501717c5c8c5168f, 0x21021084208e0, 0x11affb71d1d1b0f5f5010cf9414ff94, 0x1e5014ff1b391b0000010af17133f133f,
      0x11c0fc300f507407401c664f2f10af00, 0x183e583000f400000d61793133f83b71b, 0x18602d09808a8a012df74074000000, 0x13bcc015150fefe76007b0000008626cf, 0x19800dbfd4d4d43d0175f175f1cbfbe3b, 0x102f8f2f8f120f0dbf0c3f0c3f1c0f098,
      0x101bf38c0150bebe6c14af6c3e9f19ff, 0x18a047644764424f002b0093103f9301b, 0x1104c5f1c0f39af866a86202f2d198005, 0x2014042408421, 0x100204004040011000420100084020010800403a3, 0x1041bf38cb5150bebe539653fe76007b0,
      0x108a04764476465002b016021ef25041b, 0x1a439f528d60ebf0ebf00d5a7c83e2424, 0x10f50000000192f008608602d65bf9800, 0x10f600014ff009414ff940c8d5c8753e, 0x1becc000015076000000000c61c60120f, 0x800000202000000108000001020000001040006a00100000100400000400400001000400600000200200002004000002002000d4c00020200000010008000100008000101028fe726,
      0x1150b6bee8194fd4155fd4c40d6175fc6, 0x11b0000f500000093b79301b3d1b08c1, 0x80000080200000400800002002000002001000080008001440040004000040000100020040000080140000200400000200200010000010288000040040000100400000101408b5726, 0x1024240640fdf170f7f0c3093133f8376, 0x174a474742800ebf0ebf292f76d5a7c8, 0x17495eb9414ff9438cfc8d5c875000064,
      0x10ebf0ebf13138f13a7c83e2424007417, 0x1a30c886f33eb524005d3f5f5f5280, 0x10026ef2753765376680000960960ebf, 0x10652b00016f421ef25041b041bf30b5, 0x143432800ebf0ebf13138f13a7c802424, 0x14443960960ebfa386c8000024047d343,
      0x1472b43] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1285f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x124065255a9853b553fe77cb058a08e0, 0x15a0e4240146314632800013013a70024, 0x10d324014631463a5664c135f13d71313, 0x1138b0e2f0e4a40063063b50b50a30000, 0x1c61c6179fbb1f60140140a5964cb5130, 0x21009c87388e0,
      0x21009c87388e0, 0x100174f7704f3f00caee77192f0f3f, 0x1156f007717700000411fb72f4fb70f2f, 0x4400020889000080004000000110000000100800000904440004400000004020001004000008010444040000040040000088000000420888004000080010200000010000ca5726, 0x1b7007e1dcf460000000010004f4f0f2f, 0x4400020cb90000000840000001100000001008000009065c000440020000402000100000200801065c040000040040000080004000420cb8004000080010200000010000ca5726,
      0x10021df2ccf000ca00000000b7192f, 0x1495384538468cb0524000001e7f1cdf, 0x1002884bbcb133613a74902424065275a, 0x1140a5664c281312af13135a4ee44e000, 0x100000f384bbcba3dbd4dbd300240140, 0x10140140a5964cf313013540e2f0e4a4,
      0x110daf0d150f1aff83e5830e3f0d9f157, 0x21011886308e0, 0x21011886308e0, 0x119dfb9120ffc1140fa6150f3601d5f00, 0xd011886408e0, 0x119df65cf29bfa610d360f8f3600000,
      0x2010850440421, 0x1140fa91f7fc40000950950110f7911cf, 0x11cef1065df070000086b936dffc0f3f, 0x2010850440421, 0x18cb51509509501affdc11cfdc65ef0a6, 0x1b43b4901515016250cefb404840484f3,
      0x1b4b40cef4ed74e000003dbebbcbb42a, 0x1d4dbc40015095095018791fef3db40a, 0x1b46712af0d7070000058be58cbc6101f, 0x11140f252ff6095095018881fef58b40, 0x21011886308e0, 0x1ecbbbb143f9c01f60f7b7ecb7bac81c8,
      0x21011886308e0, 0x100800a2000814020402010080504002100082da2, 0x1103f0f3fec000000000001133f4cbf8c, 0xd011886408e0, 0x1133f4a8cf7bbd813bf9900f600000100, 0x1e6f30079bcc00f3f3003cc00f3f3003cfcc007a730f303cc3cc3cc0798f3000f6ccf300f3000f30ae85,
      0x10125fba169fbaecf70f70ce0000000ba, 0x1b72d9fc8135fc877140f2f9ff600c000, 0x1bb2f9fee1143fba0f6f602cdfb7159f, 0x9021084408e0, 0x12f9f1c9fba2a9fba00000103f133fbb, 0x1f600000135f065ff103f135f0c6f1ebf,
      0x1ce000004d133f4abbf7eed813bf9900, 0x14d663f4d662ff7661ff72cdf0660f, 0x11b0a1b1eff16df0ddf1fbf000002d9f, 0x1ab269f9c010ff1fbf00dff7cad0d9f0a, 0x19c10ff9c00000145f175f2d2dab664f, 0x10145f0d3f1a6f145fab0e5fabab1c2f,
      0x16c2d12bf117f9d1bbfeb0038af03c03c, 0x1ab12bf2e3f010ff10df000006c175f, 0x139f503c03c0145f112f1a6f6cab1a4f, 0x1291d4e01f50b9940d1f94b9176a1713e, 0x21021084208e0, 0x100800820020100804020100804040021000825a2,
      0x1115fe500039000000117179fbb115fb7, 0x9021084408e0, 0x1b7e611bfc300f5000001c0010af29df, 0x1b9235f83e5830f40000000d61793bb83, 0x100866a8602d09808a0650000236fb90, 0x10159f008608602d098000105f0000d1f,
      0x100b7159fb70c80c877140f0f60007b00, 0x1fc3d0001b7fbea63b0015150fe001c9f, 0x1000d4d4d43d0000be03b00151506a06a, 0x1098021dff729df00b9001b7f0a603600, 0x101500019ff004a333f4a01b01b7b16df, 0x1011cf011cf00250d125f0bee5bef38c,
      0x12d057000000930d1f930be0bef38c015, 0x11d0039f506400110f0000d0083e5830, 0x1e583000006495f495951c000199fc8e5, 0x12d1980058a0951b95e90000199f83, 0x304042408421, 0x18df60000011cdf0d1f00866a86201f,
      0x40800820040011000420100804020010800403a3, 0x19904e0d4f130f18df058c858c877140f, 0x1954e18003db479b4b400d70053fe0, 0x10666f1b2a1b7b16df26cf9805395665f, 0x116df0ddf1fbf00cb0cb1d7f115fad, 0x11500000d9f0dff7cad00a1b0a1b1eff,
      0x12406508408416250d004be04bef38cb5, 0x100e42401463146328000131e13a70024, 0x1a300000024014631463a5000131e1313, 0x196001301300e2f0e4008463d36318000, 0x14da306a86f33e392408a0146614a4a5, 0x100864f5f8602d19800a4000d6155f,
      0x3b9aca0001ebbd0280007aef40a0000fd51da8000218711a0000430e2403e00b64dc500ee6ee1acaee6b2f735b1cd650ee6b283b9ad8e6e3780265bb34135940773770d6500ee729b59401dcda09ae27c01310fa729b594003b9acbdcd73e6b281dcda09ca6d65000eee2675afe2e8, 0x1155f940766a7603e39f50000000192f, 0x10000000f700c60c60120f1f600000094, 0x80000004200000040800000102000000101000008008001040040004000040000200010040000080140000400400000400800040000004280800040000800101000000104008a5726, 0x1000000d622ffd60766d7600e1f0ecf57, 0x10e8148fd4159fd4c40d60c6be0000015,
      0x10019ff004a667f4a01b01b7b16df098, 0x1f500000093b7930be0be08c16cf150b6, 0x1024064114f1712ff0c30930837600000, 0x1000000006495a495e9f4000a3760000, 0x1a77b3e2424009517951f2ff49409486, 0x15886f33eb524005000028b90d013013,
      0x1360e1f22bf57068d30000b900a30dbf, 0x1570530db0fc1a7fb9ad0668f76a676, 0x1005386ec000b9006b766d7610e1f0ecf, 0x8800220020104004020900804020020800825a2, 0x11a2f074074016250f4040040f30b5, 0x10dff7cad00a00a111f1eff1faf0ddf,
      0x10000fbff71d1d00f5f5065270000d9f, 0x10028130e5f131300e4007443744310af, 0x1c34349025083cb00000f50149a1406a5, 0x1a4a5960c3130cef13540e2f0e4008443, 0x1146614] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1285f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x166af42ef669f42ff42ff0f608e8e0, 0x1430f4f7f66df4f6f4f6f66cf066bf, 0x100003bdfc61c60e3fbb66ff430f66ef, 0x44000000110000000440000000500008000600020000100080000400200001000400040020200000022000400002000000280400020200000010800000100008000100029fe726, 0x10002e5f00b70b700dbf0029ef00077, 0x17e9e010bf010bf00016bf001114af,
      0x44020000050000000400100000400408000600020000100080000400200001000400040020200000022000400002000000280400020000800010800000100008000100029fa726, 0x799e601e679803ccfa983cc1e601e67980798798f300f33cc03cc0025f8003ea60007987981e616824, 0x1163fb70b7408f0dbf0019af000460fbf, 0x100474f111cef249f1a5f344f40cf0, 0x20fd33000f6cc010323000f300f33cc00f33cc099d173303d3a75046079879bcd6cfa733cfcc003cc3a45, 0x88b000222c0004bf000f560ecbcde60079f98f30983c1307983cc002321d979bcc007980f31e616b84,
      0x12a5f6e6e98002d9f034ef1faf28cf, 0x19aee9a0fcf0c6f0c6f166f0000c3f, 0x11f1f47bf0156f36df2dbf77177019bf, 0x1018042440421, 0x1120fee6eeb98069314f69196f17a263f, 0x104804a440421,
      0x11f9fca0cc9a4d9a00c6f0166f6b00, 0x10263f0274f0e8f35ef0e8f0f0f10df, 0x114ef164f24af9e0f5f5069eb69eb1c4f, 0x10e8f0e7f0e7f314f0003f8f6b4a9f6b, 0x100f9201f971977701b6f001d1d8424af, 0xc00000203000000208000001002000002080506000000418000005040000004010004000700010001c0002000100002000100080000020200000080800000102000000102818fbd26,
      0x1140f1b6ff60d4d40e7ff70124f290e3f, 0x110af099124f290e3f000201f9709777, 0x1000171d1d08cf5f500c5168f74437443, 0x100431f186f224f000fff0000010aff6, 0x10f7368c15f50012cf3bef12cf00021df, 0x13b3bc80151507500930c311ef008317,
      0x13bc800150d5954495443d07ed82ccfe6, 0x10c3fcc0989801f744b744000d8f7e6e6, 0x1ebc1307983cc001023000f300f30f300f379809a3f8f303cc0f4e60079f983cd8ae0f307980003cc3a45, 0x103c9a3c9a19ff00f2f0f2f4f8f6e0c3f, 0x10e91e9185f007e27cf002a150f7b000, 0x3d398007a73001e9ccb645b20798f301e60798f30f4e9cc003cfcc00fa98007b66001ed98001e631464,
      0x1ae0f7b70d8fb7bac80c800000140f1f6, 0x3db3000f6cc001f53007983cc1e62d903cc7983cc0f30f303cc3cc102379801e7e6007a01181e816e04, 0x1283f0c4f000166f002cef150f138f00, 0x110af182f66e5186f7b039f609400c4f, 0x1e583138f00009474670f74b91c0187f, 0x1015150c574097409186187ff422ef83,
      0x35280f379800f33cc079bcc000f6cc0011160009a4af3303cc0f4e61ed9f983cdc7a0f316c80003cc3a45, 0x13b76000e3f000000ec0ec01faf00fff, 0x11d7f006e4f9fd81d7fd87b0214f003b, 0x1186f186f169f00fff0fff06b4a15ef4a, 0x1188f481f1abf023af23af218f2f5f, 0x100d81d7fd87b16df0980e6e6188f19af,
      0x10fff015150954495443d04a15ef4a000, 0x10000672f190f114af337f1faf671f, 0x87804a410421, 0x10d82ad87b0000b43b764faf00e3f673f, 0x17b16df0980e6e6b40fd15ef185f0006e, 0x10954495443d0015ef185f00000d82ad8,
      0x101faf1001a7f0001dcf00fff9e0f5, 0x20800820020100808040101004020020800825a2, 0x17ed8003b3bc8ec15150753e0f0f0283f, 0x1e6d80003bc8ecec150d5954495443de6, 0x10000f1f2aff0f1f4fbf0044b744f7e6, 0x1f5f500e8f0154f236f164f28cf0038cf,
      0x17b001bff0000010af17001a7f01d1d00, 0x10fbfe6f50e90e9185f007e0002a150f, 0x1312f135f980070930432f170083000c3, 0x1094eb01bef0144f1bcf0010ef000120f, 0x1074b91c66187f10af00e507b1b6f39f6, 0x174074000187f0083e583000f409474,
      0x12dbf86674f86ee2d2def9808a8a012df, 0x1f3021cf00fefe1719bf4a7b4a1f1f000, 0x1d4185fc6932b930daf00f9283fd41d4, 0x400000201000000202000001002000002080506000000418000005040000004010004000700010001c0002000100002000100080000020200000080800000102000000102818fbd26, 0x10daf000283fd40d4f38c21cf15015bf, 0x12d1980058a047644764424f0932b93,
      0x1018042408421, 0x1fe173dbf5c7b0d6f10000866a86233f, 0x80600002001000002806000020008000028000640020000100080000400200001000400040300200000402000400002000004080600020000800010800000100008000100028fa726, 0x1882b251600f904d404d4f30b50053, 0x100004d404d4f38cb515015bfd4531a4f, 0x1573e242408a047644764650882b2516,
      0x198021dfa439f5280f6f6223f0d5a7, 0x10ee4a192f4a0000ee86676f8612d675f, 0x218042408421, 0x110cf947b94007b013efc8d5c8753e1f5, 0x218042408421, 0x12effb70014af0391fc61c61120f1f60,
      0x218042408421, 0x218042408421, 0x301810070000c0004200800c400401810060323, 0x129af93100f9b7d41d4000001d2b2fb7, 0x85674030004010080002000100040000400040000200100000200200001000200002850702000040002000002010000400020080004003a00000002800000012000000040003fbd27, 0xf3001e7e6003d39800fe645b20798f301e60798f316c83cc0f303cc3cc798007b66001ed98001edc9464,
      0x12807e7e223f0d5a7d8024240d4e8b793, 0x10000b7d40d418c0150187fa4187f187f, 0x801020041004040080408010100800210008a5a2, 0x19410119ff13ef0d53d750000b793093, 0x842042480421, 0x842042480421,
      0x1013a7573e2424009464b664163f941c, 0x10186f33eb524005d3f5f5f5280f6f613, 0x80112000900014000422100884004010100403a3, 0x197770000531d689620bf961f1f0000a3, 0x102424053f7ec677f290000d8f4fcf971, 0x600000201800000206000001008000002080506000000418000005040000004010004000700010001c0002000100002000400080000020200000080800000102000000102018fbd26,
      0x1015bfd3d8d8d82807e7e130e9f13a7d8, 0x1479647276596096016000a300000024] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10d6f02f1f10ef1164f14cf9e00c5ff50, 0x2018050408421, 0x10017ff0131f27af02ecf14cdf0d6f0, 0x4010100500024000804800100808020200805a2, 0x1067af1679f4fdf678f4fdf022ff02c8f, 0x16b8050412de1,
      0x11101f0167ff67ef67df01067cf67bf, 0x10020020910001400044010100400824020046ba3, 0x10a8050412de1, 0x2010850408421, 0x101224f280f101f00129f125f0e7f101f, 0x2012050408421,
      0x100e6f14fef0e7f14cf0e7f0267f0ee, 0x20528504214a1, 0x1293f4fef681f211f433f680f1d9f4fff, 0x1101f000125f0e8f34af17ff1fff0147f, 0x1000e6f14ef111ff11000001224f2cff, 0x20420504214a1,
      0x20528504214a1, 0x20508504214a1, 0x20508504214a1, 0x10e7f5d15d0147f00012faf683f682f, 0x20420504214a1, 0x218050408421,
      0x10e7f01aaf5dee5d10280f0000125f, 0x818050408421, 0x1211f101d9f4fff00e6f1684f0e7f14cf, 0x1298050442521, 0x20010800500024000804800100804020100805a2, 0x10e8f5d198f5d0147f293f685f487f,
      0x1022ff5d1cff5d00004d4f0129f125f, 0x104e0f0687f00e6f14ef111ff686f27ef, 0x298050442521, 0x1b51500c5c518cf147f232f688f2e7f0, 0x1150e400930de15de1504004150ff38c, 0x1000c3198f24af235f0800822bf2e8cd7,
      0x10128f3db4e6b4b42e0d71bff01354fa0, 0x114cf980c95d137a25ff0b25ff128f, 0x10b500c90000ba1b434f1b0005d116df, 0x100044001020100804100100804020020800825a2, 0x10a87a9d939dde0de0faf04cc04150ff3, 0x10ac9d0b9dc301bcf0faf08cc0800000,
      0x11d1f01d1f1d1f585a5858146f08d9b, 0x1e41500f6f12dfc5124f3bff0dcf25df, 0x13db40b4b42e334fd71bff01354fabb, 0x1f3334fb51bff013000b0128fe6128f, 0x1e6980c900930de1bde109f04004150f, 0x1000128f1b128f109f080080fbfc30fbf,
      0x19dde0de004004150ff313cfb5ae0c90, 0x19d0000080080fbfc313cf0ae0a809d93, 0x101d1f01d1f207f5e05e0790790009d0b, 0x118b201f144f689fae0242400f6f000, 0x4011910070000c00044008100400401810060323, 0x1a7060f0f123f169f123f000068af142f,
      0x1356f0ee123f299f97a6093602cbf0013, 0x10097a609360e1f05700909132d76d676, 0x1d7f50240ead343434328076d67600ee, 0x1ae0d744d7440009a890068b12af8c, 0x10000500f142f68bf8b2e2f144f2a9f, 0x10612af8cd715010df123f0cbf123f,
      0x198012aff468df9a000089142f68cf, 0x10c4f10c4f0000111c6fdc11cbf105f, 0x218050408421, 0x4400110100424010084802010808020200885a2, 0x16b8050412de1, 0x1298050442521,
      0x101123f501f970e6f0900000b41c6f, 0x8420504814a1, 0x1060000f5009b4357f76322f76435f, 0x1570436f440c4f441800c4f9a89311f, 0x1000007607600000970e6f0900e1f105f, 0x1064318f418018010c4f891a0f502f060,
      0x8420504814a1, 0x1ea7a43] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x18e] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100097670c4293f7768efe6150cb058a0, 0x116000040040f384b584053fe8d448d44, 0x106f606000a9860460004957053025015, 0x10ddf06000a9bd04615a05a36ef026cf, 0x218048420421, 0x100d4fbe00c6000c40d6fd41500ddf06,
      0x1285709713013a7982a0f24240658d08d, 0x16609713013135a68ffe424014631463, 0x197a30f4136f250d6fd324014631463a5, 0x113013208f0e2fd7e4a40b563b5630b90, 0x1149614b5a5000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1f799f70503f184f00c6179fbb1f60, 0x4bf000222c0004bf07980f31e600044580f30798f303cc3cc0798003cc1e61e60f307981e61e619764, 0x1000f3fc60f2f12cf0cbf12cf00002f5f, 0x100b70b7411f0dbf003bff0007704f3f, 0x17e9e0000010004f4f0156f0077177, 0x1400000009000000044000000050000000408002808940448000400000010200010004000080014044400040000400000088000000428088004000080010200000010000ca5726,
      0xc00000009000000044000000050000000008002808940440000400000010200008000000080014044400000000400000080000000428088004000080010200000010000c85726, 0x1163fb70b72aaf0dbf0019af000460fbf, 0x1262f10cf0021df000690fca505f504f0, 0x1166f0000c3f192f6e6e98001cdf04a4f, 0x16eeb9807719bf9aee9a0fcf0c6f0c6f, 0x1cc9a4d9a00c6f0166f6b011ff120fee,
      0x1ca] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d4097830c3f7846b3bf5068cb05240, 0x10d4097830c3f7846b0f50533643a943, 0x10028840013013a700242405386432543, 0x10d8123f0000bd04615a05a113f000, 0x218048420421, 0x1f3000168400a3000d30d6fd42401eff,
      0x1a9060cb0d8860460e3f4914ef9857065, 0x19aa56602813013135a691fe45707b06, 0x11eff13540e2f12afe4a4027141cbf14, 0x1149614f3a500013] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100e8f2cef0e3f336f27efae00d9f1570, 0x4800120100404010080802000804020100805a2, 0x1830dbf0c4f174f0c4f01ddf0166f14af, 0x101c6f0437f0341f001f9f00000083e5, 0x100b90fc0cc0010a60360000202f1c6f, 0x3db3000408c00102305c52a27e0f6cc1e60f30f30b8a34c001ed980079f9807987980799e601e612ec4,
      0x112cf112cf000010eb10ccf00ccf0f1f, 0x218048420421, 0x228048420421, 0x28804a420421, 0x1186b90fc1cc000000c4287fa9ae0202f, 0x3db3000408c00102305c52a285983cc003db30f30b8a34c0f307980079f980799e60079bcc01e612ec4,
      0x3db3000408c00102307985b21e603cc7980f30f30f4e9cc3cc0798008127307b660007983cc1e612ec4, 0x10174f00e9ff70990d9f150f209faef60, 0x121df10a610ccf360f8f3601b090c3f09, 0x218050440421, 0x628050440ce1, 0x1209f10dff60950c4f950c4f110f790,
      0x1090c3f090196f00e9ff70990d9f0daf, 0x1dc0000693f0a62cef136ff692f0701b, 0x218050440421, 0x195dc95] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1d7151600cef49040041de68cb5f50240, 0x100002f5ff718aff732df144f1ae0d7f4, 0x418042408421, 0x1004840484f38cb5150694f11ef184f0, 0x113cf1cbf198012af250cefb41600cef, 0x418042408421,
      0x1cbd400000d313cfdb12a10100866a86, 0x418048420421, 0x418048420421, 0x418050440421, 0x10b5f50d4a36ab96a0e6f101f5ff9dbd4, 0x442048480421,
      0x101feff41fefbb1600cef490449041de6, 0x1b5006ab96a000000d40d400e1f0ecf57, 0x10463182518b41600cefcb04840484f30, 0x10463] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10390000001f6001172a1d08c3b9ff500, 0x222b0d07983cc0098d3086ff28f379800f6d3989baa29303d3a74e6007980f737f9502300079803cc3a45, 0x500a10210860, 0x10f708c0ecff5000001ca9010af01e500, 0x3db3000408c001f5304d5e6607981e6003db30f309ab9f30f3079800798f307980f31e607981e612d44, 0x18308c2a7f57000930c311ef0e3f08317,
      0x1fcd8c6e6c4000015000001f4036083e5, 0x504210210860, 0x16a06a6dec0d9fc4000000c844d644760, 0x1447604ed8c6e6c4000015086b96d695f, 0x115df06b0e9ff70d9f990000f60c844d6, 0x13e09c0f2f6b6eeb00009801b09115f09,
      0x100ccf029ff6ceb0000000dbf9a4d9a, 0x1c80c800001140f252ff601113df00ccf, 0x842048480421, 0x882048480421, 0x1f53000408c001f53003ccf300798079bccf307983cc0f300f3798081366001e60f31e7e6001e704c64, 0x11ac2a107b105f7b0941f7b70d8fb7ba,
      0x2139f307983cc007a730079800f379800f6cc009a3f8f303cc0f4e60079f983cd8ae0f307980003cc3a45, 0x100010000800040004000100004000100040400028081400010004000001002000100000200800140404000080004000008080000010200000040800000102000000100048b5726, 0x1024050480ce1, 0x18394e912cfe912cf12ff01f3f341f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x12a9ff6001c9f4e000fc97140f0570150, 0x10000000000ec279fec01faf00fff00ca, 0x100b7159fb7001c9f00c80c877140f0f6, 0x1d800000c40000001006b06b0218f09e, 0x1e601e61e601e6798081185b21e603cc7980f30f310233cc3cc079803d3a7307b660007983cc1ee246c4, 0x1570e6c6119f4a19ff4a0006e3c0fd88c,
      0x10276fca276fbb0004e23ef9c1fc9700, 0x20080802004010100404100104100104000423a3, 0x1000004a19ff4a00000d80d8016df098, 0x1044d64423efb71b7000bb23efc81c877, 0x20100804004010100404100104100104000423a3, 0x20100804040011000440101004100104000423a3,
      0x11f2f4eef103f0bbbb08c0143fba0f6f6, 0x11f2f133f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10000010d6f000866a8602d1980058a0, 0x480412000140009004002200080402010080522, 0x480412000140009004000200080002010080522, 0x1fe18df4418df44770e697670c4000015, 0x1119f062906c80499d86a946000057053, 0x100ad06ad06cb049a986f946000057053,
      0x1b5150ad06ad065a05aa9bd113f460000, 0x1002424065025001684084040040f38c, 0x11300e424014631463280bb9713013a7, 0x1b9f4000024014631463a504c97136613, 0x11311300e2f0e4000d630d63250d397a3, 0x8c40584835a1,
      0x11496149aa51a4f4ca4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x11001000120f506f0e3f9803e39f50, 0x20800820020100810080102004020022000825a2, 0x20800820020100810080102004020022000825a2, 0x10d8c60c46b76ecfc150eb01bef0696f, 0x16d0000000c406a31ff6a00044d6440e6, 0x10044d6440e60d8c60c46b76ec01500b9,
      0x10460290244f1b0f0086000a92ccff757, 0x100390000003fef1700697f06a1d000f5, 0x1c30fbfe6f5000001c0010af698f86e50, 0x1120ff41b7f9e007093013df170083000, 0x17b0940000148f1b0f00480f83e583, 0x1094e90e9012ffac00002a0155f7b105f,
      0x1c4b900188f1b0f006b000031ff00] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1240050000285700138413a703e242400, 0x1f5068160160d30d6f00a384086f33eb5, 0x1f50531a7f433d438403b9783d4c30000, 0x100f605386432543840499783d4c30000, 0x10000018af0919ff09cb0ba7ef7f99900, 0x10ecf5700dff10dff05a05a0bd2a4f460,
      0x842048480421, 0x12865507fb90f7f14976076f900010e1f, 0x20800820020100810080102004020022000825a2, 0x20800820020100810080102004040021000825a2, 0x1140dff143da504c281366131300e4570, 0x116a5184ca4130dff13540e2f0e40027,
      0x1149614] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10155f069af866a860fff2d699f9808a0, 0x186086ee2d69cf98069bfae105fae394f, 0x177140f2f9ff6019bf4a7b4a508f0000, 0x100fe2cdfb7159fb72cdf01c9f00c80c8, 0x10000a625a6fc00eb0e8f146e546f300, 0x4000400004000000020004000020000000e0006000040002000e0006000040002000400068000400180004000100004000400080000020200000020800000102000000102008faf26,
      0x100000c693ec93000f9325fd436afd4f3, 0x10e50f38c0150d40000000119f083e583, 0x10000d40d4f38c4c1f1500250000000, 0x183e583135f2d69df570093093484f, 0x19564509f103f110f103f438f000509f, 0x1e964] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1000a117f0a8b1eff144f0ddfae0e4240, 0x116df0ddf1fbf0335f7c439f11ef0dff0, 0x17cad0d9f0dff01c2f00a1b0a1b1eff, 0x10d8fb497b49712af0d70013132e3f, 0x1010ff10ff09713112f881ee618069ef, 0x1120f145f014df0fcfab134fabab9d,
      0x197b49712af0e1fd757011cf10df11cf, 0x114631463a50881ee618000b4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1105f196f0004ea306a86f33e392408a0, 0x1192f4a0000ee8623df8612d198025a4, 0x218042408421, 0x218042408421, 0x1940d1f940000b9176a1713e39f50ee4a, 0x218042408421,
      0x1b7f7b700000dafc6f7c61120f1f60b9, 0x218042408421, 0x218042408421, 0x1bb9310188ff9b7d4bbd400000a40daf, 0x842048480421, 0x10100ccf4ea34e6a0000240d4e8b793,
      0x842048480421, 0x10930000b7d40d418c16cf15025a413ff, 0x801020041004040100808020100800220008a5a2, 0x112ff94100ccfbbb9176a1700000b793, 0x842048480421, 0x19464b664b994] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x19898160148f004570457f38cb51500, 0x1363f208f1a7f12af8cd7150e4c311af, 0x1b500138813540e2f668866233f000089, 0x10c311af3d166f160016bf049d049df30, 0x114df145fab1c7fabab9d2c6f10ff197f, 0x10890000000011cf10df11cf120f145f0,
      0x1149614a4a566886601800] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x100004f4040f30b500533b68cb052400, 0x113013a79c13ef2424053935705716, 0x1d42400def9cf5f5f528840fcf0fcf, 0x10f50f5168416efdb540bb101fd30d6f, 0x1f5f52884aeae13013a7989e242400def, 0x1f50840ae540f60fffd39e152409857f5,
      0x10000f810effacbe42400c5fb693f515, 0x1f81b8f198f43af198f000089f4001eff, 0x18425ff0fcfb40b4a79c13ef10ff240, 0x1281301313fa1d9fe49809c0226f00d4f, 0x10d6fd4240a8192f2abf337fc9128fc9, 0x1faa4e4de000001884222fdb000101fd3,
      0x11fcf10ff240a8000c94ec95d1301354, 0x10d8f1aaf0d8f0d4f8469ff0000a71d9f, 0x1c9181fc9281301313fa1d9fe498019bf, 0x16a0fd31fcf198f240a8192f435f1b6f, 0x1e49301b8f0d8f13df0d8f08400b40b4, 0x1a811ef368f26bfc90c9013c31354faa4,
      0x1de004004150ff38cb51500c50d0f18cf, 0x1000800822bf2e8cd7150e49315015de0, 0x1150ff30b50013a41354fac3024af000, 0x1000c9931aaf7a1aafde0de109f049c04, 0x100c9c3000128f0128f109f089c08000, 0x10342f1aaf251f8c3e2f13bf0cbf0251f,
      0x1585a58bc146f08d004d9d20cf9d208f, 0x1000000dcf0d124fa91d1f01d1f2aff, 0x19d13bf9d1050af1aaf0eff8c190f13bf, 0x8420504814a1, 0x128579898138413a7f63e242400c5a83e, 0x1548412efdcf33eb52400515aeaeae,
      0x104f9f30b500533b680000d30d6f11def, 0x2012050420421, 0x1ba53931def3d1def164916ef4904f4, 0x176262f760012efba10e1f0ecf5700def, 0x2010850408421, 0x1144f138413a78c0242400def000049,
      0x15484144f0000240288c8c8c8c280144f, 0x124000f6fb6938c0e1f8cd308c144f, 0x1015000185750bf98588458a7f63e0ddf, 0x1a80790c9e6c92813d71313fa239fe498, 0x10d30d6f0e7f1def0840dc12af3ed7240, 0x10790c9a4c9f31301354fa3ee4150000,
      0x1f91f9002f1f10ef1218f14cf9e0a8, 0x2010850408421, 0x20528504214a1, 0x141af4989f4113ff900000f8000022bf, 0x110e1f105f570c9baf81b8f0000dff49, 0x2010850408421,
      0x158a7000240c900004976370f76000ba, 0x10c9281301313fa0e4980000000005884, 0x11b8f000d3000b484b40000240a8000c9, 0x10f6fa8000c9a4c99313c31354fa0e400, 0x115434343280989813013a7f63e242400, 0x1d343ee43000054012efdcf33eb524005,
      0x10fcf134913a79c02424053d3533b68, 0x105449000002400def9c4343432800fcf, 0x12400eab64306430defd3430431600, 0x1e498015434343180098000a7f63e0ddf, 0x10a80912cf09c90c9281301313fa239f, 0x1430e7f430000bd06a1fdc12af3ed724,
      0x11caff3c90c90132e1354fa3ee4150d3, 0x150cf1a7f2f1f10ef1218f14cf9e0a8a4, 0x218050408421, 0x149b4a79c00240f8d3f822bff91f90000, 0x1298050442521, 0x11313fa0e49809c4343430000fcfb4,
      0x100000240a80912cf09c90c9281350df, 0x1128f1354fa0e400d34304318000bd49, 0x1eaa84312cf43a8a42abfdec90c95d13] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 5) (a := [0x150ff]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 5) (a := [0x152bf]) (b := []) (by decide) ?_
    decide +kernel
  · exact SearchNode.check _ 4 [0x10000150feb0daf157bf0c60149f8e0, 0x28820240a121, 0x1ceb71b70f7c60cbf11bffae107ccf, 0x28820840a121, 0x28820240a121, 0x1008202442121,
      0x13acf10771a9f9e143f107cdf0000143f, 0x1008208442121, 0xf300003cde600f3007981e61e607987980f300000f303cc3cc0000798001e60000000003ea60f33505, 0x177177199f07cefec00156f1ce0daf, 0x1e76c80f31e611176c816c800097e0f39f78000799023b64f6cc000f303cc0f31e60799e600f31e619824, 0x1e76c80f31e611176c816c800097e0f39f78000799023bdddeec000f303cc0f31e60799e600f31e619824,
      0x1000000010184f143ff7b711bfb700e3f, 0x1e9e80080799e7e60079f981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a73088eb65, 0x1b701ca301f00000100150fcef71f7046, 0x4c820241a1a1, 0x3e80080799e601e679f981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a73088eb65, 0x1e6b640f31e61116b6416c800097e0f362b80007984bf62bb15c0003cc3cc0f31e60799e600f31e619824,
      0x110000077ee0ee10dbf0ee00000b71, 0x10008400204010080500814000402020080807a2, 0x810860108860, 0x1e60000f31e60f33cc00f33cc079bdb30003cc097e0f307983cc1e60003cc0f31e60799e600f31e619824, 0x1ee0000f7b70b70077177000ec00156f, 0x1e60000f31e60f33cc00f33cc097e0f30003cc097e0f307983cc1e60003cc0f31e60799e600f31e619824,
      0x100000f70f70460fff7e0fff10dbf2e2f, 0x810860108860, 0x1a7b654051501981981ca01110cf07cff, 0x210860108860, 0x214060108860, 0x210860108860,
      0xf300f31e60f30f3016c800097e0f3079800097e0f307983cc1e60003cc0f31e60799e600f31e619824, 0x2008080300014000500804000402020080807a2, 0x1530000101ccf0eff49766d76111ba053, 0x2080a0240a121, 0x100004000002404010002100084002000090081a3, 0x2080a0240a121,
      0x208220840a121, 0x1f52800fcf0fcf13134f13a79c024240, 0x1f50f516000d300054002400def9cf5f5, 0x1f5280aeae13013a7572a1f242400def0, 0x1000aed301549542f4ff62405798f5f5, 0x11a9f01a9ff7c61c608e8e068f3f515f5,
      0x208202442121, 0x153ef1d0c5168f273d7f983d7f9810100, 0x808208442121, 0x808208442121, 0x11d1dc5750b90101143f163f94d594fd0, 0x2002208442121,
      0x2002208442121, 0x18a12df7515b9150000094d5940f701d0, 0x1cb042504158d84b58408e00cdfa78a8a, 0x119800000000f7c60c60f30f601600cef, 0xf300f31e60f30f3016c8003ea600025f8003cc04c0e60222c0003cc3cc7981e63cc1e607981e619824, 0x100057cffce5fc0c3f83302f8300c198,
      0x1e600f31e60f31e6016c8003ea60004458003cc04bff30222c0003cc3cc7981e63cc1e607981e619824, 0x1946a94b9171170530c3ff60c3ff62f3f, 0x2080a0240a121, 0x1b71b70c6fc80c80530000100ccfbbb9, 0x2082208422121, 0x20412084121a1,
      0x1532553fe6c0058a07704d0000bb23ef, 0x100000946a9400000772424246505acb, 0x106505acb53275328168405840015015, 0x124246500053053fe1586058a08a6803d, 0x168f50f5650005327530f3005008a024, 0x13d8f0dbf3d8f0000c61c608e8e00cdf,
      0xa109605208e0, 0x1131e0f13a7d30242401c0f9809810dbf, 0xa109605208e0, 0x101bf50c5168fc8f5f5f52800ebf0ebf, 0x11717c5015015c3093133f0fdf17a6083, 0x11501510cf9414ff9400d500c819dfc80,
      0x1040084b58408e0285f848a8a8a12df75, 0x10000f7c61c60f35705716250cef15040, 0xa109605208e0, 0x10d000e5008308300c19819819afee0ee, 0xf300f31e60f30f300f30f4e60088b0000f4e7e60fa9f9803cde60003cfcc01e7e601e63cc01e619824, 0xa109605208e0,
      0x12465000530453fea40058a00f60f600, 0x115015c30930114f176a08300f5002424, 0x1c806805706527013534953a7a4005000, 0x10982cdfb7159fb72d9f0135f00c82f9f, 0x10dff7cad0d9f0a00a001b0ddf1b07798, 0x10d1f940000b91711701eff461f01a2f,
      0x8121204208e0, 0x1ae53053fe086058a08a65115115b994, 0x4000000400200001040000010002000010400020000400020004004000004000200800002002000100008000020020000080004000004004000010040000100040000100408e2726, 0x8121204208e0, 0x149530530084058408a7724242465255a, 0x1ec24240c68e8e0285f68f50f565275a,
      0x10c5168f57f5f5f5280f6f613013a7d3, 0x101515c5759409400ae9800d50015015, 0x1c3159315120f17ae980000830fff57f5, 0x10174f18afdb18b024240f58a8a8a12df, 0x208202442121, 0x1f6013a7d3217f9e1fff9e10102e2f0,
      0x808208442121, 0x808208442121, 0x113360d601019e22af76a6760faf0455f, 0x2002208442121, 0x2002208442121, 0x136f6d6f60000076a676018af0f60f6f6,
      0x1fccaf6418ff600cc6248e057f5f5f528, 0x1a46a058a036b9aefc1dcf00fff000a6, 0x115f61501524242465042bef5753053fe, 0x153053a7a4f505f500940940009800000, 0x115753053fe01058a0156827571365000, 0x1ea4583cc3cc03cc1e60f324120007d4c0010231e616eaa581e61e60007d4c007a730007b66001e612ec4,
      0x2de3883cc3cc03cc1e61aa93dc710f6cc00088b1e616f23d80f31e60007d4c007a730007b66001e612ec4, 0x17d0f980000830fff57f5015242424651, 0x8000a0402104008101000840140400220008a522, 0x1f65305300f505f50c31593150fdf17, 0x1228f688a248a682702865497d1f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x153ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x18e] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c5f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1ae107d2f0000150feb0daf157bf0c60, 0x21820240a121, 0x21820840a121, 0x10000143fceb71b70f7c60cbf1359f, 0x21820240a121, 0x1088202442121,
      0x10daf4bdf10771a9f0fbf143f10358f, 0x1088208442121, 0x4000100900404010020100004000400110081a3, 0x1b7017716ff77000ec0016ff7d3f0f0f, 0x4a82104529e1, 0x11f704600000001015cf143ff7b711bf,
      0x1e9db5d907983ea6000fa981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a7308ad165, 0x43820241a1e1, 0x11b701ca7d4f000001016ff150f14aff7, 0x3db5d907983cc1e60fa981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a7308ad165, 0x4a82104529e1, 0x10010400404010080500814000402020080807a2,
      0x1000000077ee0ee10dbf358fee00000b7, 0x810860108860, 0x1ee0000f7b70b700770770044efec00, 0x1014aff70f704613cf7e13cf10dbf396f, 0x810860108860, 0x1348f7d5f06e1ca01110cf01f1f000,
      0x210860108860, 0x214060108860, 0x210860108860, 0x1468f7d7f256f0256f0000135ef7d6f, 0x1088210442121, 0x116e511f46af,
      0x2010080500014000500804000402020080807a2] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x126df1b111fd0131d0fd3108fe41a2f0, 0x100014020001400050002100044002400090083a3, 0x100014020002404010002100084002000090083a3, 0x100014020002400090002100084002000090083a3, 0x11aef0b5300f01300001056cf190fba1b, 0x100014020020400810020100804002400090083a3,
      0x1000c9e7000de0de1e0f04219f04302f, 0x10c90000128f0128f4edfc30002511df, 0x15dde0de004004302f35cf7d8fb5463f, 0x1000010255f36ff1112d8f0e75d3cef, 0x21821040a521, 0x21821040a521,
      0x21821040a521, 0x4b821040ade1, 0x157df2511df292f469f01235f7d9f235f, 0x109821040a521, 0x1fa2e5d43af5d0000c30111f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x16e18011cf0b40ab48d0ddf67d7f608e0, 0x101f3f001a9f01a9ff7c61c6012af6e7c, 0x218202442121, 0x11304b40e41d0168f273d7f6e3d7f6e1, 0x8482084421a1, 0x194a694fd001d00e2f0880a500013b4,
      0x1013b41304b454e4b40750b90000022af, 0x10021ff000000f70f700e2f0880a500, 0x104c0130136c0e5f8be41d003d0f03d0f, 0x100940940f701d00e2f0d8f880d8fa5, 0x1013161854e43d0750d8fb90d8f001a1f, 0x1253f863eaf8600e2f6e886ea504c013,
      0x18607daff90fbff9284f0002aaf010c3f, 0x4282084421e1, 0x1f93d9ff900007dbf0204f196f2dbf861, 0x29821044a521, 0x1f90000ce07b23ff19af867dcf8601, 0x1088210442121,
      0x1000199204f7b14ef86186024aff946af, 0x29821044a521, 0x4a82104529e1, 0x11385f3d9f385f0, 0x1088210442121] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x102adf000d8f00d8f14af8b1100c5f240, 0x8482084121a1, 0x218202412121, 0x1154e4040c5c5272aef1fcf169f1fcf1, 0x8482084121a1, 0x1000140204024000900061000840041001100a3a3,
      0x100f6f12dfc5fa000c90c95d131b131b, 0x100f6ffa6e06ec90c90130130054e404, 0x1057ef07ddf186f298f14af337f324f, 0x1bc8d0a01b6f109f34af109f249f07def, 0x157ff167f1d1f01d1f058058460f7dff, 0x1161f00e3f319f201f14af000146f167f,
      0x118cf1109f7e0f109f0000, 0x1088210412121] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x11801fefcbd725d70294f840ddf8408e0, 0x108300c06e06e00000000f7c60c600000, 0x17e1f209f00000c3ffc302ffc0c3f83, 0x1bbb9940e6f94b9171170132f3f209f, 0x10000c020001400050001100044001400050081a3, 0x1b7103fb70c6fc80c80130000101a1f,
      0x1001040200204008100201008040204008100a1a3, 0x1254c0182f0d78a000000021ffbb3eef, 0x100000940e6f94000000000a504ccb4c, 0x14ccba527a500dff84d784000d8f00d8f, 0x1f900000000c3f253f8608600000a50, 0x100007e3f0ab327f7e2f8608a00f90fbf,
      0x10ce07b23ff19af8608600e2ff9468ff9, 0x100e2f27001eff00001ccff9550ff9000, 0x10e2ff9365ff9000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1764a493daf10c5a7270d0f0c5f530, 0x1001040200204008100201008040084002100a1a3, 0x15d005130c500001023efdbd676129f, 0x1001040200204008100201008040084002100a1a3, 0x100f6f680000def00defba53db530c3f, 0x1051300f6f0000c90c9bab60001301358,
      0x1f90def00def053053174f253f14af, 0x1102f1f232f7e5f482f7e4f0068f936ff, 0x4a82104129e1, 0x12b1f1314af13001236f7e6f236f0000, 0x1088210412121, 0x118cffaf945cff90000b60201f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x106e18103f580f8db40b40067d7f608e0, 0x10dbf00dbf14af03d8f00c61c6012af6e, 0xa109605208e0, 0x100ebf0a1e0f0aa7d3002401c0f6e06e1, 0xa109605208e0, 0x1299f170e6f08301bf5013168fc800000,
      0x11301300c8e4c8017130000c3093133f, 0x17e7fc800e2f0d8f00d8fa5175f1133f, 0x8121204208e0, 0x10750d8f00d8f2faf94581f9400000c8, 0x10e2f6e06ea518582f16130130054e43d, 0x10c6f7e8f2f8f2aaf0100863eaf860,
      0x775366fb830dd4d8594003b9acbdcd66dd4d85940007735b1dc8ec0dedaca01dcd82cd653b9b059aca10c38c89aca077360b35cf9aca07736826b2803b9e83aca07736826b28077394daca00ee8361ae132f143a5f7f44b3150300735947735b1cd65ee6b28ee6b2f94e7adff89, 0x100f2f0000000860860202ff90f9284f, 0x17b2f8f000019af863d8f8600f90f9, 0x18424aff90f9ce0c6f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x157000280f6f6139e13a7d30242400, 0x1e4160f0000000006700a7d3002400c5f, 0x10c5c5fa000c90c91a3f137e9f1313d30, 0x10000c3093109fb41bb43b128f0128f0, 0x1c91bc91b130130054e4de00f6f12dfc5, 0x157ef000014af337f000f6ffa6e06e,
      0x150df01b6f109f0109f249f190f01def, 0x10167f1d1f0f2f1d1f05805800bc8d, 0x11def0000201f14af07eaf0146f167f, 0x118cf1109f0109f161f190f0e3f, 0x2010080480012000500014000402020100807a2] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x15d05dd725d71e4f00000840ddf8408e0, 0x116e06e19afee0ee0000f7c61c6012af, 0xa109605208e0, 0xa109605208e0, 0x1008a00209f0209f0000000008308300c, 0x1172a08300f500000130130130a130ca,
      0x113b4134913a7ca00000000c3093023bf, 0x1b7103fb700004dc87ebfc8000001327, 0x100000e5fcc294fcc02cdf0faf00faf4d, 0x1170230f236f0236f11cf112f11cf1b7f, 0x10a510d8f00d8fb99421bf940000b9171, 0x8121204208e0,
      0x8121204208e0, 0x10c6f7edf253f440f07ecf0086539f86, 0x1f9025181f00000086d78a01f90f92aaf, 0x1814320c209e0, 0x17b253f000019af8646af8600e2ff90, 0x15a490000084d78401ccff90f9ce0c6f,
      0x10e2ff90f90e2f27] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x11131d0fd3108fe4de00d0f0c5f0def0, 0x100014020002400090022100084020400810083a3, 0x153a7a4005280fa000c9128fc9232f13, 0x1a7c90c900c5680000def00defa75376, 0x1231f100f6f49c50000b6093fd137613, 0x2121204208e0,
      0x10f6f1109f0109fd676370f7600004a49, 0x8121204208e0, 0x10def101f0def13ef530530014af05280, 0x10000000000b00b1d0fc3000068f90f9, 0x1f9b6101f201f13ef0000c914afc90d4f, 0x118cffaf90] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10dff010000a7d3ec153f240c6d78e0, 0x218208442121, 0x113001b6fe400168f24af7eef3a7f2def, 0x100000a60000000e2f0004a5004f7f130, 0x10583f251f130130054e4b4075940940, 0x113cf7eff01005d217f5d00e2f0004a5,
      0x3ca7047238146f73597b9acbdcf41d650430e237b9acbdcd65ee6b29dd11eaca0077447ab2801dcddc359401dd4d8594001dd4d85cf9aca07736826b281dcda09aca00ee7a0eb280ee6ee1aca00ee853bb9309dc5cb4195cd653b9acdb9acaee6b45cd653b9acbdcd65f0487576a09, 0x1f5010e3f0c6f00c6f27ff202f26bf, 0x80040002000040002800400020000400028000600020000800080001000200004000800040022000000028000400220000000240000020040000020200000100200000100029faf26, 0x10c6f37df17365f190f0000831e0f1aef, 0x135ef7f1f348f7f0f04aa5c30c6f93, 0x13b5f3d9f7f3f256f0256f00007f2f,
      0x114ef4a3d9f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d6f2818aff6f613013a7d3db242400, 0x11cef000a7d38b8b2400c5f570d6f0d6f, 0x1160f01a7f10ef10ef10ef671cef1cef, 0x11455fc90c91a3f1301313d3223fe4, 0x298210442521, 0x100c90c95d130130054e400c5c5fa7f4f,
      0x1109f0000013cf6c6e00f6f12dfc5fa0, 0x1105d0f6fc313cf9313cf128f1b128f, 0x1088210442121, 0x10d1f00d1f00007f5f0e8f3b5f0fdf, 0x118cf5d2fcf3b5f57ff7f6f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10000fcca209f361f209f00cc60cbf8e0, 0x1ca327f14cf8a036b9287ffc1f6f07f7f, 0x100000000130cbf13000a0284f13013b4, 0x1013a7ca19af24af19af009409400000, 0x113cf000005d7f8f5d01327130000013, 0x114cf8a00e3f0c6f00c6f7faf202f7f9f,
      0x11a4f7fbfa52caf1a4f284f0002c4f00, 0x117258f190f0000831e0f1aeff5010cbf, 0x214220140860, 0x100019af24af19af0c30c6f930c6f114f, 0x11c1f7fcf04aa527a518a549018af00, 0x12caf327f159f0159f000011c4f7fdf,
      0x1088210442121, 0x10e2f4a2c4f45cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10130131d0fd3108fe4e700d0f0c5f680, 0x1053053a7a44d05f60fa2e12defc90c9, 0x298210442521, 0x113a7fa4dfaf60c568d6eea70def00def, 0x1ba53053004d05f60c5b60000000130, 0x14dfaf600f6f68192f0192f0def760def,
      0x14a0f6fb60c6f930c6fc976c9ba0000fa, 0x1196f0b00b00001d0fc31cdf5c1e8f0, 0x118cf4a2fcf52df7fef] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10000db3e13edbcb565fcb00518bf00, 0x40101005004040100a2102084086412190083a3, 0x118bf0534d5318bf193f10d6f13d1f, 0x1018202442121, 0x1018202442121, 0x1023ff23ff13290f13303f160f018bf,
      0x10d300db00def0fcf8422df22df1a3f, 0x118bf18bf00def084022df16000003aff, 0x122df1a3f01e8f1e8f13013303f160fcb, 0x14903affdbd3cbd4db0193f376f8422df, 0x1cb0e418bf00c5fb8e784193f22df0000, 0x110d6f1232f0000db3e136f3edbcb136f,
      0x1018210442521, 0x1018210442521, 0x111ef102adf002b6f02b6ff7cb1cb0a3, 0x218202442121, 0x818208442121, 0x100109f0109fec11bf110584f0d6f584f,
      0xa1820a412121, 0x218202412121, 0x1000000004dcb0cb00233f0198f102cff, 0x818208412121, 0x1002bafb40b4000018bf0b600d6f011ef, 0x100c90c91a3f130131300e4009b84000,
      0x1e4de008400180000000d300db0fa128f, 0x118bf0fa0502f0c90c95d130130a3a4, 0x19b847fff11ef1801000022efeccb0ddf, 0x818208442121, 0x1c90c91a3f13013130f3f11bfe4190f0, 0x1000049023dfdbd3cbd4db0fa1122ef,
      0x1018210442521, 0x1018210442521, 0x1130effa3a4e4e7012af84505f11ef, 0x1c5303f0cfa4e2d7f11efc90c90130eff, 0x1003e000db10ebf204f0c6fba0022df00, 0x100014000420400090020100804008400210083a3,
      0x1801f0105f03daf1800f010105f3f4f00, 0x2010a0240a121, 0x2010a0240a121, 0x14600fd490ebf9701014cf300f0000f9, 0x100014000402404010002100084002000090083a3, 0x11ca802ff94a4914910105f1fbf00003e,
      0x2010a0240a121, 0x2010a064131a1, 0x2010a0a422121, 0x1109f3e0000023efdbd676129f760000, 0x10ba0022df0110280f11effdcc1cc4d3e, 0x812208482121,
      0x1014210482521, 0x2012208482121, 0x1ee000000003e111ef803fdb10ebf204f, 0x8010200420402010020100804100404010083a3, 0x200108004804020900a0102004100414010083a3, 0x1022fff9159f0f2f159f03daf20bf1e3f,
      0x11026ff3e46000490ebf97db000003ccf, 0x80012000480404010080102004100014010083a3, 0x1c510804f43df1ca585f04a4914900000, 0x4142144835a1, 0x814218482521, 0x1014210482521,
      0x11fbf138413303f376f018bf18bf00, 0x10b51e8f005193f01e8f1e8f1a3f01fbf, 0x101fbf053269f0d8f0000d30049084000, 0x115df531010049049563fdb6adb860, 0x2014202442121, 0x2014202442121,
      0x14976262f76d60805f0eff000000def, 0x113303f13bf018bf18bf00def10126bf, 0x1014202482121, 0x1014202482121, 0x101ddf1ddf1a3f170f29cf29cf1384, 0x1b8e7000d3000084000000026ef1ddf,
      0x1000000463f5884584a00018bf000f6f, 0x1fa000c90c91a3f13d7131300e40012af, 0x1e4160f00000d3004908400c60d71e8f0, 0x1760f3f0100fa000c9a4c90130130a30, 0x214202482121, 0x1c60d7000003e1db23ef37af4a7612ef,
      0x814208482121, 0x10ad140f128fe6128f58b4138fb4138f, 0x13edbcb101fcbd676129f76000002e, 0x1568f10cf010cf0f3f00394f0b610159f, 0x1014210482521, 0x1129f0ebf00000c9806f0000101f0101f,
      0x10c910159f144f4976370f76d60ebf, 0x1014210482521, 0x118144f1239f588458013bf00ddf18bf, 0x814208482121, 0x1c9e6c91a3f13272f1313f70e4000003e, 0x13ed3000084104f000000fa00d239f,
      0x1c9a4c9e713cc13cca30e40012af00d1f, 0x1013303fc83e18bf18bf000f6ffa00d8c, 0x1193f1bbf0ebf0ebf1a3f841fbf1fbf13, 0x1084000c6f0c8138f194f3eb51e8f005, 0x118bf053765376ccd30e1f202f0ebf, 0x11a3f8423ff23ff13cc13303fc8018bf,
      0x149ccc8138f000000def0fcf00ebf0ebf, 0x10555f0ebf0defd30d40ebf168416ef0, 0x1760000d6cc807fcc860d6f0ecf22df, 0x14a537f3e10ff18bf000eafb84976288f, 0x1012af1bbf0ccf1a2f0d4f84808f0000, 0x10d300fc9d7c91a3f1301313f71e41fbf,
      0x21820240a121, 0x184000c6f0104f0dbfc63ed71e8f0fae6, 0x113cca30effe4160f0d30e1f809f239f0, 0x157dfee22df0faa40d163fc90c9013cc, 0x10119cf155f37af4a048ef007607610cf, 0x1218212442521,
      0x10128f0b4138fb4138fc624dfd7193f, 0x176129f7600105f22df02ee6ad58128f, 0x100b40b400010ff18bf0b600000000d6, 0x1c91a3f130131300e40000000d4f84, 0x101884222f04900000000fa000c9128f, 0x1a40dec94ec95d130130a30e400d30d4,
      0x10469fcc0cc0eff18af80af1a2f0fa, 0x110ff80df00f5f3e45df3e80cf080bf, 0x12abf02abf0ab564fab39af29ff80ef, 0x10ebf10d6f105f22df01caf6c14df120f, 0x21820240a121, 0x10eaffa497620bf760000d60ebf129f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10391fc61c62b2fb72effb708e8e00, 0x46001181002040100200830040c06001180c123, 0x1949e940c5168f241120f10c3f0014af, 0x1088210442121, 0x1088210442121, 0x10940f5f5c57509e098098f61f5d5f583,
      0x1e61c7a7984459e601e600f4e6000f4e6007a733b538f303cc0f522c079faf39e9e61116003d3983cfa45, 0x10fefe12df753e03b009800f5d5f58394, 0x10014af03bdfc61c60e8f120f1d5ff6, 0x488218472121, 0x1b7f7b70058e0149f240e3fbb579f0c3f, 0x10541120f10c3f00000dafc6f7c60daf,
      0x1088210442121, 0x1088210442121, 0x11143f1010083e5832cef0d9f10d9f, 0x288202442121, 0x888208442121, 0x888208442121,
      0x1088210442121, 0x110100866a8613cfdb12a02cef0d9f, 0x288202412121, 0x888208412121, 0x888208412121, 0x1000100000008394194013cf1cbf1150f,
      0x1088210412121, 0x80000010200000040800000102000000100040400020089000400014000001000002000100200000900440004000080004008000100010000800040004000100004000100048b5726, 0x1e61a947983cc1e601e60799e600799e603ccf320bf8f303cc0f4e6007a04eaa51e60f3001e67983cfa45, 0x18a00218f0186f001006b06b000000c0, 0x1e9cc1ed98001e60f3081183cd11600025f800079889a300222c0003cfcc79807987980799e601e690384, 0x106b09409400013a76500053053fe0005,
      0x100053053054270528003ea63b000006b, 0x11053053fe208f136f058a0fe68013065, 0x888208442121, 0x1c6f7c6ca120f77f60293fcb13a7650, 0x1f75427050e3f0179fbb10c3f00000f3f, 0x1088210442121,
      0x100cdf168f0d0f68cb131d6501053f753, 0x888208442121, 0x139194f0d6003b000b71172a1dd600f50, 0x100404010020402010020100804008400210081a3, 0x1f5000a6194f1c0429f10af29df1e5010, 0x2080a0240a121,
      0x2080a0240a121, 0x102a7f5700003bc300b78317930100ecf, 0x100004010002404010002100084002000090081a3, 0x1b783946a9400001f41861aff83e5831, 0x2080a0240a121, 0x2080a0a422121,
      0x2080a0a422121, 0x10c3fbac81c8f7b70d8fb7000000ccf, 0xc221846808e0, 0x1218fb71172a1dd600f5011140f15cf, 0x4220846808e0, 0x2082208482121,
      0x424084280860, 0x11e522ef0039194f0d68c80ff3b10c3f, 0x424084280860, 0x421084280860, 0x100f50136afa6194f1ca942bf10af29df, 0x421084280860,
      0x1000018c2a3bc311ef0e3fb7831793f70, 0x424084280860, 0x10cdf18c36bf143f1f41361aff83e5830, 0x421084280860, 0x421084280860, 0x421084280860,
      0x1760120f00c3f00000c61c6000008e8e0, 0x84c50020200000010008000100008000100004420280010010000040040000040100040040020020000020200400000200000280000020200000010800000102000000100029fe726, 0x19413efc8d5c88300001717c5c8c5168f, 0x1c600000fefe12df753e13b10cf9414ff, 0x8221084808e0, 0x1bb42ef0c3f0f0fee2dbf2a5f3bdfc61,
      0x1c24388e809e0, 0x100053b553fe00058a08e0285f840e3f, 0x110c3f00f700c60c6000000013a765, 0x4000420088004000080010000100010000100800000904000004400000004020001004000008010004040040000040000088000000420000004080000010200000010000ca5726, 0x10680130652700530530540052400120f, 0x1143f10daf0d150f1aff83e5831cef010,
      0x284202482121, 0xc211886808e0, 0x1250cefb404840484670b5000e3f0d9f1, 0xc211886808e0, 0x1f7b7ecb7bac81c800000f38cb4fc16, 0xc211886808e0,
      0x1c8135fc8f702f9f000c1140f15cf0c3f, 0xc211886808e0, 0x10077140f2f9f0c3f2cdfb7159fb72d9f, 0x10dff7cad0d9f0a1b0a1b12bf00ddf, 0x194b9176a17000001eff16dfab3d5f, 0x153fe8b0058a0fe6513ea63bb9940d1f,
      0x8221084808e0, 0x1c61c60000077cb13a765255a150f53b4, 0x1c24388e809e0, 0x15400500179fbb10c3fcaee77192f0f3f, 0x1c24388e809e0, 0x18e0285f68cb131d65275a4953845384,
      0x1000ec0c3f174f0c3f194fbb36dff608e, 0x1d53b830186f00c5168f1d46b7174fb70, 0x1c57594186f94150f0c3f150f0c3f13b, 0x425210a80960, 0x117150f0c3f830c3ffc174f000f503b3b, 0x18a08e0c51db7fefe12dfc3ee933b120f,
      0x1f601113a765b5153f3b8f53053fe1105, 0x28820240a121, 0x28820240a121, 0x28820240a121, 0x288212442121, 0x1b70000ec120f1dcf120f179fbb252f,
      0x1010530f3f530f3f54db0524046b71dcf, 0x28820a422121, 0x16b119f6b000006a8368271329af65, 0x1399f000c839419410f3f4eaf0f3f119f, 0x425210a80960, 0x425210a80960,
      0x1ee32df224f1f4f0fbf30df8c18c119f0, 0x825290c809e0, 0x111b6f532f5f53fe11058a00e7fee3b6f, 0x4020100802400090080802000900024000805a2, 0x880a0a482121, 0x1425290a80960,
      0x183140f1bbf179f000f501113a7651, 0x1c22390e809e0, 0x424210280860, 0x424210280860, 0x15400500c3ee933b0fdf171e7f198f, 0x1682713286549426f2a0f530f3f5329bf,
      0x1228f68b713fe] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100018010b467b4f610ff0ddfd78d08e0, 0xf307981e9cc007a7307981e61e607987980f30f300f33cc03cc0f3079800f4e60025f800097e1026865, 0x100003fff00c60c62b2fb7810fb7012af, 0x10586ff613f513f55815e4040168f2410, 0x2040041100014000201800040402020080807a2, 0x100000f61f5a6f5839409400e2f0660a5,
      0x1e61e58e18465e46000798f4e6000f4e6007a733cb0df303cc0f532e37a72cad63d2f497183d3984d1d45, 0x1660a50811f98135413b45858e4040750, 0x1586f013f513f5812f0e42e0f0f50e2f0, 0x10004e9f00f50f5839409400e2f000a50, 0x1000a50101354133d0d4f0e41607500, 0xf307981e9cc007a7307981e61e607987980f30f300f33cc03cc0f307987981e61e679803cde61026865,
      0x1250f300000ae98015015c69309300e2f, 0x10000180452f98104f15f615179f010ff, 0x124000000098015f615093f6930] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x18b0a10ff153f144f0ddf144f00c5f240, 0x1cce4cc0c5c5e41eff0000dff01dbf00a, 0x112dfc5fa0660c90c95d135413b5d7, 0x1fa000c90c90135413b5d70e4000f6f, 0x1db317f15df2a98314fd81d9fd800f6f, 0x10804d78d0b52507b015ef014ef01f5f,
      0x1377f00d84ad801adf02b0de0de26ef04, 0x118cf0000102adfdb0e7f15df, 0x1001040040204008100011000441004008100a1a3] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10000000dafc6f7c60dafb7f7b70e48e0, 0x1000000083083170f0d9f10d9f015bf10, 0x2040081100014000402800080402020080807a2, 0x4040101100014000402800080804020100805a2, 0x1055bf00000000860862adb2a00813f0, 0x1119f6b000000c0000000000008394094,
      0x100000a5000b40000008a00000000006b, 0x1000a527a5000000000006b06b094094, 0x1f300000000000c69309300000a5000b4, 0x19300e2f0000000b400a0c3f0136f08a0, 0x10e2f27574f0e3f00000000000000930, 0x10e2f0000000b4f70f7] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c6f8b274f11ff4dcb0f0fcb00c5f240, 0x153f4c3005980c50d0fc5a4d310000000, 0x2040081100014000402800000402020080807a2, 0x1b600000f6f6806600def00defba5349, 0x1f4c3005000f6f0000c90c9baf449f4f4, 0x104ca460b5250680000def00def053053,
      0x10f4f4b600001adf02b0de0de1aef0408, 0x118cffa0000000f4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1168f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1c5] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d6e6e6e6000b711712ef1dd600f500, 0x20422084121a1, 0x100f8f10af587f142bf0100f8f194f, 0x2010a0240a121, 0x2010a0240a121, 0x1c300b7831793010105ff500b90b9814f,
      0x100014000402404010002100084002000090083a3, 0x101f456ef86dc83183100f8f5700e60e6, 0x2010a0240a121, 0x2030a064131e1, 0x2050a0a4221a1, 0x1b70d8fb7000001a1fb783940e6f94000,
      0x112ef1dd600f50116e26ff6ebac81c8f7, 0xc221846808e0, 0x4220846808e0, 0x20422084821a1, 0x10194f0336f0d6e6e6e616e585fb7117, 0x424084280860,
      0x424084280860, 0x120cfb9aca9ac10af587f147f0d3f10ef, 0x1e6c36e4eb7831793f7000f503bafb9, 0x10e7f1f4569f36dc83183000001e6155f, 0x424084280860, 0x421084280860,
      0x421084280860, 0x110d9f815f, 0x421084280860] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1c5] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1180580f8db467b4f610ff0d7008e0, 0x1000000000c60c60000012af010ff241f, 0x113c813c8260f0e4001713c813168f76, 0x1c88300000e2f12fbf131fa5175f1133f, 0x8221084808e0, 0x1027308e809e0,
      0x1754a2a4f4a2faf94581f9410cfc8273f, 0x1208fa518582f161354133d0d4f0e400, 0x1282fbe3b3b0dbf0151500e2f10d4f, 0x1024308880960, 0x10dbfd70dbf0ccd4d4d43d4a175f175f, 0x1cc20cfcc187e13db40d3fb4b421ef,
      0x8221084808e0, 0x1d4c44ad6175fc6becc6b00015053af, 0x1841b6fd4295f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10b41cefb4199f2c9f0d7000c5ff60, 0x10f6f12dfc554c5c5c912af0001801dff, 0x136ef5dc91bc91b135413de128f0e400, 0x1175f0c3f0c3f101f0989800f6ffa5d, 0x100098096f99d9d9d19ff5ddbdb1d9f, 0x119d20bf9deb5d9cdb10ef175f2d413f,
      0x424084280860, 0x118cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100000000e40e40b40ddf0000e48a08e0, 0x100b4000a90e4240000000f700c60c60, 0x1150f1aef832a830000000000dff27, 0x18400000817f109f816f109f10daf41ef, 0xc211886808e0, 0x10012af13bfab334fb425b40a104f840a,
      0x10000c16e26ff6ef7b7ecb7bac81c8000, 0xc211886808e0, 0xc211886808e0, 0x10c6f10c6f4db7103fb74dc8818fc800, 0x8221084808e0, 0x111cf1b7f0e5fcc20dfcc000002cdf,
      0x11700000230f1c7f1b7f3e1f11cf112f, 0x1150a514a13df4ab99421bf94b9170e6f, 0x8221084808e0, 0x13d4a10cf0c6f81afbe819f3b119f015, 0x1791d7fb40d3fb40c3f0008a01d4d4d4, 0x1824308c809e0,
      0x181bf6b0001500e2f0d6f124f0e7f7925, 0x1000001ccfd41c9fd4c44ad60c6fc6be, 0x10e2fcb588f770e2f275a49b484b484] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x19300def240def2453c85328de0052400, 0x1000b6000c9c8c90128f0e42400c5f680, 0x1231f1000000f6f49c50d0fc50defc90, 0x4221084808e0, 0x1005000f6f1f91ccff9d676370f764a49, 0x8221084808e0,
      0x1689793970deff90def134f53c85328de, 0x197b6f9134f134fc9c8c90d4f0000096, 0x118cffa970b] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1046b70b70000ec000194fbb0f60d78e0, 0x1290f3f02d9f0d8f81cf97197f70194f0, 0x58b48795790815f65760000002b3fb0159fd8015a0033fb000159fd959fd800159fdd67f615a084fec0000568213fb000015a02e7f60000567f8b3fb00002b4263fb000002b4263fb46a4f2af4c3fb00000000acfec00002b4109fd80159fd80acff167f6000acfec0159fd80ad0173fb023527962606c00000002b3fb000000164cd6c0159fd82b3fb002b3fb0acfec00acfec0567f90a78ca42b, 0x1a50fbf16e13e613e6580e400168f7701, 0x20100880404010100401010041002040100c3a3, 0x1425290a80960,
      0x12cef6e1e6a6e6830431f000e2f4e6604, 0x425210a80960, 0x1135413b4580e4007594147f942cef6e, 0x16b081df000e2f586604a511ef583f5d, 0x14a3b6f4a417f138f2a2f6e41ffd81d8, 0x825290c809e0,
      0x1111167f1166f2bef166f25df01007b, 0x10080400201400050080102004100084010091a3, 0x1425290a80960, 0x1425290a80960, 0x1c22390e809e0, 0x1425290a80960,
      0x10f2f1166f000f50409f13ef52ef167f, 0x825290c809e0, 0x1021cf00a5c34a934a37df17315f5d83, 0x100f3931930daf4a2b2ff9425fd41d4c6, 0x1021210880960, 0x1025210880960,
      0x120cf251826ff81eff9104fd41d4000, 0x1425290a80960, 0x1201f9314a1f9b7d41d4000002e3f155f, 0x1021210880960, 0x1025210880960, 0x1024210880960,
      0x12911d9f81fff9249f97197f70100b793, 0x80402000201400050080102004100404010081a3, 0x1021210880960, 0x1024210880960, 0x1770cbf3bcf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d4f01e4f0fff589858a90cef08d000, 0x100206f0206fa9000000c5f77f6124ff6, 0x121ef58bc58a90cef08d0000b700dff0, 0x15a0e400c5c5146f0124f291d1f01d1f, 0x112dfc5facc66ccc95dc95d135413e6, 0x1128f1b128f109fab5dabd8000000f6f,
      0x115df2a9d173f01d9f000f6fc35d935d, 0x10b5007bd815efd814ef5d1f5fdb317f, 0x11adf882b25de5cde26ef040804d40cef, 0x14ad815d2adfdb0e7f15df255f9d00000, 0x1025294a80960, 0x118cf8cd8] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1f60e40e4000ddf00b400d701e48a08e0, 0x4040101100404010080802000802020080805a2, 0x1e424046b70b70000ec0004f9fbb2a9f, 0x1cbd400000831eff27000000b4000a9db, 0x1000007bb9129f204f10d6f320ff9dbd4, 0x1425290a80960,
      0x18394147f9416e0e5f6e0d9fe60d9fe6, 0x425210a80960, 0x1821f138f3cdf6e820fd83ed8000000c, 0x1b4a93e2c4f0822f08a00e7f4a19ff4a, 0x1000f501b9237f22efa52caf0e5ff9, 0x424210280860,
      0x14a934a114f1721bf5d830f2f0e1f166f, 0x127a518a5490e5ff9b4d4bbd400000c3, 0x14a823ff9425fd42c3fd4c6049bf00a5, 0x15d58d858d86c08d00f3930cbf932b2f, 0x1bbd400000588f5a124fa90d4f6c824f, 0x10e2fb793bb9314a21bff9b7d4,
      0x1024210880960] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10240def00def053053143ff3b7052400, 0x1b70000fa0faee2eb7e42400c5f6824, 0x1143ff300500c50d0fc568fab6b7253f, 0x1680d6f660d6f0def760defba534953, 0x1f993f9c976c9bafa49faee000000f6f, 0x1192fcb403fdb0cbf0192f000f6fb6,
      0x10b5007797124f970c6ff918af0d6f, 0x1882b25de33bfde1aef0408042e146f, 0x1971f9396f0d6f4dcb101fdb000001adf, 0x1024210880960, 0x118cfb797db] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x100fff2b2fc60c600000b70b708e8e00, 0x1f6f62805757138313a7d302424010fff, 0x240860108860, 0x10d500949e940f5f5c5e8c5168f15f6, 0x115151512df759810af9898f50f5167f, 0x1c60c600000dafb70b70058e0149f24,
      0x1041043bc311afb5f60113cf013cf0daf, 0x240860108860, 0x1e60079f9801e7e6003cc0222c00088b3cc0f3079bcc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0x1023af08308300e5000000f303d016000, 0x1e800006500053a353fea40058a0023af, 0x118c068028065000538353a7a42705130,
      0xa409605208e0, 0x113cf589f13cf16b06b3c4f04ebf008c, 0x8408604208e0, 0x100101f0101f086086006a0000001ddf, 0x10c11f4f01f4f19af6b06b00008394194, 0xa409605208e0,
      0xa409605208e0, 0x12f0fec0ec44af01001faf4e3f0fff0, 0x20460f379800f307983cc0222cf307981e60f3097e16c87980799e601e63cc0079bcc007a73001ea5c384, 0x153a353fe00058a0190f101f267f101f, 0x1001faf825f0fff00101f0101f65ec0ec, 0x10577f101f40bf101f826fec0ec001b6f,
      0x1101f28101f65f70f7530530027050e3f, 0x1aeaeae2809898133713a715024240068, 0x1a7b6000054000d34900930b524005f6, 0x100001ca1dc242f496a49102a8f98053, 0x2080a0240a121, 0x2080a0a422121,
      0x2080a0a422121, 0x1016f400040040930b51500def15df53, 0x1144f133713a78c0242400deff303d, 0x1d308c49000240288c8c8c8c280144f, 0x100008e8e068f38c0e1f8c540144f144f, 0x1e8c5168f270186f0186f0c60c600000,
      0x11f711d167f94d5940f3f01001d1dc5, 0x204202482121, 0x8410884808e0, 0x8410884808e0, 0x100cdfa73b3b3b12df750c3f10af0c3f, 0x1f78bf7650bd8653a353feb50058a08e,
      0x105240019af019af0c60c600000000067, 0x10302f006802806583bd83532753f4c30, 0x10f3f2f3f83302f8357cffce5fc0c3f, 0x16a9400000a3c653e8530c3f0f3f174f, 0x114af0058a0860c1ec1ecf7c6ecc68394, 0xc411886808e0,
      0xc411886808e0, 0x1005008667f78bf76586bd8653a353fe, 0x1940cdf686b286b6583bd8353275386f3, 0x14a117179fb786c6c61d08c1f500285f, 0x2421204208e0, 0x2421204208e0,
      0x11c1532f10af086e51003900d64a4a, 0x8421204108e0, 0x8421204208e0, 0x10c60008c0ecff504c7f827f470f194f, 0x100e50013bf2a7f570c34a04a831793b7, 0x1b786c6c61d0701f500f400167f83083,
      0x1004202482121, 0x1186e5107039570d64a4a4a117179f, 0x4421084808e0, 0x8421044808e0, 0x8421084808e0, 0x1000f506d201f12ef249f1c6a0e6f10af,
      0x1070000c34a864a831793b71c66a150f, 0x4421084808e0, 0x1941f4828f2e1f167f831831f7e5fc, 0x8421084808e0, 0x8421084808e0, 0x8421084808e0,
      0x1000bb0f608e8e0285f14a14a839414df, 0x8421204808e0, 0x8421204808e0, 0x1d302424046b70b7ec1b1f166f1b1f00, 0x1c5168fd8d8d8d828166f7e7e138313a7, 0x18a08e012dfd4d4d4d412dfd8e6e6c5e8,
      0x1f609797979765b5a9a953a353fe0005, 0x146b70b7ec1b1f166f1b1f00000bb252f, 0x10682728065970e9f975305300db05240, 0x10e9f1b4f0e9f1b4ff7a6fcca0418f0, 0x153a353fea46a058a036b914fffc1dcf, 0x18353a7a400500e8979797976504a9a9,
      0x197d40cd8d4e66827281365970e9f9753, 0x1228f68d4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d4f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x17a0e9f18670f6b40b4000ddfd78d08e0, 0x10e9f829fc60c600000b70b7012af0e9f, 0x100000057ab83aba7d30024010e9f17df, 0x240860108860, 0x1f5130130015e42e0f0f504e804168f15, 0x10f5dc06d009419400e2fe666e6a5f50,
      0xa409605208e0, 0x113013000d4fe416075e60edfe634fff5, 0x10000930fff9300e2fd866d8a55403d, 0x10010ff250f3d4237fd4135f15015199f, 0x10793f693012afd4acd41a0f150150000, 0x1240e3fd417dfd4f7150150000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x157000280f6f61329bf13a7d30242400, 0x1160f000000000d70d7a7d3002400c5f, 0x1c5c5fa000c90c91a3f13d71313d30e4, 0x154c9b51301300cce4cc00f6f12dfc5e4, 0x1317f02a00d81d9fd800f6ffad866d8c9, 0x1000b52507b9d15ef9d14ef15df1f5f98,
      0x14ad801adf1b4f2b1b4fde08ded704004, 0x119d17df9d0e7f15df377f1000010dfd8, 0x8421204408e0, 0x8421204408e0, 0x118cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10e9f0dafc60c600000dafb70b70e48e0, 0x10b41b422cfc415bfd71e8f010e9f0edf, 0x240860108860, 0x1e600f379803cde6007980222c00088b3cc0f30f33cc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0x19d08308300000000012af0001811df0, 0x10e800001800013a3130130138a009dac,
      0x108c18c0000018000138313a7132713ab, 0xa409605208e0, 0x1082af1b4f237f1b4f119f6b06b0000, 0x11b1f0edf1b1f086086000000320f402f, 0x100c1e6ace619af6b06b0000839419400, 0xa409605208e0,
      0xa409605208e0, 0x117dfd4353fec0ec187f000093337f93, 0x1d479d418ec0ec0a300008d8a0f3d4, 0x10edfd4f7ec0ec000007931b6f9300e2f, 0x1d418f70f700000e2f2700e3f013dfd4, 0x10e2fd479] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1166f0c6f8b0000004dcb0cb00c5f240, 0x1131131d0fd325e41a2f01166f17df, 0x2100084002014000500814000402020080807a2, 0x100014020002400090002100084002000090083a3, 0x13753a7a4005a70fa000c9108fc91aef, 0x1b6370ddf490c5680000def00deffd53,
      0x1b51bff0c50000128f0128ffd133713a7, 0x10f6ff3000de0de1e0f04dc043bc30, 0x1490def05305300d405d400f6f0d0f, 0x1de08de004004000b525068d466d40def, 0x1000000b6d40fbfd401adf0e9f2b0e9f, 0x118cffad479d4049] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1186711cff6b40b48d0ddf0d7008e0, 0x10c61f3fc600000000012af0e9f7a0e9f, 0x1082bf0004e804168f2700e9f17df0e9f, 0x182cff721fff7448f150f30ff150fec, 0x1b4136c0e5f0e400186f166f237f166f, 0x16d940f3f01000e2fe666e6a58b4c1d13,
      0x214202482121, 0x116180e40075e60edfe61f71a1f1ddc94, 0x8410884808e0, 0x10fff000e2fd866d8a5544c3d130d4f13, 0x1d4237fd4135f6b39df3b199f931934d0, 0x8410908809e0,
      0x1d4acd41a0f6bb43babf7ab2500000f3, 0x1d4f76b266f3b079314ef930000012af, 0x186186199204f7b000000e3fd417df, 0x441084280860, 0x441084280860, 0x111b1f0edf1b1f14ef,
      0x441084280860] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1237f166f08b2adf10000000000c5f240, 0x841082180860, 0x111df0e4000f6f12dfc513c5c5270166f, 0x1000f6ffad866d8c954c90413cc13cc, 0x115df1f5f0c3f317fd82ad813bf01d9f, 0x1b404ab0425880b5007b9d15ef9d14ef,
      0x1d84ad8000001adf1b4f2b1b4fde08de, 0x119d17df9d0e7f15df26df14af10df, 0x8421104808e0, 0x118cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100000180243f86e4a3e40d70e48a08e0, 0x1e424000e9f0edf0e9f0c60c600000000, 0x1fc0000000001883243f83f427f4f4c40, 0x12f3f9dac9d0c3f83174f830c3ffc302f, 0x1c6ecc683940e6f9400000a3c613e813, 0x186187f93119f934d00000c1e6ace6f7,
      0xc411886808e0, 0x1a3587e0008a0f3d417dfd4353f8643af, 0x16b93000000e2fd479d41886243f8658, 0x10000013dfd40edfd4f7860f3f860793, 0x10e2fd479d41883243f830e2f27bd86] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10000def00def1353245324f60052400, 0x127000013013b4b6000250e42400c5f68, 0x111bf005000f6f0d0f0f6f53c537c5a7, 0x1b50068d466d40def490def1353d453d4, 0x10e9f2b0e9fde08deb404ab0425880, 0x179d4134913b4b6d40fbfd4000001adf,
      0x118cffad4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x194] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10f6f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1e6e6e61171e7fb786c6c61d08c1f500, 0x2421204208e0, 0x2421204208e0, 0x1b9211f1540f10af08601000f8f00d6, 0x8421204108e0, 0x8421204208e0,
      0x11793b70c60008c105ff503edfb90f8f, 0x1dc830830000013bf0f8f570c3e60e683, 0x1e61171e7fb786c6c61d0701f500f400, 0x1084202482121, 0x4421084808e0, 0x10e6f2a10af186a62a000570d6e6e6,
      0x8421084808e0, 0x193b71c62a150f000f50a6b9a6b9211f, 0x4421084808e0, 0x1dc831831f7a6fc00000c3e686e68317, 0x8421084808e0, 0x8421084808e0,
      0x11e6ace683941dbf941f482df10ef, 0x8421084808e0, 0x8421204808e0] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10f6f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1b7ec2f8f13ef167f00000bb0f60d78e0, 0x11cbf1140fab83aba7d30153f24046b70, 0x214208482121, 0x1a5e61d804e804168f0e3f000daf0dff, 0x8442204809e0, 0x17793ac93] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c5f57000280f6f613013a7d30242400, 0x113d30e4160f000000000000a7d300240, 0x100c5c5fa088344fc9111fc91a3f13013, 0x1166f5c166f0d1daf0d1ab1ab3d5f000, 0x441084280860, 0x4421084808e0,
      0x118cfd896d80f6f540f6f12dfc599] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1180ddf1c7f135f0a30d700e48a08e0, 0x113ef167f00000bb2a9ff60e42de482ef, 0x10e3ff700000dbe424046b70b7ec2f8f, 0x10faf7ef7204ffcca0361f000270018f7, 0x1a313b40008a036b9a9fc1f6f2a5f2fbf, 0x100000e8132d13204f180a1c7f135f13,
      0x1e6cbd8132713ab18f70e3ff7138313a7, 0x10e2f9379930c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x193240defc80def9c5305300b7052400, 0x10b7fac8fa9c00000b7e42400c5f6824, 0x1c9108fc9e7130131d0fd30e400b6b7, 0x1c80def9c533753a7a400500fa0881ddf, 0x1fa9c133713a700000c568d693a70def, 0x196d40f6f0d0f0f6f68c5b6372e36fac8,
      0x118cfd4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d4f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x183575713013a7d327ef24240b78e8e00, 0x10f600d500940940c5168f1543434328, 0x12464646412dfe8f5f5c575f557f50c6, 0x10040043bc311afb5f60b7058e0149f, 0x10d9f0d9f570f3534f249f2a1f160221f, 0x1058a01f7f090909a9f7f7287f000fcce,
      0x163636365a312bf1abf53053fea4db, 0x1270513000000c6000000094094023df, 0x19e068ec1b6fec65012bf053053a7a4, 0x10f3f0f3f0fbf3c0f01174f0164f164f, 0x4200000004800000041000000041000866502020000400028000010000004000280004332a000000028000010020000040004000020010000080020000100020000100229fbf26, 0x1053fe00058a00eff12cf12cf12cf17ff,
      0x1002705280e8063636365a312bf1abf53, 0x19e06468ec1b6fec658301def53053, 0x10f3f0f3f1def000174f0f0f136f136f, 0x12424000c64101f12cf12cf12cf164f, 0x1005f64343432837989813013a715364f, 0x12b5f430000d30589f58af93136fb524,
      0x101ccf0eff49766d760000053a7b65443, 0x113134f13a79c024240530014efba1, 0x282208482121, 0x10002400def9c43434328370fcf0fcf, 0x10def54438b43160221f14afd30671cef, 0x11602acf0040604069313bfb51509a06,
      0x11a9f16bfbb98f608e8e068f3f4123f9a, 0x10c5168f27f79a0c3f9a06b0174f9904a, 0x1c5754dfc1d1c61143f163f94d5940000, 0x481084280860, 0x481084280860, 0x1058a08e00cdfa764646412dfe81d1d,
      0x1f60063636365a30053053feb5136f, 0x10f79a09a06b009904a1a9f4e1fbb37ff, 0x10053fc6800065000532753f4c3db0524, 0x10053b9177b171c60ccfbbb9946a94000, 0x481084280860, 0x1c8263f6b135fbb23efb71b70c6f0218f,
      0x4831886808e0, 0x1a35acb532553fe6c0f3f058a077c8ba, 0x15acb532753281600500e87763636365, 0x1cb042504066e0b5006468844e846583, 0x1f608e8e00cdf0c64f3844e8416860cef, 0x19a138f9a996b4a2a5f0cc01a9f0bb98,
      0x14328830ebf0ebf13013a7d3024240f7, 0x10fdf17a6ba03e0f50c5168fc84343, 0x16412dfe81717c583441b44c3c693133f, 0x1bd8653b553fe00058a08e0285f846464, 0x10cc01a9f0bb37fff606763636365a3, 0x15305300db05240f79aec9a996b4a0f3f,
      0x1fcce0d9f0d9f5706883dc836527bd0, 0x18a0ec090909a9f7f7119f38bf1b0e6f, 0x106763636365a3bd86530453fea4db05, 0x183448644c3c6936b114f176aba03e0f5, 0x16883dc836527bd13534953a7a400500, 0x1228f644364285f0c64a36465e8bdc6] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d6f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x182ff57000a7d327ef1e4f240b78d8e00, 0x113013000e4040168f15434343145f83, 0x10f600a6009409400e2ff50f5a5670f6, 0x1a5dc09813013000e404075f557f50c6, 0x124002464646416e8321ff50e2f540b4, 0x157434343280f6f613013a7d3217f24,
      0x14343d70d70000a7d3830f0ddf2400c5f, 0x1c91a3f1301313d3831fe4160f01d9f43, 0x1013000e400c5c5fa2acf215f0c4fc9d7, 0x1e40f6f12dfc5fa541e4fb5c9dcc95d13, 0x1d71e8f0b7e48e018cf440c4f440f6f, 0x1117f451f180243f0b40b422cfc415bf,
      0x1f7287f000fcce0d9f0d9f57012af11df, 0x1130130a13db138a01f7f090909a9f7, 0x1000000940940221f6358bf630a301abf, 0x106ec000013013a71327130000000c60, 0x10fbf000174f0164f164f9e012afec, 0x18a00eff12cf12cf12cf17ff0f3f0f3f,
      0x16358bf63a5a3195f1abf0000a00195f, 0x183195f1def0000a527a5145f0e8221f, 0x1174f0f0f136f136f9e06412afec0eca5, 0x112cf12cf12cf164f0f3f0f3f1def000, 0x11d0fd325e41a2f04d0c5f2400c64101f, 0x158af05a70fa108f5c123fc90c9013013,
      0x1000c568069a060def00def053053a7a4, 0x1005980c52e0632cf06000013013a7b60, 0x1000f6f68069a00def370defba5305300, 0x1b50600f6f00600c937c9ba0000b6370, 0x10f3123f142f9ade0de0040043bc306, 0x102abf2abfab0ababeb519f10ff142f,
      0x18e018cf0d0f1caf120f329f197f2abf, 0x19a06b01dcf9904a1a9f16bfbb98f608d, 0x113b41304b40e400168f27f79a0c3f, 0x194000000e2fab12bf1da567206f129f, 0x100754d2e1f1d1c64e2f19bf22af94a6, 0x481084280860,
      0x1206fb4a5dc206f541f13b41304b40e4, 0x119bf150f150f0c6f179faeae00e2f54, 0x1123f123f123f135f119f11bf11bf832f, 0x100000000c5f2407b64646416e86c0d8f, 0x11b131b00e400c5c5270001d3f000000, 0x1130f6f12dfc5fa54206f04c9dcc95d13,
      0x10ad7136fe48a08e018cf440c4f440f6f, 0x152afbb45bff600630630a300e40e4, 0x1f4c4dbe4240f79a09a06b009904a1a9f, 0x10e6f940000013fc12af0000000f427f4, 0x1b70000013b9171171c61a1fbbb994, 0x481084280860,
      0x485084280860, 0x1c8833fc8341f6b21ffbb3eefb7103f, 0x163a5a34ccb4c254c0a00f3f08a00d8f, 0x1834ccba527a5145f00000e86c6344cf, 0x125191f06000006412af841eaf84a5, 0x1000c64230f843acf8418861fefcb834f,
      0x1069a130def00def053245324f6db0524, 0x113061300000b600025dbe42400c5f68, 0x1118b23efdbd676129f7600000c5a727, 0x481084280860, 0x484084280860, 0x1ba53db530c3f5d00500c54a493daf,
      0x1b44a000000f6f68069a130def370def, 0x10d0f58530f6f13061358c937c9bab637, 0x14a2a5f0cc01a9f0bb98f608d8e018cf, 0x10a00aa7d301e4f240f79a138f9a996b, 0x10f5013168fc8434343145f832f8f0ebf, 0x1441b44c3c693133f299f170e6fba03e,
      0x1d302424008464646416e8133f171383, 0x12400c5f5743434328545ff6f613013a7, 0x11dff23ef1dff3c0f000a7d32adf1dbf, 0x11301313d32cffe4160f01d9f434343, 0x13b00000c5c5fa000c4fc9128fc91a3f, 0x1123f128f32cfc314af93109fb41bb4,
      0x118cf440c4f440f6fc90f6f12dfc5128f, 0x1639a63e4a3e48600ddf00a00e48a08e0, 0x1996b4a0f3f0cc01a9f0bb45bff6012bf, 0x1321f830270000000dbe4240f79aec9a, 0x1575f1b204ffcce0d9f0d9f57012af83, 0x10a130a0db08a0ec090909a9f7f7119f,
      0x12aba03e0f5012bf639a6313a3138613, 0x113a70000083448644c3c6936b23bf17, 0x1e8162fc612af83321f83132713b41349, 0x10def245305300db0524000c64a364a5, 0x10100000dbe42400c5f68069a280def24, 0xa809605208e0,
      0x1130131d0fd30e400c906c918b622bf, 0x17653a7a400500fa108f0dec90c9232f, 0x113a700000c568069a280def10defa753, 0xc811886808e0, 0x1370f6f49c5c906c918b68b93fd1376, 0x118cf640c4f6418cf0d0f1d1f0def0f6f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d6f] (by decide) (by decide +kernel)

private theorem vb11_3_14 : nb11_3_14.Valid :=
  SearchNode.cover16 nb11_3_14 (by decide) rfl
    checkedBranches1.vb11_3_14_0 checkedBranches1.vb11_3_14_1 checkedBranches1.vb11_3_14_2 checkedBranches1.vb11_3_14_3 checkedBranches1.vb11_3_14_4 checkedBranches1.vb11_3_14_5 checkedBranches1.vb11_3_14_6 checkedBranches1.vb11_3_14_7 checkedBranches1.vb11_3_14_8 checkedBranches1.vb11_3_14_9 checkedBranches1.vb11_3_14_10 checkedBranches1.vb11_3_14_11 checkedBranches1.vb11_3_14_12 checkedBranches1.vb11_3_14_13 checkedBranches1.vb11_3_14_14 checkedBranches1.vb11_3_14_15

private theorem vb11_3 : nb11_3.Valid :=
  SearchNode.cover16 nb11_3 (by decide) rfl
    checkedBranches1.vb11_3_0 checkedBranches1.vb11_3_1 checkedBranches1.vb11_3_2 checkedBranches1.vb11_3_3 checkedBranches1.vb11_3_4 checkedBranches1.vb11_3_5 checkedBranches1.vb11_3_6 checkedBranches1.vb11_3_7 checkedBranches1.vb11_3_8 checkedBranches1.vb11_3_9 checkedBranches1.vb11_3_10 checkedBranches1.vb11_3_11 checkedBranches1.vb11_3_12 checkedBranches1.vb11_3_13 vb11_3_14 checkedBranches1.vb11_3_15

private theorem tv_b11_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_3

private theorem vb11_15_2 : nb11_15_2.Valid :=
  SearchNode.cover16 nb11_15_2 (by decide) rfl
    checkedBranches1.vb11_15_2_0 checkedBranches1.vb11_15_2_1 checkedBranches1.vb11_15_2_2 checkedBranches1.vb11_15_2_3 checkedBranches1.vb11_15_2_4 checkedBranches1.vb11_15_2_5 checkedBranches1.vb11_15_2_6 checkedBranches1.vb11_15_2_7 checkedBranches1.vb11_15_2_8 checkedBranches1.vb11_15_2_9 checkedBranches1.vb11_15_2_10 checkedBranches1.vb11_15_2_11 checkedBranches1.vb11_15_2_12 checkedBranches1.vb11_15_2_13 checkedBranches1.vb11_15_2_14 checkedBranches1.vb11_15_2_15

private theorem vb11_15_6 : nb11_15_6.Valid :=
  SearchNode.cover16 nb11_15_6 (by decide) rfl
    checkedBranches1.vb11_15_6_0 checkedBranches1.vb11_15_6_1 checkedBranches1.vb11_15_6_2 checkedBranches1.vb11_15_6_3 checkedBranches1.vb11_15_6_4 checkedBranches1.vb11_15_6_5 checkedBranches1.vb11_15_6_6 checkedBranches1.vb11_15_6_7 checkedBranches1.vb11_15_6_8 checkedBranches1.vb11_15_6_9 checkedBranches1.vb11_15_6_10 checkedBranches1.vb11_15_6_11 checkedBranches1.vb11_15_6_12 checkedBranches1.vb11_15_6_13 checkedBranches1.vb11_15_6_14 checkedBranches1.vb11_15_6_15

private theorem vb11_15_10 : nb11_15_10.Valid :=
  SearchNode.cover16 nb11_15_10 (by decide) rfl
    checkedBranches1.vb11_15_10_0 checkedBranches1.vb11_15_10_1 checkedBranches1.vb11_15_10_2 checkedBranches1.vb11_15_10_3 checkedBranches1.vb11_15_10_4 checkedBranches1.vb11_15_10_5 checkedBranches1.vb11_15_10_6 checkedBranches1.vb11_15_10_7 checkedBranches1.vb11_15_10_8 checkedBranches1.vb11_15_10_9 checkedBranches1.vb11_15_10_10 checkedBranches1.vb11_15_10_11 checkedBranches1.vb11_15_10_12 checkedBranches1.vb11_15_10_13 checkedBranches1.vb11_15_10_14 checkedBranches1.vb11_15_10_15

private theorem vb11_15 : nb11_15.Valid :=
  SearchNode.cover16 nb11_15 (by decide) rfl
    checkedBranches1.vb11_15_0 checkedBranches1.vb11_15_1 vb11_15_2 checkedBranches1.vb11_15_3 checkedBranches1.vb11_15_4 checkedBranches1.vb11_15_5 vb11_15_6 checkedBranches1.vb11_15_7 checkedBranches1.vb11_15_8 checkedBranches1.vb11_15_9 vb11_15_10 checkedBranches1.vb11_15_11 checkedBranches1.vb11_15_12 checkedBranches1.vb11_15_13 checkedBranches1.vb11_15_14 checkedBranches1.vb11_15_15

private theorem tv_b11_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_15

def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_new (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left))
    (r : State) (hthird : M 2 0 = some (some r, Stmt.write 1 Dir.left)) : False := by
  let tb := baseTable.set 1 0 ⟨2, 1, true⟩
  have hm : Matches M tb := matches_set hm0 (m := ⟨2, 1, true⟩) hM10
  let h2 : HistItem := ⟨2, 128, h1.c.move ⟨2, 1, true⟩⟩
  have live1 : M.multiStep (Machine.init []) 1 = some h1.c.view := (hv h1 (by simp)).2
  have live2 : M.multiStep (Machine.init []) 2 = some h2.c.view := by
    change M.multiStep (Machine.init []) (1 + 1) = _
    rw [Machine.multiStep_succ, live1]
    exact step_move hm h1.c ⟨2, 1, true⟩ rfl
  have hv2 : HistValid M (h2 :: [h1, h0]) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨by decide, live2⟩
    · exact hv x hx
  fin_cases r
  · exact tv_b11_3 M hG (matches_set hm (m := ⟨0, 1, true⟩) hthird) rfl hv2 (by simp)
  · exact checkedBranches1.tv_b11_7 M hG (matches_set hm (m := ⟨1, 1, true⟩) hthird) rfl hv2 (by simp)
  · exact checkedBranches1.tv_b11_11 M hG (matches_set hm (m := ⟨2, 1, true⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_15 M hG (matches_set hm (m := ⟨3, 1, true⟩) hthird) rfl hv2 (by simp)

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H4 := by
  intro M hFirst second hRun _hUsed hForm hMissing hLoop hHalts
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts⟩
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 0, false⟩ rfl
  have hv : HistValid M [h1, h0] := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact ⟨by decide, hrun1⟩
    · exact ⟨by decide, rfl⟩
  obtain ⟨q', hNew, hM10, r, hthird⟩ := second
  rcases hNew with rfl | rfl
  · exact solve_new M hG hm0 hv hM10 r hthird
  · have h01_base : UsesOnly01 baseTable := by
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro q a m' hget
      fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
      subst hget; exact Or.inr rfl
    have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
      intro h hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
    have hM10' : (reindex23 M) 1 0 = some (some 2, Stmt.write 1 Dir.left) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    have hthird' : (reindex23 M) 2 0 = some (some (swap23 r), Stmt.write 1 Dir.left) := by
      simp [reindex23, swap23_2, hthird]
    exact solve_new (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01) hM10' (swap23 r) hthird'

end OMA.BB4H1

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H4 := OMA.BB4H1.h1_proof
