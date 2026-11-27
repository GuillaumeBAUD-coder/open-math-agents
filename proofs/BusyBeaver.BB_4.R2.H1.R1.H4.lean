import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1

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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581109144422496, 581109144422496, 580628108150880, 565226355427424, 580613075765344, 88038308972640, 
    564326525075489, 564326525075489, 564326525075489, 564332967526433, 564332967526433, 1461596415859588229274168971387781693606640225698, 
    74852759373920, 79250805885024, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 565426071341152, 565426071341152, 565426071341152, 565426071341152, 565426071341152, 
    580681795176544, 580613075699808, 565426071341152, 580615223314528, 565226355361888, 565226355361888, 
    565226355361888, 565226355361888, 565432513792096, 565226355361888, 565226355361888, 565226355361888, 
    565226355361888, 565432513792096, 565226355361888, 565226355361888, 565226355361888, 565226355361888, 
    565226355361888, 565432513792096, 567425378748512, 571789165076769, 571789165076769, 571892210737441, 
    571892210737441, 571892210737441, 565226355361888, 565226355361888, 565432513792096, 567425378748512, 
    1461596426387717800621932840897606914240223382946, 564195629343009, 1461518362985516617491241738907202425865784820003, 564195629343009, 567494164226465, 565295140970849, 
    580613075765344, 52819542442017, 52819542442017, 52819542442017, 580613075765344, 580613075765344, 
    580613075765344, 580613075765344, 580613075765344, 368230089832420255470096403832045081724608581026, 88038308972640, 88038308972640, 
    88038308972640, 1465075331751636301328260406549693658628469309859, 1462220839088483316933651542317791527809849508259, 88038308972640, 88038308972640, 1461518362935016347435633918330517302885698535843, 
    1461529513350150908612321994122575452995422552995, 1462934465657105616875019543921902366820648649123, 1461864025804187743912964267884319956287143059875, 1461596415840958275672450448874924353653766654883, 94198707057438813867571248047423337334292614562, 283759968651360, 
    730764756679094307405451802725419544341549023651, 72653736118368, 72653736118368, 72653736118368, 53052544417825, 53053618159649, 
    53060060610593, 53060060610593, 48526606666316474607371013562748753338763316642, 143022480296032, 2108623662504510070204107781643184112109953340074324104352718075588604665279070081783292380668167140, 1982522845157666168539792518005747172823886807700710547306401948220455846475868627646764080527396432705724512083352910555225433506073580917098799034396261485753862530903555110, 
    3879633488058325618509967203304951143764264210200574315979545834052943139808911600068901546472222365086304850688315023901913169747474363386660246628962823679318670925518630, 72653736118368, 730764756684411239671001069868705196529921687971, 72653736118368, 72653736118368, 72653736118368, 
    72653736118368, 580578715961440, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    88238024886368, 88238024886368, 981230230566952290560025527830757515894273542794107617909890711816643715308897946933729324951285403399797217495969714986520785305302020454082367843454859125740623310313254, 88238024886368, 88238024886368, 1978658307749821103328700726245097430261063721323732106580176110259740037117871553140590876470640418616038868118254787239665652380249828266138437933231165983806891274088830758, 
    234839012240743482438425180599805310686892120664697085952810785323620674474633946662983844691027363118222084365657628726069193907066004760722942067833106021445221997312273421640096921950965143658093584452869825215263058516373304633653429782405575644020774082250760, 3879633488002089196078177248519819412418189610171941248383584279078610963475525935831244902806645719829284537027357020384486818320339738950775552889807527202243058686711590, 580612001957984, 580612001957984, 88236951144544, 580578715961440, 
    580613075699808, 580613075699808, 580613075699808, 580613075699808, 88238024886368, 88238024886368, 
    3879633372773659626643202710028824009032412250497972752543180900099522018712372159044194260662346631570128232025409502476987221124425512230528339812468455402789543278001190, 61847696218876081133648532114025352445965965699128136345754243197869796781017837059089805213469755808881208089761515770997749801941454087039312964416763452440396302956608550, 53054727620704, 88238024886368, 88238024886368, 7560670634479108855437536186797703994533052022643170831690317376582005065704681182018955815859494584937138450825515204245214687641638535030254750139517515346099327115567681650210173947342896059612664445493720942052548138073172716309216709057021176971270122998760, 
    1978658307750130403652075570996415654783467132576529401807680038276438053742805961390969322726669932558694248300505059053931377135837164462413985020408440441201645626654807846, 1947364611321266876727316719347866800002413845499650686328054386393750453625704943217444943793190100595927182794598790367778751140456265791722014643578192065810595191543591, 1982522845157666168539792518005747172823886807700710547306401948220455846475868627646764080527396432705724512083352910555228338971328593561111913719307556127857124034024029222, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 580613075699808, 88238024886368, 88238024886368, 88238024886368, 88238024886368, 
    88238024886368, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 88238024886368, 
    1464356317835240673301050880071291293851556777378, 981230230566952290560025527830757515894273369586869471527078308877216446984635641412992370237874040080518895442553707121010587523920328253968106600089857419017820444448550, 88238024886368, 88238024886368, 1984455114034234518000883447562533043956712728316072082953094598375293920300786394631407366613014845816239096786113070854563938485661483058860802166347105919994362846692482086, 1984455114034234518000883447562533139224917999189858441034064745909400928425648154285791853377127625259002789167938794996489774155899010864748349387952890054061441672004213798, 
    3879633488058325618509967203304951143764264210200574315979545834052943139808911600068901546472222365086304850688315023901895631727998150076354970392555131935281070369036070, 580613075699808, 580613075699808, 580613075699808, 53054727620704, 88238024886368, 
    61847696221575429410295888569120643854412909826524738579857506073548754361694967025908869024264142883360701773454660475496462389243301672973253650324562060096769229388225574, 88238024886368, 88238024886368, 45287549105766743131829437917762702757679175775907093032975519288614747139894702321483902480160408932139300270593420054690420659313027841519451103825155684733738120927015, 1984455114034234518000883447562533043956712728489406246417648103009277729389443256817531137987933133184642446996676255230312825674492225972362789797847517765160281689717447718, 1984455114034234518000883447562533139224917999363192604498618250543384737514305016471915624752045912627406139378501979372238661344729753778250337019453301899227360515029179430, 
    580615223183456, 580615223183456, 88240172632160, 1978658307750130403652075570996415654783467132403914467227204079175831604568797629269250399466721205009062165440868000619225237045044793992638302884698640498410787277455841062, 88038308907104, 88038308907104, 
    88038308907104, 88038308907104, 88244467337312, 52888297637984, 88038308907104, 88038308907104, 
    88038308907104, 88038308907104, 88244467337312, 88038308907104, 88038308907104, 88038308907104, 
    88038308907104, 88003949168736, 88038308907104, 88038308907104, 88038308907104, 88038308907104, 
    88244467337312, 571789165076769, 571789165076769, 572923069998369, 571892210737441, 571892210737441, 
    571789165076769, 571789165076769, 572923069998369, 571892210737441, 565192095310177, 565192095310177, 
    88038308907104, 88038308907104, 88038308907104, 88038308907104, 981230230566952290560025527830757515894273391163736295352670473980301224500060592199779954471633833280449489003128356287052649403004872138299619163261375384492664695707430, 88038308907104, 
    88038308907104, 88038308907104, 88038308907104, 88244467337312, 16641875556787413440752102237660966418024304451120476121168989534958436253449609791385887167744250692, 158407053215840, 
    88038308907104, 88038308907104, 564092583682337, 564126976976161, 564195629343009, 1461529524151623746352644407962943318734080607139, 
    564092583682337, 564126976976161, 564195629343009, 571789165076769, 571789165076769, 572923069998369, 
    571892210737441, 568490630193569, 569624535115233, 567494164226465, 565192095310177, 565192095310177, 
    565226488604001, 565295140970849, 571789165076769, 571789165076769]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [565427177554977, 580681864448224, 565427177554977, 581094181243104, 580613144905952, 580613144905952, 
    158606838466784, 564326525108257, 564326525108257, 564326525108257, 567633784154593, 158606838466784, 
    565427177620513, 48526606666940848151114952046680785688296168866, 158469399513312, 1461591189122392161799558868651515407690055032226, 265783407324249547732710350891728110217247699866844112342111144685897210924626030152133609152915876196, 265783407324249547732710350891728110217247699866844112342111144685897210924626030152133609152915876196, 
    265783454844217486601109291989952361289037511378047360375732563616053409386551200061789689908646554820, 567427625920993, 567631603311009, 150085623417056, 158400680036576, 564126809325601, 
    564332967755809, 564332967755809, 564126809325601, 564332967755809, 564332967755809, 565195249550369, 
    265783850844012938265135989590185423348299673841699211219060449606000417465191764860106770785095051652, 565195249550369, 565263969027105, 265783787484045930357267132347011171619233005025482999452868779442958718079197734966123094648264551620, 265783787484045930357267132347016085069537498601132805324291077755023854597094315500759421353776655556, 564126809325601, 
    1461864036693207908492419494229423488157460996515, 1461864025804172167022388663401436050340878229923, 567631603311009, 3122383149676804049759275521854715809098465027829564872561427685221659802652342581735068105779620196, 580613144905952, 580613144905952, 
    158400680036576, 564326525304865, 564326525304865, 564326525304865, 564326525304865, 564326525304865, 
    565432582998496, 564326525075489, 564326525075489, 566525615473697, 143494996036064, 567494167366112, 
    145272975392801, 145272975392801, 564332967526433, 564332967526433, 565260747605025, 265783454844217486601109292097497962606543002212780826793395902243756278053090696723055757561688540868, 
    283957536490529, 290554807591201, 290554807591201, 567425447823840, 265783407324249547732709478517868270233747802868777155508476498066154980371001875195437839123078071140, 567494167366112, 
    145694019291616, 567425447823840, 3879633372941493632236854824865284473055870862811319310314301053647107967481105368342880365208480519098769991736811095204699253433046115888652864772372135472557009784497446, 145694019291616, 732180854653160467481549336735547450358271350178, 265783407324249547732709478517868270233747802868777155508476498066154980371001875195437839123078071140, 
    565295144110560, 565432582998496, 247330409031279710613461799202108127414303908845699778625613599995188362419887949548834525989676107135804042099129384937319571829813045977014915636734868500073187018078381350, 567425447823840, 145277404582049, 145277404582049, 
    145277404582049, 145419138507169, 564126809128993, 564126809128993, 564126809128993, 564332967755809, 
    564332967755809, 282857991307297, 282857991307297, 564126809128993, 564126809128993, 564126809128993, 
    564332967755809, 564332967755809, 282857991307297, 282857991307297, 283957536490529, 564126809128993, 
    564126809128993, 281758446125089, 281758446125089, 1461864025802214663426521738718235599187684629922, 290554807591201, 145419138507169, 
    46385726981044820237992771771979780935496768930, 1046199806413757721292132953433353256466842702591735998440965672284004502372244827601535580070773412]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [565432513792096, 565432513792096, 565191995623520, 215574208054305, 145273109610529, 145273109610529, 
    290829551018273, 290829551018273, 290554673373473, 290554673373473, 565191995623520, 565226355361888, 
    565432513792096, 145277404582049, 145277404582049, 145277404582049, 145419138507169, 282033457996065, 
    290829551018273, 36842365002017, 36842365002017, 145694016151969, 281758580351265, 281758580351265, 
    290554673373473, 36567487357217, 36567487357217, 145419138507169]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580615292389600, 88236950094881, 580617442101472, 580684011931872, 265785434843201353880842708301710276394937755331885218706106391932234076389357765642913003459002261188, 265785434843669645873327073648629838204349005505444810729100944476668953281599786954287430198738575044, 
    265752994540108411252272281178803296057984686439969978397743290674732530520570601884281285423588728516, 368230612510777939390525540809631618146343453091, 1461864025804172166962968141256550210702026483106, 565253399382113, 567521309889697, 564085168276513, 
    564085168276513, 265785434843201353880842708301710276394937755331885218706106391932234076389357765642913003459002261188, 564085168276513, 567521309889697, 580617442101472, 580684011931872, 
    265751030381104730270277535265267887877453131408416701503771209473969036056203090369219587449305646020, 265751980780636284726588424648300224776703874990108203048915113030664600632604321607126399098510593508, 53052544417825, 580617442101472, 580684011931872, 53052544417825, 
    580615292389600, 1464356840508960158100059012405800438145049175458, 53056944474336, 158608985950432, 158608985950432, 88236950094881, 
    158608985950432, 580617442101472, 456791912024916798872480452023733297145563109635106014674315986135837947868575154557449151775528476356, 191040945127532847629300509356555999372904753959217172962180242200588377362382449860710078111619768004, 16641875742412316784231806828678235166152644401024590069405123379830038217139149702585180051110649540, 368230612510778101650421340042637699896163173283, 
    228773721278688, 158471546996960, 228773721278688, 158471546996960, 565253399382113, 567521309889697, 
    564085168276513, 564085168276513, 1464361718812918590195893712420361200856327529762, 580750586087648, 580750586087648, 580613147134176, 
    580681864448224, 8337158084876851524728486526446717380466427273229131032979319773293678249672692611109909853954395236, 53052544417825, 53052544417825, 53052544417825, 551485184257773599563979394960585784816016885902218952986827693365999045343718223884306423051718596, 
    551485184257712285974206110450973435119369786969070734288945538974214536237008896103453349679206340, 94199055511234149291888319685105895527166780706, 88239131100193, 53052544417825, 53053618192417, 53053618192417, 
    158606838466784, 580750586087648, 580681864513760, 265783787484047818631458183496871788330209802535828999731814274296434407192041260616204353456013843108, 266821493095122442477757434172849719351741393576423300524752595587458103174187310037942706560671423140, 228906865264864, 
    228769426311392, 158469399513312, 1464356840524906411622081501481989059042280482082, 1464356840524906411622081501481989059042280482082, 88315333444641, 33251439385686811160569273645768217023006205429333838491322128621638618418309872740634033866753186468, 
    22881261663389434989934144678244133902987306274, 52853902409761, 53060060839969, 1464357014729539784217367443855384685494252610850, 53060060839969, 52853902409761, 
    53060060839969, 1464356840504967920696874150607585680428928345378, 53060060839969, 88315333444641, 14278063002748050469660628056533714483183354275, 580617442101472, 
    580617442101472, 228773721278688, 53053618389025, 53053618389025, 1464356187166811775660673642385701729391224029603, 53053618389025, 
    53053618389025, 265751030381104730270277535171348923590327180352610351075114631035630380890672948255464693779530990532, 580617442101472, 580617442101472, 228773721278688, 1461596415843597270637536285950170490823745482146, 
    1461551814353199580678626195392294802562908431650, 145139831406625, 48526606666280067543483160247222248312920081315, 48526606670928471350681391262055554515336703394, 25690643587632484590639398200948451791352636706, 551485184257712285974206110450973435119393480691066119188348510082807928773508177476679040079499204, 
    145139831406625, 145139831406625, 578420566329824, 571892213877216, 431567050901984, 46737973905888, 
    150092065802720, 150092065802720, 290829562546656, 290829562546656, 571823494334944, 415284540732747162117829705486018152883658660353634906858820313996794274874649813785505762009043246788, 
    308436323322105728520880430614472526670198252297056079215405661587625647376905142339658993990704836, 282409058830929381025240105966198428225844447575241959027888932274248471530744559539422333607164583620, 16658095893543367776301115112215507906304085005593352917363430821584714426299048828388187499504934596, 132924142480290222037920208731226519360596889737175525387397836176819559177266540217599649247170207428, 132924143965289456161831515790488492358365496614244333027754491425579485813958723772711163300795981508, 2124839861371993694923700854630416521706274072057802480740247512064988884746220795650263274241203908, 
    290829562546656, 45761826407232773384909911167531607101641616802, 37941880883680, 143494996036064, 143494996036064, 565226424568288, 
    1978643219271028833475400513349780785764059803593180872443710857551188889353792323969574785904653037767804115528005628311087773628577868290155058038227938720790606828974778150, 1978643329836334248168994818800014454893647051513678405930581336126604633754343583090099797788096511017972610697812827896024573656435140898149870732927684226426843679307736870, 569624473307616, 567494167366112, 565226424568288, 569624473307616, 
    569624473307616, 265783439004225616607008523913951746123043096944065978590801312805534735164944434790780970954801356484, 145273109610529, 145273109610529, 44263968079905, 44263968079905, 
    9079562436641, 46028912996243421226257700624509243081980671394, 282395884165244226729414774623001986467241705634713756618298433685082678027957572408644772203204304676, 9079562436641, 52819542442017, 52819542442017, 
    53060060610593, 52819542442017, 52819542442017, 53060060610593, 88003948119073, 88003981640737, 
    88038307857441, 88313185960993, 88003948119073, 88003948119073, 88072701117473, 48527303564568802091240952205660977145227783586, 
    79448373724193, 149817185018145, 149817185018145, 143220115251553, 145281699553697, 365466006471646154284629664738497539979535199650, 
    365422798777823352328574893708493090720095675682, 282858226189345, 282858226189345, 205613567969359667089821938218005241891647923618, 182777604888385274562208632254372262045607798178, 66437869465220763316143089532826203076183816467155712307983644292368860857092621607968669950317704293, 
    283957737818209, 290554807591201, 290554807591201, 578420566329824, 576290260388320, 132891703662604454512555867168697828909069262007479854487672653047007674557035041520632238629986719748, 
    519108241116671364975733943594938990081016694416437229233565025866923789111582718647763874907112388, 94199045999288387650736148994912086716028839202, 132891703662604380751846365473047167435749987301996367908787982786085227027282609246610159744726554628, 569624473307616, 567494167366112, 145694019291616, 
    145694019291616, 732180855333725201323445606549341590771517138338, 265751030381104730270278304555510914993640317461704061837512124526542188883530744907537196163516285892, 565226426796512, 565295144110560, 565226426796512, 
    265751030381104730277649446130078588815480744728193591547434771899918675336881315900229901028277044164, 569624473307616, 569624473307616, 72709637148833, 143078381326497, 569624473307616, 
    74908660404385, 145277404582049, 145277404582049, 74908660404385, 145277404582049, 145419138507169, 
    519108241116671375794594113349721735189236322225678867642066138124051429292242894051115273120072644, 52819542442017, 52819542442017, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52819542442017, 52819542442017, 
    52819542442017, 52819542442017, 52819542442017, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52888329061409, 88313185960993, 
    88003948119073, 88003948119073, 75188168832417, 79448373724193, 94198707057438735426767669767552359172416220578, 142120603623713, 
    142120603623713, 1978884747222783456185379191100483388765130552759692159062909161175373963017227321870916896755428448238948496596172269137703625848199497771022380491967032003743911408926961446, 142120603623713, 142120603623713, 141021091995937, 145419138507169, 
    145419138507169, 52819542442017, 52819542442017, 9079562436641, 9079562436641, 142120603623713, 
    142120603623713, 149817185018145, 182777691998350889651594041784203797765525349794, 143220115251553, 141021091995937, 145419138507169, 
    154215231529377, 281758714560545, 281758714560545, 132891703662604380751846365473047167435750017093709682341667389272351434829293138794898694993952856068, 732180855333725201481901931577870265958605039010, 33218935722611761806880484664749187571624357581326648360467859742017385490025374371259118281484878788, 
    3879633489801668436839246347618501545532100722795991394438257467927692209038335033143219006737316285737360559053608605324929159894196974736212526167896676808794470483711782, 282858226189345, 3879633489801668436839246347618501545532100722795991394438257467927692209038335033143219006737316285737360559053608605324929159894196974736212526167896676808794470483711782, 282858226189345, 281758714560545, 182777604888390466720417882682038201753235105186, 
    283957737818209, 281758714560545, 3864655464910453568257511072522472795374019957926804551958585385415209227539367910602160259954495839082935926337352543737251365070445916081295318867984488941961159495014182, 290554807591201]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [44540020172065, 88031799543904, 580681864448224, 158469399513312, 88238024886368, 158606838270176, 
    158606838466784, 290554673373473, 286156626862497, 290554673373473, 88244467337312, 88244467337312, 
    16662150931431873879035661911235814165396651080369372517640129643792835843873513268877340807908892356, 16658095893543367776301115112215507906304085008502699961369124825446449536103560471066026396424675012, 16609688878692677949137898630977887529057843484206301311570943228486459561411482292564389013962556612, 9079696662817, 36833774829601, 36833774829601, 
    730842809600955878539077721977649862829041814946, 213375184798753, 213375184798753, 143075160097825, 215574208054305, 145273109610529, 
    145273109610529, 290829551018273, 290829551018273, 22925253537925832852981985252140647472668608418, 290554673373473, 290554673373473, 
    74912955376033, 74912955376033, 145281699553697, 88003949168736, 88038308907104, 88244467337312, 
    61848403839529232214468087892861177496180681898162621828545991845241119140226260349645259114084563817393668864949974586350056562097850511024398857851488305833668287457640230, 61848403839529232214468088692028806377074693131851512655596566116882243662458874969589440778179728955253667615748336970604001179013544878104494319086170079731469325867925286, 91522607445766636584894994473903720401723757986, 145419138507169, 213380553513185, 213380553513185, 
    145206537619553, 145206537619553, 219977623279841, 145277404582049, 145277404582049, 368231298536001055806153132919557142912363414946, 
    22880608321244946802938973368425646347797407523, 145277404582049, 36834848572449, 36834848572449, 213380553513185, 143078381326497, 
    730842809600966263172408872890039092618472230306, 213380553513185, 143078381326497, 424699386933729, 215579576768737, 145277404582049, 
    215579576768737, 145277404582049, 282033457996065, 290829551018273, 44538946167073, 282033457996065, 
    282033457996065, 282033457996065, 36842364772641, 290829551018273, 290829551018273, 145694016151969, 
    22925253519321437720163327736398228749732554146, 182777604888390466720417882682038201753235105186, 281758580351265, 281758580351265, 281758580351265, 290554673373473, 
    290554673373473, 145419138507169]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨1, [], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_0
  · exact tv_b3_1
  · exact tv_b3_2
  · exact tv_b3_3
  · exact tv_b3_4
  · exact tv_b3_5
  · exact tv_b3_6
  · exact tv_b3_7
  · exact tv_b3_8
  · exact tv_b3_9
  · exact tv_b3_10
  · exact tv_b3_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580646329190496, 564325454709793, 567624123810849, 2415337909841188095370712234775366329940453084132835857266049504924725359055737824086313825244435698113625555515733320703791997618422932927130876340507898974831970862671654, 580646329190496, 580646329190496, 
    123421290727520, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351526178370926382825721534092318953103670718174424119329185788576830694338878844557781286032910710689422553902452623873990057666526701974999530886347673382191768792548486618074901339582464486231871538912960222515656341996994752960799037203108568009715665921153204216701908497077194728422621327257706615989181783185410547749396684621433172105626132111176179217887604293375585249575061890587333070652089718419241680632333119825792068387873447150074385988539986849667476727416845296400413797898030, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 580648478836960, 564325454480417, 
    565425436073185, 567624392152225, 567624392152225, 580577608665184, 580577608665184, 580648476706912, 
    580687135738080, 1461551814183058052351566407747190105717760066978, 265752994540108411252272281131948634137862342345329376603206483602215547622169549049995749800335678340, 564325823677473, 564325823677473, 1464361708588496461248882028300339658628276687779, 
    1461507212527836739910363371722207058301473523106, 1461529513358105862263739523306341408103803127714, 1461551814188374984617115674890475757906132731298, 1461551825077410726087146505718463195722715497890, 265752994540085751962200810330748666540694791401796776248839312137504071611063059066227675669033714564, 564325823677473, 
    564325823677473, 567624358565025, 1464356230722953767981422175021998432235200972194, 88236917590112, 88236917590112, 94198707067427454380637360583561794639385597858, 
    567624358565025, 1982749284860969392887280207987783610871466996499715810074701766986012142199930256843420905335557281536995470394971298990700930294072251032205285481135405141467279224284882726, 1982764410194750122970980988588570105092407386125972114495166369041701948151521137401203421325884975014295109256012642819327829699128722755981148234415443998050459234917656358, 2968221476721395911463059958353637030322414197924683716333860813541162146582843238778888601151044450904936008831456644952262218590266075805562031838614423566094237396703880998, 283125590787105, 283125590787105, 
    284225102417121, 36835019719713, 36835019719713, 37934531349729, 45631112750369, 91411103124259396610367800923972526316529911714, 
    3381578341693589203573397599502001423639513874536637613221310728339829316874796487253223026680119849966547847779811295526602203675139398579783224951447040395043042776665879888771289405782298835781885756287199381360951160787191653843175950355377602966232978134527769802133505143970573051151282948859550946683343286998854869092510922792053880067272728644218934002996092895288807403, 142388236649505, 182710702416187494792801618027792928452528048034, 283125590787105, 283125590787105, 283125590787105, 
    283125590787105, 2062153481806272082696230099498809485374663185562076457660896771723864471687240533595123451007167003469957402452784032660537998172102876044099509281235822902922248959058492711, 142388236649505, 142388236649505, 580578715961440, 580578715961440, 
    1461864025804167289658714133649602292448175063971, 580613075699808, 580613075699808, 1461596415838362441859455598862257813112626611107, 1461551814177824197152664610067797544538059572131, 1461864025801591910099930732245425747610332038051, 
    580578715961440, 185542907841756801165800578694734280144485352355, 580613075699808, 580613075699808, 580613075699808, 1464356317830588357568695271320917333352907279778, 
    88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 
    580681799370976, 580686094469344, 1464356317832582207168276303168047247359289601442, 228842373646560, 185542907841756780883390975043062730293032256419, 580680791098401, 
    88238024886368, 88238024886368, 1464356317835240673301050880071292279017733361058, 48526606668269102587544453187528831558675071907, 88238024886368, 88238024886368, 
    88238025082976, 88238025082976, 731110419545566014228979025326678953383424164771, 132876499250053204127652857062343501514054441412196596376778551283343757072117136448543640861693941573, 551485161054599252787988895751659964160240593110359001461221882560037137441668838095124126113264644, 488939176371167750122479837506656181880713256327783968008718928137630499674157553141026467699594272342208380717694967334119649877412147711245273705106453586113949278238775788022828987654694102913814260144579999718710659035175260194100678821683777910097313920622998761, 
    551485161054599252787988895751659964160240593110359001461221882560037663875678388681061817867629572, 234839012131548078085559836105080199830132563338198318611022250068046974525065296633660349376597227498932487400348255543883611114902617517719545809388974783844475022006519385603974406137512067969002604175890734842711639481328222617932207504951225870188562122998760, 282850713142305, 282850713142305, 290547294545185, 16641875742412316784231373977134354840303423123443909307375798524182157023640718156546980745872471044, 
    61847696218876081133648532114025352445965965699128136345754243197869796781017837059089805213469640129870189656078346966552879686632455327101377501606759866467488212049706022, 239867512599282460298726820536461589501687638947, 368231298520029814262402438815419302682451772323, 282850713142305, 282850713142305, 282850713142305, 
    283950224772321, 282850713142305, 286149248029857, 53054727620704, 53053653846112, 88238024886368, 
    88238024886368, 88238024886368, 88238024886368, 551485184257712170723207426278453692238237792974056778249639716234397629292367806759544118629702756, 158606773258464, 730764756684370066222287342824270999519756551075, 
    730775907099504627398975418616329149663840306083, 730753606354306096775833882898056501233614848931, 290547294545185, 283950224772321, 286149248029857, 291962732323023090610657363470801025536376144116876581682062578581469852247580880010041601814506820, 
    45287664297291153648993808650978138268244481317250563670330160614406471449324272285505525987296899035862993609343178554740246496181212267370373719589899750409497238656807, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 269416721272826801985775785541464292775933284380511360933836614225917810256486157768406234569394695492, 2108619733444055966542291085149140100899869405817194885692192211412797122692729368549036842889311236, 291962732323023105016161381752216401732287115977390200477850003430571063239184130926755080711762948, 
    2108619733444055736040073892350231783795746672362558990133177616847413947728243467106780154618508292, 1978658307750130403652078844387023550925337190128941335339870008173111329784261698424267587418865036631653673914376007536767498120442862374124968042252530295595862118915200806, 2108619733444055736040073892350231783795746672362558990133177616847414474162253017692717846372873220, 1978658307750130403652075570996415654783467132576529401807680038276438053742805961390967333919391516468557901239719110707364130424259195728813801516938705951306234377877935910, 183045258415733431442659162770716032405625643939, 142113359004705, 
    16641875556787413440751762143777470093037922804221074878260175784881357109795955222746260086824122949, 282850713142305, 282850713142305, 282850713142305, 290547294545185, 283950224772321, 
    286149248029857, 580584157186272, 265785719963038019306933667855116887407957207679802917800136637640007690955765678458397693222433418116, 1978658810821847388679108615728090579101047978651067971390831864667978036068914964279267975461877719973145713458247487217472370067234666897373050072632793955033044407770146598, 580684011931872, 564325454480417, 
    1462220837730002255269132840286975734142606771107, 1978643241384089909763846640838663517566217621753008739587996067383891851968163714416576312575760263035096576365305019323099566474405700406895824989303594373791173648048973606, 1978643329836334255033792478930624166828642580121624955203296598685449033502152596269628231799593697231084375488892598070056567149897712844548243021114342535062640154720818982, 580584157186272, 580584157186272, 256629561980004568547537148242723635068352586470684813130995139968140735703653191367933689101704056524915884114980518457546403268038815154592510599874165501662802299475750, 
    256629562921964637577751621226329656263099133917018383194382296224208889934676538586616993256519272046398497064536421679184748467731469186822593655338578177267449182443302, 580617442101472, 580617442101472, 228773721278688, 564085171422241, 564085171422241, 
    580617442101472, 580617442101472, 1464357014728881003962411330610203687763667594658, 228773721278688, 16641875742412316784231394584905083586404828919108361468810981153902126270517065813883039218458996357, 158471546996960, 
    580684011931872, 1464356840506301691967284378834157612050862843298, 158471546996960, 53052547564577, 368230612510778101650421410878405158918483608483, 480481077047106023417608928812220475621679691140126938132446925915845818451067871585851485674779503600845030881056129750655237608253697744866894986898412447880805374588361001744356287680997204065845466733522940692808401884709191053896157578041545593395879938624578280, 
    1978643215585518646978916083887156159871267932237536735174074438944238569036254857207932212696333830359420182067519764989913271592453338160472424492767452828466360228944434982, 48526606668273970384419034640617149741071345058, 256629444902802611661739412627240199085161552244778173243235960756986740629479012524466927876685169630196651010660950068126077086006890664238863144024107773695580581127974, 256658928973702200747542086469917423923579749103233441683948161990923798346693511671057231103149319381624985341298556766003577177861368323591714707605544658233161775294246, 259775868603384269922686089263728683130131485468566016744427326236565791813395494038655170418665508, 288621376783731252276945334416367344685631943167213647335793373173177097307585339572461144268354632261, 
    291962732323023105016161448155859307603112226308791559182205673817679543385067670516841524379085700, 283125355906081, 286424025007137, 2967964847334094142790534565495942894290806081588745824760363666416087143454039040971400032281964117562013341988928980736524487739552181626804592627772791707390608062505008422, 268897676423098020835752910709862756525011056959003128318165659576948934283754155627785639305082059333, 2092399566058740735068065036014131628472055539333215595492349126397264093748269972767056759030486116, 
    2108619733444055736040121984730598892290064572253298904587185658392444794017452800824077821914738180, 465066216835937661938260974420118238929494864333171955331588820126930513860957300690797535541515270725, 148985071338529, 185542907841761638558905876609777112021473961378, 989321635434085677161180641965087114300653893817659666921525389682807852426274726002283072800574735964671661775949301924111670603124108066973411608864548411697693072246684966, 283125355676705, 
    1984440019912342195969222754386660348744783430703271039525651334900562624373468978272959509454090119334829458194915764463288214899187813372483771881778855272441588476353160998, 36834751054881, 36834751054881, 36834751054881, 36834751054881, 17160510691429025185760866878542165099105616675, 
    2062168592398009454738483073582752505135686806555657344191751879816041378989950389955011373384394234210699757771692549331437069259438179541574865077308736997365389976064212263, 132875735960437393561945257729544290316199400617296354943943213104411722037246814990504141715744265316, 731110419564195731373076798821243516127178958242, 145274085835809, 145274085835809, 731132719118385533065640293497218937665729332131, 
    1483982438409087793570614092836927756076648413234323876023726887110886219417453821481492099791862292729260962945004370035641778919709488547275921178719928762804513259320753446, 564600567268385, 22858351047118790312341079409045840127043569058, 399673823145441, 1462215438485637117535219554264088352308708273059, 293021195251169, 
    564085171192865, 564188250407969, 568620656759969, 567486785393825, 568620656759969, 568483217806497, 
    568483217806497, 567486785393825, 36834985935905, 142388102202401, 327106055906593, 182710702416187819312595634354685742761533506978, 
    45631079195937, 1461596415840942698722724592725701640651419428258, 365767153431434634298232246806513907940846863139, 36834985935905, 24263303354094267839379794032493113305297618338, 399673823145441, 
    327106055906593, 145274320721057, 145274320721057, 36834851816481, 162201519890827817511536265787101897056688430089044941540925893613117369005752599293441561715644260, 75479248504339073950171048391661825880178811269791609704816428123630267173093951473673537873593226185371165783743980864686518509561406950282497291308893924052517132064550, 
    45287549105766743132238611743755674752840668836765965462870242264128797823041825421436451638355902483502400082387368534219350395076108937133483371175779989151133829977894, 36834851816481, 25690556491317449418341342858051310647612278178, 2108619710240942702854620989769378371493332699280136643416557431851649308117252986145175367680339652, 36834851816481, 37934363444257, 
    44531466765345, 2108619710240942702854620989772628414078086633454879002907031792481733166579700258732935756126432964, 2108619710240942702854832306403898621896351482245503451496233976121316639492875668088214478861184708, 36834986165281, 108303241972961, 36834986165281, 
    72019123143713, 72019123143713, 72019223905313, 72019223905313, 72019358254113, 74905442321441, 
    298937397101151230930536545322285907068455008716405370289812855926230733386576862681559111381363210821, 88004150495328, 2108619710240942818105621363643031080818009042086879280656051476713042161879809224100738728112237892, 88244668663904, 145274186499105, 149672233010209, 
    1070530010783380518061108401250008830808941323650020090672272810615024616868070985346791216033844324, 290697560111706829943434310504335278661232069711091651872526776330472898002617775934295241476430117445, 966149122907510248296126204581808566603189877065825473055087098563131319285553601390346849682955695287455925608994834009148524735293456218521750626645390215573554569369382, 283950224772321, 16609688693064941272390051504078365796348309773574930072459219318007600310722599722875078786511161028, 182866808207135930470836328696010979763768533923, 
    183045214849288909297845541368941381519352800163, 183045214854273533296870515141649719302077817763, 25696131656432430395413549300015874831639119138, 25696131656432430395413539855282838723604514082, 154207986922913, 185542907841761638598597329414512522271222408610, 
    185542907841761638598597329414512522271222408610, 145274186499105, 185542907841761638598597329414512522271222408610, 185542907841761638598597329414513085216880862626, 989336701756513946551633305859901898115936771060957333712967801314443117209407033117605087431733340660226519630279920940350038322847302712359872640711260359131573531414867750, 36834751054881, 
    36834751054881, 36834751054881, 36834751054881, 36834751054881, 145274186499105, 145274186499105, 
    731110419564195731412768251625978926374779921826, 145274186499105, 145274320721057, 564188250506273, 564085171192865, 564085171192865, 
    568620656759969, 564085171192865, 36834985935905, 327106055906593]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580615223183456, 580615223183456, 580615223183456, 580615223183456, 88034014136416, 88034014136416, 
    88034014136416, 228908945639648, 88034014136416, 290550519957856, 290550519957856, 564325454480417, 
    564325823677473, 265783439004225734624146370479393073482713426520553944321377951062398286185558108421523209513670356676, 2125093301300450100468358697445578821046335593247926585678523813163758314649594863508015754252037828, 290550788131168, 732180864850979437470565335558054178544102704546, 265783439004225734624145923961796311422433966033303569026171190688902569886287075280948685287575972740, 
    281754426935648, 72847018428768, 495059621906912, 154211216525792, 290550519957856, 81643379886432, 
    564325689361441, 142113359004705, 142113359004705, 282850713142305, 72640851609696, 72640851609696, 
    72640851609696, 72640851609696, 213378339965024, 72640851609696, 72640851609696, 213584712305120, 
    145140367231072]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 36834851718177, 36834985935905, 9080097802336, 9080097802336, 
    732180864850997610578894849654733641819303216546, 5753614230702594312420318140803585265730857379, 283958013200736, 5798215891240839019172621309036185704626923939, 281758989945184, 290555082967392, 
    45639702684961, 45639702684961, 22925253537946277599546221193286166653685990818]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88038308907104, 88003949168736, 88038308907104, 88038308907104, 88244467337312, 2108619733444055736040073945179649982523787674473684621606527587445552260624270576682443703002133508, 
    36834851718177, 36834985935905, 88038308907104, 88038308907104, 88038308907104, 1432828334178097069929407614776357822635967906, 
    2108619733444055736040073945179649982523787674473684621606527587445552787058280127268381394756498436, 88038309103712, 36842368147745, 45639669130529, 45639534912801]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 88038308907104, 88038309103712, 9079628499040, 22858351036505046087704026701463228968681382819, 
    72645146576992, 495270008195552, 290554680707424, 281758587685216, 290554680707424, 354395210910048, 
    81924626655713, 81924626655713, 1984440489929837483293235241291086758375741837860202614833627185401425533326208190765865034442555685500416473033491816736567212240531016896023039557550153891441492212176648998]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [123257008228448, 123257008228448, 123257008228448, 123428806920288, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351717142984214254662347383686083590644867514403640469517019407014118370049617879117055983964809807886972864025622581570419213603682712442395599112349605641516208329741783448167392099499040473080079728415519920417388674947597616311532368730176083550323265613926877108787448443396460552997483026703540052458472036787201631336472754167448202837960499327191419378093946161178641950460701706036238144440645692730114056418587382450856814804232882843262651519955831306953229231819553510355256549562158, 88003949168736, 
    88038308907104, 88038308907104, 88003949168736, 88038308907104, 88038308907104, 88038309103712, 
    497400244865504, 79448374773856, 88038309365856, 88244467796064, 72645146576992, 72645146576992, 
    215581796600288, 9079829825632, 266140254622296127312129299213221869627250625909798475537396539540831788541009512089385598645109364772, 81924626655713, 81924626655713, 74844169832544]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [25696044544229575384828505936284314909561849250, 25696044544229575384828496491551278801527244194, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269518246845658697122, 290417514383840, 
    435553049250272, 36567889741920, 72851506333792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [16644916896595362606194719733137530198452223968205265722021357604898191729631200863325446124574727780, 154353084533216, 8340199424715012154549699770557994538954024863845222243612596443653748321047420327311608465526948260, 149679749204448, 149817456593376, 149817456593376, 
    149817188157920, 149817322375648, 16609688693064942194413866485572845602054608574280450093608263118845854563723652457336820354294891844, 143220118391264, 143288980474336, 145281702693344, 
    154352950446560, 154215503104480, 149817188157920, 141021095135712, 141021095135712, 145419141646816, 
    154353084533216, 154215234669024]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 88038308907104, 88038309103712, 88038309103712, 9080097867872, 
    9079695607904, 9080098261088, 9080098261088, 149679749204448, 145281702693344, 36361228257376, 
    36361228257376, 36361228257376, 61832602211931006545952620795707570920629961556582665318838464320757278005018180782647807751939661129647415584881517083439809957099473292603705926824644700917782604733726503, 36327371343968, 36327371343968, 182710702405574075087992431570052414887610581923, 
    72645146576992, 72645146576992, 72645146576992, 143082679437792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [368231298514733347026056182693119085570651866530, 368231298520050259009195846184734313811773244834, 36834985935905, 11440325949328794423484043742211855044299467171, 11440325949332688660983225334358238429414695331, 36833912161313, 
    368231298514816403810605272530975465712095085986, 368231298520050259009505332375142916719127315874, 989336701756513946551633305859901898115939610101432257544833080886329657572483162615939414065826290204338389686058779831571048314798289717672398024251824231730676669569019686, 281552563472736, 281552563472736, 8304780986568768591145375763158153178624701317834816914121106810927450699452556803786760229645133733, 
    290554680707424, 368231298520050259009505332375147279597909329314, 284026334611936, 283751586728288, 284026464635232, 284026464635232, 
    281758989879648, 91522433200238746533710073470342660892449184035, 281758721902944, 281758587685216, 281758453467488, 281758721902944, 
    281758721902944, 281758453467488, 281758721902944, 281758990338400]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72645146576992]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [44538848649505, 44538949312801, 44538848649505, 282033360478497, 282033461141793, 519044857478258431224927348913358577860456706946898352136632176955061585460679309884105158674298117, 
    266529538259592713261084123339689282262670312031212436050035342328378926152146714291314930460641040420, 266529538259592713261084123339689282262670312031212436093176308139508280139940854537552190859284420644, 267886954284390445574071078493450397308759794386031781446571119598062259318942787106971927180902722405, 84121267315105, 2135991223254437984746673734937780556798411501574317053291269305080394540947142966953732060909988709, 266140254622296127312129299186440290769307979327943446858122296418142644139076025152119188581832038436, 
    91355351197792352758278187256483970604033640354, 141872971417696, 265750970984999482815610430483453287654720476041595239667395950134249470782536131160317453919024420900, 265750970984999482815610430483466287825253209414949977460405333147096644468692756544807131083335374884, 141872971417696, 36319855151200, 
    36560373319776, 36319855151200, 519052773592314808620951952878429528499687685824660793738222441783778821940779783000071940679505956, 11429175534193259687576444552099457472706119586, 571789033906465, 1461507212517389554755246540980438905766912491939, 
    571789033906465, 571892213784865, 35742755856673, 141295972786465, 141295972786465, 563096120992033, 
    563096120992033, 519052773592314808620951953245298884096815844001878235966239972047389959731348967837099172441462820, 1038097623321096073894050824243954207278306299171730693471514646715681313533111146990003211752020004, 571789033906465, 571892213883169, 567425447829921, 
    177061642766560, 177061642766560, 177061642766560, 519052773592314808620073089333369249175410802349572862293192422692837790373524405521134468995323940, 177061642766560, 141979275102432, 
    61832600598648638020570484964173728965800415309145707011219247430918064923509617443035525406669674676445523033360990694982933502699656427947531190752809713633409444409648934, 141979275102432, 35742755856673, 141295972786465, 141295972786465, 563096120992033, 
    563096120992033, 268086696572633456944473943235793159315930706974597350010997670356238355588508488977327167771408150212, 401481222952930212500126771340084097847224634114064840642560768271170241801574665029668293250677550788, 730764778453157326950446389265263201898803537186, 36842267255073, 36842367918369, 
    36842267255073, 290829453500705, 290829554164001, 22836050387010971646546585449079425585419157923, 81922479172065, 267859962938431858908404585158080272904445380002028743049414247542502765231922026912406642013778923877, 
    74225662665185, 2108999877295851319080180399567656152483997117571278656134397249520900453926382772388446893786190181, 81922479172065, 91366501612926913934966263048542120713757656994, 141872971417696, 141872971417696, 
    36319855151200, 36560373319776, 36319855151200, 290829688381729, 11440325949327820864264520344157607582430136226, 1461529524151540669285956585730406476968523498403, 
    1461529524151623826848418907526698991945001239459, 1461529524151623746352605793034131996904347698083, 1461529524154116058352118279920486170193756717987, 36842502137121, 36842502137121, 36842502137121, 
    83021990505953, 291929199781153, 36842267484449, 145694019297697, 73126251864545, 45638595421473, 
    290829688381729, 45638595421473, 81922479172065, 290829688381729, 145694019101089, 36842267287841, 
    145694019101089, 1461529524236694338082845244603254143563006518179, 290829688185121, 1461518373778941403974384608945450520566342648227, 1461864035332094017699241315694576423383941030307, 1461864035332094017699241315694576001169865351587, 
    1461864035332094017699241315694576001169865351587, 81922478909921, 290829688185121, 177061642766560, 177061642766560, 141979275102432, 
    234839179937625725399785637170026631905791442318244139240761352556851894793540841549500167086573721909217168821110234999747824250231339354401499247709445993959818928543200940140226929902426912180625618004737454192103263063350298457329886160329890452218000123494281, 11440325938693956333165386317042978760876885922, 177061642766560, 177061642766560, 141979275102432, 141979275102432, 
    423600289090016, 1461529524151623746352644478660360197203579405219, 36426158835936, 141979275102432, 36842368147745, 488927266614483527188666297671265138138231160342456660308215515478150195860818728940971640348494930510471421205511727851498656121261255892701331139423825376713200670136530577424803526330487453414830152084163308519250188992099775978930420842800017353081897088124938761, 
    1978884747222783456185379191100483388765130552759692159062909161175373963017227322123509295609850297551749768951612288320888437991541760332204659286546943485011581351409725222, 45638595388705, 290829688381729, 36567889741920, 290829688381729, 45638595388705, 
    22858351047138910539610666257579863707628897187, 283132872106273, 283132872106273, 283133106988321, 283133106988321, 36842267484449, 
    142395484414241, 177579889860897, 36842267287841, 142395484217633, 142395484414241, 283133106988321, 
    283133106988321, 1461529513350150899104942563246621978563360883619, 564092452512033, 564092452512033, 1461529513347658677108622692564555205986360525731, 564092452512033, 
    564092519657889, 564092586828065, 141983167815969, 282858229343521, 564195632881953, 45694401224110967890824698060184156271556985763, 
    182710702405574075642589569169902778042418234275, 730775907099525072145846121975095445811797984163, 71752063923617, 142120875205921, 282858229343521, 564332970909985, 
    564332970909985, 282857994461473, 282857994461473, 36567389839649, 142120606769441, 282858229343521, 
    282858229343521, 142120606769441, 36842267255073, 318317512631585, 36842267255073, 24976929922695149516470799243815114423536763171, 
    290829688381729, 290829688381729, 265811792590005360315000283544750211689065523584806084539262089115086989585203733232451731961627343429, 79723590263073, 290829688381729, 290829688381729, 
    44538848878881, 150092065808673, 150092065808673, 290829688381729, 44538848682273, 150092065612065, 
    150092065612065, 290829688185121, 1978643226642049188448275514282335596360334153916591705545571203266111934756485911779450602938525638149413622843903736911000338623614780312303907709066347647824836608274421542, 265807737552056429439041995755217920631544499608146838780830061328379358059949560130303250816518912581, 267827399859917987289356521017186770752455264120739252408581600694254743145051321482077415516658008964, 150092065808673, 
    290829688381729, 150092065808673, 1462934465657105647298634020235175039534737949091, 571789033906465, 571789033906465, 1461507217961907425490261956394432624675203875235, 
    571789033906465, 571789168222497, 571789168222497, 213449211119840, 72707427797216, 571892214276385, 
    72844862556256, 72844862556256, 72638704126048, 72638704126048, 72844862556256, 72638704126048, 
    72638704126048, 72638704126048, 2052371371315403541614559934292352371708363918009079696877117222637762781027665102380355344071577886433240535861246868602575022030417201507659756204906286921336954565718697766, 143078384470240, 495070292216288, 241537395990455532404661607022772314804523262191177869786697130884535018194882324987273827821308005168166669084639520559219005995437555796326056955693086049214837369231142, 
    44263971234081, 213380558751968, 213380558751968, 213380558751968, 213380558751968, 143078384470240, 
    495070292216288, 495070292216288, 72920234199392, 44538848649505, 44538848649505, 44538848649505, 
    44539117314337, 44538982965537, 72920234199392, 72920234199392, 143291127957984, 22880651856306457964047589284486984122350699938, 
    149576703549729, 354397358393696, 494932987480544, 72851506333792, 72851506333792, 8305731417490991822198750988250692466801143723125570014684467186718712480143613388964821325217687653, 
    11507206662063704983404066160907277331625150370, 265815784267942908839380841476552725439264220120388200709031968028485073768323732822143885558332333381, 8305731417490991822198750988250692466801143723125570014684467186718713077082177825095652088836417637, 1461864025804187743912926861876721035868440142243, 11507228440135187924085906766956143749842339746, 22925253537925832852675517834519905690251167138, 
    11507228440135187924085906757732771712987563938, 567494167306657, 564092452512033, 564092452512033, 1461529513347658677108622692564555205986360525731, 564092452512033, 
    566291542913505, 568490633339297, 213449211119840, 72707427797216, 567494167765409, 72844862556256, 
    72844862556256, 72844862556256, 72638704126048, 72638704126048, 72638704126048, 143078384470240, 
    284168070629856, 283961905908064, 143078384470240, 72844862556256, 213380558751968, 213380558751968, 
    213380558751968, 143078384470240, 143078384470240, 424699398457824, 72709640292576, 143078384470240, 
    6559998005155875671795276005997647789902152602174762625604399404117417065935997527971294023111235392136759542020291619114137023820374324012857883704173123032327190092380811577800534872248024462474358933150740587733950518564325381772113812045549899634725638159458207573952838609726233641081931896193930554956572997287475958743066428468826280697071433785127138398307621839915, 11440328570585812451527870566639035493134680995, 354397358393696, 72920234199392, 143291127957984, 91522606786552546612432809996723952924590379427, 
    354397358393696, 354397358393696, 494932987480544, 354397358393696, 143291127957984, 283751586728288, 
    284026464635232, 354397358393696, 283751586728288, 284026464635232, 283957745158496, 732180853993946377509377030002552157031226180003, 
    283751586728288, 283957745158496, 284028681324896, 22925253537946277599698546427630048251549844898, 354397358393696, 72920234199392, 
    72851506333792, 283957745158496, 283957745158496, 39618390034528, 39618390034528, 265751980780621178533169708502942808043426501670120649039660670347236940229473550247493808884040398788, 
    180360177649888, 145171509545184, 180360177649888, 180360177649888, 282362429731406690676345327770024509745648094966542045806405476232422908495307235237568497501207905156, 571789033906465, 
    571789168222497, 571789168222497, 35467878211873, 145206540765408, 145206540765408, 215579582007520, 
    215579582007520, 39724693719264, 39724693719264, 145277809920224, 145277809985760, 281758482833697, 
    74908663548128, 145277340616928, 145277407725792, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277810378976, 145277810378976, 39618390034528, 180360177649888, 145277810116832, 
    145277810116832, 39618390034528, 265752994540108411252271842382692025685938813880171198419623098311608482187255858523174602410685691844, 180360177649888, 180360177649888, 180360177649888, 
    11774838382263161731821259345920656661845378978, 1461529524151623746352605793034131996904347698083, 36567389839649, 145206540765408, 145206679177696, 74837727381600, 
    74837727381600, 74837727381600, 145206436956256, 145277541943520, 215579582007520, 39724693719264, 
    39724693719264, 145277809920224, 145277809985760, 290554575855905, 74908663548128, 145277407725792, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277810378976, 36567490502945, 
    145419544300000, 74837727381600, 74908663548128, 249081520042175852701008967875103546052691429028832122841110366012771736957970197074685083815900635637666742658164775363776965385185003547980719153351579303204077353025318, 44126632943905, 79235773892704, 
    79235773892704, 79235773892704, 79377579116768, 79235773892704, 79235773892704, 79510651799648, 
    79235773892704, 79441932322912, 184758224160992, 219977628518624]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 0, [1]⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_0
  · exact tv_b11_1
  · exact tv_b11_2
  · exact tv_b11_3
  · exact tv_b11_4
  · exact tv_b11_5
  · exact tv_b11_6
  · exact tv_b11_7
  · exact tv_b11_8
  · exact tv_b11_9
  · exact tv_b11_10
  · exact tv_b11_11
  · exact tv_b11_12
  · exact tv_b11_13
  · exact tv_b11_14
  · exact tv_b11_15


def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_branch (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (q' : State) (hq' : q' ≠ 3)
    (hM10 : M 1 0 = some (some q', Stmt.write 1 Dir.left)) : False := by
  let m : Move := ⟨q', 1, true⟩
  have hm_cmd : M 1 0 = m.command := hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  have h01_base : UsesOnly01 baseTable := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro q a m' hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact Or.inr rfl
  have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
  fin_cases q'
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inl rfl)
    exact tv_b3 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inr rfl)
    exact tv_b7 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · exact tv_b11 M hG hm1 rfl hv (by simp)
  · exact absurd rfl hq'

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := by
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
  obtain ⟨q', hM10⟩ := second
  by_cases h3 : q' = 3
  · subst h3
    have h01_base : UsesOnly01 baseTable := by
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
    exact solve_branch (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01)
      2 (by decide) hM10'
  · exact solve_branch M hG hm0 hv q' h3 hM10

end OMA.BB4H1

-- Adaptation by @ubuwaits.
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := OMA.BB4H1.h1_proof
