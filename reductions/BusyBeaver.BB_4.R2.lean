import FormalConjectures.Wikipedia.BusyBeaver

/-!
A machine running past step 107 determines a partial table: keep exactly the
instructions it reads in the first 107 steps. It suffices to certify that
these partial tables run forever. A leaf with a repeatable segment of at
most 107 steps can be discarded, even when the head drifts and leaves a
different tape behind it. The free tail in the hypotheses describes this
unobserved portion of the tape.

H3 isolates the two published RepWL cases (the BB4 enumeration of Coq-BB5).
Each list gives A0,A1,...,D1, with 16 for an undefined instruction and
4 * nextState + 2 * writtenBit + left for a running instruction.

The witness and finite-alphabet normalization are from @steveDOTdigital.
The first-move symmetry and immediate cases are from @Halldon.
-/
-- Credit: @henry10101001
namespace OMA.R_BusyBeaver_BB_4_R2
open Turing Turing.BusyBeaver BusyBeaver

def H1 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

def H2 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  let special (second : Bool) : Machine (Fin 2) (Fin 4) := fun q a =>
    let entries : List ℕ := if second then [6,4,11,6,16,13,2,15] else [6,3,3,8,15,10,16,1]
    let v := entries[2*q.val+a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩, Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩
      (if v % 2 = 0 then Dir.right else Dir.left))
  (∀ b, M ≠ special b) → ¬ M.IsHalting

def H3 : Prop :=
  let special (second : Bool) : Machine (Fin 2) (Fin 4) := fun q a =>
    let entries : List ℕ := if second then [6,4,11,6,16,13,2,15] else [6,3,3,8,15,10,16,1]
    let v := entries[2*q.val+a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩, Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩
      (if v % 2 = 0 then Dir.right else Dir.left))
  ∀ b, ¬ (special b).IsHalting

theorem restore_second (bounded : H2) (exceptional : H3) : ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting := by
  intro M hFirst hRun hUsed hForm hMissing hLoop hHalts
  apply bounded M hFirst hRun hUsed hForm hMissing hLoop ?_ hHalts
  intro b eq
  subst M
  exact exceptional b hHalts

theorem witness : ∃ C : Candidate 4, C.M.haltingNumber = (107 : ℕ) := by
  let champion : Machine (Fin 2) (Fin 4) := fun q s =>
    match q.val,s.val with
    | 0,0 => some (some 1, ⟨1,.right⟩)
    | 0,_ => some (some 1, ⟨1,.left⟩)
    | 1,0 => some (some 0, ⟨1,.left⟩)
    | 1,_ => some (some 2, ⟨0,.left⟩)
    | 2,0 => some (none,   ⟨1,.right⟩)
    | 2,_ => some (some 3, ⟨1,.left⟩)
    | _,0 => some (some 3, ⟨1,.right⟩)
    | _,_ => some (some 0, ⟨0,.right⟩)
  have stop : champion.multiStep (Machine.init []) 108 = none := by rfl
  have live : (champion.multiStep (Machine.init []) 107).isSome := by rfl
  let C : Candidate 4 :=
    { Γ := Fin 2
      Λ := Fin 4
      Γ_fintype := inferInstance
      Γ_card := Fintype.card_fin _
      Γ_inhabited := inferInstance
      Λ_fintype := inferInstance
      Λ_card := Fintype.card_fin _
      Λ_inhabited := inferInstance
      M := champion
      M_isHalting := (Machine.isHalting_iff_exists_haltsAt champion).mpr ⟨107,stop⟩ }
  refine ⟨C,?_⟩
  exact Machine.haltingNumber_def champion 107 (Option.isSome_iff_exists.mp live) stop

theorem normalize (n : ℕ) [NeZero n] (C : Candidate n) :
    ∃ M : Machine (Fin 2) (Fin n), M.IsHalting ∧ M.haltingNumber = C.M.haltingNumber := by
  classical
  let a := (Fintype.equivFinOfCardEq C.Γ_card).setValue default (default : Fin 2)
  let b := (Fintype.equivFinOfCardEq C.Λ_card).setValue default (default : Fin n)
  let f : PointedMap C.Γ (Fin 2) := ⟨a,by simp [a]⟩
  let conf (s : Cfg C.Γ C.Λ) : Cfg (Fin 2) (Fin n) := ⟨s.q.map b,s.tape.map f⟩
  let M : Machine (Fin 2) (Fin n) := fun q t =>
    (C.M (b.symm q) (a.symm t)).map (fun (q',cmd) => (q'.map b, Stmt.write (f cmd.symbol) cmd.dir))
  have step (s : Cfg C.Γ C.Λ) : M.step (conf s) = (C.M.step s).map conf := by
    obtain ⟨q,T⟩ := s
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step,conf,Option.map_some,Tape.map_fst,M]
      change ((C.M (b.symm (b q)) (a.symm (a T.head))).map _).map _ = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      cases h : C.M q T.head with
      | none => rfl
      | some z =>
        obtain ⟨q',⟨t,d⟩⟩ := z
        simp [Tape.map_move,Tape.map_write]
  have start : conf (Machine.init []) = Machine.init [] := by
    simp [conf,Machine.init,Tape.map_mk₁,b]
  have trace (k : ℕ) : M.multiStep (Machine.init []) k = (C.M.multiStep (Machine.init []) k).map conf := by
    induction k with
    | zero => simp [start]
    | succ k ih =>
      rw [Machine.multiStep_succ,Machine.multiStep_succ,ih]
      cases he : C.M.multiStep (Machine.init []) k with
      | none => rfl
      | some s => exact step s
  have stops (k : ℕ) : M.HaltsAfter (Machine.init []) k ↔ C.M.HaltsAfter (Machine.init []) k := by
    simp only [Machine.HaltsAfter,trace,Option.map_eq_none_iff]
  refine ⟨M,?_,?_⟩
  · obtain ⟨k,hk⟩ := (Machine.isHalting_iff_exists_haltsAt _).mp C.M_isHalting
    exact (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k,(stops k).mpr hk⟩
  · unfold Machine.haltingNumber
    congr 1
    ext e
    constructor <;> rintro ⟨k,hk,rfl⟩
    · exact ⟨k,(stops k).mp hk,rfl⟩
    · exact ⟨k,(stops k).mpr hk,rfl⟩


-- Relabel the first noninitial state as 1 and reflect a leftward first move.
theorem orient_first (M : Machine (Fin 2) (Fin 4)) (q : Fin 4) (a : Fin 2) (d : Dir)
    (hq : q ≠ 0) (first : M 0 0 = some (some q, Stmt.write a d)) :
    ∃ N : Machine (Fin 2) (Fin 4), N 0 0 = some (some 1, Stmt.write a Dir.right) ∧
      ∀ n, N.HaltsAfter (Machine.init []) n ↔ M.HaltsAfter (Machine.init []) n := by
  let e := Equiv.swap q (1 : Fin 4)
  have he0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hq) (by decide)
  have heInv : e.symm 0 = 0 := e.symm_apply_eq.mpr he0.symm
  have heq : e q = 1 := Equiv.swap_apply_left _ _
  let mirror := match d with
    | .left => true
    | .right => false
  let turn (direction : Dir) := if mirror then
    match direction with
    | .left => Dir.right
    | .right => Dir.left
    else direction
  let N : Machine (Fin 2) (Fin 4) := fun s b => (M (e.symm s) b).map fun (s', action) =>
    (s'.map e, Stmt.write action.symbol (turn action.dir))
  let image (c : Cfg (Fin 2) (Fin 4)) : Cfg (Fin 2) (Fin 4) :=
    ⟨c.q.map e, if mirror then ⟨c.tape.head, c.tape.right, c.tape.left⟩ else c.tape⟩
  have step (c : Cfg (Fin 2) (Fin 4)) : N.step (image c) = (M.step c).map image := by
    obtain ⟨s, ⟨b, l, r⟩⟩ := c
    cases s with
    | none => rfl
    | some s =>
      cases d <;>
        simp only [Machine.step, image, mirror, Option.map_some, N, Equiv.symm_apply_apply,
          Bool.false_eq_true, if_false, if_true]
      all_goals
        cases ht : M s b with
        | none => rfl
        | some entry =>
          obtain ⟨t, z, direction⟩ := entry
          cases direction <;> rfl
  have start : image (Machine.init []) = Machine.init [] := by
    cases d <;> simpa [image, Machine.init, Tape.mk₁, Tape.mk₂, Tape.mk'] using he0
  have trace (n : ℕ) : N.multiStep (image (Machine.init [])) n =
      (M.multiStep (Machine.init []) n).map image := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases he : M.multiStep (Machine.init []) n with
      | none => rfl
      | some c => exact step c
  refine ⟨N, ?_, fun n => ?_⟩
  · cases d <;> simp [N, turn, mirror, heInv, first, heq]
  · unfold Machine.HaltsAfter
    conv_lhs => rw [← start, trace]
    exact Option.map_eq_none_iff

-- A self-transition from the blank start state keeps seeing fresh blank cells.
theorem self_never_halts (M : Machine (Fin 2) (Fin 4)) (a : Fin 2) (d : Dir)
    (first : M 0 0 = some (some 0, Stmt.write a d)) : ¬ M.IsHalting := by
  let blank := ListBlank.mk ([] : List (Fin 2))
  have trace (n : ℕ) : ∃ t : Tape (Fin 2),
      M.multiStep (Machine.init []) n = some ⟨some 0, t⟩ ∧ t.head = 0 ∧
        (match d with | .left => t.left | .right => t.right) = blank := by
    induction n with
    | zero =>
      refine ⟨Tape.mk₁ [], rfl, rfl, ?_⟩
      cases d <;> rfl
    | succ n ih =>
      obtain ⟨t, ht, ha, hs⟩ := ih
      refine ⟨(t.write a).move d, ?_, ?_, ?_⟩
      · simp [Machine.multiStep_succ, ht, Machine.step, ha, first]
      · cases d <;> simp [Tape.write, Tape.move, hs, blank]
      · cases d <;> simp [Tape.write, Tape.move, hs, blank]
  intro halts
  obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  obtain ⟨t, ht, _⟩ := trace (n + 1)
  rw [Machine.HaltsAfter, ht] at hn
  contradiction

theorem stops_immediately (M : Machine (Fin 2) (Fin 4))
    (h : M 0 0 = none ∨ ∃ action, M 0 0 = some (none, action)) :
    M.HaltsAfter (Machine.init []) 107 := by
  have h2 : M.multiStep (Machine.init []) 2 = none := by
    change M.multiStep (Machine.init []) (1 + 1) = none
    rw [Machine.multiStep_succ, Machine.multiStep_one]
    have hi : M.step (Machine.init []) = (M 0 0).map
        (fun (q, a) => (⟨q, ((Tape.mk₁ []).write a.symbol).move a.dir⟩ : Cfg (Fin 2) (Fin 4))) := by
      change (M 0 0).map _ = _
      cases M 0 0 <;> rfl
    rcases h with h | ⟨action, h⟩ <;> rw [hi, h] <;> rfl
  exact Machine.multiStep_eq_none_mono h2 (by decide)


theorem run_add (M : Machine (Fin 2) (Fin 4)) (x : Cfg (Fin 2) (Fin 4)) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp

theorem no_repeat {M : Machine (Fin 2) (Fin 4)} (halts : M.IsHalting)
    {i p : ℕ} (hp : 0 < p) {α : Type} (cfg : α → Cfg (Fin 2) (Fin 4))
    (entered : ∃ v, M.multiStep (Machine.init []) i = some (cfg v))
    (cycle : ∀ v, ∃ w, M.multiStep (cfg v) p = some (cfg w)) : False := by
  have recur (m : ℕ) : ∃ v, M.multiStep (Machine.init []) (i + p * m) = some (cfg v) := by
    induction m with
    | zero => simpa using entered
    | succ m ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := cycle v
      refine ⟨w, ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add M _ (i + p*m) p, hv]
      exact hw
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  obtain ⟨v, hv⟩ := recur (k + 1)
  have hle : k + 1 ≤ i + p * (k + 1) := by
    have := Nat.mul_le_mul_right (k+1) hp
    omega
  have hnone := Machine.multiStep_eq_none_mono hk hle
  rw [hv] at hnone
  contradiction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem freeze_bound (bit : Fin 2)
    (residual : ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write bit Dir.right) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting)
    (M : Machine (Fin 2) (Fin 4))
    (first : M 0 0 = some (some 1, Stmt.write bit Dir.right)) (halts : M.IsHalting) :
    M.HaltsAfter (Machine.init []) 107 := by
  classical
  by_contra late
  let start : Cfg (Fin 2) (Fin 4) := Machine.init []
  have alive (i : ℕ) (hi : i ≤ 108) : M.multiStep start i ≠ none :=
    fun h => late (Machine.multiStep_eq_none_mono h hi)
  let seen (q : Fin 4) (a : Fin 2) : Prop := ∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep start i = some ⟨some q, t⟩ ∧ t.head = a
  let P : Machine (Fin 2) (Fin 4) := fun q a => if seen q a then M q a else none
  have used {q a} (h : seen q a) : ∃ r z, M q a = some (some r, z) := by
    obtain ⟨i, hi, t, ht, rfl⟩ := h
    have ha := alive (i+1+1) (by omega)
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ht] at ha
    cases hc : M q t.head with
    | none => simp [Machine.step, hc] at ha
    | some entry =>
      obtain ⟨s, z⟩ := entry
      cases s with
      | none => simp [Machine.step, hc] at ha
      | some s => exact ⟨s, z, rfl⟩
  have agree (i : ℕ) (hi : i ≤ 107) : P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih (by omega)]
      cases h : M.multiStep start i with
      | none => rfl
      | some c =>
        obtain ⟨q, t⟩ := c
        cases q with
        | none => rfl
        | some q =>
          have hv : seen q t.head := ⟨i, by omega, t, h, rfl⟩
          simp [Machine.step, P, hv]
  have restrictRun (i : ℕ) : P.multiStep start i = none ∨ P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => exact Or.inr rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ]
      rcases ih with hi | hi
      · simp [hi]
      · rw [hi]
        cases hc : M.multiStep start i with
        | none => exact Or.inl rfl
        | some c =>
          obtain ⟨q, t⟩ := c
          cases q with
          | none => exact Or.inl rfl
          | some q => by_cases h : seen q t.head <;> simp [Machine.step, P, h]
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  have haltP : P.IsHalting := by
    apply (Machine.isHalting_iff_exists_haltsAt P).mpr
    refine ⟨k, ?_⟩
    rcases restrictRun (k+1) with h | h
    · exact h
    · exact h.trans hk
  apply (residual P ?_ ?_ ?_ ?_ ?_ ?_) haltP
  · have h : seen 0 0 := ⟨0, by decide, Tape.mk₁ [], rfl, rfl⟩
    simpa [P, h] using first
  · obtain ⟨q,t,ht⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) 107 late
    exact ⟨q,t,(agree 107 (by decide)).trans ht⟩
  · intro q a
    have eq : (∃ i < 107, ∃ t : Tape (Fin 2), P.multiStep start i = some ⟨some q,t⟩ ∧ t.head = a) ↔ seen q a := by
      constructor <;> rintro ⟨i,hi,t,ht,ha⟩ <;> refine ⟨i,hi,t,?_,ha⟩
      · exact (agree i (by omega)).symm.trans ht
      · exact (agree i (by omega)).trans ht
    apply eq.trans
    by_cases h : seen q a
    · simpa [P,h] using used h
    · simp [P,h]
  · intro q a
    by_cases h : seen q a
    · right
      simpa [P,h] using used h
    · left
      simp [P,h]
  · by_contra! all
    apply Machine.not_isHalting_of_forall_isSome P _ haltP
    intro q a
    by_cases h : seen q a
    · simpa [P,h] using used h
    · exact (all q a (by simp [P,h])).elim
  · intro i p q a side near fixed hp _ cfg enter loop
    exact no_repeat haltP hp cfg enter loop

theorem canonical_bound (h1 : H1) (h2 : H2) (h3 : H3) (M : Machine (Fin 2) (Fin 4))
    (halts : M.IsHalting) (k : ℕ) (hk : M.haltingNumber = k) : k ≤ 107 := by
  have bound : M.HaltsAfter (Machine.init []) 107 := by
    cases h : M 0 0 with
    | none => exact stops_immediately M (Or.inl h)
    | some cmd =>
      obtain ⟨q, a, d⟩ := cmd
      cases q with
      | none => exact stops_immediately M (Or.inr ⟨_, h⟩)
      | some q =>
        by_cases hq : q = 0
        · subst q
          exact (self_never_halts M a d h halts).elim
        · obtain ⟨N, hN, timing⟩ := orient_first M q a d hq h
          obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
          have haltsN := (Machine.isHalting_iff_exists_haltsAt N).mpr ⟨n, (timing n).mpr hn⟩
          apply (timing 107).mp
          fin_cases a
          · exact freeze_bound 0 h1 N hN haltsN
          · exact freeze_bound 1 (restore_second h2 h3) N hN haltsN
  have hle : M.haltingNumber ≤ (107 : ℕ) := sInf_le ⟨107, bound, rfl⟩
  rw [hk] at hle
  exact_mod_cast hle


theorem main : H1 → H2 → H3 → type_of% @BusyBeaver.BB_4 := by
  intro h1 h2 h3
  let S := {n : ℕ | ∃ C : Candidate 4, C.M.haltingNumber = n}
  have hm : 107 ∈ S := witness
  have hub : ∀ k ∈ S, k ≤ 107 := by
    rintro k ⟨C,hC⟩
    obtain ⟨M,hM,h⟩ := normalize 4 C
    exact canonical_bound h1 h2 h3 M hM k (h.trans hC)
  change sSup S = 107
  exact le_antisymm (csSup_le ⟨107,hm⟩ hub) (le_csSup ⟨107,hub⟩ hm)
end OMA.R_BusyBeaver_BB_4_R2
