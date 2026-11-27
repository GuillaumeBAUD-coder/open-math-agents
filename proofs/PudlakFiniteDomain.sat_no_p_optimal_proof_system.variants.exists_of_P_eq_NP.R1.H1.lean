import OMAReductions.R_PudlakFiniteDomain_sat_no_p_optimal_proof_system_variants_exists_of_P_eq_NP_R1
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Computability.TuringMachine.Computable

/-! A polynomial-time decider yields a polynomial-time retraction onto its language. -/

open Turing Computability ComplexityTheory

namespace OMA.Retract

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) : RIn f a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn f a (some b) m₁) (h₂ : RIn f b c m₂) : RIn f a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma RIn.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn f a b m) (hm : m ≤ m') : RIn f a b m' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hm, e⟩

inductive Slot
  | inp
  | save
  | rev
  | out
  deriving DecidableEq

instance : Fintype Slot :=
  ⟨{Slot.inp, Slot.save, Slot.rev, Slot.out}, by intro x; cases x <;> simp⟩

inductive Ph
  | dup
  | toM
  | read
  | emit
  | wipe
  | write
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{Ph.dup, Ph.toM, Ph.read, Ph.emit, Ph.wipe, Ph.write}, by intro x; cases x <;> simp⟩

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eOut : M.Γ M.k₁ ≃ Bool)

abbrev G : Slot ⊕ M.K → Type := fun k => Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

def liftStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | .push k f q => .push (Sum.inr k) (fun v => f v.1) (liftStmt q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr Ph.read)

def pushRev : List Bool → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | [] => .load (fun _ => (M.initialState, none)) .halt
  | b :: bs => .push (Sum.inl Slot.out) (fun _ => b) (pushRev bs)

variable (const : List Bool)

def prog : M.Λ ⊕ Ph → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | Sum.inl l => liftStmt M (M.m l)
  | Sum.inr .dup =>
    .pop (Sum.inl Slot.inp) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl Slot.save) (fun v => v.2.getD false) <|
          .push (Sum.inl Slot.rev) (fun v => v.2.getD false) <|
            .goto fun _ => Sum.inr Ph.dup)
        (.goto fun _ => Sum.inr Ph.toM)
  | Sum.inr .toM =>
    .pop (Sum.inl Slot.rev) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inr M.k₀) (fun v => e.symm (v.2.getD false)) <|
          .goto fun _ => Sum.inr Ph.toM)
        (.load (fun _ => (M.initialState, none)) <|
          .goto fun _ => Sum.inl M.main)
  | Sum.inr .read =>
    .pop (Sum.inr M.k₁) (fun v o => (v.1, o.map eOut)) <|
      .branch (fun v => v.2.getD false)
        (.goto fun _ => Sum.inr Ph.emit)
        (.goto fun _ => Sum.inr Ph.wipe)
  | Sum.inr .emit =>
    .pop (Sum.inl Slot.save) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl Slot.out) (fun v => v.2.getD false) <|
          .goto fun _ => Sum.inr Ph.emit)
        (.load (fun _ => (M.initialState, none)) .halt)
  | Sum.inr .wipe =>
    .pop (Sum.inl Slot.save) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.goto fun _ => Sum.inr Ph.wipe)
        (.goto fun _ => Sum.inr Ph.write)
  | Sum.inr .write => pushRev M const.reverse

def N : FinTM2 :=
  letI := M.kFin
  letI := M.kDecidableEq
  letI := M.ΛFin
  letI := M.σFin
  { K := Slot ⊕ M.K
    k₀ := Sum.inl Slot.inp
    k₁ := Sum.inl Slot.out
    Γ := G M
    Λ := M.Λ ⊕ Ph
    main := Sum.inr Ph.dup
    σ := M.σ × Option Bool
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog M e eOut const }

variable {M e eOut const}

def mk (inp save rev out : List Bool) (S : ∀ k, List (M.Γ k)) :
    ∀ k : Slot ⊕ M.K, List (G M k)
  | Sum.inl .inp => inp
  | Sum.inl .save => save
  | Sum.inl .rev => rev
  | Sum.inl .out => out
  | Sum.inr k => S k

lemma upd_inp (i i' save rev out : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk i save rev out S) (Sum.inl Slot.inp) i' = mk i' save rev out S := by
  funext k
  cases k with
  | inl s => cases s <;> simp [Function.update, mk]
  | inr k => simp [Function.update, mk]

lemma upd_save (i save save' rev out : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk i save rev out S) (Sum.inl Slot.save) save' = mk i save' rev out S := by
  funext k
  cases k with
  | inl s => cases s <;> simp [Function.update, mk]
  | inr k => simp [Function.update, mk]

lemma upd_rev (i save rev rev' out : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk i save rev out S) (Sum.inl Slot.rev) rev' = mk i save rev' out S := by
  funext k
  cases k with
  | inl s => cases s <;> simp [Function.update, mk]
  | inr k => simp [Function.update, mk]

lemma upd_out (i save rev out out' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk i save rev out S) (Sum.inl Slot.out) out' = mk i save rev out' S := by
  funext k
  cases k with
  | inl s => cases s <;> simp [Function.update, mk]
  | inr k => simp [Function.update, mk]

lemma upd_inr (i save rev out : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K)
    (v : List (G M (Sum.inr k))) :
    Function.update (mk i save rev out S) (Sum.inr k) v = mk i save rev out (Function.update S k v) := by
  funext k'
  cases k' with
  | inl s => cases s <;> rfl
  | inr k' =>
    by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]

def cfg (l : Ph) (v : M.σ × Option Bool) (inp save rev out : List Bool)
    (S : ∀ k, List (M.Γ k)) : (N M e eOut const).Cfg :=
  ⟨some (Sum.inr l), v, mk inp save rev out S⟩

def embed (c : TM2.Cfg M.Γ M.Λ M.σ) (save : List Bool) : (N M e eOut const).Cfg :=
  ⟨match c.l with
    | some l => some (Sum.inl l)
    | none => some (Sum.inr Ph.read),
   (c.var, none), mk [] save [] [] c.stk⟩

lemma stepAux_lift (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (save : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftStmt M q) (v, none) (mk [] save [] [] S) =
      embed (e := e) (eOut := eOut) (const := const) (TM2.stepAux q v S) save := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    rw [upd_inr]
    exact ih _ _
  | peek k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    rw [upd_inr]
    exact ih _ _
  | load a q ih =>
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftStmt, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_embed (c : TM2.Cfg M.Γ M.Λ M.σ) (save : List Bool) (hl : c.l.isSome) :
    (N M e eOut const).step (embed c save) =
      (M.step c).map (fun c' => embed c' save) := by
  rcases c with ⟨_ | l, v, S⟩
  · simp at hl
  · change some (TM2.stepAux (liftStmt M (M.m l)) (v, none) (mk [] save [] [] S)) = _
    rw [stepAux_lift]
    rfl

lemma iterate_embed (n : ℕ) (c : TM2.Cfg M.Γ M.Λ M.σ) (save : List Bool)
    (h : ∀ k < n, ((flip bind M.step)^[k] (some c)).elim False (fun c' => c'.l.isSome)) :
    (flip bind (N M e eOut const).step)^[n] (some (embed c save)) =
      ((flip bind M.step)^[n] (some c)).map (fun c' => embed c' save) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih c (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
    cases hM : (flip bind M.step)^[n] (some c) with
    | none => rfl
    | some c' =>
      have hl : c'.l.isSome := by
        have hk := h n (Nat.lt_succ_self n)
        rwa [hM] at hk
      exact step_embed c' save hl

lemma none_iter {σ : Type} (f : σ → Option σ) (m : ℕ) : (flip bind f)^[m] none = none := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl

lemma isSome_iterate_le {σ : Type} {f : σ → Option σ} {o : Option σ} {b : σ} {m n : ℕ}
    (h : (flip bind f)^[n] o = some b) (hm : m ≤ n) : ((flip bind f)^[m] o).isSome := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hm
  rw [Nat.add_comm, Function.iterate_add_apply] at h
  cases hp : (flip bind f)^[m] o with
  | none => rw [hp, none_iter] at h; simp at h
  | some _ => simp

lemma running_before {n k : ℕ} {a b : M.Cfg}
    (h : (flip bind M.step)^[n] (some a) = some b) (_hb : b.l = none) (hk : k < n) :
    ((flip bind M.step)^[k] (some a)).elim False (fun c => c.l.isSome) := by
  have hs := isSome_iterate_le h (Nat.succ_le_of_lt hk)
  rw [Function.iterate_succ_apply'] at hs
  cases hc : (flip bind M.step)^[k] (some a) with
  | none =>
    rw [hc] at hs
    simp [flip, Option.bind] at hs
  | some c =>
    simp only [Option.elim]
    rcases c with ⟨l, v, S⟩
    cases l with
    | some _ => simp
    | none =>
      exfalso
      rw [hc] at hs
      simp [TM2.step] at hs
      cases hs

lemma step_dup_cons (v : M.σ) (o : Option Bool) (b : Bool) (rest save rev : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .dup (v, o) (b :: rest) save rev [] S) =
      some (cfg .dup (v, some b) rest (b :: save) (b :: rev) [] S) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .dup)) (v, o)
    (mk (b :: rest) save rev [] S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_save, upd_rev, cfg]; rfl

lemma step_dup_nil (v : M.σ) (o : Option Bool) (save rev : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .dup (v, o) [] save rev [] S) =
      some (cfg .toM (v, none) [] save rev [] S) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .dup)) (v, o) (mk [] save rev [] S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, cfg]; rfl

lemma dup_run (v : M.σ) (o : Option Bool) (s save rev : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e eOut const).step (cfg .dup (v, o) s save rev [] S)
      (some (cfg .toM (v, none) [] (s.reverse ++ save) (s.reverse ++ rev) [] S))
      (s.length + 1) := by
  induction s generalizing o save rev with
  | nil =>
    simpa using RIn.single (step_dup_nil (M := M) (e := e) (eOut := eOut) (const := const) v o save rev S)
  | cons b s ih =>
    have h1 := RIn.single (step_dup_cons (M := M) (e := e) (eOut := eOut) (const := const)
      v o b s save rev S)
    have h2 := ih (some b) (b :: save) (b :: rev)
    have := RIn.trans h1 h2
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma step_toM_cons (v : M.σ) (o : Option Bool) (c : Bool) (a save : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .toM (v, o) [] save (c :: a) [] S) =
      some (cfg .toM (v, some c) [] save a []
        (Function.update S M.k₀ (e.symm c :: S M.k₀))) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .toM)) (v, o)
    (mk [] save (c :: a) [] S)) = _
  simp [prog, TM2.stepAux, mk, upd_rev, upd_inr, cfg]; rfl

lemma step_toM_nil (v : M.σ) (o : Option Bool) (save : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .toM (v, o) [] save [] [] S) =
      some (embed (e := e) (eOut := eOut) (const := const)
        ⟨some M.main, M.initialState, S⟩ save) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .toM)) (v, o) (mk [] save [] [] S)) = _
  simp [prog, TM2.stepAux, mk, upd_rev, cfg, embed]; rfl

lemma toM_run (v : M.σ) (o : Option Bool) (a save : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e eOut const).step (cfg .toM (v, o) [] save a [] S)
      (some (embed (e := e) (eOut := eOut) (const := const)
        ⟨some M.main, M.initialState,
          Function.update S M.k₀ ((a.map e.symm).reverse ++ S M.k₀)⟩ save))
      (a.length + 1) := by
  induction a generalizing o S with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact RIn.single (step_toM_nil (M := M) (e := e) (eOut := eOut) (const := const) v o save S)
  | cons c a ih =>
    have h1 := RIn.single (step_toM_cons (M := M) (e := e) (eOut := eOut) (const := const)
      v o c a save S)
    have h2 := ih (some c) (Function.update S M.k₀ (e.symm c :: S M.k₀))
    have := RIn.trans h1 h2
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.map_cons, List.append_assoc, Nat.add_comm] using this

lemma step_read (v : M.σ) (bit : M.Γ M.k₁) (save : List Bool) :
    (N M e eOut const).step
        (cfg .read (v, none) [] save [] [] (Function.update (fun _ => []) M.k₁ [bit])) =
      some (cfg (if eOut bit then Ph.emit else Ph.wipe) (v, some (eOut bit)) [] save [] []
        (fun _ => [])) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .read)) (v, none)
    (mk [] save [] [] (Function.update (fun _ => []) M.k₁ [bit]))) = _
  cases hbit : eOut bit with
  | false =>
    simp [prog, TM2.stepAux, mk, upd_inr, cfg, hbit, List.tail]
    congr 1
  | true =>
    simp [prog, TM2.stepAux, mk, upd_inr, cfg, hbit, List.tail]
    congr 1

lemma step_emit_cons (v : M.σ) (o : Option Bool) (b : Bool) (rest out : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .emit (v, o) [] (b :: rest) [] out S) =
      some (cfg .emit (v, some b) [] rest [] (b :: out) S) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .emit)) (v, o)
    (mk [] (b :: rest) [] out S)) = _
  simp [prog, TM2.stepAux, mk, upd_save, upd_out, cfg]; rfl

lemma step_emit_nil (v : M.σ) (o : Option Bool) (out : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .emit (v, o) [] [] [] out S) =
      some ⟨none, (M.initialState, none), mk [] [] [] out S⟩ := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .emit)) (v, o) (mk [] [] [] out S)) = _
  simp [prog, TM2.stepAux, mk, upd_save]; rfl

lemma emit_run (v : M.σ) (o : Option Bool) (a out : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e eOut const).step (cfg .emit (v, o) [] a [] out S)
      (some ⟨none, (M.initialState, none), mk [] [] [] (a.reverse ++ out) S⟩)
      (a.length + 1) := by
  induction a generalizing o out with
  | nil =>
    simpa using RIn.single (step_emit_nil (M := M) (e := e) (eOut := eOut) (const := const) v o out S)
  | cons b a ih =>
    have h1 := RIn.single (step_emit_cons (M := M) (e := e) (eOut := eOut) (const := const)
      v o b a out S)
    have h2 := ih (some b) (b :: out)
    have := RIn.trans h1 h2
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma step_wipe_cons (v : M.σ) (o : Option Bool) (b : Bool) (rest : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .wipe (v, o) [] (b :: rest) [] [] S) =
      some (cfg .wipe (v, some b) [] rest [] [] S) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .wipe)) (v, o)
    (mk [] (b :: rest) [] [] S)) = _
  simp [prog, TM2.stepAux, mk, upd_save, cfg]; rfl

lemma step_wipe_nil (v : M.σ) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .wipe (v, o) [] [] [] [] S) =
      some (cfg .write (v, none) [] [] [] [] S) := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .wipe)) (v, o) (mk [] [] [] [] S)) = _
  simp [prog, TM2.stepAux, mk, upd_save, cfg]; rfl

lemma wipe_run (v : M.σ) (o : Option Bool) (a : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e eOut const).step (cfg .wipe (v, o) [] a [] [] S)
      (some (cfg .write (v, none) [] [] [] [] S)) (a.length + 1) := by
  induction a generalizing o with
  | nil =>
    exact RIn.single (step_wipe_nil (M := M) (e := e) (eOut := eOut) (const := const) v o S)
  | cons b a ih =>
    have := RIn.trans (RIn.single (step_wipe_cons (M := M) (e := e) (eOut := eOut) (const := const)
      v o b a S)) (ih (some b))
    simpa [Nat.add_comm] using this

lemma stepAux_pushRev (bits acc : List Bool) (v : M.σ × Option Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (pushRev M bits) v (mk [] [] [] acc S) =
      ⟨none, (M.initialState, none), mk [] [] [] (bits.reverse ++ acc) S⟩ := by
  induction bits generalizing acc with
  | nil => simp [pushRev, TM2.stepAux, mk]
  | cons b bs ih =>
    simp only [pushRev, TM2.stepAux, mk]
    rw [upd_out]
    have hih := ih (b :: acc)
    simp only [List.reverse_cons, List.append_assoc] at hih ⊢
    exact hih

lemma step_write (v : M.σ × Option Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e eOut const).step (cfg .write v [] [] [] [] S) =
      some ⟨none, (M.initialState, none), mk [] [] [] const S⟩ := by
  show some (TM2.stepAux (prog M e eOut const (Sum.inr .write)) v (mk [] [] [] [] S)) = _
  simp only [prog]
  rw [stepAux_pushRev]
  simp [List.reverse_reverse]; rfl

lemma init_eq (l : List Bool) :
    initList (N M e eOut const) l =
      cfg .dup (M.initialState, none) l [] [] [] (fun _ => []) := by
  simp only [initList, cfg]
  congr 1
  funext k
  cases k with
  | inl s => cases s <;> rfl
  | inr k => rfl

lemma halt_eq (s : List Bool) :
    haltList (N M e eOut const) s =
      ⟨none, (M.initialState, none), mk [] [] [] s (fun _ => [])⟩ := by
  simp only [haltList, N]
  congr 1
  funext k
  cases k with
  | inl s' =>
    cases s' with
    | inp => simp [mk, dif_neg]
    | save => simp [mk, dif_neg]
    | rev => simp [mk, dif_neg]
    | out => with_unfolding_all rfl
  | inr k => simp [mk, dif_neg]

lemma init_embed (s : List (M.Γ M.k₀)) (save : List Bool) :
    embed (e := e) (eOut := eOut) (const := const) (initList M s) save =
      embed ⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ s⟩ save := by
  simp only [initList, embed]
  congr 1
  funext k
  cases k with
  | inl slot => cases slot <;> rfl
  | inr k =>
    by_cases h : k = M.k₀
    · subst h
      simp [mk]
    · simp [mk, Function.update_of_ne h, h]

lemma sim_run {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ} (save : List Bool)
    (h : TM2OutputsInTime M s (some out) T) :
    RIn (N M e eOut const).step
      (embed (e := e) (eOut := eOut) (const := const) (initList M s) save)
      (some (embed (haltList M out) save)) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  have hrun : ∀ k < n, ((flip bind M.step)^[k] (some (initList M s))).elim False
      (fun c => c.l.isSome) :=
    fun k hk => running_before (M := M) hn (by simp [haltList]) hk
  have := iterate_embed (e := e) (eOut := eOut) (const := const) n (initList M s) save hrun
  rw [this, hn]
  rfl

end OMA.Retract

open OMA.Retract

theorem OMA.solution :
    OMA.R_PudlakFiniteDomain_sat_no_p_optimal_proof_system_variants_exists_of_P_eq_NP_R1.H1 := by
  intro L fallback hL
  obtain ⟨M⟩ := hL
  let machine := N M.tm M.inputAlphabet M.outputAlphabet (BitstringEncoding.bitEncode fallback)
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := M.time + 3 * Polynomial.X + 5
            outputsFun := fun w => ?_ }⟩
  let input := BitstringEncoding.bitEncode (α := List Bool) w
  have hbound : M.time.eval input.length + 3 * input.length + 5 ≤
      (M.time + 3 * Polynomial.X + 5).eval input.length := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  have hMout : List.map M.outputAlphabet.invFun (BitstringEncoding.bitEncode (L w)) =
      [M.outputAlphabet.symm (L w)] := by
    simp [BitstringEncoding.bitEncode]
    rfl
  have hrun : RIn machine.step (initList machine input)
      (some (haltList machine (if L w then input else BitstringEncoding.bitEncode fallback)))
      (M.time.eval input.length + 3 * input.length + 5) := by
    rw [init_eq]
    have hdup := dup_run (M := M.tm) (e := M.inputAlphabet) (eOut := M.outputAlphabet)
      (const := BitstringEncoding.bitEncode fallback) M.tm.initialState none input [] [] (fun _ => [])
    simp only [List.append_nil] at hdup
    have hto := toM_run (M := M.tm) (e := M.inputAlphabet) (eOut := M.outputAlphabet)
      (const := BitstringEncoding.bitEncode fallback) M.tm.initialState none
      input.reverse input.reverse (fun _ => [])
    simp only [List.map_reverse, List.reverse_reverse, List.append_nil] at hto
    rw [← init_embed] at hto
    have hsim := sim_run (e := M.inputAlphabet) (eOut := M.outputAlphabet)
      (const := BitstringEncoding.bitEncode fallback) input.reverse (M.outputsFun w)
    have hembed : embed (e := M.inputAlphabet) (eOut := M.outputAlphabet)
        (const := BitstringEncoding.bitEncode fallback)
        (haltList M.tm (List.map M.outputAlphabet.invFun (BitstringEncoding.instBool.encode (L w))))
        input.reverse =
        cfg (M := M.tm) (e := M.inputAlphabet) (eOut := M.outputAlphabet)
          (const := BitstringEncoding.bitEncode fallback) .read
          (M.tm.initialState, none) [] input.reverse [] []
          (Function.update (fun _ => []) M.tm.k₁ [M.outputAlphabet.symm (L w)]) := by
      have hlist : List.map M.outputAlphabet.invFun (BitstringEncoding.instBool.encode (L w)) =
          [M.outputAlphabet.symm (L w)] := hMout
      simp only [hlist, haltList, embed, cfg]
      congr 1
      funext k
      cases k with
      | inl s => cases s <;> simp [mk]
      | inr k =>
        by_cases hk : k = M.tm.k₁
        · subst hk
          simp [mk]
        · simp [mk, hk]
    rw [hembed] at hsim
    have hread := step_read (M := M.tm) (e := M.inputAlphabet) (eOut := M.outputAlphabet)
      (const := BitstringEncoding.bitEncode fallback) M.tm.initialState
      (M.outputAlphabet.symm (L w)) input.reverse
    have hbit : M.outputAlphabet (M.outputAlphabet.symm (L w)) = L w := by simp
    rw [hbit] at hread
    have hlen : input.reverse.length = input.length := by simp
    have htime : M.time.eval (BitstringEncoding.instList.encode w).length =
        M.time.eval input.length := rfl
    cases hLw : L w with
    | true =>
      simp only [hLw, ite_true] at hread hsim ⊢
      have hemit := emit_run (M := M.tm) (e := M.inputAlphabet) (eOut := M.outputAlphabet)
        (const := BitstringEncoding.bitEncode fallback) M.tm.initialState (some true)
        input.reverse [] (fun _ => [])
      simp only [List.reverse_reverse, List.append_nil] at hemit
      rw [← halt_eq] at hemit
      refine (((hdup.trans hto).trans hsim).trans ((RIn.single hread).trans hemit)).mono ?_
      rw [hlen, htime]
      omega
    | false =>
      simp only [hLw, ite_false] at hread hsim ⊢
      have hwipe := wipe_run (M := M.tm) (e := M.inputAlphabet) (eOut := M.outputAlphabet)
        (const := BitstringEncoding.bitEncode fallback) M.tm.initialState (some false)
        input.reverse (fun _ => [])
      have hwrite := step_write (M := M.tm) (e := M.inputAlphabet) (eOut := M.outputAlphabet)
        (const := BitstringEncoding.bitEncode fallback) (M.tm.initialState, none) (fun _ => [])
      rw [← halt_eq] at hwrite
      refine (((hdup.trans hto).trans hsim).trans
        (((RIn.single hread).trans hwipe).trans (RIn.single hwrite))).mono ?_
      rw [hlen, htime]
      omega
  have hin : List.map ((Equiv.refl Bool : machine.Γ machine.k₀ ≃ Bool).invFun)
      (BitstringEncoding.bitEncode w) = input := by
    simp [input, List.map_id]
  have hout : List.map ((Equiv.refl Bool : machine.Γ machine.k₁ ≃ Bool).invFun)
      (BitstringEncoding.bitEncode (if L w then w else fallback)) =
      if L w then input else BitstringEncoding.bitEncode fallback := by
    cases h : L w <;> simp [input, h, BitstringEncoding.bitEncode, List.map_id]
  have result : TM2OutputsInTime machine input
      (some (if L w then input else BitstringEncoding.bitEncode fallback))
      ((M.time + 3 * Polynomial.X + 5).eval input.length) :=
    Classical.choice (by
      obtain ⟨n, hle, he⟩ := hrun.mono hbound
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  have hin1 : List.map ((Equiv.refl Bool : machine.Γ machine.k₀ ≃ Bool).invFun)
      (BitstringEncoding.instList.encode w) = input := hin
  have hout1 : List.map ((Equiv.refl Bool : machine.Γ machine.k₁ ≃ Bool).invFun)
      (BitstringEncoding.instList.encode (if L w then w else fallback)) =
      if L w then input else BitstringEncoding.bitEncode fallback := by
    cases h : L w <;> simpa [h, input, BitstringEncoding.bitEncode] using hout
  rw (config := { transparency := .default }) [hin1, hout1]
  have hlenIn : (BitstringEncoding.instList.encode w).length = input.length := rfl
  rw (config := { transparency := .default }) [hlenIn]
  exact result
