import FormalConjectures.Paper.PudlakFiniteDomainConjectures

-- The reachability relation and stack-machine lifting adapt the credited construction
-- in proofs/ComplexityTheory.P_subset_BPP.lean in this repository.
-- Here the decider preserves an input copy and its terminal state starts a branch.
open Turing Computability ComplexityTheory

namespace OMA.Retraction

/-! Reachability of a configuration within a step budget, as a `Prop`. -/

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    RIn f a (some b) 1 :=
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

-- Copy and restore duplicate the encoded input on the external stack and the decider input.
-- After the decider halts, inspect its bit and clear the external stack only on rejection.
inductive Ph
  | copy
  | restore
  | inspect
  | clear
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{Ph.copy, Ph.restore, Ph.inspect, Ph.clear}, by intro x; cases x <;> simp⟩

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool)

abbrev G : Bool ⊕ M.K → Type := fun k => Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

def liftStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | .push k f q => .push (Sum.inr k) (fun v => f v.1) (liftStmt q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto fun _ => Sum.inr .inspect

-- Embed the fixed fallback in the finite control of the new machine.
def put : List Bool → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool) →
    TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | [], q => q
  | b :: bs, q => put bs (.push (Sum.inl false) (fun _ => b) q)

def prog (outE : M.Γ M.k₁ ≃ Bool) (fallback : List Bool) :
    M.Λ ⊕ Ph → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | Sum.inl l => liftStmt M (M.m l)
  | Sum.inr .copy =>
    .pop (Sum.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl true) (fun v => v.2.getD false) <| .goto fun _ => Sum.inr .copy)
        (.goto fun _ => Sum.inr .restore)
  | Sum.inr .restore =>
    .pop (Sum.inl true) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl false) (fun v => v.2.getD false) <|
         .push (Sum.inr M.k₀) (fun v => e.symm (v.2.getD false)) <| .goto fun _ => Sum.inr .restore)
        (.goto fun _ => Sum.inl M.main)
  | Sum.inr .inspect =>
    .pop (Sum.inr M.k₁) (fun v o => (v.1, o.map outE)) <|
      .branch (fun v => v.2.getD false)
        (.load (fun _ => (M.initialState, none)) .halt)
        (.goto fun _ => Sum.inr .clear)
  | Sum.inr .clear =>
    .pop (Sum.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome) (.goto fun _ => Sum.inr .clear)
        (put M fallback (.load (fun _ => (M.initialState, none)) .halt))

def N (outE : M.Γ M.k₁ ≃ Bool) (fallback : List Bool) : FinTM2 :=
  letI := M.kFin
  letI := M.ΛFin
  letI := M.σFin
  { K := Bool ⊕ M.K
    k₀ := Sum.inl false
    k₁ := Sum.inl false
    Γ := G M
    Λ := M.Λ ⊕ Ph
    main := Sum.inr .copy
    σ := M.σ × Option Bool
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog M e outE fallback }

def mk (i a : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k : Bool ⊕ M.K, List (G M k)
  | Sum.inl false => i
  | Sum.inl true => a
  | Sum.inr k => S k

variable {M} {e}

lemma upd_inp (i a : List Bool) (i' : List (G M (Sum.inl false))) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i a S) (Sum.inl false) i' = mk M i' a S := by
  funext k
  rcases k with (_ | _) | k <;> simp [Function.update, mk]

lemma upd_aux (i a : List Bool) (a' : List (G M (Sum.inl true))) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i a S) (Sum.inl true) a' = mk M i a' S := by
  funext k
  rcases k with (_ | _) | k <;> simp [Function.update, mk]

lemma upd_inr (i a : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K) (v : List (G M (Sum.inr k))) :
    Function.update (mk M i a S) (Sum.inr k) v = mk M i a (Function.update S k v) := by
  funext k'
  rcases k' with (_ | _) | k'
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]

variable {outE : M.Γ M.k₁ ≃ Bool} {fallback : List Bool}

-- Every simulated configuration retains the word i. A halted decider transfers control
-- to the inspect phase of the enclosing machine.
def liftCfg (i : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) : (N M e outE fallback).Cfg :=
  ⟨some (match c.l with | none => Sum.inr .inspect | some l => Sum.inl l), (c.var, none), mk M i [] c.stk⟩

def cfg (l : Ph) (o : Option Bool) (i a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e outE fallback).Cfg :=
  ⟨some (Sum.inr l), (M.initialState, o), mk M i a S⟩

lemma stepAux_lift (i : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftStmt M q) (v, none) (mk M i [] S) = liftCfg (e := e) (outE := outE) (fallback := fallback) i (TM2.stepAux q v S) := by
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

lemma step_sim {i : List Bool} {c d : M.Cfg} (h : M.step c = some d) :
    (N M e outE fallback).step (liftCfg i c) = some (liftCfg i d) := by
  rcases c with ⟨_ | l, v, S⟩
  · cases h
  · change some (TM2.stepAux (M.m l) v S) = some d at h
    cases Option.some.inj h
    change some (TM2.stepAux (liftStmt M (M.m l)) (v, none) (mk M i [] S)) = _
    exact congrArg some (stepAux_lift (e := e) (outE := outE) (fallback := fallback) i (M.m l) v S)

lemma iterate_sim (i : List Bool) (n : ℕ) (c d : M.Cfg)
    (h : (flip bind M.step)^[n] (some c) = some d) :
    (flip bind (N M e outE fallback).step)^[n] (some (liftCfg i c)) = some (liftCfg i d) := by
  induction n generalizing d with
  | zero =>
    cases Option.some.inj h
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    generalize hv : (flip bind M.step)^[n] (some c) = o at h
    cases o with
    | none => cases h
    | some v =>
      rw [ih v hv]
      exact step_sim h

lemma copy_step (o : Option Bool) (b : Bool) (i a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e outE fallback).step (cfg .copy o (b :: i) a S) =
      some (cfg .copy (some b) i (b :: a) S) := by
  change some (TM2.stepAux (prog M e outE fallback (.inr .copy)) _ _) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, cfg]
  rfl

lemma copy_nil (o : Option Bool) (a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e outE fallback).step (cfg .copy o [] a S) = some (cfg .restore none [] a S) := by
  change some (TM2.stepAux (prog M e outE fallback (.inr .copy)) _ _) = _
  simp [prog, TM2.stepAux, mk, upd_inp, cfg]
  rfl

lemma restore_step (o : Option Bool) (b : Bool) (i a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e outE fallback).step (cfg .restore o i (b :: a) S) =
      some (cfg .restore (some b) (b :: i) a (Function.update S M.k₀ (e.symm b :: S M.k₀))) := by
  change some (TM2.stepAux (prog M e outE fallback (.inr .restore)) _ _) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, upd_inr, cfg]
  rfl

lemma restore_nil (o : Option Bool) (i : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e outE fallback).step (cfg .restore o i [] S) =
      some (liftCfg i ⟨some M.main, M.initialState, S⟩) := by
  change some (TM2.stepAux (prog M e outE fallback (.inr .restore)) _ _) = _
  simp [prog, TM2.stepAux, mk, upd_aux, cfg, liftCfg]
  rfl

lemma copy_run (i a : List Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e outE fallback).step (cfg .copy o i a S)
      (some (cfg .restore none [] (i.reverse ++ a) S)) (i.length + 1) := by
  induction i generalizing a o with
  | nil => exact RIn.single (copy_nil o a S)
  | cons b i ih =>
    have := RIn.trans (RIn.single (copy_step (e := e) (outE := outE) (fallback := fallback) o b i a S))
      (ih (b :: a) (some b))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma restore_run (i a : List Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e outE fallback).step (cfg .restore o i a S)
      (some (liftCfg (a.reverse ++ i) ⟨some M.main, M.initialState,
        Function.update S M.k₀ ((a.map e.symm).reverse ++ S M.k₀)⟩)) (a.length + 1) := by
  induction a generalizing i o S with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact RIn.single (restore_nil o i S)
  | cons b a ih =>
    have := RIn.trans (RIn.single (restore_step (e := e) (outE := outE) (fallback := fallback) o b i a S))
      (ih (b :: i) (some b) _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma init_N (i : List Bool) :
    initList (N M e outE fallback) i = cfg .copy none i [] (fun _ => []) := by
  simp only [initList, cfg]
  congr 1
  funext k
  rcases k with (_ | _) | k <;> rfl

lemma halt_N (i : List Bool) :
    haltList (N M e outE fallback) i =
      ⟨none, (M.initialState, none), mk M i [] (fun _ => [])⟩ := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with (_ | _) | k <;> rfl

lemma init_stack (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst h
    simp [initList]
  · simp [initList, h, Function.update_of_ne]

lemma halt_stack (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = Function.update (fun _ => []) M.k₁ s := by
  funext k
  by_cases h : k = M.k₁
  · subst h
    simp [haltList]
  · simp [haltList, h, Function.update_of_ne]

lemma put_aux (bs : List Bool) (q : TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool))
    (v : M.σ × Option Bool) (i a : List Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (put M bs q) v (mk M i a S) = TM2.stepAux q v (mk M (bs ++ i) a S) := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    rw [put, ih]
    simp only [TM2.stepAux, mk, upd_inp, List.cons_append]

lemma clear_step (o : Option Bool) (b : Bool) (i : List Bool) :
    (N M e outE fallback).step (cfg .clear o (b :: i) [] (fun _ => [])) =
      some (cfg .clear (some b) i [] (fun _ => [])) := by
  change some (TM2.stepAux (prog M e outE fallback (.inr .clear)) _ _) = _
  simp [prog, TM2.stepAux, mk, upd_inp, cfg]
  rfl

lemma clear_nil (o : Option Bool) :
    (N M e outE fallback).step (cfg .clear o [] [] (fun _ => [])) =
      some (haltList (N M e outE fallback) fallback) := by
  rw [halt_N]
  change some (TM2.stepAux (prog M e outE fallback (.inr .clear)) _ _) = _
  simp [prog, TM2.stepAux, upd_inp, cfg, mk, put_aux]
  rfl

lemma clear_run (o : Option Bool) (i : List Bool) :
    RIn (N M e outE fallback).step (cfg .clear o i [] (fun _ => []))
      (some (haltList (N M e outE fallback) fallback)) (i.length + 1) := by
  induction i generalizing o with
  | nil => exact RIn.single (clear_nil o)
  | cons b i ih =>
    have := RIn.trans (RIn.single (clear_step (M := M) (e := e) (outE := outE) (fallback := fallback) o b i))
      (ih (some b))
    simpa [Nat.add_comm] using this

lemma inspect (b : Bool) (i : List Bool) :
    RIn (N M e outE fallback).step (liftCfg i (haltList M [outE.symm b]))
      (some (haltList (N M e outE fallback) (if b then i else fallback))) (i.length + 2) := by
  cases b with
  | true =>
    refine (RIn.single ?_).mono (by omega)
    change (N M e outE fallback).step (liftCfg i (haltList M [outE.symm true])) = some (haltList (N M e outE fallback) i)
    erw [halt_N (M := M) (e := e) (outE := outE) (fallback := fallback) i]
    change some (TM2.stepAux (prog M e outE fallback (.inr .inspect)) (M.initialState, none)
      (mk M i [] (haltList M [outE.symm true]).stk)) = _
    rw [halt_stack]
    simp [prog, TM2.stepAux, mk, upd_inr, Function.update_idem] <;> rfl
  | false =>
    have first : (N M e outE fallback).step (liftCfg i (haltList M [outE.symm false])) =
        some (cfg .clear (some false) i [] (fun _ => [])) := by
      change some (TM2.stepAux (prog M e outE fallback (.inr .inspect)) (M.initialState, none)
        (mk M i [] (haltList M [outE.symm false]).stk)) = _
      rw [halt_stack]
      simp [prog, TM2.stepAux, mk, upd_inr, Function.update_idem, cfg] <;> rfl
    exact ((RIn.single first).trans (clear_run (some false) i)).mono (by omega)

-- Copy, restore, and rejection each cost at most one traversal of the input.
lemma run (i : List Bool) (b : Bool) (t : ℕ)
    (h : TM2OutputsInTime M (i.map e.symm) (some [outE.symm b]) t) :
    RIn (N M e outE fallback).step (initList (N M e outE fallback) i)
      (some (haltList (N M e outE fallback) (if b then i else fallback))) (3 * i.length + 4 + t) := by
  rw [init_N]
  have a := copy_run (M := M) (e := e) (outE := outE) (fallback := fallback) i [] none (fun _ => [])
  have d := restore_run (M := M) (e := e) (outE := outE) (fallback := fallback) [] i.reverse none (fun _ => [])
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, List.map_reverse] at a d
  have t0 : (⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ (i.map e.symm)⟩ : M.Cfg) =
      initList M (i.map e.symm) := by
    congr 1
    exact (init_stack _).symm
  rw [t0] at d
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  have old : RIn (N M e outE fallback).step (liftCfg i (initList M (i.map e.symm)))
      (some (liftCfg i (haltList M [outE.symm b]))) t :=
    ⟨n, hle, iterate_sim i n _ _ hn⟩
  exact (((a.trans d).trans old).trans (inspect b i)).mono (by omega)

lemma branch_poly (L : DecisionProblem) (y : List Bool) (poly : IsPolyTime L) :
    IsPolyTime (fun w => if L w then w else y) := by
  obtain ⟨D⟩ := poly
  let M := D.tm
  let e := D.inputAlphabet
  let outE := D.outputAlphabet
  let fallback := BitstringEncoding.bitEncode y
  refine ⟨{ tm := N M e outE fallback
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 3 * Polynomial.X + 4 + D.time
            outputsFun := fun w => ?_ }⟩
  let i := BitstringEncoding.bitEncode w
  have hm : TM2OutputsInTime M (i.map e.symm) (some [outE.symm (L w)]) (D.time.eval i.length) :=
    D.outputsFun w
  have hw := run (M := M) (e := e) (outE := outE) (fallback := fallback) i (L w) _ hm
  apply Classical.choice
  obtain ⟨n, hle, hs⟩ := hw
  constructor
  refine ⟨⟨n, ?_⟩, ?_⟩
  · change (flip bind (N M e outE fallback).step)^[n]
      (some (initList (N M e outE fallback) (i.map id))) =
        some (haltList (N M e outE fallback) ((BitstringEncoding.bitEncode (if L w then w else y)).map id))
    have eo : (BitstringEncoding.bitEncode (if L w then w else y)).map (id : Bool → Bool) =
        (if L w then i else fallback) := by
      rw [List.map_id]
      cases h : L w <;> simp [i, fallback, h]
    exact ((congrArg (fun x : List Bool => (flip bind (N M e outE fallback).step)^[n]
      (some (initList (N M e outE fallback) x))) (List.map_id i)).trans hs).trans
        (congrArg (fun x : List Bool => some (haltList (N M e outE fallback) x)) eo.symm)
  · simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, i, BitstringEncoding.bitEncode] using hle

end OMA.Retraction

open ComplexityTheory PudlakFiniteDomain

theorem OMA.solution : type_of% @PudlakFiniteDomain.sat_no_p_optimal_proof_system.variants.exists_of_P_eq_NP := by
  intro eq L complete nonemptyL
  obtain ⟨y, hy⟩ := nonemptyL
  have dec : L ∈ P := eq ▸ complete.mem
  let r := fun w => if L w then w else y
  have time : IsPolyTime r := OMA.Retraction.branch_poly L y dec
  have sound (w) : L (r w) = true := by
    by_cases h : L w = true
    · simpa [r, h] using h
    · simpa [r, h] using hy
  have fixed (w) (hw : L w = true) : r w = w := by simp [r, hw]
  refine ⟨r, ⟨time, fun z => ⟨fun hz => ⟨z, fixed z hz⟩, ?_⟩⟩, ?_⟩
  · rintro ⟨w, rfl⟩
    exact sound w
  · intro Q hQ
    exact ⟨Q, hQ.1, fun w => fixed (Q w) ((hQ.2 (Q w)).2 ⟨w, rfl⟩)⟩
