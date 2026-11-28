import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2
import Mathlib.Tactic

-- Step: polynomial-time composition for Bayesian security games.
-- Credit: @unknownuser17769 for this specialization.
-- The generic machine constructions below are reused verbatim from
-- proofs/PolyTime.isPolyTime_squareRootSumTwoSided.R1.H4.lean, PR 6723,
-- by @nijv (Pedro Bessa), commit 1d0fa4fe096ce2c63fc6496ac0de23bdee83122f.
-- Their original namespace is retained to make the provenance explicit.

namespace PolyTimeSqrtH4Proof

open Computability Turing StateTransition BitstringEncoding ComplexityTheory BigOperators

local instance instKFin (M : FinTM2) : Fintype M.K := M.kFin
local instance instΛFin (M : FinTM2) : Fintype M.Λ := M.ΛFin
local instance instσFin (M : FinTM2) : Fintype M.σ := M.σFin
local instance instΓk₀Fin (M : FinTM2) : Fintype (M.Γ M.k₀) := M.Γk₀Fin

private lemma iterate_bind_none {σ : Type*} (step : σ → Option σ) (t : ℕ) :
    (flip bind step)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    exact ih

private lemma flip_bind_some {σ : Type*} (step : σ → Option σ) (x : σ) :
    flip bind step (some x) = step x := rfl

private def stmtPushes {K : Type*} {Γ : K → Type*} {Λ σ : Type*} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtPushes q
  | .peek _ _ q => stmtPushes q
  | .pop _ _ q => stmtPushes q
  | .load _ q => stmtPushes q
  | .branch _ q₁ q₂ => max (stmtPushes q₁) (stmtPushes q₂)
  | .goto _ => 0
  | .halt => 0

private lemma stepAux_stk_length_le {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + stmtPushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    have h1 := ih v (Function.update S k' (f v :: S k'))
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, List.length_cons] at h1
      omega
    · simp only [Function.update_of_ne hk] at h1
      omega
  | peek k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    exact ih _ S
  | pop k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    have h1 := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self] at h1
      have htail : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
      omega
    · simp only [Function.update_of_ne hk] at h1
      exact h1
  | load a q ih =>
    simp only [TM2.stepAux, stmtPushes]
    exact ih _ S
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, stmtPushes]
    cases p v
    · simp only [Bool.cond_false]
      have h2 := ih₂ v S
      omega
    · simp only [Bool.cond_true]
      have h1 := ih₁ v S
      omega
  | goto _ =>
    simp [stmtPushes]
  | halt =>
    simp [stmtPushes]

private def maxPushes (tm : FinTM2) : ℕ :=
  Finset.univ.sup fun l : tm.Λ => stmtPushes (tm.m l)

private lemma evals_stk_length_le (tm : FinTM2) (s : ℕ) (c c' : tm.Cfg)
    (heval : (flip bind tm.step)^[s] (some c) = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + s * maxPushes tm := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq, zero_mul, add_zero] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval
    rcases c with ⟨l_opt, v, S⟩
    rcases l_opt with _ | l
    · change (flip bind tm.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval
      cases heval
    · change (flip bind tm.step)^[s] (some (TM2.stepAux (tm.m l) v S)) = some c' at heval
      have hrec := ih (TM2.stepAux (tm.m l) v S) heval
      have hstep := stepAux_stk_length_le (tm.m l) v S k
      have hle : stmtPushes (tm.m l) ≤ maxPushes tm :=
        Finset.le_sup (f := fun l : tm.Λ => stmtPushes (tm.m l)) (Finset.mem_univ l)
      dsimp only
      rw [Nat.succ_mul]
      omega

private lemma initList_stk_length_le (tm : FinTM2) (L : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm L).stk k).length ≤ L.length := by
  by_cases hk : k = tm.k₀
  · subst hk
    simp [initList]
  · simp [initList, hk]

private lemma haltList_stk_k1 (tm : FinTM2) (L : List (tm.Γ tm.k₁)) :
    (haltList tm L).stk tm.k₁ = L := by
  simp [haltList]

private lemma poly_eval_mono (P : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) :
    P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

private def delimitRevAux : List Bool → List Bool → List Bool
  | [], acc => acc
  | b :: rest, acc => delimitRevAux rest (true :: b :: acc)

private lemma delimitRevAux_append (xs ys acc : List Bool) :
    delimitRevAux (xs ++ ys) acc = delimitRevAux ys (delimitRevAux xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b xs ih => exact ih (true :: b :: acc)

private lemma delimitRevAux_reverse (L acc : List Bool) :
    delimitRevAux L.reverse (false :: acc) = delimit L ++ acc := by
  induction L with
  | nil => rfl
  | cons b l ih =>
    simp only [List.reverse_cons, delimitRevAux_append, ih, delimitRevAux, delimit,
      List.cons_append]

/- ### 1. Composition `x ↦ g (f x)` -/

private structure CompData where
  tmF : FinTM2
  tmG : FinTM2
  outF : tmF.Γ tmF.k₁ ≃ Bool
  inG : tmG.Γ tmG.k₀ ≃ Bool

private abbrev CompData.CK (C : CompData) : Type := Unit ⊕ C.tmF.K ⊕ C.tmG.K
private abbrev CompData.CΛ (C : CompData) : Type := Fin 2 ⊕ C.tmF.Λ ⊕ C.tmG.Λ
private abbrev CompData.Cσ (C : CompData) : Type := Option Bool × C.tmF.σ × C.tmG.σ

private abbrev CompData.cΓ (C : CompData) : C.CK → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl kf) => C.tmF.Γ kf
  | Sum.inr (Sum.inr kg) => C.tmG.Γ kg

private def CompData.liftF (C : CompData) (next : C.CΛ) :
    TM2.Stmt C.tmF.Γ C.tmF.Λ C.tmF.σ → TM2.Stmt C.cΓ C.CΛ C.Cσ
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (C.liftF next q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (C.liftF next q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (C.liftF next q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (C.liftF next q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2.1) (C.liftF next q₁) (C.liftF next q₂)
  | .goto l => .goto (fun v => Sum.inr (Sum.inl (l v.2.1)))
  | .halt => .goto (fun _ => next)

private def CompData.liftG (C : CompData) :
    TM2.Stmt C.tmG.Γ C.tmG.Λ C.tmG.σ → TM2.Stmt C.cΓ C.CΛ C.Cσ
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun v => f v.2.2) (C.liftG q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (C.liftG q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (C.liftG q)
  | .load a q => .load (fun v => (v.1, v.2.1, a v.2.2)) (C.liftG q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2.2) (C.liftG q₁) (C.liftG q₂)
  | .goto l => .goto (fun v => Sum.inr (Sum.inr (l v.2.2)))
  | .halt => .halt

private def CompData.cStmt (C : CompData) : C.CΛ → TM2.Stmt C.cΓ C.CΛ C.Cσ
  | Sum.inl 0 =>
    .pop (Sum.inr (Sum.inl C.tmF.k₁)) (fun v o => (o.map C.outF.toFun, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl ()) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 0))))
        (.goto (fun _ => Sum.inl 1)))
  | Sum.inl 1 =>
    .pop (Sum.inl ()) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inr C.tmG.k₀)) (fun v => C.inG.invFun (v.1.getD false))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 1))))
        (.goto (fun _ => Sum.inr (Sum.inr C.tmG.main))))
  | Sum.inr (Sum.inl lf) => C.liftF (Sum.inl 0) (C.tmF.m lf)
  | Sum.inr (Sum.inr lg) => C.liftG (C.tmG.m lg)

private abbrev CompData.cTM (C : CompData) : FinTM2 where
  K := C.CK
  k₀ := Sum.inr (Sum.inl C.tmF.k₀)
  k₁ := Sum.inr (Sum.inr C.tmG.k₁)
  Γ := C.cΓ
  Λ := C.CΛ
  main := Sum.inr (Sum.inl C.tmF.main)
  σ := C.Cσ
  initialState := (none, C.tmF.initialState, C.tmG.initialState)
  Γk₀Fin := C.tmF.Γk₀Fin
  m := C.cStmt

private abbrev CompData.mkCfg (C : CompData) (l : Option C.CΛ) (v : C.Cσ)
    (S : ∀ k : C.CK, List (C.cΓ k)) : C.cTM.Cfg :=
  ⟨l, v, S⟩

private abbrev CompData.initVar (C : CompData) : C.Cσ :=
  (none, C.tmF.initialState, C.tmG.initialState)

@[simp]
private def CompData.mergeF (C : CompData)
    (Sf : ∀ kf, List (C.tmF.Γ kf)) : ∀ k : C.CK, List (C.cΓ k)
  | Sum.inr (Sum.inl kf) => Sf kf
  | _ => []

private def CompData.embedF (C : CompData) (next : C.CΛ) (v1 : Option Bool) (v3 : C.tmG.σ)
    (c : C.tmF.Cfg) : C.cTM.Cfg :=
  C.mkCfg
    (match c.l with
      | some lf => some (Sum.inr (Sum.inl lf))
      | none => some next)
    (v1, c.var, v3)
    (C.mergeF c.stk)

private lemma comp_stepAux_liftF (C : CompData) (next : C.CΛ) (v1 : Option Bool) (v3 : C.tmG.σ)
    (q : TM2.Stmt C.tmF.Γ C.tmF.Λ C.tmF.σ) (vf : C.tmF.σ) (Sf : ∀ kf, List (C.tmF.Γ kf)) :
    TM2.stepAux (C.liftF next q) (v1, vf, v3) (C.mergeF Sf) =
      C.embedF next v1 v3 (TM2.stepAux q vf Sf) := by
  induction q generalizing vf Sf with
  | push kf f q ih =>
    simp only [CompData.liftF, TM2.stepAux]
    have hupd : Function.update (C.mergeF Sf) (Sum.inr (Sum.inl kf))
        (f vf :: C.mergeF Sf (Sum.inr (Sum.inl kf))) =
        C.mergeF (Function.update Sf kf (f vf :: Sf kf)) := by
      funext k; rcases k with (_ | k' | _)
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
      · simp
    rw [hupd]; exact ih vf _
  | peek _ _ _ ih => simp only [CompData.liftF, TM2.stepAux, CompData.mergeF]; exact ih _ Sf
  | pop kf f q ih =>
    simp only [CompData.liftF, TM2.stepAux]
    have hupd : Function.update (C.mergeF Sf) (Sum.inr (Sum.inl kf))
        (C.mergeF Sf (Sum.inr (Sum.inl kf))).tail =
        C.mergeF (Function.update Sf kf (Sf kf).tail) := by
      funext k; rcases k with (_ | k' | _)
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
      · simp
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [CompData.liftF, TM2.stepAux]; exact ih _ Sf
  | branch p _ _ ih₁ ih₂ =>
    simp only [CompData.liftF, TM2.stepAux]
    cases p vf
    · simp only [Bool.cond_false]; exact ih₂ vf Sf
    · simp only [Bool.cond_true]; exact ih₁ vf Sf
  | goto _ => rfl
  | halt => rfl

private lemma comp_sim_tmF (C : CompData) (v1 : Option Bool) (v3 : C.tmG.σ)
    (s : ℕ) (c c' : C.tmF.Cfg)
    (heval : (flip bind C.tmF.step)^[s] (some c) = some c') :
    (flip bind C.cTM.step)^[s] (some (C.embedF (Sum.inl 0) v1 v3 c)) =
      some (C.embedF (Sum.inl 0) v1 v3 c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | lf, vf, Sf⟩
    · change (flip bind C.tmF.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind C.tmF.step)^[s] (some (TM2.stepAux (C.tmF.m lf) vf Sf)) = some c' at heval
      have hstep : C.cTM.step (C.embedF (Sum.inl 0) v1 v3 ⟨some lf, vf, Sf⟩) =
          some (C.embedF (Sum.inl 0) v1 v3 (TM2.stepAux (C.tmF.m lf) vf Sf)) :=
        congrArg some (comp_stepAux_liftF C (Sum.inl 0) v1 v3 (C.tmF.m lf) vf Sf)
      rw [hstep]; exact ih _ heval

@[simp]
private def CompData.mergeG (C : CompData)
    (Sg : ∀ kg, List (C.tmG.Γ kg)) : ∀ k : C.CK, List (C.cΓ k)
  | Sum.inr (Sum.inr kg) => Sg kg
  | _ => []

private def CompData.embedG (C : CompData) (v1 : Option Bool) (v2 : C.tmF.σ)
    (c : C.tmG.Cfg) : C.cTM.Cfg :=
  C.mkCfg (c.l.map fun lg => Sum.inr (Sum.inr lg)) (v1, v2, c.var) (C.mergeG c.stk)

private lemma comp_stepAux_liftG (C : CompData) (v1 : Option Bool) (v2 : C.tmF.σ)
    (q : TM2.Stmt C.tmG.Γ C.tmG.Λ C.tmG.σ) (vg : C.tmG.σ) (Sg : ∀ kg, List (C.tmG.Γ kg)) :
    TM2.stepAux (C.liftG q) (v1, v2, vg) (C.mergeG Sg) =
      C.embedG v1 v2 (TM2.stepAux q vg Sg) := by
  induction q generalizing vg Sg with
  | push kg f q ih =>
    simp only [CompData.liftG, TM2.stepAux]
    have hupd : Function.update (C.mergeG Sg) (Sum.inr (Sum.inr kg))
        (f vg :: C.mergeG Sg (Sum.inr (Sum.inr kg))) =
        C.mergeG (Function.update Sg kg (f vg :: Sg kg)) := by
      funext k; rcases k with (_ | _ | k')
      · simp
      · simp
      · by_cases hk : k' = kg
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih vg _
  | peek _ _ _ ih => simp only [CompData.liftG, TM2.stepAux, CompData.mergeG]; exact ih _ Sg
  | pop kg f q ih =>
    simp only [CompData.liftG, TM2.stepAux]
    have hupd : Function.update (C.mergeG Sg) (Sum.inr (Sum.inr kg))
        (C.mergeG Sg (Sum.inr (Sum.inr kg))).tail =
        C.mergeG (Function.update Sg kg (Sg kg).tail) := by
      funext k; rcases k with (_ | _ | k')
      · simp
      · simp
      · by_cases hk : k' = kg
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [CompData.liftG, TM2.stepAux]; exact ih _ Sg
  | branch p _ _ ih₁ ih₂ =>
    simp only [CompData.liftG, TM2.stepAux]
    cases p vg
    · simp only [Bool.cond_false]; exact ih₂ vg Sg
    · simp only [Bool.cond_true]; exact ih₁ vg Sg
  | goto _ => rfl
  | halt => rfl

private lemma comp_sim_tmG (C : CompData) (v1 : Option Bool) (v2 : C.tmF.σ)
    (s : ℕ) (c c' : C.tmG.Cfg)
    (heval : (flip bind C.tmG.step)^[s] (some c) = some c') :
    (flip bind C.cTM.step)^[s] (some (C.embedG v1 v2 c)) =
      some (C.embedG v1 v2 c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | lg, vg, Sg⟩
    · change (flip bind C.tmG.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind C.tmG.step)^[s] (some (TM2.stepAux (C.tmG.m lg) vg Sg)) = some c' at heval
      have hstep : C.cTM.step (C.embedG v1 v2 ⟨some lg, vg, Sg⟩) =
          some (C.embedG v1 v2 (TM2.stepAux (C.tmG.m lg) vg Sg)) :=
        congrArg some (comp_stepAux_liftG C v1 v2 (C.tmG.m lg) vg Sg)
      rw [hstep]; exact ih _ heval

private lemma comp_phase0 (C : CompData) (ws : List Bool)
    (S : ∀ k : C.CK, List (C.cΓ k))
    (hw : S (Sum.inr (Sum.inl C.tmF.k₁)) = ws.map C.outF.invFun) :
    ∃ S₁ : ∀ k : C.CK, List (C.cΓ k),
      (flip bind C.cTM.step)^[ws.length + 1] (some (C.mkCfg (some (Sum.inl 0)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 1)) C.initVar S₁) ∧
      S₁ (Sum.inr (Sum.inl C.tmF.k₁)) = [] ∧
      S₁ (Sum.inl ()) = ws.reverse ++ S (Sum.inl ()) ∧
      ∀ k, k ≠ Sum.inr (Sum.inl C.tmF.k₁) → k ≠ Sum.inl () → S₁ k = S k := by
  induction ws generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inr (Sum.inl C.tmF.k₁)) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.cStmt ⟨some (Sum.inl 0), C.initVar, S⟩ =
        some ⟨some (Sum.inl 1), C.initVar, Function.update S (Sum.inr (Sum.inl C.tmF.k₁)) []⟩
      simp [CompData.cStmt, hw]
    · intro k hkf1 _
      exact Function.update_of_ne hkf1 _ _
  | cons b ws ih =>
    let S' : ∀ k : C.CK, List (C.cΓ k) := Function.update
      (Function.update S (Sum.inr (Sum.inl C.tmF.k₁)) (ws.map C.outF.invFun))
      (Sum.inl ()) (b :: S (Sum.inl ()))
    have hstep : C.cTM.step (C.mkCfg (some (Sum.inl 0)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 0)) C.initVar S') := by
      change TM2.step C.cStmt ⟨some (Sum.inl 0), C.initVar, S⟩ =
        some ⟨some (Sum.inl 0), C.initVar, S'⟩
      simp [CompData.cStmt, hw, S']
    have hS'kf1 : S' (Sum.inr (Sum.inl C.tmF.k₁)) = ws.map C.outF.invFun := by simp [S']
    have hS'0 : S' (Sum.inl ()) = b :: S (Sum.inl ()) := by simp [S']
    obtain ⟨S₁, heval, h1kf1, h10, h1other⟩ := ih S' hS'kf1
    refine ⟨S₁, ?_, h1kf1, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h10, hS'0, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hkf1 hk0
      rw [h1other k hkf1 hk0]
      simp [S', Function.update_of_ne hk0, Function.update_of_ne hkf1]

private lemma comp_phase1 (C : CompData) (zs : List Bool)
    (S : ∀ k : C.CK, List (C.cΓ k))
    (hz : S (Sum.inl ()) = zs) :
    ∃ S₂ : ∀ k : C.CK, List (C.cΓ k),
      (flip bind C.cTM.step)^[zs.length + 1] (some (C.mkCfg (some (Sum.inl 1)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂) ∧
      S₂ (Sum.inl ()) = [] ∧
      S₂ (Sum.inr (Sum.inr C.tmG.k₀)) =
        zs.reverse.map C.inG.invFun ++ S (Sum.inr (Sum.inr C.tmG.k₀)) ∧
      ∀ k, k ≠ Sum.inl () → k ≠ Sum.inr (Sum.inr C.tmG.k₀) → S₂ k = S k := by
  induction zs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl ()) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.cStmt ⟨some (Sum.inl 1), C.initVar, S⟩ =
        some ⟨some (Sum.inr (Sum.inr C.tmG.main)), C.initVar, Function.update S (Sum.inl ()) []⟩
      simp [CompData.cStmt, hz]
    · intro k hk0 _
      exact Function.update_of_ne hk0 _ _
  | cons b zs ih =>
    let S' : ∀ k : C.CK, List (C.cΓ k) := Function.update
      (Function.update S (Sum.inl ()) zs)
      (Sum.inr (Sum.inr C.tmG.k₀))
      (C.inG.invFun b :: S (Sum.inr (Sum.inr C.tmG.k₀)))
    have hstep : C.cTM.step (C.mkCfg (some (Sum.inl 1)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 1)) C.initVar S') := by
      change TM2.step C.cStmt ⟨some (Sum.inl 1), C.initVar, S⟩ =
        some ⟨some (Sum.inl 1), C.initVar, S'⟩
      simp [CompData.cStmt, hz, S']
    have hS'0 : S' (Sum.inl ()) = zs := by simp [S']
    have hS'kg0 : S' (Sum.inr (Sum.inr C.tmG.k₀)) =
        C.inG.invFun b :: S (Sum.inr (Sum.inr C.tmG.k₀)) := by simp [S']
    obtain ⟨S₂, heval, h20, h2kg0, h2other⟩ := ih S' hS'0
    refine ⟨S₂, ?_, h20, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h2kg0, hS'kg0, List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
        List.singleton_append]
    · intro k hk0 hkg0
      rw [h2other k hk0 hkg0]
      simp [S', Function.update_of_ne hkg0, Function.update_of_ne hk0]

theorem isPolyTime_comp {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {f : α → β} {g : β → γ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => g (f x)) := by
  rcases hf with ⟨Mf⟩
  rcases hg with ⟨Mg⟩
  let C : CompData := {
    tmF := Mf.tm
    tmG := Mg.tm
    outF := Mf.outputAlphabet
    inG := Mg.inputAlphabet
  }
  let Bf : ℕ := maxPushes C.tmF
  let polyY : Polynomial ℕ := Polynomial.X + Mf.time * Polynomial.C Bf
  let totalTime : Polynomial ℕ :=
    Mf.time + Polynomial.C 2 * polyY + Polynomial.C 2 + Mg.time.comp polyY
  have hout : ∀ x : α, Nonempty (TM2OutputsInTime C.cTM
      (List.map Mf.inputAlphabet.invFun ((BitstringEncoding.toEncoding (α := α)).encode x))
      (some (List.map Mg.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := γ)).encode (g (f x)))))
      (totalTime.eval ((BitstringEncoding.toEncoding (α := α)).encode x).length)) := fun x => by
    let L : List Bool := bitEncode x
    let Y : List Bool := bitEncode (f x)
    let Z : List Bool := bitEncode (g (f x))
    change Nonempty (TM2OutputsInTime C.cTM (L.map Mf.inputAlphabet.invFun)
      (some (Z.map Mg.outputAlphabet.invFun)) (totalTime.eval L.length))
    have hMf_out : TM2OutputsInTime C.tmF (L.map Mf.inputAlphabet.invFun)
        (some (Y.map C.outF.invFun)) (Mf.time.eval L.length) := Mf.outputsFun x
    have hMg_out : TM2OutputsInTime C.tmG (Y.map C.inG.invFun)
        (some (Z.map Mg.outputAlphabet.invFun)) (Mg.time.eval Y.length) := Mg.outputsFun (f x)
    have hY_len : Y.length ≤ L.length + hMf_out.steps * Bf := by
      have hlen1 := evals_stk_length_le C.tmF hMf_out.steps _ _ hMf_out.evals_in_steps C.tmF.k₁
      rw [haltList_stk_k1, List.length_map] at hlen1
      have hlen0 := initList_stk_length_le C.tmF (L.map Mf.inputAlphabet.invFun) C.tmF.k₁
      rw [List.length_map] at hlen0
      exact le_trans hlen1 (Nat.add_le_add_right hlen0 _)
    have hY_poly : Y.length ≤ polyY.eval L.length := by
      have h1 : hMf_out.steps * Bf ≤ Mf.time.eval L.length * Bf :=
        Nat.mul_le_mul_right Bf hMf_out.steps_le_m
      simp only [polyY, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      omega
    have hMg_steps_le : hMg_out.steps ≤ (Mg.time.comp polyY).eval L.length := by
      rw [Polynomial.eval_comp]
      exact le_trans hMg_out.steps_le_m (poly_eval_mono Mg.time hY_poly)
    have hinit_eq : initList C.cTM (L.map Mf.inputAlphabet.invFun) =
        C.embedF (Sum.inl 0) none C.tmG.initialState
          (initList C.tmF (L.map Mf.inputAlphabet.invFun)) := by
      dsimp [CompData.embedF, CompData.mkCfg, initList, CompData.cTM]
      congr 1; funext k; rcases k with (_ | kf | _)
      · simp
      · by_cases hkf : kf = C.tmF.k₀
        · subst hkf; simp
        · simp [hkf]
      · simp
    have hp0 := comp_sim_tmF C none C.tmG.initialState hMf_out.steps _ _ hMf_out.evals_in_steps
    let c1 := C.embedF (Sum.inl 0) none C.tmG.initialState
      (haltList C.tmF (Y.map C.outF.invFun))
    have hc1_eq : c1 = C.mkCfg (some (Sum.inl 0)) C.initVar c1.stk := rfl
    have hc1_kf1 : c1.stk (Sum.inr (Sum.inl C.tmF.k₁)) = Y.map C.outF.invFun := by
      dsimp [c1, CompData.embedF]; simp [haltList]
    obtain ⟨S₁, hp1, hS1_kf1, hS1_0, hS1_other⟩ := comp_phase0 C Y c1.stk hc1_kf1
    have hc1_0 : c1.stk (Sum.inl ()) = [] := rfl
    rw [hc1_0, List.append_nil] at hS1_0
    obtain ⟨S₂, hp2, hS2_0, hS2_kg0, hS2_other⟩ := comp_phase1 C Y.reverse S₁ hS1_0
    have hS1_kg0 : S₁ (Sum.inr (Sum.inr C.tmG.k₀)) = [] := by
      rw [hS1_other _ (by simp) (by simp)]; rfl
    rw [List.reverse_reverse, hS1_kg0, List.append_nil] at hS2_kg0
    have hcfg3_eq : C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂ =
        C.embedG none C.tmF.initialState (initList C.tmG (Y.map C.inG.invFun)) := by
      dsimp [CompData.embedG, CompData.mkCfg, CompData.initVar, initList]
      congr 1; funext k; rcases k with (_ | kf | kg)
      · simp [hS2_0]
      · simp only [CompData.mergeG]
        rw [hS2_other _ (by simp) (by simp)]
        by_cases hkf1 : kf = C.tmF.k₁
        · subst hkf1; exact hS1_kf1
        · rw [hS1_other _ (by simp [hkf1]) (by simp)]
          dsimp [c1, CompData.embedF, haltList]; simp [hkf1]
      · by_cases hkg0 : kg = C.tmG.k₀
        · subst hkg0; simp [hS2_kg0]
        · simp only [CompData.mergeG, hkg0, ↓reduceDIte]
          rw [hS2_other _ (by simp) (by simp [hkg0]), hS1_other _ (by simp) (by simp)]
          rfl
    have hp3 := comp_sim_tmG C none C.tmF.initialState hMg_out.steps _ _ hMg_out.evals_in_steps
    have hhalt_eq : C.embedG none C.tmF.initialState
        (haltList C.tmG (Z.map Mg.outputAlphabet.invFun)) =
        haltList C.cTM (Z.map Mg.outputAlphabet.invFun) := by
      dsimp [CompData.embedG, CompData.mkCfg, haltList, CompData.cTM]
      congr 1; funext k; rcases k with (_ | _ | kg)
      · simp
      · simp
      · by_cases hkg1 : kg = C.tmG.k₁
        · subst hkg1; simp
        · simp [hkg1]
    let e0 : EvalsTo C.cTM.step (initList C.cTM (L.map Mf.inputAlphabet.invFun)) (some c1) :=
      ⟨hMf_out.steps, by rw [hinit_eq]; exact hp0⟩
    let e1 : EvalsTo C.cTM.step c1
        (some (C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂)) :=
      EvalsTo.trans C.cTM.step _ _ _
        ⟨Y.length + 1, by rw [hc1_eq]; exact hp1⟩
        ⟨Y.reverse.length + 1, hp2⟩
    let e2 : EvalsTo C.cTM.step (C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂)
        (some (haltList C.cTM (Z.map Mg.outputAlphabet.invFun))) :=
      ⟨hMg_out.steps, by rw [hcfg3_eq, ← hhalt_eq]; exact hp3⟩
    let eAll := EvalsTo.trans C.cTM.step _ _ _ e0 (EvalsTo.trans C.cTM.step _ _ _ e1 e2)
    refine ⟨⟨eAll, ?_⟩⟩
    dsimp only [eAll, e0, e1, e2, EvalsTo.trans]
    have hMf_le := hMf_out.steps_le_m
    simp only [List.length_reverse, totalTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C]
    omega
  exact ⟨{
    tm := C.cTM
    inputAlphabet := Mf.inputAlphabet
    outputAlphabet := Mg.outputAlphabet
    time := totalTime
    outputsFun := fun x => Classical.choice (hout x)
  }⟩

/- ### 2. Pairing with identity `x ↦ (x, f x)` -/

private structure PairIdData where
  tmF : FinTM2
  inF : tmF.Γ tmF.k₀ ≃ Bool
  outF : tmF.Γ tmF.k₁ ≃ Bool

private abbrev PairIdData.PK (D : PairIdData) : Type := Fin 4 ⊕ D.tmF.K
private abbrev PairIdData.PΛ (D : PairIdData) : Type := Fin 5 ⊕ D.tmF.Λ
private abbrev PairIdData.Pσ (D : PairIdData) : Type := Option Bool × D.tmF.σ

private abbrev PairIdData.pΓ (D : PairIdData) : D.PK → Type
  | Sum.inl _ => Bool
  | Sum.inr kf => D.tmF.Γ kf

private def PairIdData.liftF (D : PairIdData) (next : D.PΛ) :
    TM2.Stmt D.tmF.Γ D.tmF.Λ D.tmF.σ → TM2.Stmt D.pΓ D.PΛ D.Pσ
  | .push k f q => .push (Sum.inr k) (fun v => f v.2) (D.liftF next q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (v.1, f v.2 o)) (D.liftF next q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (v.1, f v.2 o)) (D.liftF next q)
  | .load a q => .load (fun v => (v.1, a v.2)) (D.liftF next q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2) (D.liftF next q₁) (D.liftF next q₂)
  | .goto l => .goto (fun v => Sum.inr (l v.2))
  | .halt => .goto (fun _ => next)

private def PairIdData.pStmt (D : PairIdData) : D.PΛ → TM2.Stmt D.pΓ D.PΛ D.Pσ
  | Sum.inl 0 =>
    .pop (Sum.inl 0) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 1) (fun v => v.1.getD false)
          (.push (Sum.inl 2) (fun v => v.1.getD false)
            (.load (fun v => (none, v.2))
              (.goto (fun _ => Sum.inl 0)))))
        (.goto (fun _ => Sum.inl 1)))
  | Sum.inl 1 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr D.tmF.k₀) (fun v => D.inF.invFun (v.1.getD false))
          (.load (fun v => (none, v.2))
            (.goto (fun _ => Sum.inl 1))))
        (.goto (fun _ => Sum.inr D.tmF.main)))
  | Sum.inl 2 =>
    .pop (Sum.inr D.tmF.k₁) (fun v o => (o.map D.outF.toFun, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 1) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2))
            (.goto (fun _ => Sum.inl 2))))
        (.goto (fun _ => Sum.inl 3)))
  | Sum.inl 3 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 3) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2))
            (.goto (fun _ => Sum.inl 3))))
        (.push (Sum.inl 3) (fun _ => false)
          (.goto (fun _ => Sum.inl 4))))
  | Sum.inl 4 =>
    .pop (Sum.inl 2) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 3) (fun v => v.1.getD false)
          (.push (Sum.inl 3) (fun _ => true)
            (.load (fun v => (none, v.2))
              (.goto (fun _ => Sum.inl 4)))))
        .halt)
  | Sum.inr lf => D.liftF (Sum.inl 2) (D.tmF.m lf)

private abbrev PairIdData.pTM (D : PairIdData) : FinTM2 where
  K := D.PK
  k₀ := Sum.inl 0
  k₁ := Sum.inl 3
  Γ := D.pΓ
  Λ := D.PΛ
  main := Sum.inl 0
  σ := D.Pσ
  initialState := (none, D.tmF.initialState)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := D.pStmt

private abbrev PairIdData.mkCfg (D : PairIdData) (l : Option D.PΛ) (v : D.Pσ)
    (S : ∀ k : D.PK, List (D.pΓ k)) : D.pTM.Cfg :=
  ⟨l, v, S⟩

private abbrev PairIdData.initVar (D : PairIdData) : D.Pσ :=
  (none, D.tmF.initialState)

@[simp]
private def PairIdData.mergeF (D : PairIdData)
    (baseStk : ∀ k : D.PK, List (D.pΓ k))
    (Sf : ∀ kf, List (D.tmF.Γ kf)) : ∀ k : D.PK, List (D.pΓ k)
  | Sum.inr kf => Sf kf
  | other => baseStk other

private def PairIdData.embedF (D : PairIdData) (next : D.PΛ) (v1 : Option Bool)
    (baseStk : ∀ k : D.PK, List (D.pΓ k)) (c : D.tmF.Cfg) : D.pTM.Cfg :=
  D.mkCfg
    (match c.l with
      | some lf => some (Sum.inr lf)
      | none => some next)
    (v1, c.var)
    (D.mergeF baseStk c.stk)

private lemma pairId_stepAux_liftF (D : PairIdData) (next : D.PΛ) (v1 : Option Bool)
    (baseStk : ∀ k : D.PK, List (D.pΓ k))
    (q : TM2.Stmt D.tmF.Γ D.tmF.Λ D.tmF.σ) (vf : D.tmF.σ) (Sf : ∀ kf, List (D.tmF.Γ kf)) :
    TM2.stepAux (D.liftF next q) (v1, vf) (D.mergeF baseStk Sf) =
      D.embedF next v1 baseStk (TM2.stepAux q vf Sf) := by
  induction q generalizing vf Sf with
  | push kf f q ih =>
    simp only [PairIdData.liftF, TM2.stepAux]
    have hupd : Function.update (D.mergeF baseStk Sf) (Sum.inr kf)
        (f vf :: D.mergeF baseStk Sf (Sum.inr kf)) =
        D.mergeF baseStk (Function.update Sf kf (f vf :: Sf kf)) := by
      funext k; rcases k with (_ | k')
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih vf _
  | peek _ _ _ ih => simp only [PairIdData.liftF, TM2.stepAux, PairIdData.mergeF]; exact ih _ Sf
  | pop kf f q ih =>
    simp only [PairIdData.liftF, TM2.stepAux]
    have hupd : Function.update (D.mergeF baseStk Sf) (Sum.inr kf)
        (D.mergeF baseStk Sf (Sum.inr kf)).tail =
        D.mergeF baseStk (Function.update Sf kf (Sf kf).tail) := by
      funext k; rcases k with (_ | k')
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [PairIdData.liftF, TM2.stepAux]; exact ih _ Sf
  | branch p _ _ ih₁ ih₂ =>
    simp only [PairIdData.liftF, TM2.stepAux]
    cases p vf
    · simp only [Bool.cond_false]; exact ih₂ vf Sf
    · simp only [Bool.cond_true]; exact ih₁ vf Sf
  | goto _ => rfl
  | halt => rfl

private lemma pairId_sim_tmF (D : PairIdData) (v1 : Option Bool)
    (baseStk : ∀ k : D.PK, List (D.pΓ k))
    (s : ℕ) (c c' : D.tmF.Cfg)
    (heval : (flip bind D.tmF.step)^[s] (some c) = some c') :
    (flip bind D.pTM.step)^[s] (some (D.embedF (Sum.inl 2) v1 baseStk c)) =
      some (D.embedF (Sum.inl 2) v1 baseStk c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | lf, vf, Sf⟩
    · change (flip bind D.tmF.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind D.tmF.step)^[s] (some (TM2.stepAux (D.tmF.m lf) vf Sf)) = some c' at heval
      have hstep : D.pTM.step (D.embedF (Sum.inl 2) v1 baseStk ⟨some lf, vf, Sf⟩) =
          some (D.embedF (Sum.inl 2) v1 baseStk (TM2.stepAux (D.tmF.m lf) vf Sf)) :=
        congrArg some (pairId_stepAux_liftF D (Sum.inl 2) v1 baseStk (D.tmF.m lf) vf Sf)
      rw [hstep]; exact ih _ heval

private lemma pairId_p0 (D : PairIdData) (xs : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (h0 : S (Sum.inl 0) = xs) :
    ∃ S₁ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[xs.length + 1] (some (D.mkCfg (some (Sum.inl 0)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 1)) D.initVar S₁) ∧
      S₁ (Sum.inl 0) = [] ∧
      S₁ (Sum.inl 1) = xs.reverse ++ S (Sum.inl 1) ∧
      S₁ (Sum.inl 2) = xs.reverse ++ S (Sum.inl 2) ∧
      ∀ k, k ≠ Sum.inl 0 → k ≠ Sum.inl 1 → k ≠ Sum.inl 2 → S₁ k = S k := by
  induction xs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 0) [], ?_, by simp, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 0), D.initVar, S⟩ =
        some ⟨some (Sum.inl 1), D.initVar, Function.update S (Sum.inl 0) []⟩
      simp [PairIdData.pStmt, h0]
    · intro k hk0 _ _
      exact Function.update_of_ne hk0 _ _
  | cons b xs ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) :=
      Function.update
        (Function.update (Function.update S (Sum.inl 0) xs) (Sum.inl 1) (b :: S (Sum.inl 1)))
        (Sum.inl 2) (b :: S (Sum.inl 2))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 0)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 0)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 0), D.initVar, S⟩ =
        some ⟨some (Sum.inl 0), D.initVar, S'⟩
      simp [PairIdData.pStmt, h0, S']
    have hS'0 : S' (Sum.inl 0) = xs := by simp [S']
    have hS'1 : S' (Sum.inl 1) = b :: S (Sum.inl 1) := by simp [S']
    have hS'2 : S' (Sum.inl 2) = b :: S (Sum.inl 2) := by simp [S']
    obtain ⟨S₁, heval, h10, h11, h12, h1other⟩ := ih S' hS'0
    refine ⟨S₁, ?_, h10, ?_, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h11, hS'1, List.reverse_cons, List.append_assoc, List.singleton_append]
    · rw [h12, hS'2, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hk0 hk1 hk2
      rw [h1other k hk0 hk1 hk2]
      simp [S', Function.update_of_ne hk2, Function.update_of_ne hk1, Function.update_of_ne hk0]

private lemma pairId_p1 (D : PairIdData) (ys : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (h1 : S (Sum.inl 1) = ys) :
    ∃ S₂ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[ys.length + 1] (some (D.mkCfg (some (Sum.inl 1)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inr D.tmF.main)) D.initVar S₂) ∧
      S₂ (Sum.inl 1) = [] ∧
      S₂ (Sum.inr D.tmF.k₀) = ys.reverse.map D.inF.invFun ++ S (Sum.inr D.tmF.k₀) ∧
      ∀ k, k ≠ Sum.inl 1 → k ≠ Sum.inr D.tmF.k₀ → S₂ k = S k := by
  induction ys generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 1) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 1), D.initVar, S⟩ =
        some ⟨some (Sum.inr D.tmF.main), D.initVar, Function.update S (Sum.inl 1) []⟩
      simp [PairIdData.pStmt, h1]
    · intro k hk1 _
      exact Function.update_of_ne hk1 _ _
  | cons b ys ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 1) ys)
      (Sum.inr D.tmF.k₀) (D.inF.invFun b :: S (Sum.inr D.tmF.k₀))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 1)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 1)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 1), D.initVar, S⟩ =
        some ⟨some (Sum.inl 1), D.initVar, S'⟩
      simp [PairIdData.pStmt, h1, S']
    have hS'1 : S' (Sum.inl 1) = ys := by simp [S']
    have hS'kf : S' (Sum.inr D.tmF.k₀) = D.inF.invFun b :: S (Sum.inr D.tmF.k₀) := by simp [S']
    obtain ⟨S₂, heval, h21, h2kf, h2other⟩ := ih S' hS'1
    refine ⟨S₂, ?_, h21, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h2kf, hS'kf, List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
        List.singleton_append]
    · intro k hk1 hkf
      rw [h2other k hk1 hkf]
      simp [S', Function.update_of_ne hkf, Function.update_of_ne hk1]

private lemma pairId_p2 (D : PairIdData) (ws : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (hw : S (Sum.inr D.tmF.k₁) = ws.map D.outF.invFun) :
    ∃ S₄ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[ws.length + 1] (some (D.mkCfg (some (Sum.inl 2)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 3)) D.initVar S₄) ∧
      S₄ (Sum.inr D.tmF.k₁) = [] ∧
      S₄ (Sum.inl 1) = ws.reverse ++ S (Sum.inl 1) ∧
      ∀ k, k ≠ Sum.inr D.tmF.k₁ → k ≠ Sum.inl 1 → S₄ k = S k := by
  induction ws generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inr D.tmF.k₁) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 2), D.initVar, S⟩ =
        some ⟨some (Sum.inl 3), D.initVar, Function.update S (Sum.inr D.tmF.k₁) []⟩
      simp [PairIdData.pStmt, hw]
    · intro k hkf1 _
      exact Function.update_of_ne hkf1 _ _
  | cons b ws ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inr D.tmF.k₁) (ws.map D.outF.invFun))
      (Sum.inl 1) (b :: S (Sum.inl 1))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 2)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 2)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 2), D.initVar, S⟩ =
        some ⟨some (Sum.inl 2), D.initVar, S'⟩
      simp [PairIdData.pStmt, hw, S']
    have hS'kf1 : S' (Sum.inr D.tmF.k₁) = ws.map D.outF.invFun := by simp [S']
    have hS'1 : S' (Sum.inl 1) = b :: S (Sum.inl 1) := by simp [S']
    obtain ⟨S₄, heval, h4kf1, h41, h4other⟩ := ih S' hS'kf1
    refine ⟨S₄, ?_, h4kf1, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h41, hS'1, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hkf1 hk1
      rw [h4other k hkf1 hk1]
      simp [S', Function.update_of_ne hk1, Function.update_of_ne hkf1]

private lemma pairId_p3 (D : PairIdData) (zs : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (hz : S (Sum.inl 1) = zs) :
    ∃ S₅ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[zs.length + 1] (some (D.mkCfg (some (Sum.inl 3)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 4)) D.initVar S₅) ∧
      S₅ (Sum.inl 1) = [] ∧
      S₅ (Sum.inl 3) = false :: (zs.reverse ++ S (Sum.inl 3)) ∧
      ∀ k, k ≠ Sum.inl 1 → k ≠ Sum.inl 3 → S₅ k = S k := by
  induction zs generalizing S with
  | nil =>
    let S₅ : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 1) [])
      (Sum.inl 3) (false :: S (Sum.inl 3))
    refine ⟨S₅, ?_, by simp [S₅], by simp [S₅], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 3), D.initVar, S⟩ =
        some ⟨some (Sum.inl 4), D.initVar, S₅⟩
      simp [PairIdData.pStmt, hz, S₅]
    · intro k hk1 hk3
      simp [S₅, Function.update_of_ne hk3, Function.update_of_ne hk1]
  | cons b zs ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 1) zs)
      (Sum.inl 3) (b :: S (Sum.inl 3))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 3)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 3)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 3), D.initVar, S⟩ =
        some ⟨some (Sum.inl 3), D.initVar, S'⟩
      simp [PairIdData.pStmt, hz, S']
    have hS'1 : S' (Sum.inl 1) = zs := by simp [S']
    have hS'3 : S' (Sum.inl 3) = b :: S (Sum.inl 3) := by simp [S']
    obtain ⟨S₅, heval, h51, h53, h5other⟩ := ih S' hS'1
    refine ⟨S₅, ?_, h51, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h53, hS'3, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hk1 hk3
      rw [h5other k hk1 hk3]
      simp [S', Function.update_of_ne hk3, Function.update_of_ne hk1]

private lemma pairId_p4 (D : PairIdData) (rs acc : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k))
    (hr : S (Sum.inl 2) = rs) (hacc : S (Sum.inl 3) = acc) :
    ∃ S₆ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[rs.length + 1] (some (D.mkCfg (some (Sum.inl 4)) D.initVar S)) =
        some (D.mkCfg none D.initVar S₆) ∧
      S₆ (Sum.inl 2) = [] ∧
      S₆ (Sum.inl 3) = delimitRevAux rs acc ∧
      ∀ k, k ≠ Sum.inl 2 → k ≠ Sum.inl 3 → S₆ k = S k := by
  induction rs generalizing acc S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 2) [], ?_, by simp, by simp [delimitRevAux, hacc], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 4), D.initVar, S⟩ =
        some ⟨none, D.initVar, Function.update S (Sum.inl 2) []⟩
      simp [PairIdData.pStmt, hr]
    · intro k hk2 _
      exact Function.update_of_ne hk2 _ _
  | cons b rs ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 2) rs)
      (Sum.inl 3) (true :: b :: S (Sum.inl 3))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 4)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 4)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 4), D.initVar, S⟩ =
        some ⟨some (Sum.inl 4), D.initVar, S'⟩
      simp [PairIdData.pStmt, hr, S']
    have hS'2 : S' (Sum.inl 2) = rs := by simp [S']
    have hS'3 : S' (Sum.inl 3) = true :: b :: acc := by simp [S', hacc]
    obtain ⟨S₆, heval, h62, h63, h6other⟩ := ih (true :: b :: acc) S' hS'2 hS'3
    refine ⟨S₆, ?_, h62, h63, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · intro k hk2 hk3
      rw [h6other k hk2 hk3]
      simp [S', Function.update_of_ne hk3, Function.update_of_ne hk2]

theorem isPolyTime_pairId {α β : Type}
    [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (hf : IsPolyTime f) :
    IsPolyTime (fun x => (x, f x)) := by
  rcases hf with ⟨Mf⟩
  let D : PairIdData := {
    tmF := Mf.tm
    inF := Mf.inputAlphabet
    outF := Mf.outputAlphabet
  }
  let Bf : ℕ := maxPushes D.tmF
  let polyY : Polynomial ℕ := Polynomial.X + Mf.time * Polynomial.C Bf
  let totalTime : Polynomial ℕ :=
    Polynomial.C 3 * Polynomial.X + Polynomial.C 5 + Mf.time + Polynomial.C 2 * polyY
  have hout : ∀ x : α, Nonempty (TM2OutputsInTime D.pTM
      (List.map (Equiv.refl Bool).invFun ((BitstringEncoding.toEncoding (α := α)).encode x))
      (some (List.map (Equiv.refl Bool).invFun
        ((BitstringEncoding.toEncoding (α := α × β)).encode (x, f x))))
      (totalTime.eval ((BitstringEncoding.toEncoding (α := α)).encode x).length)) := fun x => by
    let L : List Bool := bitEncode x
    let Y : List Bool := bitEncode (f x)
    change Nonempty (TM2OutputsInTime D.pTM (List.map (Equiv.refl Bool).invFun L)
      (some (List.map (Equiv.refl Bool).invFun (delimit L ++ Y))) (totalTime.eval L.length))
    have hmapL : List.map (Equiv.refl Bool).invFun L = L := by simp [Equiv.refl]
    have hmapP : List.map (Equiv.refl Bool).invFun (delimit L ++ Y) = delimit L ++ Y := by
      simp [Equiv.refl]
    rw [hmapL, hmapP]
    have hMf_out : TM2OutputsInTime D.tmF (L.map D.inF.invFun)
        (some (Y.map D.outF.invFun)) (Mf.time.eval L.length) := Mf.outputsFun x
    have hY_len : Y.length ≤ L.length + hMf_out.steps * Bf := by
      have hlen1 := evals_stk_length_le D.tmF hMf_out.steps _ _ hMf_out.evals_in_steps D.tmF.k₁
      rw [haltList_stk_k1, List.length_map] at hlen1
      have hlen0 := initList_stk_length_le D.tmF (L.map D.inF.invFun) D.tmF.k₁
      rw [List.length_map] at hlen0
      exact le_trans hlen1 (Nat.add_le_add_right hlen0 _)
    have hY_poly : Y.length ≤ polyY.eval L.length := by
      have h1 : hMf_out.steps * Bf ≤ Mf.time.eval L.length * Bf :=
        Nat.mul_le_mul_right Bf hMf_out.steps_le_m
      simp only [polyY, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      omega
    let c0 := initList D.pTM L
    have hc0_eq : c0 = D.mkCfg (some (Sum.inl 0)) D.initVar c0.stk := rfl
    have hc0_in : c0.stk (Sum.inl 0) = L := by simp [c0, PairIdData.pTM, initList]
    have hc0_other : ∀ k : D.PK, k ≠ Sum.inl 0 → c0.stk k = [] := by
      intro k hk; simp [c0, PairIdData.pTM, initList, hk]
    obtain ⟨S₁, hp0, hS1_0, hS1_1, hS1_2, hS1_other⟩ := pairId_p0 D L c0.stk hc0_in
    rw [hc0_other (Sum.inl 1) (by simp), List.append_nil] at hS1_1
    rw [hc0_other (Sum.inl 2) (by simp), List.append_nil] at hS1_2
    obtain ⟨S₂, hp1, hS2_1, hS2_kf0, hS2_other⟩ := pairId_p1 D L.reverse S₁ hS1_1
    have hS1_kf0 : S₁ (Sum.inr D.tmF.k₀) = [] := by
      rw [hS1_other _ (by simp) (by simp) (by simp)]; exact hc0_other _ (by simp)
    rw [List.reverse_reverse, hS1_kf0, List.append_nil] at hS2_kf0
    have hcfg2_eq : D.mkCfg (some (Sum.inr D.tmF.main)) D.initVar S₂ =
        D.embedF (Sum.inl 2) none S₂ (initList D.tmF (L.map D.inF.invFun)) := by
      dsimp [PairIdData.embedF, PairIdData.mkCfg, PairIdData.initVar, initList]
      congr 1; funext k; rcases k with (_ | kf)
      · rfl
      · by_cases hkf : kf = D.tmF.k₀
        · subst hkf; simp [hS2_kf0]
        · simp only [PairIdData.mergeF, hkf, ↓reduceDIte]
          rw [hS2_other _ (by simp) (by simp [hkf]),
            hS1_other _ (by simp) (by simp) (by simp), hc0_other _ (by simp)]
    have hp2 := pairId_sim_tmF D none S₂ hMf_out.steps _ _ hMf_out.evals_in_steps
    let c3 := D.embedF (Sum.inl 2) none S₂ (haltList D.tmF (Y.map D.outF.invFun))
    have hc3_eq : c3 = D.mkCfg (some (Sum.inl 2)) D.initVar c3.stk := rfl
    have hc3_kf1 : c3.stk (Sum.inr D.tmF.k₁) = Y.map D.outF.invFun := by
      dsimp [c3, PairIdData.embedF]; simp [haltList]
    obtain ⟨S₄, hp3, hS4_kf1, hS4_1, hS4_other⟩ := pairId_p2 D Y c3.stk hc3_kf1
    have hc3_1 : c3.stk (Sum.inl 1) = [] := by
      dsimp [c3, PairIdData.embedF]; exact hS2_1
    rw [hc3_1, List.append_nil] at hS4_1
    obtain ⟨S₅, hp4, hS5_1, hS5_3, hS5_other⟩ := pairId_p3 D Y.reverse S₄ hS4_1
    have hS4_3 : S₄ (Sum.inl 3) = [] := by
      rw [hS4_other _ (by simp) (by simp)]
      dsimp [c3, PairIdData.embedF]
      rw [hS2_other _ (by simp) (by simp), hS1_other _ (by simp) (by simp) (by simp),
        hc0_other _ (by simp)]
    rw [List.reverse_reverse, hS4_3, List.append_nil] at hS5_3
    have hS5_2 : S₅ (Sum.inl 2) = L.reverse := by
      rw [hS5_other _ (by simp) (by simp), hS4_other _ (by simp) (by simp)]
      dsimp [c3, PairIdData.embedF]
      rw [hS2_other _ (by simp) (by simp)]; exact hS1_2
    obtain ⟨S₆, hp5, hS6_2, hS6_3, hS6_other⟩ :=
      pairId_p4 D L.reverse (false :: Y) S₅ hS5_2 hS5_3
    rw [delimitRevAux_reverse] at hS6_3
    have hhalt_eq : D.mkCfg none D.initVar S₆ = haltList D.pTM (delimit L ++ Y) := by
      dsimp [PairIdData.mkCfg, PairIdData.initVar, haltList, PairIdData.pTM]
      congr 1; funext k; rcases k with (i | kf)
      · fin_cases i
        · rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp),
            hS4_other _ (by simp) (by simp)]
          dsimp [c3, PairIdData.embedF]
          rw [hS2_other _ (by simp) (by simp)]; exact hS1_0
        · rw [hS6_other _ (by simp) (by simp)]; exact hS5_1
        · exact hS6_2
        · simp [hS6_3]
      · simp only [show (Sum.inr kf : D.PK) ≠ Sum.inl 3 by simp, ↓reduceDIte]
        rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp)]
        by_cases hkf1 : kf = D.tmF.k₁
        · subst hkf1; exact hS4_kf1
        · rw [hS4_other _ (by simp [hkf1]) (by simp)]
          dsimp [c3, PairIdData.embedF, haltList]; simp [hkf1]
    let e0 : EvalsTo D.pTM.step c0 (some (D.mkCfg (some (Sum.inl 1)) D.initVar S₁)) :=
      ⟨L.length + 1, by rw [hc0_eq]; exact hp0⟩
    let e1 : EvalsTo D.pTM.step (D.mkCfg (some (Sum.inl 1)) D.initVar S₁) (some c3) :=
      EvalsTo.trans D.pTM.step _ _ _
        ⟨L.reverse.length + 1, hp1⟩
        ⟨hMf_out.steps, by rw [hcfg2_eq]; exact hp2⟩
    let e2 : EvalsTo D.pTM.step c3 (some (D.mkCfg (some (Sum.inl 4)) D.initVar S₅)) :=
      EvalsTo.trans D.pTM.step _ _ _
        ⟨Y.length + 1, by rw [hc3_eq]; exact hp3⟩
        ⟨Y.reverse.length + 1, hp4⟩
    let e3 : EvalsTo D.pTM.step (D.mkCfg (some (Sum.inl 4)) D.initVar S₅)
        (some (haltList D.pTM (delimit L ++ Y))) :=
      ⟨L.reverse.length + 1, by rw [← hhalt_eq]; exact hp5⟩
    let eAll := EvalsTo.trans D.pTM.step _ _ _ e0
      (EvalsTo.trans D.pTM.step _ _ _ e1 (EvalsTo.trans D.pTM.step _ _ _ e2 e3))
    refine ⟨⟨eAll, ?_⟩⟩
    dsimp only [eAll, e0, e1, e2, e3, EvalsTo.trans]
    have hMf_le := hMf_out.steps_le_m
    simp only [List.length_reverse, totalTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    omega
  exact ⟨{
    tm := D.pTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := totalTime
    outputsFun := fun x => Classical.choice (hout x)
  }⟩

end PolyTimeSqrtH4Proof

theorem OMA.solution : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2.H1 := by
  intro threshold solver hthreshold hsolver
  exact PolyTimeSqrtH4Proof.isPolyTime_comp
    (PolyTimeSqrtH4Proof.isPolyTime_pairId hthreshold) hsolver
