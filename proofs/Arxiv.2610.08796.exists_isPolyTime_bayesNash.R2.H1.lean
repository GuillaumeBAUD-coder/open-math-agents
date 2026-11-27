import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2
import Mathlib.Tactic

/-!
# Proof of Arxiv.2610.08796 H1

Polynomial-time computability is closed under `x ↦ h (x, f x)`.
-/

namespace Arxiv2610R2H1Proof

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

private structure MachData where
  tmF : FinTM2
  tmH : FinTM2
  inF : tmF.Γ tmF.k₀ ≃ Bool
  outF : tmF.Γ tmF.k₁ ≃ Bool
  inH : tmH.Γ tmH.k₀ ≃ Bool

private abbrev MachData.CombK (D : MachData) : Type := Fin 3 ⊕ D.tmF.K ⊕ D.tmH.K
private abbrev MachData.CombΛ (D : MachData) : Type := Fin 5 ⊕ D.tmF.Λ ⊕ D.tmH.Λ
private abbrev MachData.Combσ (D : MachData) : Type := Option Bool × D.tmF.σ × D.tmH.σ

private abbrev MachData.combΓ (D : MachData) : D.CombK → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl kf) => D.tmF.Γ kf
  | Sum.inr (Sum.inr kh) => D.tmH.Γ kh

private def MachData.liftStmtF (D : MachData) (next : D.CombΛ) :
    TM2.Stmt D.tmF.Γ D.tmF.Λ D.tmF.σ → TM2.Stmt D.combΓ D.CombΛ D.Combσ
  | .push k f q =>
    .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (D.liftStmtF next q)
  | .peek k f q =>
    .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (D.liftStmtF next q)
  | .pop k f q =>
    .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (D.liftStmtF next q)
  | .load a q =>
    .load (fun v => (v.1, a v.2.1, v.2.2)) (D.liftStmtF next q)
  | .branch p q₁ q₂ =>
    .branch (fun v => p v.2.1) (D.liftStmtF next q₁) (D.liftStmtF next q₂)
  | .goto l =>
    .goto (fun v => Sum.inr (Sum.inl (l v.2.1)))
  | .halt =>
    .goto (fun _ => next)

private def MachData.liftStmtH (D : MachData) :
    TM2.Stmt D.tmH.Γ D.tmH.Λ D.tmH.σ → TM2.Stmt D.combΓ D.CombΛ D.Combσ
  | .push k f q =>
    .push (Sum.inr (Sum.inr k)) (fun v => f v.2.2) (D.liftStmtH q)
  | .peek k f q =>
    .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (D.liftStmtH q)
  | .pop k f q =>
    .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (D.liftStmtH q)
  | .load a q =>
    .load (fun v => (v.1, v.2.1, a v.2.2)) (D.liftStmtH q)
  | .branch p q₁ q₂ =>
    .branch (fun v => p v.2.2) (D.liftStmtH q₁) (D.liftStmtH q₂)
  | .goto l =>
    .goto (fun v => Sum.inr (Sum.inr (l v.2.2)))
  | .halt =>
    .halt

private def MachData.combStmt (D : MachData) : D.CombΛ → TM2.Stmt D.combΓ D.CombΛ D.Combσ
  | Sum.inl 0 =>
    .pop (Sum.inl 0) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 1) (fun v => v.1.getD false)
          (.push (Sum.inl 2) (fun v => v.1.getD false)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => Sum.inl 0)))))
        (.goto (fun _ => Sum.inl 1)))
  | Sum.inl 1 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inl D.tmF.k₀)) (fun v => D.inF.invFun (v.1.getD false))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 1))))
        (.goto (fun _ => Sum.inr (Sum.inl D.tmF.main))))
  | Sum.inl 2 =>
    .pop (Sum.inr (Sum.inl D.tmF.k₁)) (fun v o => (o.map D.outF.toFun, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 1) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 2))))
        (.goto (fun _ => Sum.inl 3)))
  | Sum.inl 3 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inr D.tmH.k₀)) (fun v => D.inH.invFun (v.1.getD false))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 3))))
        (.push (Sum.inr (Sum.inr D.tmH.k₀)) (fun _ => D.inH.invFun false)
          (.goto (fun _ => Sum.inl 4))))
  | Sum.inl 4 =>
    .pop (Sum.inl 2) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inr D.tmH.k₀)) (fun v => D.inH.invFun (v.1.getD false))
          (.push (Sum.inr (Sum.inr D.tmH.k₀)) (fun _ => D.inH.invFun true)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => Sum.inl 4)))))
        (.goto (fun _ => Sum.inr (Sum.inr D.tmH.main))))
  | Sum.inr (Sum.inl lf) => D.liftStmtF (Sum.inl 2) (D.tmF.m lf)
  | Sum.inr (Sum.inr lh) => D.liftStmtH (D.tmH.m lh)

private abbrev MachData.combTM (D : MachData) : FinTM2 where
  K := D.CombK
  k₀ := Sum.inl 0
  k₁ := Sum.inr (Sum.inr D.tmH.k₁)
  Γ := D.combΓ
  Λ := D.CombΛ
  main := Sum.inl 0
  σ := D.Combσ
  initialState := (none, D.tmF.initialState, D.tmH.initialState)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := D.combStmt

private abbrev MachData.mkCfg (D : MachData) (l : Option D.CombΛ) (v : D.Combσ)
    (S : ∀ k : D.CombK, List (D.combΓ k)) : D.combTM.Cfg :=
  ⟨l, v, S⟩

private abbrev MachData.initVar (D : MachData) : D.Combσ :=
  (none, D.tmF.initialState, D.tmH.initialState)

@[simp]
private def MachData.mergeStkF (D : MachData)
    (baseStk : ∀ k : D.CombK, List (D.combΓ k))
    (Sf : ∀ kf, List (D.tmF.Γ kf)) : ∀ k : D.CombK, List (D.combΓ k)
  | Sum.inr (Sum.inl kf) => Sf kf
  | other => baseStk other

private def MachData.embedCfgF (D : MachData) (next : D.CombΛ) (v1 : Option Bool) (v3 : D.tmH.σ)
    (baseStk : ∀ k : D.CombK, List (D.combΓ k))
    (c : D.tmF.Cfg) : D.combTM.Cfg :=
  D.mkCfg
    (match c.l with
      | some lf => some (Sum.inr (Sum.inl lf))
      | none => some next)
    (v1, c.var, v3)
    (D.mergeStkF baseStk c.stk)

private lemma stepAux_liftStmtF (D : MachData) (next : D.CombΛ) (v1 : Option Bool) (v3 : D.tmH.σ)
    (baseStk : ∀ k : D.CombK, List (D.combΓ k))
    (q : TM2.Stmt D.tmF.Γ D.tmF.Λ D.tmF.σ) (vf : D.tmF.σ) (Sf : ∀ kf, List (D.tmF.Γ kf)) :
    TM2.stepAux (D.liftStmtF next q) (v1, vf, v3) (D.mergeStkF baseStk Sf) =
      D.embedCfgF next v1 v3 baseStk (TM2.stepAux q vf Sf) := by
  induction q generalizing vf Sf with
  | push kf f q ih =>
    simp only [MachData.liftStmtF, TM2.stepAux]
    have hupd : Function.update (D.mergeStkF baseStk Sf) (Sum.inr (Sum.inl kf))
        (f vf :: D.mergeStkF baseStk Sf (Sum.inr (Sum.inl kf))) =
        D.mergeStkF baseStk (Function.update Sf kf (f vf :: Sf kf)) := by
      funext k
      rcases k with (i | k' | kh)
      · simp [MachData.mergeStkF]
      · by_cases hk : k' = kf
        · subst hk; simp [MachData.mergeStkF]
        · simp [MachData.mergeStkF, hk]
      · simp [MachData.mergeStkF]
    rw [hupd]
    exact ih vf _
  | peek kf f q ih =>
    simp only [MachData.liftStmtF, TM2.stepAux, MachData.mergeStkF]
    exact ih _ Sf
  | pop kf f q ih =>
    simp only [MachData.liftStmtF, TM2.stepAux]
    have hupd : Function.update (D.mergeStkF baseStk Sf) (Sum.inr (Sum.inl kf))
        (D.mergeStkF baseStk Sf (Sum.inr (Sum.inl kf))).tail =
        D.mergeStkF baseStk (Function.update Sf kf (Sf kf).tail) := by
      funext k
      rcases k with (i | k' | kh)
      · simp [MachData.mergeStkF]
      · by_cases hk : k' = kf
        · subst hk; simp [MachData.mergeStkF]
        · simp [MachData.mergeStkF, hk]
      · simp [MachData.mergeStkF]
    rw [hupd]
    exact ih _ _
  | load a q ih =>
    simp only [MachData.liftStmtF, TM2.stepAux]
    exact ih _ Sf
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [MachData.liftStmtF, TM2.stepAux]
    cases p vf
    · simp only [Bool.cond_false]; exact ih₂ vf Sf
    · simp only [Bool.cond_true]; exact ih₁ vf Sf
  | goto l =>
    rfl
  | halt =>
    rfl

private lemma sim_tmF (D : MachData) (v1 : Option Bool) (v3 : D.tmH.σ)
    (baseStk : ∀ k : D.CombK, List (D.combΓ k))
    (s : ℕ) (c c' : D.tmF.Cfg)
    (heval : (flip bind D.tmF.step)^[s] (some c) = some c') :
    (flip bind D.combTM.step)^[s]
      (some (D.embedCfgF (Sum.inl 2) v1 v3 baseStk c)) =
      some (D.embedCfgF (Sum.inl 2) v1 v3 baseStk c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨l_opt, vf, Sf⟩
    rcases l_opt with _ | lf
    · change (flip bind D.tmF.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval
      cases heval
    · change (flip bind D.tmF.step)^[s] (some (TM2.stepAux (D.tmF.m lf) vf Sf)) = some c' at heval
      have hstep : D.combTM.step (D.embedCfgF (Sum.inl 2) v1 v3 baseStk ⟨some lf, vf, Sf⟩) =
          some (D.embedCfgF (Sum.inl 2) v1 v3 baseStk (TM2.stepAux (D.tmF.m lf) vf Sf)) := by
        exact congrArg some (stepAux_liftStmtF D (Sum.inl 2) v1 v3 baseStk (D.tmF.m lf) vf Sf)
      rw [hstep]
      exact ih _ heval

@[simp]
private def MachData.mergeStkH (D : MachData)
    (Sh : ∀ kh, List (D.tmH.Γ kh)) : ∀ k : D.CombK, List (D.combΓ k)
  | Sum.inr (Sum.inr kh) => Sh kh
  | _ => []

private def MachData.embedCfgH (D : MachData) (v1 : Option Bool) (v2 : D.tmF.σ)
    (c : D.tmH.Cfg) : D.combTM.Cfg :=
  D.mkCfg (c.l.map fun lh => Sum.inr (Sum.inr lh)) (v1, v2, c.var) (D.mergeStkH c.stk)

private lemma stepAux_liftStmtH (D : MachData) (v1 : Option Bool) (v2 : D.tmF.σ)
    (q : TM2.Stmt D.tmH.Γ D.tmH.Λ D.tmH.σ) (vh : D.tmH.σ) (Sh : ∀ kh, List (D.tmH.Γ kh)) :
    TM2.stepAux (D.liftStmtH q) (v1, v2, vh) (D.mergeStkH Sh) =
      D.embedCfgH v1 v2 (TM2.stepAux q vh Sh) := by
  induction q generalizing vh Sh with
  | push kh f q ih =>
    simp only [MachData.liftStmtH, TM2.stepAux]
    have hupd : Function.update (D.mergeStkH Sh) (Sum.inr (Sum.inr kh))
        (f vh :: D.mergeStkH Sh (Sum.inr (Sum.inr kh))) =
        D.mergeStkH (Function.update Sh kh (f vh :: Sh kh)) := by
      funext k
      rcases k with (i | kf | k')
      · simp [MachData.mergeStkH]
      · simp [MachData.mergeStkH]
      · by_cases hk : k' = kh
        · subst hk; simp [MachData.mergeStkH]
        · simp [MachData.mergeStkH, hk]
    rw [hupd]
    exact ih vh _
  | peek kh f q ih =>
    simp only [MachData.liftStmtH, TM2.stepAux, MachData.mergeStkH]
    exact ih _ Sh
  | pop kh f q ih =>
    simp only [MachData.liftStmtH, TM2.stepAux]
    have hupd : Function.update (D.mergeStkH Sh) (Sum.inr (Sum.inr kh))
        (D.mergeStkH Sh (Sum.inr (Sum.inr kh))).tail =
        D.mergeStkH (Function.update Sh kh (Sh kh).tail) := by
      funext k
      rcases k with (i | kf | k')
      · simp [MachData.mergeStkH]
      · simp [MachData.mergeStkH]
      · by_cases hk : k' = kh
        · subst hk; simp [MachData.mergeStkH]
        · simp [MachData.mergeStkH, hk]
    rw [hupd]
    exact ih _ _
  | load a q ih =>
    simp only [MachData.liftStmtH, TM2.stepAux]
    exact ih _ Sh
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [MachData.liftStmtH, TM2.stepAux]
    cases p vh
    · simp only [Bool.cond_false]; exact ih₂ vh Sh
    · simp only [Bool.cond_true]; exact ih₁ vh Sh
  | goto l =>
    rfl
  | halt =>
    rfl

private lemma sim_tmH (D : MachData) (v1 : Option Bool) (v2 : D.tmF.σ)
    (s : ℕ) (c c' : D.tmH.Cfg)
    (heval : (flip bind D.tmH.step)^[s] (some c) = some c') :
    (flip bind D.combTM.step)^[s]
      (some (D.embedCfgH v1 v2 c)) =
      some (D.embedCfgH v1 v2 c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨l_opt, vh, Sh⟩
    rcases l_opt with _ | lh
    · change (flip bind D.tmH.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval
      cases heval
    · change (flip bind D.tmH.step)^[s] (some (TM2.stepAux (D.tmH.m lh) vh Sh)) = some c' at heval
      have hstep : D.combTM.step (D.embedCfgH v1 v2 ⟨some lh, vh, Sh⟩) =
          some (D.embedCfgH v1 v2 (TM2.stepAux (D.tmH.m lh) vh Sh)) := by
        exact congrArg some (stepAux_liftStmtH D v1 v2 (D.tmH.m lh) vh Sh)
      rw [hstep]
      exact ih _ heval

private lemma phase0_eval (D : MachData) (xs : List Bool)
    (S : ∀ k : D.CombK, List (D.combΓ k))
    (h0 : S (Sum.inl 0) = xs) :
    ∃ S₁ : ∀ k : D.CombK, List (D.combΓ k),
      (flip bind D.combTM.step)^[xs.length + 1] (some (D.mkCfg (some (Sum.inl 0)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 1)) D.initVar S₁) ∧
      S₁ (Sum.inl 0) = [] ∧
      S₁ (Sum.inl 1) = xs.reverse ++ S (Sum.inl 1) ∧
      S₁ (Sum.inl 2) = xs.reverse ++ S (Sum.inl 2) ∧
      ∀ k, k ≠ Sum.inl 0 → k ≠ Sum.inl 1 → k ≠ Sum.inl 2 → S₁ k = S k := by
  induction xs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 0) [], ?_, by simp, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.combStmt ⟨some (Sum.inl 0), D.initVar, S⟩ =
        some ⟨some (Sum.inl 1), D.initVar, Function.update S (Sum.inl 0) []⟩
      simp [MachData.combStmt, h0]
    · intro k hk0 _ _
      exact Function.update_of_ne hk0 _ _
  | cons b xs ih =>
    let S' : ∀ k : D.CombK, List (D.combΓ k) :=
      Function.update
        (Function.update
          (Function.update S (Sum.inl 0) xs)
          (Sum.inl 1) (b :: S (Sum.inl 1)))
        (Sum.inl 2) (b :: S (Sum.inl 2))
    have hstep : D.combTM.step (D.mkCfg (some (Sum.inl 0)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 0)) D.initVar S') := by
      change TM2.step D.combStmt ⟨some (Sum.inl 0), D.initVar, S⟩ =
        some ⟨some (Sum.inl 0), D.initVar, S'⟩
      simp [MachData.combStmt, h0, S']
    have hS'0 : S' (Sum.inl 0) = xs := by simp [S']
    have hS'1 : S' (Sum.inl 1) = b :: S (Sum.inl 1) := by simp [S']
    have hS'2 : S' (Sum.inl 2) = b :: S (Sum.inl 2) := by simp [S']
    obtain ⟨S₁, heval, h10, h11, h12, h1other⟩ := ih S' hS'0
    refine ⟨S₁, ?_, h10, ?_, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]
      exact heval
    · rw [h11, hS'1, List.reverse_cons, List.append_assoc, List.singleton_append]
    · rw [h12, hS'2, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hk0 hk1 hk2
      rw [h1other k hk0 hk1 hk2]
      simp [S', Function.update_of_ne hk2, Function.update_of_ne hk1, Function.update_of_ne hk0]

private lemma phase1_eval (D : MachData) (ys : List Bool)
    (S : ∀ k : D.CombK, List (D.combΓ k))
    (h1 : S (Sum.inl 1) = ys) :
    ∃ S₂ : ∀ k : D.CombK, List (D.combΓ k),
      (flip bind D.combTM.step)^[ys.length + 1] (some (D.mkCfg (some (Sum.inl 1)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inr (Sum.inl D.tmF.main))) D.initVar S₂) ∧
      S₂ (Sum.inl 1) = [] ∧
      S₂ (Sum.inr (Sum.inl D.tmF.k₀)) =
        ys.reverse.map D.inF.invFun ++ S (Sum.inr (Sum.inl D.tmF.k₀)) ∧
      ∀ k, k ≠ Sum.inl 1 → k ≠ Sum.inr (Sum.inl D.tmF.k₀) → S₂ k = S k := by
  induction ys generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 1) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.combStmt ⟨some (Sum.inl 1), D.initVar, S⟩ =
        some ⟨some (Sum.inr (Sum.inl D.tmF.main)), D.initVar, Function.update S (Sum.inl 1) []⟩
      simp [MachData.combStmt, h1]
    · intro k hk1 _
      exact Function.update_of_ne hk1 _ _
  | cons b ys ih =>
    let S' : ∀ k : D.CombK, List (D.combΓ k) := Function.update
      (Function.update S (Sum.inl 1) ys)
      (Sum.inr (Sum.inl D.tmF.k₀))
      (D.inF.invFun b :: S (Sum.inr (Sum.inl D.tmF.k₀)))
    have hstep : D.combTM.step (D.mkCfg (some (Sum.inl 1)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 1)) D.initVar S') := by
      change TM2.step D.combStmt ⟨some (Sum.inl 1), D.initVar, S⟩ =
        some ⟨some (Sum.inl 1), D.initVar, S'⟩
      simp [MachData.combStmt, h1, S']
    have hS'1 : S' (Sum.inl 1) = ys := by simp [S']
    have hS'kf : S' (Sum.inr (Sum.inl D.tmF.k₀)) =
        D.inF.invFun b :: S (Sum.inr (Sum.inl D.tmF.k₀)) := by
      simp [S']
    obtain ⟨S₂, heval, h21, h2kf, h2other⟩ := ih S' hS'1
    refine ⟨S₂, ?_, h21, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]
      exact heval
    · rw [h2kf, hS'kf, List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
        List.singleton_append]
    · intro k hk1 hkf
      rw [h2other k hk1 hkf]
      simp [S', Function.update_of_ne hkf, Function.update_of_ne hk1]

private lemma phase3_eval (D : MachData) (ws : List Bool)
    (S : ∀ k : D.CombK, List (D.combΓ k))
    (hw : S (Sum.inr (Sum.inl D.tmF.k₁)) = ws.map D.outF.invFun) :
    ∃ S₄ : ∀ k : D.CombK, List (D.combΓ k),
      (flip bind D.combTM.step)^[ws.length + 1] (some (D.mkCfg (some (Sum.inl 2)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 3)) D.initVar S₄) ∧
      S₄ (Sum.inr (Sum.inl D.tmF.k₁)) = [] ∧
      S₄ (Sum.inl 1) = ws.reverse ++ S (Sum.inl 1) ∧
      ∀ k, k ≠ Sum.inr (Sum.inl D.tmF.k₁) → k ≠ Sum.inl 1 → S₄ k = S k := by
  induction ws generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inr (Sum.inl D.tmF.k₁)) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.combStmt ⟨some (Sum.inl 2), D.initVar, S⟩ =
        some ⟨some (Sum.inl 3), D.initVar, Function.update S (Sum.inr (Sum.inl D.tmF.k₁)) []⟩
      simp [MachData.combStmt, hw]
    · intro k hkf1 _
      exact Function.update_of_ne hkf1 _ _
  | cons b ws ih =>
    let S' : ∀ k : D.CombK, List (D.combΓ k) := Function.update
      (Function.update S (Sum.inr (Sum.inl D.tmF.k₁)) (ws.map D.outF.invFun))
      (Sum.inl 1) (b :: S (Sum.inl 1))
    have hstep : D.combTM.step (D.mkCfg (some (Sum.inl 2)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 2)) D.initVar S') := by
      change TM2.step D.combStmt ⟨some (Sum.inl 2), D.initVar, S⟩ =
        some ⟨some (Sum.inl 2), D.initVar, S'⟩
      simp [MachData.combStmt, hw, S']
    have hS'kf1 : S' (Sum.inr (Sum.inl D.tmF.k₁)) = ws.map D.outF.invFun := by
      simp [S']
    have hS'1 : S' (Sum.inl 1) = b :: S (Sum.inl 1) := by
      simp [S']
    obtain ⟨S₄, heval, h4kf1, h41, h4other⟩ := ih S' hS'kf1
    refine ⟨S₄, ?_, h4kf1, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]
      exact heval
    · rw [h41, hS'1, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hkf1 hk1
      rw [h4other k hkf1 hk1]
      simp [S', Function.update_of_ne hk1, Function.update_of_ne hkf1]

private lemma phase4_eval (D : MachData) (zs : List Bool)
    (S : ∀ k : D.CombK, List (D.combΓ k))
    (hz : S (Sum.inl 1) = zs) :
    ∃ S₅ : ∀ k : D.CombK, List (D.combΓ k),
      (flip bind D.combTM.step)^[zs.length + 1] (some (D.mkCfg (some (Sum.inl 3)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 4)) D.initVar S₅) ∧
      S₅ (Sum.inl 1) = [] ∧
      S₅ (Sum.inr (Sum.inr D.tmH.k₀)) =
        D.inH.invFun false :: (zs.reverse.map D.inH.invFun ++ S (Sum.inr (Sum.inr D.tmH.k₀))) ∧
      ∀ k, k ≠ Sum.inl 1 → k ≠ Sum.inr (Sum.inr D.tmH.k₀) → S₅ k = S k := by
  induction zs generalizing S with
  | nil =>
    let S₅ : ∀ k : D.CombK, List (D.combΓ k) := Function.update
      (Function.update S (Sum.inl 1) [])
      (Sum.inr (Sum.inr D.tmH.k₀))
      (D.inH.invFun false :: S (Sum.inr (Sum.inr D.tmH.k₀)))
    refine ⟨S₅, ?_, by simp [S₅], by simp [S₅], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.combStmt ⟨some (Sum.inl 3), D.initVar, S⟩ =
        some ⟨some (Sum.inl 4), D.initVar, S₅⟩
      simp [MachData.combStmt, hz, S₅]
    · intro k hk1 hkh0
      simp [S₅, Function.update_of_ne hkh0, Function.update_of_ne hk1]
  | cons b zs ih =>
    let S' : ∀ k : D.CombK, List (D.combΓ k) := Function.update
      (Function.update S (Sum.inl 1) zs)
      (Sum.inr (Sum.inr D.tmH.k₀))
      (D.inH.invFun b :: S (Sum.inr (Sum.inr D.tmH.k₀)))
    have hstep : D.combTM.step (D.mkCfg (some (Sum.inl 3)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 3)) D.initVar S') := by
      change TM2.step D.combStmt ⟨some (Sum.inl 3), D.initVar, S⟩ =
        some ⟨some (Sum.inl 3), D.initVar, S'⟩
      simp [MachData.combStmt, hz, S']
    have hS'1 : S' (Sum.inl 1) = zs := by simp [S']
    have hS'kh0 : S' (Sum.inr (Sum.inr D.tmH.k₀)) =
        D.inH.invFun b :: S (Sum.inr (Sum.inr D.tmH.k₀)) := by
      simp [S']
    obtain ⟨S₅, heval, h51, h5kh0, h5other⟩ := ih S' hS'1
    refine ⟨S₅, ?_, h51, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]
      exact heval
    · rw [h5kh0, hS'kh0, List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
        List.singleton_append]
    · intro k hk1 hkh0
      rw [h5other k hk1 hkh0]
      simp [S', Function.update_of_ne hkh0, Function.update_of_ne hk1]

private lemma phase5_eval (D : MachData) (rs acc : List Bool)
    (S : ∀ k : D.CombK, List (D.combΓ k))
    (hr : S (Sum.inl 2) = rs)
    (hacc : S (Sum.inr (Sum.inr D.tmH.k₀)) = acc.map D.inH.invFun) :
    ∃ S₆ : ∀ k : D.CombK, List (D.combΓ k),
      (flip bind D.combTM.step)^[rs.length + 1] (some (D.mkCfg (some (Sum.inl 4)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inr (Sum.inr D.tmH.main))) D.initVar S₆) ∧
      S₆ (Sum.inl 2) = [] ∧
      S₆ (Sum.inr (Sum.inr D.tmH.k₀)) = (delimitRevAux rs acc).map D.inH.invFun ∧
      ∀ k, k ≠ Sum.inl 2 → k ≠ Sum.inr (Sum.inr D.tmH.k₀) → S₆ k = S k := by
  induction rs generalizing acc S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 2) [], ?_, by simp, by simp [delimitRevAux, hacc], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.combStmt ⟨some (Sum.inl 4), D.initVar, S⟩ =
        some ⟨some (Sum.inr (Sum.inr D.tmH.main)), D.initVar, Function.update S (Sum.inl 2) []⟩
      simp [MachData.combStmt, hr]
    · intro k hk2 _
      exact Function.update_of_ne hk2 _ _
  | cons b rs ih =>
    let S' : ∀ k : D.CombK, List (D.combΓ k) := Function.update
      (Function.update S (Sum.inl 2) rs)
      (Sum.inr (Sum.inr D.tmH.k₀))
      (D.inH.invFun true :: D.inH.invFun b :: S (Sum.inr (Sum.inr D.tmH.k₀)))
    have hstep : D.combTM.step (D.mkCfg (some (Sum.inl 4)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 4)) D.initVar S') := by
      change TM2.step D.combStmt ⟨some (Sum.inl 4), D.initVar, S⟩ =
        some ⟨some (Sum.inl 4), D.initVar, S'⟩
      simp [MachData.combStmt, hr, S']
    have hS'2 : S' (Sum.inl 2) = rs := by
      simp [S']
    have hS'kh0 : S' (Sum.inr (Sum.inr D.tmH.k₀)) =
        (true :: b :: acc).map D.inH.invFun := by
      simp [S', hacc]
    obtain ⟨S₆, heval, h62, h6kh0, h6other⟩ := ih (true :: b :: acc) S' hS'2 hS'kh0
    refine ⟨S₆, ?_, h62, h6kh0, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]
      exact heval
    · intro k hk2 hkh0
      rw [h6other k hk2 hkh0]
      simp [S', Function.update_of_ne hkh0, Function.update_of_ne hk2]

noncomputable def buildPolyTime {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    (f : α → β) (h : α × β → γ)
    (Mf : TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := α)).encode
      (BitstringEncoding.toEncoding (α := β)).encode f)
    (Mh : TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := α × β)).encode
      (BitstringEncoding.toEncoding (α := γ)).encode h) :
    TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := α)).encode
      (BitstringEncoding.toEncoding (α := γ)).encode (fun x => h (x, f x)) :=
  let D : MachData := {
    tmF := Mf.tm
    tmH := Mh.tm
    inF := Mf.inputAlphabet
    outF := Mf.outputAlphabet
    inH := Mh.inputAlphabet
  }
  let Bf : ℕ := maxPushes D.tmF
  let polyY : Polynomial ℕ := Polynomial.X + Mf.time * Polynomial.C Bf
  let polyPair : Polynomial ℕ := Polynomial.C 2 * Polynomial.X + Polynomial.C 1 + polyY
  let totalTime : Polynomial ℕ :=
    Polynomial.C 3 * Polynomial.X + Polynomial.C 5 + Mf.time +
      Polynomial.C 2 * polyY + Mh.time.comp polyPair
  have hout : ∀ x : α, Nonempty (TM2OutputsInTime D.combTM
      (List.map (Equiv.refl Bool).invFun ((BitstringEncoding.toEncoding (α := α)).encode x))
      (some (List.map Mh.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := γ)).encode (h (x, f x)))))
      (totalTime.eval ((BitstringEncoding.toEncoding (α := α)).encode x).length)) := fun x => by
    let L : List Bool := bitEncode x
    let Y : List Bool := bitEncode (f x)
    let Z : List Bool := bitEncode (h (x, f x))
    change Nonempty (TM2OutputsInTime D.combTM (List.map (Equiv.refl Bool).invFun L)
      (some (List.map Mh.outputAlphabet.invFun Z)) (totalTime.eval L.length))
    have hmap_id : List.map (Equiv.refl Bool).invFun L = L := by simp [Equiv.refl]
    rw [hmap_id]
    have hMf_out : TM2OutputsInTime D.tmF (L.map D.inF.invFun)
        (some (Y.map D.outF.invFun)) (Mf.time.eval L.length) := by
      simpa only [D, L, Y, bitEncode, List.length_map] using Mf.outputsFun x
    have hpair_enc : (BitstringEncoding.toEncoding (α := α × β)).encode (x, f x) =
        delimit L ++ Y := rfl
    have hMh_out : TM2OutputsInTime D.tmH ((delimit L ++ Y).map D.inH.invFun)
        (some (Z.map Mh.outputAlphabet.invFun)) (Mh.time.eval (delimit L ++ Y).length) := by
      have h0 := Mh.outputsFun (x, f x)
      rw [hpair_enc] at h0
      exact h0
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
    have hPair_poly : (delimit L ++ Y).length ≤ polyPair.eval L.length := by
      rw [List.length_append, length_delimit]
      simp only [polyPair, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
    have hMh_steps_le : hMh_out.steps ≤ (Mh.time.comp polyPair).eval L.length := by
      rw [Polynomial.eval_comp]
      exact le_trans hMh_out.steps_le_m (poly_eval_mono Mh.time hPair_poly)
    let c0 := initList D.combTM L
    have hc0_eq : c0 = D.mkCfg (some (Sum.inl 0)) D.initVar c0.stk := rfl
    have hc0_in : c0.stk (Sum.inl 0) = L := by
      simp [c0, MachData.combTM, initList]
    have hc0_other : ∀ k : D.CombK, k ≠ Sum.inl 0 → c0.stk k = [] := by
      intro k hk
      simp [c0, MachData.combTM, initList, hk]
    obtain ⟨S₁, hp0, hS1_0, hS1_1, hS1_2, hS1_other⟩ := phase0_eval D L c0.stk hc0_in
    rw [hc0_other (Sum.inl 1) (by simp), List.append_nil] at hS1_1
    rw [hc0_other (Sum.inl 2) (by simp), List.append_nil] at hS1_2
    obtain ⟨S₂, hp1, hS2_1, hS2_kf0, hS2_other⟩ := phase1_eval D L.reverse S₁ hS1_1
    have hS1_kf0 : S₁ (Sum.inr (Sum.inl D.tmF.k₀)) = [] := by
      rw [hS1_other _ (by simp) (by simp) (by simp)]
      exact hc0_other _ (by simp)
    rw [List.reverse_reverse, hS1_kf0, List.append_nil] at hS2_kf0
    have hcfg2_eq : D.mkCfg (some (Sum.inr (Sum.inl D.tmF.main))) D.initVar S₂ =
        D.embedCfgF (Sum.inl 2) none D.tmH.initialState S₂
          (initList D.tmF (L.map D.inF.invFun)) := by
      dsimp [MachData.embedCfgF, MachData.mkCfg, MachData.initVar, initList]
      congr 1
      funext k
      rcases k with (i | kf | kh)
      · rfl
      · by_cases hkf : kf = D.tmF.k₀
        · subst hkf
          simp [hS2_kf0]
        · simp only [MachData.mergeStkF, hkf, ↓reduceDIte]
          rw [hS2_other _ (by simp) (by simp [hkf]),
            hS1_other _ (by simp) (by simp) (by simp),
            hc0_other _ (by simp)]
      · rfl
    have hp2 := sim_tmF D none D.tmH.initialState S₂ hMf_out.steps _ _ hMf_out.evals_in_steps
    let c3 := D.embedCfgF (Sum.inl 2) none D.tmH.initialState S₂
      (haltList D.tmF (Y.map D.outF.invFun))
    have hc3_eq : c3 = D.mkCfg (some (Sum.inl 2)) D.initVar c3.stk := rfl
    have hc3_kf1 : c3.stk (Sum.inr (Sum.inl D.tmF.k₁)) = Y.map D.outF.invFun := by
      dsimp [c3, MachData.embedCfgF, MachData.mergeStkF]
      exact haltList_stk_k1 D.tmF _
    obtain ⟨S₄, hp3, hS4_kf1, hS4_1, hS4_other⟩ := phase3_eval D Y c3.stk hc3_kf1
    have hc3_1 : c3.stk (Sum.inl 1) = [] := by
      dsimp [c3, MachData.embedCfgF, MachData.mergeStkF]
      exact hS2_1
    rw [hc3_1, List.append_nil] at hS4_1
    obtain ⟨S₅, hp4, hS5_1, hS5_kh0, hS5_other⟩ := phase4_eval D Y.reverse S₄ hS4_1
    have hS4_kh0 : S₄ (Sum.inr (Sum.inr D.tmH.k₀)) = [] := by
      rw [hS4_other _ (by simp) (by simp)]
      dsimp [c3, MachData.embedCfgF, MachData.mergeStkF]
      rw [hS2_other _ (by simp) (by simp),
        hS1_other _ (by simp) (by simp) (by simp),
        hc0_other _ (by simp)]
    rw [List.reverse_reverse, hS4_kh0, List.append_nil] at hS5_kh0
    have hS5_kh0' : S₅ (Sum.inr (Sum.inr D.tmH.k₀)) = (false :: Y).map D.inH.invFun := by
      simpa only [List.map_cons] using hS5_kh0
    have hS5_2 : S₅ (Sum.inl 2) = L.reverse := by
      rw [hS5_other _ (by simp) (by simp), hS4_other _ (by simp) (by simp)]
      dsimp [c3, MachData.embedCfgF, MachData.mergeStkF]
      rw [hS2_other _ (by simp) (by simp)]
      exact hS1_2
    obtain ⟨S₆, hp5, hS6_2, hS6_kh0, hS6_other⟩ :=
      phase5_eval D L.reverse (false :: Y) S₅ hS5_2 hS5_kh0'
    rw [delimitRevAux_reverse] at hS6_kh0
    have hcfg6_eq : D.mkCfg (some (Sum.inr (Sum.inr D.tmH.main))) D.initVar S₆ =
        D.embedCfgH none D.tmF.initialState
          (initList D.tmH ((delimit L ++ Y).map D.inH.invFun)) := by
      dsimp [MachData.embedCfgH, MachData.mkCfg, MachData.initVar, initList]
      congr 1
      funext k
      rcases k with (i | kf | kh)
      · simp only [MachData.mergeStkH]
        fin_cases i
        · rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp),
            hS4_other _ (by simp) (by simp)]
          dsimp [c3, MachData.embedCfgF, MachData.mergeStkF]
          rw [hS2_other _ (by simp) (by simp)]
          exact hS1_0
        · rw [hS6_other _ (by simp) (by simp)]
          exact hS5_1
        · exact hS6_2
      · simp only [MachData.mergeStkH]
        rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp)]
        by_cases hkf1 : kf = D.tmF.k₁
        · subst hkf1; exact hS4_kf1
        · rw [hS4_other _ (by simp [hkf1]) (by simp)]
          dsimp [c3, MachData.embedCfgF, MachData.mergeStkF, haltList]
          simp [hkf1]
      · by_cases hkh0 : kh = D.tmH.k₀
        · subst hkh0; simp [hS6_kh0]
        · simp only [MachData.mergeStkH, hkh0, ↓reduceDIte]
          rw [hS6_other _ (by simp) (by simp [hkh0]),
            hS5_other _ (by simp) (by simp [hkh0]),
            hS4_other _ (by simp) (by simp)]
          dsimp [c3, MachData.embedCfgF, MachData.mergeStkF]
          rw [hS2_other _ (by simp) (by simp),
            hS1_other _ (by simp) (by simp) (by simp),
            hc0_other _ (by simp)]
    have hp6 := sim_tmH D none D.tmF.initialState hMh_out.steps _ _ hMh_out.evals_in_steps
    have hhalt_eq : D.embedCfgH none D.tmF.initialState
        (haltList D.tmH (Z.map Mh.outputAlphabet.invFun)) =
        haltList D.combTM (Z.map Mh.outputAlphabet.invFun) := by
      dsimp [MachData.embedCfgH, MachData.mkCfg, haltList, MachData.combTM]
      congr 1
      funext k
      rcases k with (i | kf | kh)
      · simp
      · simp
      · by_cases hkh1 : kh = D.tmH.k₁
        · subst hkh1; simp
        · simp [hkh1]
    let e0 : EvalsTo D.combTM.step c0 (some (D.mkCfg (some (Sum.inl 1)) D.initVar S₁)) :=
      ⟨L.length + 1, by rw [hc0_eq]; exact hp0⟩
    let e1 : EvalsTo D.combTM.step (D.mkCfg (some (Sum.inl 1)) D.initVar S₁) (some c3) :=
      EvalsTo.trans D.combTM.step _ _ _
        ⟨L.reverse.length + 1, hp1⟩
        ⟨hMf_out.steps, by rw [hcfg2_eq]; exact hp2⟩
    let e2 : EvalsTo D.combTM.step c3 (some (D.mkCfg (some (Sum.inl 4)) D.initVar S₅)) :=
      EvalsTo.trans D.combTM.step _ _ _
        ⟨Y.length + 1, by rw [hc3_eq]; exact hp3⟩
        ⟨Y.reverse.length + 1, hp4⟩
    let e3 : EvalsTo D.combTM.step (D.mkCfg (some (Sum.inl 4)) D.initVar S₅)
        (some (haltList D.combTM (Z.map Mh.outputAlphabet.invFun))) :=
      EvalsTo.trans D.combTM.step _ _ _
        ⟨L.reverse.length + 1, hp5⟩
        ⟨hMh_out.steps, by rw [hcfg6_eq, ← hhalt_eq]; exact hp6⟩
    let eAll := EvalsTo.trans D.combTM.step _ _ _ e0
      (EvalsTo.trans D.combTM.step _ _ _ e1 (EvalsTo.trans D.combTM.step _ _ _ e2 e3))
    refine ⟨⟨eAll, ?_⟩⟩
    dsimp only [eAll, e0, e1, e2, e3, EvalsTo.trans]
    have hMf_le := hMf_out.steps_le_m
    simp only [List.length_reverse, totalTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    omega
  { tm := D.combTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Mh.outputAlphabet
    time := totalTime
    outputsFun := fun x => Classical.choice (hout x) }

end Arxiv2610R2H1Proof

theorem prove_arxiv_2610_R2_H1 : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2.H1 := by
  intro Λ F ⟨Mf⟩ ⟨Mh⟩
  exact ⟨Arxiv2610R2H1Proof.buildPolyTime Λ F Mf Mh⟩

theorem OMA.solution : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2.H1 :=
  prove_arxiv_2610_R2_H1
