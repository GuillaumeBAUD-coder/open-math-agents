import OMAReductions.R_Constant14_c14_ge_5_R1
import Mathlib.Tactic

-- Step Constant14.c14_ge_5.R1.H2: hypothesis H2 of reduction Constant14.c14_ge_5.R1
-- Credit: @yhay81

/-!
# Proof of `Constant14.c14_ge_5.R1.H2`

We prove $\Sigma_1$-completeness of `𝗭𝗙𝗖` for halting Turing machines (specialized to 4 states
halting within 108 steps) via Gödel's completeness theorem for `FFL.FirstOrder.Derivation` over
`ℒₛₑₜ` combined with semantic simulation in an arbitrary model of `𝗭𝗙𝗖`.
-/

namespace C14H2Proof

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open scoped Classical

/- ## Section 1: Semantics for `ℒₛₑₜ` and Rewriting Lemmas -/

private def semTv (V : Type) {ξ : Type*} {m : ℕ} (e : Fin m → V) (ε : ξ → V) :
    Semiterm ℒₛₑₜ ξ m → V
  | .bvar i => e i
  | .fvar x => ε x
  | .func f _ => (f : Empty).elim

private def semEv (V : Type) (memV : V → V → Prop) {ξ : Type*} :
    ∀ {m : ℕ}, (Fin m → V) → (ξ → V) → Semiformula ℒₛₑₜ ξ m → Prop
  | _, _, _, .verum => True
  | _, _, _, .falsum => False
  | _, e, ε, .rel Language.Set.Rel.eq v => semTv V e ε (v 0) = semTv V e ε (v 1)
  | _, e, ε, .rel Language.Set.Rel.mem v => memV (semTv V e ε (v 0)) (semTv V e ε (v 1))
  | _, e, ε, .nrel Language.Set.Rel.eq v => semTv V e ε (v 0) ≠ semTv V e ε (v 1)
  | _, e, ε, .nrel Language.Set.Rel.mem v => ¬ memV (semTv V e ε (v 0)) (semTv V e ε (v 1))
  | _, e, ε, .and φ ψ => semEv V memV e ε φ ∧ semEv V memV e ε ψ
  | _, e, ε, .or φ ψ => semEv V memV e ε φ ∨ semEv V memV e ε ψ
  | _, e, ε, .all φ => ∀ d : V, semEv V memV (d :> e) ε φ
  | _, e, ε, .exs φ => ∃ d : V, semEv V memV (d :> e) ε φ

@[simp] private lemma semTv_bvar {V : Type} {ξ : Type*} {m : ℕ} (e : Fin m → V) (ε : ξ → V)
    (i : Fin m) : semTv V e ε (#i) = e i := rfl

@[simp] private lemma semTv_fvar {V : Type} {ξ : Type*} {m : ℕ} (e : Fin m → V) (ε : ξ → V)
    (x : ξ) : semTv V e ε (&x) = ε x := rfl

@[simp] private lemma rew_verum {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) :
    ω ▹ (Semiformula.verum : Semiformula ℒₛₑₜ ξ₁ n₁) = ⊤ := rfl

@[simp] private lemma rew_falsum {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) :
    ω ▹ (Semiformula.falsum : Semiformula ℒₛₑₜ ξ₁ n₁) = ⊥ := rfl

@[simp] private lemma rew_rel {ξ₁ ξ₂ : Type*} {n₁ n₂ k : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ₁ n₁) :
    ω ▹ (Semiformula.rel r v) = Semiformula.rel r (ω ∘ v) := rfl

@[simp] private lemma rew_nrel {ξ₁ ξ₂ : Type*} {n₁ n₂ k : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ₁ n₁) :
    ω ▹ (Semiformula.nrel r v) = Semiformula.nrel r (ω ∘ v) := rfl

@[simp] private lemma rew_and {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (φ ψ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    ω ▹ (Semiformula.and φ ψ) = (ω ▹ φ) ⋏ (ω ▹ ψ) := rfl

@[simp] private lemma rew_or {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (φ ψ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    ω ▹ (Semiformula.or φ ψ) = (ω ▹ φ) ⋎ (ω ▹ ψ) := rfl

@[simp] private lemma rew_all {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula ℒₛₑₜ ξ₁ (n₁ + 1)) :
    ω ▹ (Semiformula.all φ) = ∀¹ (ω.q ▹ φ) := rfl

@[simp] private lemma rew_exs {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula ℒₛₑₜ ξ₁ (n₁ + 1)) :
    ω ▹ (Semiformula.exs φ) = ∃¹ (ω.q ▹ φ) := rfl

private lemma rew_neg {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    ω ▹ (∼φ) = ∼(ω ▹ φ) := (Rewriting.app ω).map_neg' φ

private lemma semEv_neg {V : Type} {memV : V → V → Prop} {ξ : Type*} {m : ℕ}
    (e : Fin m → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ m) :
    semEv V memV e ε (∼φ) ↔ ¬ semEv V memV e ε φ := by
  induction φ with
  | verum => simp [semEv, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | falsum => simp [semEv, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | rel r v => cases r <;> simp [semEv, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | nrel r v => cases r <;> simp [semEv, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | and φ ψ ih1 ih2 =>
    change (semEv V memV e ε (∼φ) ∨ semEv V memV e ε (∼ψ)) ↔
      ¬ (semEv V memV e ε φ ∧ semEv V memV e ε ψ)
    rw [ih1 e, ih2 e, not_and_or]
  | or φ ψ ih1 ih2 =>
    change (semEv V memV e ε (∼φ) ∧ semEv V memV e ε (∼ψ)) ↔
      ¬ (semEv V memV e ε φ ∨ semEv V memV e ε ψ)
    rw [ih1 e, ih2 e, not_or]
  | all φ ih =>
    change (∃ d, semEv V memV (d :> e) ε (∼φ)) ↔ ¬ ∀ d, semEv V memV (d :> e) ε φ
    simp only [ih, not_forall]
  | exs φ ih =>
    change (∀ d, semEv V memV (d :> e) ε (∼φ)) ↔ ¬ ∃ d, semEv V memV (d :> e) ε φ
    simp only [ih, not_exists]

private lemma semEv_imp {V : Type} {memV : V → V → Prop} {ξ : Type*} {m : ℕ}
    (e : Fin m → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ m) :
    semEv V memV e ε (φ 🡒 ψ) ↔ (semEv V memV e ε φ → semEv V memV e ε ψ) := by
  change (semEv V memV e ε (∼φ) ∨ semEv V memV e ε ψ) ↔ _
  rw [semEv_neg, imp_iff_not_or]

private lemma semEv_iff {V : Type} {memV : V → V → Prop} {ξ : Type*} {m : ℕ}
    (e : Fin m → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ m) :
    semEv V memV e ε (φ 🡘 ψ) ↔ (semEv V memV e ε φ ↔ semEv V memV e ε ψ) := by
  change (semEv V memV e ε (φ 🡒 ψ) ∧ semEv V memV e ε (ψ 🡒 φ)) ↔ _
  rw [semEv_imp, semEv_imp]
  exact iff_iff_implies_and_implies.symm

private lemma semTv_rew {V : Type} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (e : Fin n₂ → V) (ε : ξ₂ → V) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    semTv V e ε (ω t) =
      semTv V (fun i => semTv V e ε (ω #i)) (fun x => semTv V e ε (ω &x)) t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

private lemma semTv_bShift {V : Type} {ξ : Type*} {n : ℕ}
    (d : V) (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) :
    semTv V (d :> e) ε (Rew.bShift t) = semTv V e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

private lemma semEv_rew {V : Type} {memV : V → V → Prop} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (e : Fin n₂ → V) (ε : ξ₂ → V) (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    semEv V memV e ε (ω ▹ φ) ↔
      semEv V memV (fun i => semTv V e ε (ω #i)) (fun x => semTv V e ε (ω &x)) φ := by
  induction φ generalizing n₂ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    cases r with
    | eq =>
      change semTv V e ε (ω (v 0)) = semTv V e ε (ω (v 1)) ↔ _
      rw [semTv_rew, semTv_rew]; rfl
    | mem =>
      change memV (semTv V e ε (ω (v 0))) (semTv V e ε (ω (v 1))) ↔ _
      rw [semTv_rew, semTv_rew]; rfl
  | nrel r v =>
    cases r with
    | eq =>
      change semTv V e ε (ω (v 0)) ≠ semTv V e ε (ω (v 1)) ↔ _
      rw [semTv_rew, semTv_rew]; rfl
    | mem =>
      change ¬ memV (semTv V e ε (ω (v 0))) (semTv V e ε (ω (v 1))) ↔ _
      rw [semTv_rew, semTv_rew]; rfl
  | and φ ψ ih1 ih2 => exact and_congr (ih1 ω e) (ih2 ω e)
  | or φ ψ ih1 ih2 => exact or_congr (ih1 ω e) (ih2 ω e)
  | all φ ih =>
    rw [rew_all]
    change (∀ d, semEv V memV (d :> e) ε (ω.q ▹ φ)) ↔ _
    refine forall_congr' fun d => ?_
    rw [ih ω.q (d :> e)]
    have hb : (fun i => semTv V (d :> e) ε (ω.q #i)) = (d :> fun i => semTv V e ε (ω #i)) := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => exact semTv_bShift d e ε (ω #j)
    have hf : (fun x => semTv V (d :> e) ε (ω.q &x)) = (fun x => semTv V e ε (ω &x)) := by
      funext x
      exact semTv_bShift d e ε (ω &x)
    rw [hb, hf]
  | exs φ ih =>
    rw [rew_exs]
    change (∃ d, semEv V memV (d :> e) ε (ω.q ▹ φ)) ↔ _
    refine exists_congr fun d => ?_
    rw [ih ω.q (d :> e)]
    have hb : (fun i => semTv V (d :> e) ε (ω.q #i)) = (d :> fun i => semTv V e ε (ω #i)) := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => exact semTv_bShift d e ε (ω #j)
    have hf : (fun x => semTv V (d :> e) ε (ω.q &x)) = (fun x => semTv V e ε (ω &x)) := by
      funext x
      exact semTv_bShift d e ε (ω &x)
    rw [hb, hf]

private lemma semEv_congr {V : Type} {memV : V → V → Prop} {ξ : Type*} [DecidableEq ξ] {m : ℕ}
    {e₁ e₂ : Fin m → V} {ε₁ ε₂ : ξ → V} (φ : Semiformula ℒₛₑₜ ξ m)
    (he : e₁ = e₂) (hε : ∀ x ∈ φ.freeVariables, ε₁ x = ε₂ x) :
    semEv V memV e₁ ε₁ φ ↔ semEv V memV e₂ ε₂ φ := by
  subst he
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    have ht : ∀ i, semTv V e₁ ε₁ (v i) = semTv V e₁ ε₂ (v i) := fun i => by
      cases hvi : v i with
      | bvar j => rfl
      | fvar x =>
        apply hε x
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hvi, Semiterm.freeVariables]⟩
      | func f _ => exact (f : Empty).elim
    cases r <;> simp only [semEv, ht]
  | nrel r v =>
    have ht : ∀ i, semTv V e₁ ε₁ (v i) = semTv V e₁ ε₂ (v i) := fun i => by
      cases hvi : v i with
      | bvar j => rfl
      | fvar x =>
        apply hε x
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hvi, Semiterm.freeVariables]⟩
      | func f _ => exact (f : Empty).elim
    cases r <;> simp only [semEv, ht]
  | and φ ψ ih1 ih2 =>
    exact and_congr
      (ih1 (fun x hx => hε x (Finset.mem_union_left _ hx)))
      (ih2 (fun x hx => hε x (Finset.mem_union_right _ hx)))
  | or φ ψ ih1 ih2 =>
    exact or_congr
      (ih1 (fun x hx => hε x (Finset.mem_union_left _ hx)))
      (ih2 (fun x hx => hε x (Finset.mem_union_right _ hx)))
  | all φ ih => exact forall_congr' fun d => ih hε
  | exs φ ih => exact exists_congr fun d => ih hε

private lemma semEv_subst {V : Type} {memV : V → V → Prop} {ξ : Type*} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n₁) (w : Fin n₁ → Semiterm ℒₛₑₜ ξ n₂) :
    semEv V memV e ε (φ ⇜ w) ↔ semEv V memV (fun i => semTv V e ε (w i)) ε φ :=
  semEv_rew (Rew.subst w) e ε φ

private lemma semEv_emb {V : Type} {memV : V → V → Prop} {ξ : Type*} {m : ℕ}
    (e : Fin m → V) (ε : ξ → V) (φ : Semisentence ℒₛₑₜ m) :
    semEv V memV e ε (Rewriting.emb φ) ↔ semEv V memV e Empty.elim φ := by
  rw [semEv_rew]
  have h1 : (fun i : Fin m => semTv V e ε (Rew.emb (o := Empty) (ξ := ξ) #i)) = e := rfl
  have h2 : (fun x : Empty => semTv V e ε (Rew.emb (o := Empty) (ξ := ξ) &x)) = Empty.elim := by
    funext x; exact x.elim
  rw [h1, h2]

private lemma semTv_toEmpty {V : Type} {m : ℕ} (e : Fin m → V) (ε : ℕ → V)
    (t : Semiterm ℒₛₑₜ ℕ m) (hi : t.freeVariables = ∅) :
    semTv V e Empty.elim (t.toEmpty hi) = semTv V e ε t := by
  cases t with
  | bvar j => rfl
  | fvar x => simp [Semiterm.freeVariables] at hi
  | func f _ => exact (f : Empty).elim

private lemma semEv_toEmpty {V : Type} {memV : V → V → Prop} {m : ℕ}
    (e : Fin m → V) (ε : ℕ → V) (φ : Semiproposition ℒₛₑₜ m) (h : φ.freeVariables = ∅) :
    semEv V memV e Empty.elim (φ.toEmpty h) ↔ semEv V memV e ε φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    cases r with
    | eq =>
      change semTv V e Empty.elim ((v 0).toEmpty _) = semTv V e Empty.elim ((v 1).toEmpty _) ↔
        semTv V e ε (v 0) = semTv V e ε (v 1)
      rw [semTv_toEmpty, semTv_toEmpty]
    | mem =>
      change memV (semTv V e Empty.elim ((v 0).toEmpty _)) (semTv V e Empty.elim ((v 1).toEmpty _)) ↔
        memV (semTv V e ε (v 0)) (semTv V e ε (v 1))
      rw [semTv_toEmpty, semTv_toEmpty]
  | nrel r v =>
    cases r with
    | eq =>
      change semTv V e Empty.elim ((v 0).toEmpty _) ≠ semTv V e Empty.elim ((v 1).toEmpty _) ↔
        semTv V e ε (v 0) ≠ semTv V e ε (v 1)
      rw [semTv_toEmpty, semTv_toEmpty]
    | mem =>
      change ¬ memV (semTv V e Empty.elim ((v 0).toEmpty _)) (semTv V e Empty.elim ((v 1).toEmpty _)) ↔
        ¬ memV (semTv V e ε (v 0)) (semTv V e ε (v 1))
      rw [semTv_toEmpty, semTv_toEmpty]
  | and φ ψ ih1 ih2 => exact and_congr (ih1 e _) (ih2 e _)
  | or φ ψ ih1 ih2 => exact or_congr (ih1 e _) (ih2 e _)
  | all φ ih => exact forall_congr' fun d => ih (d :> e) h
  | exs φ ih => exact exists_congr fun d => ih (d :> e) h

private lemma semEv_allClosure {V : Type} {memV : V → V → Prop} {ξ : Type*}
    {k : ℕ} (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ k)
    (h : semEv V memV Fin.elim0 ε (∀¹* φ)) (v : Fin k → V) :
    semEv V memV v ε φ := by
  induction k with
  | zero => rwa [Subsingleton.elim v Fin.elim0]
  | succ k ih =>
    have h' := ih (∀¹ φ) h (Matrix.vecTail v)
    have h0 := h' (v 0)
    have hv : (v 0 :> Matrix.vecTail v) = v := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    rwa [hv] at h0

private lemma fixitr_fvar_eq (n m x : ℕ) :
    (Rew.fixitr n m (&x : Semiterm ℒₛₑₜ ℕ n)) =
      if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Rew.fix (Rew.fixitr n m &x) = _
    rw [ih]
    by_cases hx : x < m
    · have hx' : x < m + 1 := by omega
      simp only [dif_pos hx, dif_pos hx']
      rfl
    · by_cases hx' : x < m + 1
      · have he : x = m := by omega
        subst x
        simp only [dif_neg (Nat.lt_irrefl m), dif_pos (Nat.lt_succ_self m), Nat.sub_self]
        rfl
      · have he : x - m = x - (m + 1) + 1 := by omega
        simp only [dif_neg hx, dif_neg hx', he]
        rfl

private lemma semEv_univCl_mp {V : Type} {memV : V → V → Prop} (φ : Proposition ℒₛₑₜ)
    (h : semEv V memV Fin.elim0 Empty.elim φ.univCl) (ε : ℕ → V) :
    semEv V memV Fin.elim0 ε φ := by
  unfold Semiformula.univCl at h
  rw [semEv_toEmpty Fin.elim0 ε] at h
  have hinst := semEv_allClosure ε (Rew.fixitr 0 φ.fvSup ▹ φ) h (fun i => ε i.val)
  rw [semEv_rew] at hinst
  refine (semEv_congr φ (Subsingleton.elim _ _) ?_).mp hinst
  intro x hx
  have hlt : x < φ.fvSup := by
    obtain ⟨m, hm⟩ := Finset.max_of_mem hx
    simpa only [Semiformula.fvSup, hm, WithBot.recBotCoe_coe] using
      Nat.lt_succ_of_le (Finset.le_max_of_eq hx hm)
  rw [fixitr_fvar_eq, dif_pos hlt]
  simp [Fin.natAdd]

/- ## Section 2: Gödel Completeness for `FFL.FirstOrder.Derivation` over `ℒₛₑₜ` -/

private lemma semiformula_neg_neg {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    ∼(∼φ) = φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and φ ψ ih1 ih2 => change (∼(∼φ)) ⋏ (∼(∼ψ)) = φ ⋏ ψ; rw [ih1, ih2]
  | or φ ψ ih1 ih2 => change (∼(∼φ)) ⋎ (∼(∼ψ)) = φ ⋎ ψ; rw [ih1, ih2]
  | all φ ih => change ∀¹ (∼(∼φ)) = ∀¹ φ; rw [ih]
  | exs φ ih => change ∃¹ (∼(∼φ)) = ∃¹ φ; rw [ih]

private lemma rew_ext {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} {ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂}
    (h : ∀ t, ω₁ t = ω₂ t) : ω₁ = ω₂ := by
  rcases ω₁; rcases ω₂; congr 1; exact funext h

private lemma rew_comp_eq {ξ₁ ξ₂ ξ₃ : Type*} {n₁ n₂ n₃ : ℕ}
    (ω₂ : Rew ℒₛₑₜ ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    ω₂ ▹ (ω₁ ▹ φ) = (ω₂.comp ω₁) ▹ φ := by
  induction φ generalizing n₂ n₃ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and φ ψ ih1 ih2 => change (ω₂ ▹ (ω₁ ▹ φ)) ⋏ (ω₂ ▹ (ω₁ ▹ ψ)) = _; rw [ih1, ih2]; rfl
  | or φ ψ ih1 ih2 => change (ω₂ ▹ (ω₁ ▹ φ)) ⋎ (ω₂ ▹ (ω₁ ▹ ψ)) = _; rw [ih1, ih2]; rfl
  | all φ ih =>
    rw [rew_all, Rewriting.app_all, rew_all, ih]
    congr 1
    have hq : ω₂.q.comp ω₁.q = (ω₂.comp ω₁).q := by
      apply rew_ext; intro t
      cases t with
      | bvar i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          change ω₂.q (Rew.bShift (ω₁ #j)) = Rew.bShift (ω₂ (ω₁ #j))
          cases ω₁ #j with
          | bvar _ => rfl
          | fvar _ => rfl
          | func f _ => exact (f : Empty).elim
      | fvar x =>
        change ω₂.q (Rew.bShift (ω₁ &x)) = Rew.bShift (ω₂ (ω₁ &x))
        cases ω₁ &x with
        | bvar _ => rfl
        | fvar _ => rfl
        | func f _ => exact (f : Empty).elim
      | func f _ => exact (f : Empty).elim
    rw [hq]
  | exs φ ih =>
    rw [rew_exs, Rewriting.app_exs, rew_exs, ih]
    congr 1
    have hq : ω₂.q.comp ω₁.q = (ω₂.comp ω₁).q := by
      apply rew_ext; intro t
      cases t with
      | bvar i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          change ω₂.q (Rew.bShift (ω₁ #j)) = Rew.bShift (ω₂ (ω₁ #j))
          cases ω₁ #j with
          | bvar _ => rfl
          | fvar _ => rfl
          | func f _ => exact (f : Empty).elim
      | fvar x =>
        change ω₂.q (Rew.bShift (ω₁ &x)) = Rew.bShift (ω₂ (ω₁ &x))
        cases ω₁ &x with
        | bvar _ => rfl
        | fvar _ => rfl
        | func f _ => exact (f : Empty).elim
      | func f _ => exact (f : Empty).elim
    rw [hq]

private lemma rew_congr_fv {ξ₁ ξ₂ : Type*} [DecidableEq ξ₁] {n₁ n₂ : ℕ}
    (ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (φ : Semiformula ℒₛₑₜ ξ₁ n₁)
    (hb : ∀ i : Fin n₁, ω₁ #i = ω₂ #i)
    (hf : ∀ x ∈ φ.freeVariables, ω₁ &x = ω₂ &x) :
    ω₁ ▹ φ = ω₂ ▹ φ := by
  induction φ generalizing n₂ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    change Semiformula.rel r (ω₁ ∘ v) = Semiformula.rel r (ω₂ ∘ v)
    congr 1; funext i
    dsimp only [Function.comp_apply]
    cases hvi : v i with
    | bvar j => exact hb j
    | fvar x =>
      exact hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hvi, Semiterm.freeVariables]⟩)
    | func f _ => exact (f : Empty).elim
  | nrel r v =>
    change Semiformula.nrel r (ω₁ ∘ v) = Semiformula.nrel r (ω₂ ∘ v)
    congr 1; funext i
    dsimp only [Function.comp_apply]
    cases hvi : v i with
    | bvar j => exact hb j
    | fvar x =>
      exact hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hvi, Semiterm.freeVariables]⟩)
    | func f _ => exact (f : Empty).elim
  | and φ ψ ih1 ih2 =>
    change (ω₁ ▹ φ) ⋏ (ω₁ ▹ ψ) = (ω₂ ▹ φ) ⋏ (ω₂ ▹ ψ)
    have h1 := ih1 ω₁ ω₂ hb (fun x hx => hf x (Finset.mem_union_left _ hx))
    have h2 := ih2 ω₁ ω₂ hb (fun x hx => hf x (Finset.mem_union_right _ hx))
    exact congrArg₂ (· ⋏ ·) h1 h2
  | or φ ψ ih1 ih2 =>
    change (ω₁ ▹ φ) ⋎ (ω₁ ▹ ψ) = (ω₂ ▹ φ) ⋎ (ω₂ ▹ ψ)
    have h1 := ih1 ω₁ ω₂ hb (fun x hx => hf x (Finset.mem_union_left _ hx))
    have h2 := ih2 ω₁ ω₂ hb (fun x hx => hf x (Finset.mem_union_right _ hx))
    exact congrArg₂ (· ⋎ ·) h1 h2
  | all φ ih =>
    rw [rew_all, rew_all]
    congr 1
    apply ih ω₁.q ω₂.q
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => exact congrArg Rew.bShift (hb j)
    · intro x hx
      exact congrArg Rew.bShift (hf x hx)
  | exs φ ih =>
    rw [rew_exs, rew_exs]
    congr 1
    apply ih ω₁.q ω₂.q
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => exact congrArg Rew.bShift (hb j)
    · intro x hx
      exact congrArg Rew.bShift (hf x hx)

private def liftFVar (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => f k + 1

private noncomputable def derivMapFVar {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) (f : ℕ → ℕ) :
    Derivation (Γ.map (Rew.map id f ▹ ·)) := by
  induction d generalizing f with
  | identity r v =>
    have h : (⦃Semiformula.rel r v, Semiformula.nrel r v⦄ : Sequent ℒₛₑₜ).map (Rew.map id f ▹ ·) =
        ⦃Semiformula.rel r ((Rew.map id f) ∘ v), Semiformula.nrel r ((Rew.map id f) ∘ v)⦄ := by
      simp only [Multiset.atom, Multiset.map_add, Multiset.map_singleton, rew_rel, rew_nrel]
    rw [h]
    exact Derivation.identity r ((Rew.map id f) ∘ v)
  | @cut Γ φ Δ d1 d2 ih1 ih2 =>
    have h1 := ih1 f
    have h2 := ih2 f
    simp only [Multiset.map_add, Multiset.atom, Multiset.map_singleton] at h1 h2 ⊢
    rw [rew_neg] at h2
    exact Derivation.cut h1 h2
  | @contraction Δ Γ d hsub ih =>
    exact Derivation.contraction (ih f) (Multiset.map_subset_map hsub)
  | verum =>
    have h : (⦃⊤⦄ : Sequent ℒₛₑₜ).map (Rew.map id f ▹ ·) = ⦃⊤⦄ := by
      simp [Multiset.atom]; rfl
    rw [h]
    exact Derivation.verum
  | @or Γ φ ψ d ih =>
    have h := ih f
    simp only [Multiset.map_add, Multiset.atom, Multiset.map_singleton] at h ⊢
    exact Derivation.or h
  | @and Γ φ ψ d1 d2 ih1 ih2 =>
    have h1 := ih1 f
    have h2 := ih2 f
    simp only [Multiset.map_add, Multiset.atom, Multiset.map_singleton] at h1 h2 ⊢
    exact Derivation.and h1 h2
  | @all Γ φ d ih =>
    have h := ih (liftFVar f)
    simp only [Multiset.map_add, Multiset.atom, Multiset.map_singleton] at h ⊢
    have hshift : (Rewriting.shifts Γ).map (Rew.map id (liftFVar f) ▹ ·) =
        Rewriting.shifts (Γ.map (Rew.map id f ▹ ·)) := by
      simp only [Rewriting.shifts, Multiset.map_map, Function.comp_def]
      congr 1; funext ψ
      rw [rew_comp_eq, rew_comp_eq]
      apply rew_congr_fv
      · intro i; exact Fin.elim0 i
      · intro x _; rfl
    have hfree : Rew.map id (liftFVar f) ▹ φ.free = ((Rew.map id f).q ▹ φ).free := by
      change Rew.map id (liftFVar f) ▹ (Rew.free ▹ φ) = Rew.free ▹ ((Rew.map id f).q ▹ φ)
      rw [rew_comp_eq, rew_comp_eq]
      apply rew_congr_fv
      · intro i; fin_cases i; rfl
      · intro x _; rfl
    rw [hshift, hfree] at h
    rw [Rewriting.app_all]
    exact Derivation.all h
  | @exs Γ φ t d ih =>
    have h := ih f
    simp only [Multiset.map_add, Multiset.atom, Multiset.map_singleton] at h ⊢
    have hsub : Rew.map id f ▹ (φ/[t]) = ((Rew.map id f).q ▹ φ)/[Rew.map id f t] := by
      change Rew.map id f ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![Rew.map id f t] ▹ ((Rew.map id f).q ▹ φ)
      rw [rew_comp_eq, rew_comp_eq]
      apply rew_congr_fv
      · intro i; fin_cases i; rfl
      · intro x _; rfl
    rw [hsub] at h
    rw [Rewriting.app_exs]
    exact Derivation.exs h

private noncomputable def derivAllOfFresh {Γ : Sequent ℒₛₑₜ} {φ : Semiproposition ℒₛₑₜ 1} (c : ℕ)
    (hcΓ : ∀ ψ ∈ Γ, c ∉ ψ.freeVariables) (hcφ : c ∉ φ.freeVariables)
    (d : Derivation (Γ + ⦃φ/[&c]⦄)) : Derivation (Γ + ⦃∀¹ φ⦄) := by
  let g : ℕ → ℕ := fun m => if m = c then 0 else m + 1
  have hd := derivMapFVar d g
  simp only [Multiset.map_add, Multiset.atom, Multiset.map_singleton] at hd
  have hΓ : Γ.map (Rew.map id g ▹ ·) = Rewriting.shifts Γ := by
    simp only [Rewriting.shifts]
    refine Multiset.map_congr rfl fun ψ hψ => ?_
    apply rew_congr_fv
    · intro i; exact Fin.elim0 i
    · intro x hx
      have hne : x ≠ c := fun heq => hcΓ ψ hψ (heq ▸ hx)
      change Semiterm.fvar (g x) = &(x + 1)
      simp [g, hne]
  have hφ : Rew.map id g ▹ (φ/[&c]) = φ.free := by
    change Rew.map id g ▹ (Rew.subst ![&c] ▹ φ) = Rew.free ▹ φ
    rw [rew_comp_eq]
    apply rew_congr_fv
    · intro i; fin_cases i
      change Semiterm.fvar (g c) = &0
      simp [g]
    · intro x hx
      have hne : x ≠ c := fun heq => hcφ (heq ▸ hx)
      change Semiterm.fvar (g x) = &(x + 1)
      simp [g, hne]
  rw [hΓ, hφ] at hd
  exact Derivation.all hd

private def formulaSize {ξ : Type*} {n : ℕ} : Semiformula ℒₛₑₜ ξ n → ℕ
  | .verum => 0
  | .falsum => 0
  | .rel _ _ => 0
  | .nrel _ _ => 0
  | .and φ ψ => formulaSize φ + formulaSize ψ + 1
  | .or φ ψ => formulaSize φ + formulaSize ψ + 1
  | .all φ => formulaSize φ + 1
  | .exs φ => formulaSize φ + 1

private lemma formulaSize_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    formulaSize (ω ▹ φ) = formulaSize φ := by
  induction φ generalizing n₂ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and φ ψ ih1 ih2 =>
    change formulaSize (ω ▹ φ) + formulaSize (ω ▹ ψ) + 1 = formulaSize φ + formulaSize ψ + 1
    rw [ih1, ih2]
  | or φ ψ ih1 ih2 =>
    change formulaSize (ω ▹ φ) + formulaSize (ω ▹ ψ) + 1 = formulaSize φ + formulaSize ψ + 1
    rw [ih1, ih2]
  | all φ ih =>
    rw [rew_all]
    change formulaSize (ω.q ▹ φ) + 1 = formulaSize φ + 1
    rw [ih]
  | exs φ ih =>
    rw [rew_exs]
    change formulaSize (ω.q ▹ φ) + 1 = formulaSize φ + 1
    rw [ih]

private lemma formulaSize_neg {n : ℕ} (ψ : Semiproposition ℒₛₑₜ n) :
    formulaSize (∼ψ) = formulaSize ψ := by
  induction ψ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and a b iha ihb =>
    change formulaSize (∼a) + formulaSize (∼b) + 1 = formulaSize a + formulaSize b + 1
    rw [iha, ihb]
  | or a b iha ihb =>
    change formulaSize (∼a) + formulaSize (∼b) + 1 = formulaSize a + formulaSize b + 1
    rw [iha, ihb]
  | all a iha =>
    change formulaSize (∼a) + 1 = formulaSize a + 1
    rw [iha]
  | exs a iha =>
    change formulaSize (∼a) + 1 = formulaSize a + 1
    rw [iha]

private noncomputable def derivEmAux : ∀ (k : ℕ) (φ : Proposition ℒₛₑₜ), formulaSize φ ≤ k → Derivation ⦃φ, ∼φ⦄
  | _, .verum, _ =>
    Derivation.contraction Derivation.verum (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact Or.inl hx)
  | _, .falsum, _ =>
    Derivation.contraction Derivation.verum (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact Or.inr hx)
  | _, .rel r v, _ => Derivation.identity r v
  | _, .nrel r v, _ =>
    Derivation.contraction (Derivation.identity r v) (by
      change ⦃Semiformula.rel r v, Semiformula.nrel r v⦄ ⊆
        ⦃Semiformula.nrel r v, Semiformula.rel r v⦄
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact hx.symm)
  | k + 1, .and φ ψ, hk => by
    have h1 : formulaSize φ ≤ k := by simp [formulaSize] at hk; omega
    have h2 : formulaSize ψ ≤ k := by simp [formulaSize] at hk; omega
    have d1 : Derivation (⦃∼φ, ∼ψ⦄ + ⦃φ⦄) :=
      Derivation.contraction (derivEmAux k φ h1) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        tauto)
    have d2 : Derivation (⦃∼φ, ∼ψ⦄ + ⦃ψ⦄) :=
      Derivation.contraction (derivEmAux k ψ h2) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        tauto)
    have d3 : Derivation (⦃φ ⋏ ψ⦄ + ⦃∼φ, ∼ψ⦄) :=
      Derivation.contraction (Derivation.and d1 d2) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        tauto)
    exact Derivation.or d3
  | k + 1, .or φ ψ, hk => by
    have h1 : formulaSize φ ≤ k := by simp [formulaSize] at hk; omega
    have h2 : formulaSize ψ ≤ k := by simp [formulaSize] at hk; omega
    have d1 : Derivation (⦃φ, ψ⦄ + ⦃∼φ⦄) :=
      Derivation.contraction (derivEmAux k φ h1) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        tauto)
    have d2 : Derivation (⦃φ, ψ⦄ + ⦃∼ψ⦄) :=
      Derivation.contraction (derivEmAux k ψ h2) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        tauto)
    have d3 : Derivation (⦃∼φ ⋏ ∼ψ⦄ + ⦃φ, ψ⦄) :=
      Derivation.contraction (Derivation.and d1 d2) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        tauto)
    have d4 : Derivation (⦃∼φ ⋏ ∼ψ⦄ + ⦃φ ⋎ ψ⦄) := Derivation.or d3
    exact Derivation.contraction d4 (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      change x = φ ⋎ ψ ∨ x = ∼φ ⋏ ∼ψ
      tauto)
  | k + 1, .all φ, hk => by
    have h1 : formulaSize φ.free ≤ k := by
      rw [formulaSize_rew]
      simp [formulaSize] at hk; omega
    have d0 : Derivation ⦃φ.free, ∼(φ.free)⦄ := derivEmAux k φ.free h1
    have hrew : ((Rew.shift).q ▹ (∼φ))/[&0] = ∼(φ.free) := by
      change Rew.subst ![&0] ▹ ((Rew.shift).q ▹ (∼φ)) = ∼(Rew.free ▹ φ)
      rw [rew_comp_eq, ← rew_neg]
      apply rew_congr_fv
      · intro i; fin_cases i; rfl
      · intro x _; rfl
    have d1 : Derivation (⦃φ.free⦄ + ⦃((Rew.shift).q ▹ (∼φ))/[&0]⦄) := by
      rw [hrew]; exact d0
    have d2 : Derivation (⦃φ.free⦄ + ⦃∃¹ ((Rew.shift).q ▹ (∼φ))⦄) := Derivation.exs d1
    have d3 : Derivation (Rewriting.shifts ⦃∃¹ (∼φ)⦄ + ⦃φ.free⦄) := by
      refine Derivation.contraction d2 ?_
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton, Rewriting.shifts,
        Multiset.map_singleton, Rewriting.app_exs] at hx ⊢
      exact hx.symm
    have d4 : Derivation (⦃∃¹ (∼φ)⦄ + ⦃∀¹ φ⦄) := Derivation.all d3
    exact Derivation.contraction d4 (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      change x = ∀¹ φ ∨ x = ∃¹ (∼φ)
      tauto)
  | k + 1, .exs φ, hk => by
    have h1 : formulaSize (∼φ).free ≤ k := by
      rw [formulaSize_rew, formulaSize_neg]
      simp [formulaSize] at hk; omega
    have d0 : Derivation ⦃(∼φ).free, ∼((∼φ).free)⦄ := derivEmAux k (∼φ).free h1
    have hrew : ((Rew.shift).q ▹ φ)/[&0] = ∼((∼φ).free) := by
      change Rew.subst ![&0] ▹ ((Rew.shift).q ▹ φ) = ∼(Rew.free ▹ (∼φ))
      rw [rew_comp_eq, ← rew_neg, semiformula_neg_neg]
      apply rew_congr_fv
      · intro i; fin_cases i; rfl
      · intro x _; rfl
    have d1 : Derivation (⦃(∼φ).free⦄ + ⦃((Rew.shift).q ▹ φ)/[&0]⦄) := by
      rw [hrew]; exact d0
    have d2 : Derivation (⦃(∼φ).free⦄ + ⦃∃¹ ((Rew.shift).q ▹ φ)⦄) := Derivation.exs d1
    have d3 : Derivation (Rewriting.shifts ⦃∃¹ φ⦄ + ⦃(∼φ).free⦄) := by
      refine Derivation.contraction d2 ?_
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton, Rewriting.shifts,
        Multiset.map_singleton, Rewriting.app_exs] at hx ⊢
      exact hx.symm
    exact Derivation.all d3
  | 0, .and _ _, hk => by simp [formulaSize] at hk
  | 0, .or _ _, hk => by simp [formulaSize] at hk
  | 0, .all _, hk => by simp [formulaSize] at hk
  | 0, .exs _, hk => by simp [formulaSize] at hk

private noncomputable def derivEm (φ : Proposition ℒₛₑₜ) : Derivation ⦃φ, ∼φ⦄ :=
  derivEmAux (formulaSize φ) φ le_rfl

-- Countability of Proposition ℒₛₑₜ
private def encTermNat {n : ℕ} : Semiterm ℒₛₑₜ ℕ n → ℕ
  | .bvar i => 2 * i.val
  | .fvar x => 2 * x + 1
  | .func f _ => (f : Empty).elim

private lemma encTermNat_inj {n : ℕ} : Function.Injective (@encTermNat n) := by
  intro t₁ t₂ h
  cases t₁ with
  | bvar i =>
    cases t₂ with
    | bvar j => simp only [encTermNat] at h; exact congrArg Semiterm.bvar (Fin.ext (by omega))
    | fvar y => simp only [encTermNat] at h; omega
    | func f _ => exact (f : Empty).elim
  | fvar x =>
    cases t₂ with
    | bvar j => simp only [encTermNat] at h; omega
    | fvar y => simp only [encTermNat] at h; exact congrArg Semiterm.fvar (by omega)
    | func f _ => exact (f : Empty).elim
  | func f _ => exact (f : Empty).elim

private def encForm {n : ℕ} : Semiproposition ℒₛₑₜ n → List ℕ
  | .verum => [0]
  | .falsum => [1]
  | .rel Language.Set.Rel.eq v => [2, encTermNat (v 0), encTermNat (v 1)]
  | .rel Language.Set.Rel.mem v => [3, encTermNat (v 0), encTermNat (v 1)]
  | .nrel Language.Set.Rel.eq v => [4, encTermNat (v 0), encTermNat (v 1)]
  | .nrel Language.Set.Rel.mem v => [5, encTermNat (v 0), encTermNat (v 1)]
  | .and φ ψ => 6 :: (encForm φ).length :: (encForm φ ++ encForm ψ)
  | .or φ ψ => 7 :: (encForm φ).length :: (encForm φ ++ encForm ψ)
  | .all φ => 8 :: encForm φ
  | .exs φ => 9 :: encForm φ

private lemma encForm_inj {n : ℕ} : Function.Injective (@encForm n) := by
  intro φ
  induction φ with
  | verum =>
    intro ψ h; cases ψ with
    | verum => rfl
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | falsum =>
    intro ψ h; cases ψ with
    | falsum => rfl
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | rel r v =>
    intro ψ h
    cases r with
    | eq =>
      cases ψ with
      | rel r' v' =>
        cases r' with
        | eq =>
          simp only [encForm, List.cons.injEq, and_true, true_and] at h
          congr 1; funext k; fin_cases k
          · exact encTermNat_inj h.1
          · exact encTermNat_inj h.2
        | mem => simp [encForm] at h
      | nrel r' _ => cases r' <;> simp [encForm] at h
      | _ => simp [encForm] at h
    | mem =>
      cases ψ with
      | rel r' v' =>
        cases r' with
        | eq => simp [encForm] at h
        | mem =>
          simp only [encForm, List.cons.injEq, and_true, true_and] at h
          congr 1; funext k; fin_cases k
          · exact encTermNat_inj h.1
          · exact encTermNat_inj h.2
      | nrel r' _ => cases r' <;> simp [encForm] at h
      | _ => simp [encForm] at h
  | nrel r v =>
    intro ψ h
    cases r with
    | eq =>
      cases ψ with
      | nrel r' v' =>
        cases r' with
        | eq =>
          simp only [encForm, List.cons.injEq, and_true, true_and] at h
          congr 1; funext k; fin_cases k
          · exact encTermNat_inj h.1
          · exact encTermNat_inj h.2
        | mem => simp [encForm] at h
      | rel r' _ => cases r' <;> simp [encForm] at h
      | _ => simp [encForm] at h
    | mem =>
      cases ψ with
      | nrel r' v' =>
        cases r' with
        | eq => simp [encForm] at h
        | mem =>
          simp only [encForm, List.cons.injEq, and_true, true_and] at h
          congr 1; funext k; fin_cases k
          · exact encTermNat_inj h.1
          · exact encTermNat_inj h.2
      | rel r' _ => cases r' <;> simp [encForm] at h
      | _ => simp [encForm] at h
  | and φ₁ φ₂ ih1 ih2 =>
    intro ψ h; cases ψ with
    | and ψ₁ ψ₂ =>
      simp only [encForm, List.cons.injEq, true_and] at h
      obtain ⟨hlen, happ⟩ := h
      have h12 := List.append_inj happ hlen
      rw [ih1 h12.1, ih2 h12.2]
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | or φ₁ φ₂ ih1 ih2 =>
    intro ψ h; cases ψ with
    | or ψ₁ ψ₂ =>
      simp only [encForm, List.cons.injEq, true_and] at h
      obtain ⟨hlen, happ⟩ := h
      have h12 := List.append_inj happ hlen
      rw [ih1 h12.1, ih2 h12.2]
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | all φ ih =>
    intro ψ h; cases ψ with
    | all ψ =>
      simp only [encForm, List.cons.injEq, true_and] at h
      rw [ih h]
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | exs φ ih =>
    intro ψ h; cases ψ with
    | exs ψ =>
      simp only [encForm, List.cons.injEq, true_and] at h
      rw [ih h]
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h

private lemma prop_countable : Countable (Proposition ℒₛₑₜ) :=
  Function.Injective.countable encForm_inj

private def Cons (S : Set (Proposition ℒₛₑₜ)) : Prop :=
  ∀ Γ : Multiset (Proposition ℒₛₑₜ), (∀ φ ∈ Γ, φ ∈ S) → IsEmpty (Derivation (∼Γ))

private lemma cons_mono {S₁ S₂ : Set (Proposition ℒₛₑₜ)} (hsub : S₁ ⊆ S₂) (hc : Cons S₂) :
    Cons S₁ :=
  fun Γ hΓ => hc Γ (fun φ hφ => hsub (hΓ φ hφ))

private lemma not_cons_insert_iff {S : Set (Proposition ℒₛₑₜ)} {φ : Proposition ℒₛₑₜ} :
    ¬ Cons (insert φ S) ↔ ∃ Δ : Multiset (Proposition ℒₛₑₜ),
      (∀ ψ ∈ Δ, ψ ∈ S) ∧ Nonempty (Derivation (∼Δ + ⦃∼φ⦄)) := by
  constructor
  · intro hnc
    unfold Cons at hnc
    push Not at hnc
    obtain ⟨Γ, hΓ, ⟨d⟩⟩ := hnc
    let Δ := Γ.filter (· ≠ φ)
    refine ⟨Δ, fun ψ hψ => ?_, ⟨?_⟩⟩
    · obtain ⟨hmem, hne⟩ := Multiset.mem_filter.mp hψ
      exact (Set.mem_insert_iff.mp (hΓ ψ hmem)).resolve_left hne
    · refine Derivation.contraction d ?_
      intro x hx
      obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.mp hx
      by_cases h : ψ = φ
      · subst h
        simp [Multiset.atom]
      · refine Multiset.mem_add.mpr (Or.inl ?_)
        exact Multiset.mem_map.mpr ⟨ψ, Multiset.mem_filter.mpr ⟨hψ, h⟩, rfl⟩
  · rintro ⟨Δ, hΔ, ⟨d⟩⟩ hc
    have hΓ : ∀ ψ ∈ Δ + ⦃φ⦄, ψ ∈ insert φ S := by
      intro ψ hψ
      rcases Multiset.mem_add.mp hψ with h | h
      · exact Set.mem_insert_of_mem φ (hΔ ψ h)
      · simp only [Multiset.atom, Multiset.mem_singleton] at h
        exact h ▸ Set.mem_insert φ S
    have heq : ∼(Δ + ⦃φ⦄) = ∼Δ + ⦃∼φ⦄ := by
      change (Δ + ⦃φ⦄).map (∼·) = Δ.map (∼·) + ⦃∼φ⦄
      simp [Multiset.atom]
    exact (hc (Δ + ⦃φ⦄) hΓ).false (heq.symm ▸ d)

private lemma cons_insert_or_neg {S : Set (Proposition ℒₛₑₜ)} (hc : Cons S)
    (φ : Proposition ℒₛₑₜ) : Cons (insert φ S) ∨ Cons (insert (∼φ) S) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨Δ₁, hΔ₁, ⟨d₁⟩⟩ := not_cons_insert_iff.mp h1
  obtain ⟨Δ₂, hΔ₂, ⟨d₂⟩⟩ := not_cons_insert_iff.mp h2
  rw [semiformula_neg_neg] at d₂
  have dcut : Derivation (∼Δ₂ + ∼Δ₁) := Derivation.cut d₂ d₁
  have hmem : ∀ ψ ∈ Δ₂ + Δ₁, ψ ∈ S := by
    intro ψ hψ
    rcases Multiset.mem_add.mp hψ with h | h
    · exact hΔ₂ ψ h
    · exact hΔ₁ ψ h
  have heq : ∼(Δ₂ + Δ₁) = ∼Δ₂ + ∼Δ₁ := Multiset.map_add (∼·) Δ₂ Δ₁
  exact (hc (Δ₂ + Δ₁) hmem).false (heq.symm ▸ dcut)

private lemma freeVariables_neg {ξ : Type*} [DecidableEq ξ] {n : ℕ}
    (φ : Semiformula ℒₛₑₜ ξ n) : (∼φ).freeVariables = φ.freeVariables := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and φ ψ ih1 ih2 =>
    change (∼φ).freeVariables ∪ (∼ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables
    rw [ih1, ih2]
  | or φ ψ ih1 ih2 =>
    change (∼φ).freeVariables ∪ (∼ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables
    rw [ih1, ih2]
  | all φ ih => exact ih
  | exs φ ih => exact ih

private lemma freeVariables_rew_subset {n₁ n₂ : ℕ} (ψ : Semiproposition ℒₛₑₜ n₁)
    (ω : SyntacticRew ℒₛₑₜ n₁ n₂) (c : ℕ)
    (hb : ∀ i : Fin n₁, (ω #i).freeVariables ⊆ {c})
    (hf : ∀ x : ℕ, (ω &x).freeVariables ⊆ {x}) :
    (ω ▹ ψ).freeVariables ⊆ ψ.freeVariables ∪ {c} := by
  induction ψ generalizing n₂ with
  | verum => simp [Semiformula.freeVariables]
  | falsum => simp [Semiformula.freeVariables]
  | rel r v =>
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    dsimp only [Function.comp_apply] at hi
    cases hvi : v i with
    | bvar j =>
      rw [hvi] at hi
      exact Finset.mem_union_right _ (hb j hi)
    | fvar y =>
      rw [hvi] at hi
      have hxy := Finset.mem_singleton.mp (hf y hi)
      subst hxy
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        by simp [hvi, Semiterm.freeVariables]⟩)
    | func f _ => exact (f : Empty).elim
  | nrel r v =>
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    dsimp only [Function.comp_apply] at hi
    cases hvi : v i with
    | bvar j =>
      rw [hvi] at hi
      exact Finset.mem_union_right _ (hb j hi)
    | fvar y =>
      rw [hvi] at hi
      have hxy := Finset.mem_singleton.mp (hf y hi)
      subst hxy
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        by simp [hvi, Semiterm.freeVariables]⟩)
    | func f _ => exact (f : Empty).elim
  | and ψ₁ ψ₂ ih1 ih2 =>
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp (ih1 ω hb hf h) with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      · exact Finset.mem_union_right _ h2
    · rcases Finset.mem_union.mp (ih2 ω hb hf h) with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      · exact Finset.mem_union_right _ h2
  | or ψ₁ ψ₂ ih1 ih2 =>
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp (ih1 ω hb hf h) with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      · exact Finset.mem_union_right _ h2
    · rcases Finset.mem_union.mp (ih2 ω hb hf h) with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      · exact Finset.mem_union_right _ h2
  | all ψ ih =>
    rw [rew_all]
    apply ih ω.q
    · intro i
      cases i using Fin.cases with
      | zero => exact Finset.empty_subset _
      | succ j =>
        have hfv : (Rew.bShift (ω #j)).freeVariables = (ω #j).freeVariables := by
          cases ω #j with
          | bvar _ => rfl
          | fvar _ => rfl
          | func f _ => exact (f : Empty).elim
        change (Rew.bShift (ω #j)).freeVariables ⊆ {c}
        rw [hfv]; exact hb j
    · intro x
      have hfv : (Rew.bShift (ω &x)).freeVariables = (ω &x).freeVariables := by
        cases ω &x with
        | bvar _ => rfl
        | fvar _ => rfl
        | func f _ => exact (f : Empty).elim
      change (Rew.bShift (ω &x)).freeVariables ⊆ {x}
      rw [hfv]; exact hf x
  | exs ψ ih =>
    rw [rew_exs]
    apply ih ω.q
    · intro i
      cases i using Fin.cases with
      | zero => exact Finset.empty_subset _
      | succ j =>
        have hfv : (Rew.bShift (ω #j)).freeVariables = (ω #j).freeVariables := by
          cases ω #j with
          | bvar _ => rfl
          | fvar _ => rfl
          | func f _ => exact (f : Empty).elim
        change (Rew.bShift (ω #j)).freeVariables ⊆ {c}
        rw [hfv]; exact hb j
    · intro x
      have hfv : (Rew.bShift (ω &x)).freeVariables = (ω &x).freeVariables := by
        cases ω &x with
        | bvar _ => rfl
        | fvar _ => rfl
        | func f _ => exact (f : Empty).elim
      change (Rew.bShift (ω &x)).freeVariables ⊆ {x}
      rw [hfv]; exact hf x

private lemma freeVariables_subst_fvar (φ : Semiproposition ℒₛₑₜ 1) (c : ℕ) :
    (φ/[(&c : Semiterm ℒₛₑₜ ℕ 0)]).freeVariables ⊆ φ.freeVariables ∪ {c} :=
  freeVariables_rew_subset φ (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)]) c
    (fun i => by fin_cases i; exact Finset.Subset.rfl)
    (fun _ => Finset.Subset.rfl)

private lemma not_mem_freeVariables_of_fvSup_le {n : ℕ} {φ : Semiproposition ℒₛₑₜ n} {c : ℕ}
    (h : φ.fvSup ≤ c) : c ∉ φ.freeVariables := by
  intro hc
  obtain ⟨m, hm⟩ := Finset.max_of_mem hc
  have hlt : c < φ.fvSup := by
    simpa only [Semiformula.fvSup, hm, WithBot.recBotCoe_coe] using
      Nat.lt_succ_of_le (Finset.le_max_of_eq hc hm)
  omega

private lemma fvSup_le_of_forall_lt {n : ℕ} {φ : Semiproposition ℒₛₑₜ n} {B : ℕ}
    (h : ∀ x ∈ φ.freeVariables, x < B) : φ.fvSup ≤ B := by
  unfold Semiformula.fvSup
  cases hmax : φ.freeVariables.max with
  | bot => simp
  | coe m =>
    have hm : m ∈ φ.freeVariables := Finset.mem_of_max hmax
    have := h m hm
    simpa using Nat.succ_le_of_lt this

private lemma cons_henkin_witness {S : Set (Proposition ℒₛₑₜ)} (hc : Cons S)
    {φ : Semiproposition ℒₛₑₜ 1} (hex : (∃¹ φ) ∈ S)
    {c : ℕ} (hcS : ∀ ψ ∈ S, c ∉ ψ.freeVariables) (hcφ : c ∉ φ.freeVariables) :
    Cons (insert (φ/[&c]) S) := by
  by_contra hnc
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := not_cons_insert_iff.mp hnc
  have hneg : ∼(φ/[(&c : Semiterm ℒₛₑₜ ℕ 0)]) = (∼φ)/[(&c : Semiterm ℒₛₑₜ ℕ 0)] :=
    (rew_neg (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)]) φ).symm
  rw [hneg] at d
  have hcΔ : ∀ ψ ∈ ∼Δ, c ∉ ψ.freeVariables := by
    intro ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := Multiset.mem_map.mp hψ
    rw [freeVariables_neg]
    exact hcS χ (hΔ χ hχ)
  have hcneg : c ∉ (∼φ).freeVariables := by rw [freeVariables_neg]; exact hcφ
  have dall : Derivation (∼Δ + ⦃∀¹ (∼φ)⦄) := derivAllOfFresh c hcΔ hcneg d
  have hsub : ∀ ψ ∈ Δ + ⦃∃¹ φ⦄, ψ ∈ S := by
    intro ψ hψ
    rcases Multiset.mem_add.mp hψ with h | h
    · exact hΔ ψ h
    · simp only [Multiset.atom, Multiset.mem_singleton] at h
      exact h ▸ hex
  have heq : ∼(Δ + ⦃∃¹ φ⦄) = ∼Δ + ⦃∀¹ (∼φ)⦄ := by
    change (Δ + ⦃∃¹ φ⦄).map (∼·) = Δ.map (∼·) + ⦃∀¹ (∼φ)⦄
    simp [Multiset.atom]; rfl
  exact (hc (Δ + ⦃∃¹ φ⦄) hsub).false (heq.symm ▸ dall)

private lemma rew_emb_q {n : ℕ} :
    (Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := n)).q =
      Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := n + 1) := by
  apply rew_ext; intro t
  cases t with
  | bvar i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  | fvar e => exact e.elim
  | func f _ => exact (f : Empty).elim

private lemma freeVariables_emb {m : ℕ} (φ : Semisentence ℒₛₑₜ m) :
    (Rewriting.emb (ξ := ℕ) φ).freeVariables = ∅ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    dsimp only [Function.comp_apply] at hi
    cases hvi : v i with
    | bvar j =>
      rw [hvi] at hi
      exact Finset.notMem_empty x hi
    | fvar e => exact e.elim
    | func f _ => exact (f : Empty).elim
  | nrel r v =>
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    dsimp only [Function.comp_apply] at hi
    cases hvi : v i with
    | bvar j =>
      rw [hvi] at hi
      exact Finset.notMem_empty x hi
    | fvar e => exact e.elim
    | func f _ => exact (f : Empty).elim
  | and φ ψ ih1 ih2 =>
    change (Rewriting.emb φ).freeVariables ∪ (Rewriting.emb ψ).freeVariables = ∅
    rw [ih1, ih2]; rfl
  | or φ ψ ih1 ih2 =>
    change (Rewriting.emb φ).freeVariables ∪ (Rewriting.emb ψ).freeVariables = ∅
    rw [ih1, ih2]; rfl
  | all φ ih =>
    change ((Rew.emb (o := Empty) (ξ := ℕ)).q ▹ φ).freeVariables = ∅
    rw [rew_emb_q]; exact ih
  | exs φ ih =>
    change ((Rew.emb (o := Empty) (ξ := ℕ)).q ▹ φ).freeVariables = ∅
    rw [rew_emb_q]; exact ih

private noncomputable def henkinStep (enum : ℕ → Proposition ℒₛₑₜ)
    (st : Set (Proposition ℒₛₑₜ) × ℕ) (k : ℕ) : Set (Proposition ℒₛₑₜ) × ℕ :=
  let S := st.1
  let B := st.2
  let φ := enum k
  let χ := if Cons (insert φ S) then φ else ∼φ
  let S₁ := insert χ S
  let B₁ := max B χ.fvSup
  match χ with
  | .exs ψ => (insert (ψ/[&B₁]) S₁, B₁ + 1)
  | _ => (S₁, B₁)

private noncomputable def henkinChain (S₀ : Set (Proposition ℒₛₑₜ))
    (enum : ℕ → Proposition ℒₛₑₜ) : ℕ → Set (Proposition ℒₛₑₜ) × ℕ
  | 0 => (S₀, 0)
  | k + 1 => henkinStep enum (henkinChain S₀ enum k) k

private lemma henkinChain_inv {S₀ : Set (Proposition ℒₛₑₜ)} (enum : ℕ → Proposition ℒₛₑₜ)
    (hc₀ : Cons S₀) (hb₀ : ∀ ψ ∈ S₀, ψ.fvSup ≤ 0) (k : ℕ) :
    Cons (henkinChain S₀ enum k).1 ∧
    (∀ ψ ∈ (henkinChain S₀ enum k).1, ψ.fvSup ≤ (henkinChain S₀ enum k).2) := by
  induction k with
  | zero => exact ⟨hc₀, hb₀⟩
  | succ k ih =>
    obtain ⟨hc, hb⟩ := ih
    dsimp only [henkinChain, henkinStep]
    set S := (henkinChain S₀ enum k).1
    set B := (henkinChain S₀ enum k).2
    set φ := enum k
    set χ := if Cons (insert φ S) then φ else ∼φ
    have hc1 : Cons (insert χ S) := by
      by_cases h : Cons (insert φ S)
      · simp [χ, h]
      · simpa [χ, h] using (cons_insert_or_neg hc φ).resolve_left h
    have hb1 : ∀ ξ ∈ insert χ S, ξ.fvSup ≤ max B χ.fvSup := by
      intro ξ hξ
      rcases Set.mem_insert_iff.mp hξ with rfl | hS
      · exact le_max_right _ _
      · exact (hb ξ hS).trans (le_max_left _ _)
    cases hχ : χ with
    | exs ψ =>
      dsimp only
      rw [hχ] at hc1 hb1
      have hψ_le : ψ.fvSup ≤ max B ψ.exs.fvSup := le_max_right _ _
      have hc2 : Cons (insert (ψ/[&(max B ψ.exs.fvSup)]) (insert (∃¹ ψ) S)) := by
        apply cons_henkin_witness hc1 (Set.mem_insert _ _)
        · intro ξ hξ
          exact not_mem_freeVariables_of_fvSup_le (hb1 ξ hξ)
        · exact not_mem_freeVariables_of_fvSup_le hψ_le
      refine ⟨hc2, fun ξ hξ => ?_⟩
      rcases Set.mem_insert_iff.mp hξ with rfl | hS1
      · apply fvSup_le_of_forall_lt
        intro x hx
        rcases Finset.mem_union.mp (freeVariables_subst_fvar ψ _ hx) with hxψ | hxc
        · have hxlt : x < ψ.fvSup := by
            obtain ⟨m, hm⟩ := Finset.max_of_mem hxψ
            simpa only [Semiformula.fvSup, hm, WithBot.recBotCoe_coe] using
              Nat.lt_succ_of_le (Finset.le_max_of_eq hxψ hm)
          have hfv_eq : ψ.exs.fvSup = ψ.fvSup := rfl
          omega
        · have := Finset.mem_singleton.mp hxc
          omega
      · exact (hb1 ξ hS1).trans (Nat.le_succ _)
    | verum => rw [hχ] at hc1 hb1; exact ⟨hc1, hb1⟩
    | falsum => rw [hχ] at hc1 hb1; exact ⟨hc1, hb1⟩
    | rel _ _ => rw [hχ] at hc1 hb1; exact ⟨hc1, hb1⟩
    | nrel _ _ => rw [hχ] at hc1 hb1; exact ⟨hc1, hb1⟩
    | and _ _ => rw [hχ] at hc1 hb1; exact ⟨hc1, hb1⟩
    | or _ _ => rw [hχ] at hc1 hb1; exact ⟨hc1, hb1⟩
    | all _ => rw [hχ] at hc1 hb1; exact ⟨hc1, hb1⟩

private lemma henkinChain_mono (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ)
    {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : (henkinChain S₀ enum k₁).1 ⊆ (henkinChain S₀ enum k₂).1 := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step _ ih =>
    intro x hx
    have hx' := ih hx
    dsimp only [henkinChain, henkinStep]
    generalize (if Cons (insert (enum _) _) then _ else _) = χ
    cases χ <;> simp [Set.mem_insert_iff, hx']

private lemma exists_max_henkin {S₀ : Set (Proposition ℒₛₑₜ)}
    (hc₀ : Cons S₀) (hb₀ : ∀ ψ ∈ S₀, ψ.fvSup ≤ 0) :
    ∃ Ω : Set (Proposition ℒₛₑₜ),
      S₀ ⊆ Ω ∧ Cons Ω ∧
      (∀ φ : Proposition ℒₛₑₜ, φ ∈ Ω ∨ ∼φ ∈ Ω) ∧
      (∀ φ : Semiproposition ℒₛₑₜ 1, (∃¹ φ) ∈ Ω → ∃ c : ℕ, φ/[&c] ∈ Ω) := by
  have : Countable (Proposition ℒₛₑₜ) := prop_countable
  have : Nonempty (Proposition ℒₛₑₜ) := ⟨⊤⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat (Proposition ℒₛₑₜ)
  let Ω : Set (Proposition ℒₛₑₜ) := ⋃ k, (henkinChain S₀ enum k).1
  have hConsΩ : Cons Ω := by
    intro Γ hΓ
    have hfin : ∃ N : ℕ, ∀ φ ∈ Γ, φ ∈ (henkinChain S₀ enum N).1 := by
      induction Γ using Multiset.induction with
      | empty => exact ⟨0, fun _ h => absurd h (Multiset.notMem_zero _)⟩
      | cons a s ih =>
        obtain ⟨k₁, hk₁⟩ := Set.mem_iUnion.mp (hΓ a (Multiset.mem_cons_self a s))
        obtain ⟨k₂, hk₂⟩ := ih (fun φ hφ => hΓ φ (Multiset.mem_cons_of_mem hφ))
        refine ⟨max k₁ k₂, fun φ hφ => ?_⟩
        rcases Multiset.mem_cons.mp hφ with rfl | hs
        · exact henkinChain_mono S₀ enum (le_max_left _ _) hk₁
        · exact henkinChain_mono S₀ enum (le_max_right _ _) (hk₂ φ hs)
    obtain ⟨N, hN⟩ := hfin
    exact (henkinChain_inv enum hc₀ hb₀ N).1 Γ hN
  refine ⟨Ω, fun x hx => Set.mem_iUnion.mpr ⟨0, hx⟩, hConsΩ, ?_, ?_⟩
  · intro φ
    obtain ⟨k, rfl⟩ := henum φ
    have hmem : (if Cons (insert (enum k) (henkinChain S₀ enum k).1) then enum k else ∼enum k) ∈
        (henkinChain S₀ enum (k + 1)).1 := by
      dsimp only [henkinChain, henkinStep]
      generalize (if Cons (insert (enum k) (henkinChain S₀ enum k).1) then enum k else ∼enum k) = χ
      cases χ <;> simp
    by_cases h : Cons (insert (enum k) (henkinChain S₀ enum k).1)
    · rw [if_pos h] at hmem
      exact Or.inl (Set.mem_iUnion.mpr ⟨k + 1, hmem⟩)
    · rw [if_neg h] at hmem
      exact Or.inr (Set.mem_iUnion.mpr ⟨k + 1, hmem⟩)
  · intro φ hex
    obtain ⟨k, hk⟩ := henum (∃¹ φ)
    have hcons : Cons (insert (∃¹ φ) (henkinChain S₀ enum k).1) :=
      cons_mono (fun x hx => by
        rcases Set.mem_insert_iff.mp hx with rfl | hk'
        · exact hex
        · exact Set.mem_iUnion.mpr ⟨k, hk'⟩) hConsΩ
    let c := max (henkinChain S₀ enum k).2 (∃¹ φ).fvSup
    refine ⟨c, Set.mem_iUnion.mpr ⟨k + 1, ?_⟩⟩
    dsimp only [henkinChain, henkinStep]
    rw [hk, if_pos hcons]
    exact Set.mem_insert _ _

private lemma maxCons_not_both {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    {φ : Proposition ℒₛₑₜ} (h1 : φ ∈ Ω) (h2 : ∼φ ∈ Ω) : False := by
  have hΓ : ∀ ψ ∈ ⦃φ, ∼φ⦄, ψ ∈ Ω := by
    intro ψ hψ
    simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hψ
    rcases hψ with rfl | rfl <;> assumption
  have heq : ∼(⦃φ, ∼φ⦄ : Sequent ℒₛₑₜ) = ⦃∼φ, φ⦄ := by
    change (⦃φ, ∼φ⦄ : Sequent ℒₛₑₜ).map (∼·) = _
    simp [Multiset.atom, semiformula_neg_neg]
  have d : Derivation (∼(⦃φ, ∼φ⦄ : Sequent ℒₛₑₜ)) := by
    rw [heq]
    exact Derivation.contraction (derivEm φ) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact hx.symm)
  exact (hc ⦃φ, ∼φ⦄ hΓ).false d

private lemma maxCons_mem_of_deriv {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    (hmax : ∀ φ, φ ∈ Ω ∨ ∼φ ∈ Ω) {Δ : Multiset (Proposition ℒₛₑₜ)}
    (hΔ : ∀ ψ ∈ Δ, ψ ∈ Ω) {φ : Proposition ℒₛₑₜ} (d : Derivation (∼Δ + ⦃φ⦄)) : φ ∈ Ω := by
  rcases hmax φ with h | hn
  · exact h
  · exfalso
    have hΓ : ∀ ψ ∈ Δ + ⦃∼φ⦄, ψ ∈ Ω := by
      intro ψ hψ
      rcases Multiset.mem_add.mp hψ with h1 | h2
      · exact hΔ ψ h1
      · simp only [Multiset.atom, Multiset.mem_singleton] at h2
        exact h2 ▸ hn
    have heq : ∼(Δ + ⦃∼φ⦄) = ∼Δ + ⦃φ⦄ := by
      change (Δ + ⦃∼φ⦄).map (∼·) = Δ.map (∼·) + ⦃φ⦄
      simp [Multiset.atom, semiformula_neg_neg]
    exact (hc (Δ + ⦃∼φ⦄) hΓ).false (heq.symm ▸ d)

private lemma maxCons_verum {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    (hmax : ∀ φ, φ ∈ Ω ∨ ∼φ ∈ Ω) : (⊤ : Proposition ℒₛₑₜ) ∈ Ω := by
  have d : Derivation (∼(0 : Sequent ℒₛₑₜ) + ⦃⊤⦄) := by
    change Derivation ((0 : Sequent ℒₛₑₜ).map (∼·) + ⦃⊤⦄)
    simpa using Derivation.verum
  exact maxCons_mem_of_deriv hc hmax (fun _ h => absurd h (Multiset.notMem_zero _)) d

private lemma maxCons_falsum {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    (hmax : ∀ φ, φ ∈ Ω ∨ ∼φ ∈ Ω) : (⊥ : Proposition ℒₛₑₜ) ∉ Ω :=
  fun hf => maxCons_not_both hc (maxCons_verum hc hmax) hf

private lemma maxCons_and_iff {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    (hmax : ∀ φ, φ ∈ Ω ∨ ∼φ ∈ Ω) (φ ψ : Proposition ℒₛₑₜ) :
    (φ ⋏ ψ) ∈ Ω ↔ φ ∈ Ω ∧ ψ ∈ Ω := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have d1 : Derivation (∼⦃φ ⋏ ψ⦄ + ⦃φ⦄) := by
        have d0 : Derivation (⦃φ⦄ + ⦃∼φ, ∼ψ⦄) :=
          Derivation.contraction (derivEm φ) (by
            intro x hx; simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢; tauto)
        have d2 : Derivation (⦃φ⦄ + ⦃∼φ ⋎ ∼ψ⦄) := Derivation.or d0
        refine Derivation.contraction d2 ?_
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        change x ∈ (⦃φ ⋏ ψ⦄ : Sequent ℒₛₑₜ).map (∼·) ∨ x = φ
        simp only [Multiset.atom, Multiset.map_singleton, Multiset.mem_singleton]
        change x = ∼φ ⋎ ∼ψ ∨ x = φ
        tauto
      exact maxCons_mem_of_deriv hc hmax (fun x hx => by
        simp only [Multiset.atom, Multiset.mem_singleton] at hx; exact hx ▸ h) d1
    · have d1 : Derivation (∼⦃φ ⋏ ψ⦄ + ⦃ψ⦄) := by
        have d0 : Derivation (⦃ψ⦄ + ⦃∼φ, ∼ψ⦄) :=
          Derivation.contraction (derivEm ψ) (by
            intro x hx; simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢; tauto)
        have d2 : Derivation (⦃ψ⦄ + ⦃∼φ ⋎ ∼ψ⦄) := Derivation.or d0
        refine Derivation.contraction d2 ?_
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        change x ∈ (⦃φ ⋏ ψ⦄ : Sequent ℒₛₑₜ).map (∼·) ∨ x = ψ
        simp only [Multiset.atom, Multiset.map_singleton, Multiset.mem_singleton]
        change x = ∼φ ⋎ ∼ψ ∨ x = ψ
        tauto
      exact maxCons_mem_of_deriv hc hmax (fun x hx => by
        simp only [Multiset.atom, Multiset.mem_singleton] at hx; exact hx ▸ h) d1
  · rintro ⟨h1, h2⟩
    have d1 : Derivation (∼⦃φ, ψ⦄ + ⦃φ⦄) :=
      Derivation.contraction (derivEm φ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        change x ∈ (⦃φ, ψ⦄ : Sequent ℒₛₑₜ).map (∼·) ∨ x = φ
        simp [Multiset.atom]; tauto)
    have d2 : Derivation (∼⦃φ, ψ⦄ + ⦃ψ⦄) :=
      Derivation.contraction (derivEm ψ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        change x ∈ (⦃φ, ψ⦄ : Sequent ℒₛₑₜ).map (∼·) ∨ x = ψ
        simp [Multiset.atom]; tauto)
    exact maxCons_mem_of_deriv hc hmax (fun x hx => by
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption) (Derivation.and d1 d2)

private lemma maxCons_or_iff {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    (hmax : ∀ φ, φ ∈ Ω ∨ ∼φ ∈ Ω) (φ ψ : Proposition ℒₛₑₜ) :
    (φ ⋎ ψ) ∈ Ω ↔ φ ∈ Ω ∨ ψ ∈ Ω := by
  have hneg : (φ ⋎ ψ) ∈ Ω ↔ ∼(φ ⋎ ψ) ∉ Ω :=
    ⟨fun h hn => maxCons_not_both hc h hn, fun hn => (hmax _).resolve_right hn⟩
  rw [hneg]
  change (∼φ ⋏ ∼ψ) ∉ Ω ↔ _
  rw [maxCons_and_iff hc hmax, not_and_or]
  have hf : ∼φ ∉ Ω ↔ φ ∈ Ω :=
    ⟨fun hn => (hmax _).resolve_right hn, fun h hn => maxCons_not_both hc h hn⟩
  have hg : ∼ψ ∉ Ω ↔ ψ ∈ Ω :=
    ⟨fun hn => (hmax _).resolve_right hn, fun h hn => maxCons_not_both hc h hn⟩
  rw [hf, hg]

private lemma maxCons_exs_iff {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    (hmax : ∀ φ, φ ∈ Ω ∨ ∼φ ∈ Ω)
    (hhen : ∀ φ : Semiproposition ℒₛₑₜ 1, (∃¹ φ) ∈ Ω → ∃ c : ℕ, φ/[&c] ∈ Ω)
    (φ : Semiproposition ℒₛₑₜ 1) :
    (∃¹ φ) ∈ Ω ↔ ∃ c : ℕ, φ/[&c] ∈ Ω := by
  constructor
  · exact hhen φ
  · rintro ⟨c, hc'⟩
    have d0 : Derivation (∼⦃φ/[&c]⦄ + ⦃φ/[&c]⦄) :=
      Derivation.contraction (derivEm (φ/[&c])) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        change x ∈ (⦃φ/[&c]⦄ : Sequent ℒₛₑₜ).map (∼·) ∨ x = φ/[&c]
        simp [Multiset.atom]; tauto)
    have d1 : Derivation (∼⦃φ/[&c]⦄ + ⦃∃¹ φ⦄) := Derivation.exs d0
    exact maxCons_mem_of_deriv hc hmax (fun x hx => by
      simp only [Multiset.atom, Multiset.mem_singleton] at hx; exact hx ▸ hc') d1

private lemma maxCons_all_iff {Ω : Set (Proposition ℒₛₑₜ)} (hc : Cons Ω)
    (hmax : ∀ φ, φ ∈ Ω ∨ ∼φ ∈ Ω)
    (hhen : ∀ φ : Semiproposition ℒₛₑₜ 1, (∃¹ φ) ∈ Ω → ∃ c : ℕ, φ/[&c] ∈ Ω)
    (φ : Semiproposition ℒₛₑₜ 1) :
    (∀¹ φ) ∈ Ω ↔ ∀ c : ℕ, φ/[&c] ∈ Ω := by
  have hneg : (∀¹ φ) ∈ Ω ↔ ∼(∀¹ φ) ∉ Ω :=
    ⟨fun h hn => maxCons_not_both hc h hn, fun hn => (hmax _).resolve_right hn⟩
  rw [hneg]
  change (∃¹ (∼φ)) ∉ Ω ↔ _
  rw [maxCons_exs_iff hc hmax hhen, not_exists]
  refine forall_congr' fun c => ?_
  have hsub : (∼φ)/[(&c : Semiterm ℒₛₑₜ ℕ 0)] = ∼(φ/[(&c : Semiterm ℒₛₑₜ ℕ 0)]) :=
    rew_neg (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)]) φ
  rw [hsub]
  exact ⟨fun hn => (hmax _).resolve_right hn, fun h hn => maxCons_not_both hc h hn⟩

private lemma rew_id_q {n : ℕ} :
    (Rew.id (L := ℒₛₑₜ) (ξ := ℕ) (n := n)).q = Rew.id := by
  apply rew_ext; intro t
  cases t with
  | bvar i => cases i using Fin.cases <;> rfl
  | fvar _ => rfl
  | func f _ => exact (f : Empty).elim

private lemma rew_id_eq {m : ℕ} (ψ : Semiproposition ℒₛₑₜ m) : Rew.id ▹ ψ = ψ := by
  induction ψ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and a b iha ihb => exact congrArg₂ (· ⋏ ·) iha ihb
  | or a b iha ihb => exact congrArg₂ (· ⋎ ·) iha ihb
  | all a iha => rw [rew_all, rew_id_q, iha]; rfl
  | exs a iha => rw [rew_exs, rew_id_q, iha]; rfl

private theorem completeness_set (T : SetTheory) (hEq : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, φ ∈ T)
    (σ : SetTheorySentence)
    (hsem : ∀ (V : Type) [Nonempty V] (memV : V → V → Prop),
      (∀ ψ ∈ T, semEv V memV Fin.elim0 Empty.elim ψ) →
      semEv V memV Fin.elim0 Empty.elim σ) :
    FFL.Entailment.Provable T σ := by
  by_contra hnp
  let S₀ : Set (Proposition ℒₛₑₜ) :=
    insert (∼Rewriting.emb σ) (Rewriting.emb '' T)
  have hc₀ : Cons S₀ := by
    intro Γ hΓ
    refine ⟨fun d => hnp ?_⟩
    let ΓT := Γ.filter (· ≠ ∼Rewriting.emb σ)
    have hmemT : ∀ χ ∈ ΓT, ∃ ψ ∈ T, Rewriting.emb ψ = χ := by
      intro χ hχ
      obtain ⟨hm, hne⟩ := Multiset.mem_filter.mp hχ
      rcases Set.mem_insert_iff.mp (hΓ χ hm) with h1 | ⟨ψ, hψ, rfl⟩
      · exact absurd h1 hne
      · exact ⟨ψ, hψ, rfl⟩
    have hexAx : ∀ s : Multiset (Proposition ℒₛₑₜ),
        (∀ χ ∈ s, ∃ ψ ∈ T, Rewriting.emb ψ = χ) →
        ∃ ax : Multiset (Sentence ℒₛₑₜ), (∀ ψ ∈ ax, ψ ∈ T) ∧ ax.map Rewriting.emb = s := by
      intro s
      induction s using Multiset.induction with
      | empty => intro _; exact ⟨0, fun _ h => absurd h (Multiset.notMem_zero _), rfl⟩
      | cons a s ih =>
        intro hs
        obtain ⟨ψ, hψ, rfl⟩ := hs a (Multiset.mem_cons_self a s)
        obtain ⟨ax, hax, hmap⟩ := ih (fun χ hχ => hs χ (Multiset.mem_cons_of_mem hχ))
        refine ⟨ψ ::ₘ ax, fun χ hχ => ?_, by simp [hmap]⟩
        rcases Multiset.mem_cons.mp hχ with rfl | h'
        · exact hψ
        · exact hax χ h'
    obtain ⟨ax, hax, hmap⟩ := hexAx ΓT hmemT
    refine ⟨⟨ax, hax, ?_⟩⟩
    change Derivation ((⦃σ⦄ + ∼ax).map Rewriting.emb)
    refine Derivation.contraction d ?_
    intro x hx
    obtain ⟨χ, hχ, rfl⟩ := Multiset.mem_map.mp hx
    simp only [Multiset.map_add, Multiset.atom, Multiset.map_singleton, Multiset.mem_add,
      Multiset.mem_singleton]
    by_cases h : χ = ∼Rewriting.emb σ
    · left
      rw [h, semiformula_neg_neg]
    · right
      have hχT : χ ∈ ΓT := Multiset.mem_filter.mpr ⟨hχ, h⟩
      rw [← hmap] at hχT
      obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.mp hχT
      have hneg : Rewriting.emb (ξ := ℕ) (∼ψ) = ∼Rewriting.emb (ξ := ℕ) ψ :=
        (Rewriting.emb (ξ := ℕ)).map_neg' ψ
      exact Multiset.mem_map.mpr ⟨∼ψ, Multiset.mem_map.mpr ⟨ψ, hψ, rfl⟩, hneg⟩
  have hb₀ : ∀ ψ ∈ S₀, ψ.fvSup ≤ 0 := by
    intro ψ hψ
    apply fvSup_le_of_forall_lt
    intro x hx
    rcases Set.mem_insert_iff.mp hψ with rfl | ⟨χ, _, rfl⟩
    · rw [freeVariables_neg, freeVariables_emb] at hx
      exact absurd hx (Finset.notMem_empty x)
    · rw [freeVariables_emb] at hx
      exact absurd hx (Finset.notMem_empty x)
  obtain ⟨Ω, hS₀Ω, hcΩ, hmaxΩ, hhenΩ⟩ := exists_max_henkin hc₀ hb₀
  -- Define equivalence relation and membership on ℕ from Ω
  let eqR (a b : ℕ) : Prop :=
    Semiformula.rel Language.Set.Rel.eq ![&a, &b] ∈ Ω
  let memR (a b : ℕ) : Prop :=
    Semiformula.rel Language.Set.Rel.mem ![&a, &b] ∈ Ω
  -- Pre-quotient truth lemma: relate semEv in ℕ-structure (with eqR/memR) directly to Ω!
  have hmp : ∀ {φ ψ : Proposition ℒₛₑₜ}, (φ 🡒 ψ) ∈ Ω → φ ∈ Ω → ψ ∈ Ω := by
    intro φ ψ himp hφ
    rcases (maxCons_or_iff hcΩ hmaxΩ (∼φ) ψ).mp himp with hn | hψ
    · exact (maxCons_not_both hcΩ hφ hn).elim
    · exact hψ
  -- Evaluate equality axioms in Ω cleanly via rew_comp_eq
  have hRefl_in : Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) ∈ Ω :=
    hS₀Ω (Set.mem_insert_of_mem _ ⟨_, hEq _ Theory.eqAxiom.refl, rfl⟩)
  have hSymm_in : Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) ∈ Ω :=
    hS₀Ω (Set.mem_insert_of_mem _ ⟨_, hEq _ Theory.eqAxiom.symm, rfl⟩)
  have hTrans_in : Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) ∈ Ω :=
    hS₀Ω (Set.mem_insert_of_mem _ ⟨_, hEq _ Theory.eqAxiom.trans, rfl⟩)
  have hMemExt_in : Rewriting.emb (Theory.Eq.relExt Language.Set.Rel.mem) ∈ Ω :=
    hS₀Ω (Set.mem_insert_of_mem _ ⟨_, hEq _ (Theory.eqAxiom.relExt Language.Set.Rel.mem), rfl⟩)
  have heq_refl : ∀ a, eqR a a := fun a => by
    have h1 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp hRefl_in a
    change Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.eq
      (Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)] ∘
        ((Rew.emb (o := Empty) (ξ := ℕ)).q ∘ ![#0, #0])) ∈ Ω at h1
    have hv : (Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)] ∘
        ((Rew.emb (o := Empty) (ξ := ℕ)).q ∘ ![#0, #0])) = ![&a, &a] := by
      funext k; fin_cases k <;> rfl
    rwa [hv] at h1
  have heq_symm : ∀ a b, eqR a b → eqR b a := fun a b hab => by
    have h1 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp hSymm_in a
    have h2 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp h1 b
    change (Semiformula.nrel (L := ℒₛₑₜ) Language.Set.Rel.eq
        (Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)] ∘
          ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
          ((Rew.emb (o := Empty) (ξ := ℕ)).q.q ∘ ![#1, #0]))) ⋎
      Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.eq
        (Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)] ∘
          ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
          ((Rew.emb (o := Empty) (ξ := ℕ)).q.q ∘ ![#0, #1])))) ∈ Ω at h2
    have hv1 : (Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)] ∘
        ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
        ((Rew.emb (o := Empty) (ξ := ℕ)).q.q ∘ ![#1, #0]))) = ![&a, &b] := by
      funext k; fin_cases k <;> rfl
    have hv2 : (Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)] ∘
        ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
        ((Rew.emb (o := Empty) (ξ := ℕ)).q.q ∘ ![#0, #1]))) = ![&b, &a] := by
      funext k; fin_cases k <;> rfl
    rw [hv1, hv2] at h2
    exact hmp h2 hab
  have heq_trans : ∀ a b c, eqR a b → eqR b c → eqR a c := fun a b c hab hbc => by
    have h1 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp hTrans_in a
    have h2 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp h1 b
    have h3 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp h2 c
    change (Semiformula.nrel (L := ℒₛₑₜ) Language.Set.Rel.eq
        (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ∘
          ((Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
          ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q.q ∘
          ((Rew.emb (o := Empty) (ξ := ℕ)).q.q.q ∘ ![#2, #1])))) ⋎
      (Semiformula.nrel (L := ℒₛₑₜ) Language.Set.Rel.eq
          (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ∘
            ((Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
            ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q.q ∘
            ((Rew.emb (o := Empty) (ξ := ℕ)).q.q.q ∘ ![#1, #0])))) ⋎
        Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.eq
          (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ∘
            ((Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
            ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q.q ∘
            ((Rew.emb (o := Empty) (ξ := ℕ)).q.q.q ∘ ![#2, #0])))))) ∈ Ω at h3
    have hv1 : (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ∘
        ((Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
        ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q.q ∘
        ((Rew.emb (o := Empty) (ξ := ℕ)).q.q.q ∘ ![#2, #1])))) = ![&a, &b] := by
      funext k; fin_cases k <;> rfl
    have hv2 : (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ∘
        ((Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
        ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q.q ∘
        ((Rew.emb (o := Empty) (ξ := ℕ)).q.q.q ∘ ![#1, #0])))) = ![&b, &c] := by
      funext k; fin_cases k <;> rfl
    have hv3 : (Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ∘
        ((Rew.subst ![(&b : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
        ((Rew.subst ![(&a : Semiterm ℒₛₑₜ ℕ 0)]).q.q ∘
        ((Rew.emb (o := Empty) (ξ := ℕ)).q.q.q ∘ ![#2, #0])))) = ![&a, &c] := by
      funext k; fin_cases k <;> rfl
    rw [hv1, hv2, hv3] at h3
    exact hmp (hmp h3 hab) hbc
  have hmem_resp : ∀ a₁ a₂ b₁ b₂, eqR a₁ a₂ → eqR b₁ b₂ → (memR a₁ b₁ ↔ memR a₂ b₂) := by
    have dir : ∀ a₁ a₂ b₁ b₂, eqR a₁ a₂ → eqR b₁ b₂ → memR a₁ b₁ → memR a₂ b₂ := by
      intro a₁ a₂ b₁ b₂ ha hb hmem
      have h1 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp hMemExt_in b₂
      have h2 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp h1 a₂
      have h3 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp h2 b₁
      have h4 := (maxCons_all_iff hcΩ hmaxΩ hhenΩ _).mp h3 a₁
      have h4' : ((Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.eq ![&a₁, &a₂] ⋏
          (Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.eq ![&b₁, &b₂] ⋏ ⊤)) 🡒
          Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.mem ![&a₁, &b₁] 🡒
          Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.mem ![&a₂, &b₂]) ∈ Ω := by
        let f : Semiterm ℒₛₑₜ Empty 4 → Semiterm ℒₛₑₜ ℕ 0 :=
          Rew.subst ![(&a₁ : Semiterm ℒₛₑₜ ℕ 0)] ∘
          (Rew.subst ![(&b₁ : Semiterm ℒₛₑₜ ℕ 0)]).q ∘
          (Rew.subst ![(&a₂ : Semiterm ℒₛₑₜ ℕ 0)]).q.q ∘
          (Rew.subst ![(&b₂ : Semiterm ℒₛₑₜ ℕ 0)]).q.q.q ∘
          (Rew.emb (o := Empty) (ξ := ℕ) (n := 0)).q.q.q.q
        let v₁ : Fin 2 → Semiterm ℒₛₑₜ ℕ 0 :=
          f ∘ (Rew.subst ![#(Fin.addCast 2 (0 : Fin 2)), #(Fin.addNat (0 : Fin 2) 2)] ∘
            (Rew.emb (o := Empty) (ξ := Empty) (n := 2) ∘ Semiterm.bvar))
        let v₂ : Fin 2 → Semiterm ℒₛₑₜ ℕ 0 :=
          f ∘ (Rew.subst ![#(Fin.addCast 2 (1 : Fin 2)), #(Fin.addNat (1 : Fin 2) 2)] ∘
            (Rew.emb (o := Empty) (ξ := Empty) (n := 2) ∘ Semiterm.bvar))
        let v₃ : Fin 2 → Semiterm ℒₛₑₜ ℕ 0 := f ∘ (fun i : Fin 2 => #(i.addCast 2))
        let v₄ : Fin 2 → Semiterm ℒₛₑₜ ℕ 0 := f ∘ (fun i : Fin 2 => #(i.addNat 2))
        have hv1 : v₁ = ![&a₁, &a₂] := by funext k; fin_cases k <;> rfl
        have hv2 : v₂ = ![&b₁, &b₂] := by funext k; fin_cases k <;> rfl
        have hv3 : v₃ = ![&a₁, &b₁] := by funext k; fin_cases k <;> rfl
        have hv4 : v₄ = ![&a₂, &b₂] := by funext k; fin_cases k <;> rfl
        change ((Semiformula.nrel (L := ℒₛₑₜ) Language.Set.Rel.eq v₁ ⋎
            (Semiformula.nrel (L := ℒₛₑₜ) Language.Set.Rel.eq v₂ ⋎ ⊥)) ⋎
          (Semiformula.nrel (L := ℒₛₑₜ) Language.Set.Rel.mem v₃ ⋎
            Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.mem v₄)) ∈ Ω at h4
        rw [hv1, hv2, hv3, hv4] at h4
        exact h4
      have hconj : (Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.eq ![&a₁, &a₂] ⋏
          (Semiformula.rel (L := ℒₛₑₜ) Language.Set.Rel.eq ![&b₁, &b₂] ⋏ ⊤)) ∈ Ω :=
        (maxCons_and_iff hcΩ hmaxΩ _ _).mpr
          ⟨ha, (maxCons_and_iff hcΩ hmaxΩ _ _).mpr ⟨hb, maxCons_verum hcΩ hmaxΩ⟩⟩
      exact hmp (hmp h4' hconj) hmem
    intro a₁ a₂ b₁ b₂ ha hb
    exact ⟨dir a₁ a₂ b₁ b₂ ha hb, dir a₂ a₁ b₂ b₁ (heq_symm _ _ ha) (heq_symm _ _ hb)⟩
  let eqSetoid : Setoid ℕ := ⟨eqR, ⟨heq_refl, fun h => heq_symm _ _ h, fun h1 h2 => heq_trans _ _ _ h1 h2⟩⟩
  let V := Quotient eqSetoid
  let memV : V → V → Prop := Quotient.lift₂ memR (fun a₁ b₁ a₂ b₂ ha hb => propext (hmem_resp a₁ a₂ b₁ b₂ ha hb))
  have : Nonempty V := ⟨Quotient.mk eqSetoid 0⟩
  -- Truth lemma for all Semiproposition ℒₛₑₜ n
  have truth : ∀ {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) (e : Fin n → ℕ),
      semEv V memV (fun i => Quotient.mk eqSetoid (e i)) (Quotient.mk eqSetoid) φ ↔
        (Rew.subst (fun i => &(e i)) ▹ φ) ∈ Ω := by
    intro n φ
    induction φ with
    | verum =>
      intro e
      exact ⟨fun _ => maxCons_verum hcΩ hmaxΩ, fun _ => trivial⟩
    | falsum =>
      intro e
      exact ⟨False.elim, fun h => absurd h (maxCons_falsum hcΩ hmaxΩ)⟩
    | rel r v =>
      intro e
      have hterm : ∀ i, ∃ a : ℕ,
          Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i) = (&a : Semiterm ℒₛₑₜ ℕ 0) ∧
          semTv V (fun j => Quotient.mk eqSetoid (e j)) (Quotient.mk eqSetoid) (v i) =
            Quotient.mk eqSetoid a := fun i => by
        cases hvi : v i with
        | bvar j => exact ⟨e j, rfl, rfl⟩
        | fvar x => exact ⟨x, rfl, rfl⟩
        | func f _ => exact (f : Empty).elim
      cases r with
      | eq =>
        obtain ⟨a, ha1, ha2⟩ := hterm 0
        obtain ⟨b, hb1, hb2⟩ := hterm 1
        have hvec : (Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v =
            ![(&a : Semiterm ℒₛₑₜ ℕ 0), &b] := by
          funext k; fin_cases k <;> simp [ha1, hb1]
        change semTv V _ _ (v 0) = semTv V _ _ (v 1) ↔
          Semiformula.rel Language.Set.Rel.eq
            ((Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v) ∈ Ω
        rw [ha2, hb2, hvec]
        exact Quotient.eq (r := eqSetoid)
      | mem =>
        obtain ⟨a, ha1, ha2⟩ := hterm 0
        obtain ⟨b, hb1, hb2⟩ := hterm 1
        have hvec : (Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v =
            ![(&a : Semiterm ℒₛₑₜ ℕ 0), &b] := by
          funext k; fin_cases k <;> simp [ha1, hb1]
        change memV (semTv V _ _ (v 0)) (semTv V _ _ (v 1)) ↔
          Semiformula.rel Language.Set.Rel.mem
            ((Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v) ∈ Ω
        rw [ha2, hb2, hvec]
        rfl
    | nrel r v =>
      intro e
      have hterm : ∀ i, ∃ a : ℕ,
          Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i) = (&a : Semiterm ℒₛₑₜ ℕ 0) ∧
          semTv V (fun j => Quotient.mk eqSetoid (e j)) (Quotient.mk eqSetoid) (v i) =
            Quotient.mk eqSetoid a := fun i => by
        cases hvi : v i with
        | bvar j => exact ⟨e j, rfl, rfl⟩
        | fvar x => exact ⟨x, rfl, rfl⟩
        | func f _ => exact (f : Empty).elim
      cases r with
      | eq =>
        obtain ⟨a, ha1, ha2⟩ := hterm 0
        obtain ⟨b, hb1, hb2⟩ := hterm 1
        have hvec : (Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v =
            ![(&a : Semiterm ℒₛₑₜ ℕ 0), &b] := by
          funext k; fin_cases k <;> simp [ha1, hb1]
        change semTv V _ _ (v 0) ≠ semTv V _ _ (v 1) ↔
          Semiformula.nrel Language.Set.Rel.eq
            ((Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v) ∈ Ω
        rw [ha2, hb2, hvec]
        have hq : Quotient.mk eqSetoid a ≠ Quotient.mk eqSetoid b ↔ ¬ eqR a b :=
          not_congr (Quotient.eq (r := eqSetoid))
        rw [hq]
        exact ⟨fun hn => (hmaxΩ (Semiformula.rel Language.Set.Rel.eq ![&a, &b])).resolve_left hn,
          fun hmem hpos => maxCons_not_both hcΩ hpos hmem⟩
      | mem =>
        obtain ⟨a, ha1, ha2⟩ := hterm 0
        obtain ⟨b, hb1, hb2⟩ := hterm 1
        have hvec : (Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v =
            ![(&a : Semiterm ℒₛₑₜ ℕ 0), &b] := by
          funext k; fin_cases k <;> simp [ha1, hb1]
        change ¬ memV (semTv V _ _ (v 0)) (semTv V _ _ (v 1)) ↔
          Semiformula.nrel Language.Set.Rel.mem
            ((Rew.subst (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0))) ∘ v) ∈ Ω
        rw [ha2, hb2, hvec]
        exact ⟨fun hn => (hmaxΩ (Semiformula.rel Language.Set.Rel.mem ![&a, &b])).resolve_left hn,
          fun hmem hpos => maxCons_not_both hcΩ hpos hmem⟩
    | and φ ψ ih1 ih2 =>
      intro e
      exact (and_congr (ih1 e) (ih2 e)).trans (maxCons_and_iff hcΩ hmaxΩ _ _).symm
    | or φ ψ ih1 ih2 =>
      intro e
      exact (or_congr (ih1 e) (ih2 e)).trans (maxCons_or_iff hcΩ hmaxΩ _ _).symm
    | all φ ih =>
      intro e
      rw [rew_all, maxCons_all_iff hcΩ hmaxΩ hhenΩ]
      change (∀ d : V, semEv V memV (d :> fun i => Quotient.mk eqSetoid (e i)) (Quotient.mk eqSetoid) φ) ↔ _
      constructor
      · intro hall c
        have hc' := hall (Quotient.mk eqSetoid c)
        have heq : (Quotient.mk eqSetoid c :> fun i => Quotient.mk eqSetoid (e i)) =
            (fun i => Quotient.mk eqSetoid ((c :> e) i)) := by
          funext i; cases i using Fin.cases <;> rfl
        rw [heq, ih (c :> e)] at hc'
        have hrew : ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)/[(&c : Semiterm ℒₛₑₜ ℕ 0)] =
            Rew.subst (fun i => (&((c :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ := by
          change Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ▹
            ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ) = _
          rw [rew_comp_eq]
          apply rew_congr_fv
          · intro i; cases i using Fin.cases <;> rfl
          · intro x _; rfl
        rwa [hrew]
      · intro hall d
        obtain ⟨c, rfl⟩ := Quotient.exists_rep d
        have hc' := hall c
        have hrew : ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)/[(&c : Semiterm ℒₛₑₜ ℕ 0)] =
            Rew.subst (fun i => (&((c :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ := by
          change Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ▹
            ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ) = _
          rw [rew_comp_eq]
          apply rew_congr_fv
          · intro i; cases i using Fin.cases <;> rfl
          · intro x _; rfl
        rw [hrew, ← ih (c :> e)] at hc'
        have heq : (Quotient.mk eqSetoid c :> fun i => Quotient.mk eqSetoid (e i)) =
            (fun i => Quotient.mk eqSetoid ((c :> e) i)) := by
          funext i; cases i using Fin.cases <;> rfl
        rwa [heq]
    | exs φ ih =>
      intro e
      rw [rew_exs, maxCons_exs_iff hcΩ hmaxΩ hhenΩ]
      change (∃ d : V, semEv V memV (d :> fun i => Quotient.mk eqSetoid (e i)) (Quotient.mk eqSetoid) φ) ↔ _
      constructor
      · rintro ⟨d, hd⟩
        obtain ⟨c, rfl⟩ := Quotient.exists_rep d
        have heq : (Quotient.mk eqSetoid c :> fun i => Quotient.mk eqSetoid (e i)) =
            (fun i => Quotient.mk eqSetoid ((c :> e) i)) := by
          funext i; cases i using Fin.cases <;> rfl
        rw [heq, ih (c :> e)] at hd
        have hrew : ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)/[(&c : Semiterm ℒₛₑₜ ℕ 0)] =
            Rew.subst (fun i => (&((c :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ := by
          change Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ▹
            ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ) = _
          rw [rew_comp_eq]
          apply rew_congr_fv
          · intro i; cases i using Fin.cases <;> rfl
          · intro x _; rfl
        exact ⟨c, hrew.symm ▸ hd⟩
      · rintro ⟨c, hc'⟩
        have hrew : ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)/[(&c : Semiterm ℒₛₑₜ ℕ 0)] =
            Rew.subst (fun i => (&((c :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ := by
          change Rew.subst ![(&c : Semiterm ℒₛₑₜ ℕ 0)] ▹
            ((Rew.subst (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ) = _
          rw [rew_comp_eq]
          apply rew_congr_fv
          · intro i; cases i using Fin.cases <;> rfl
          · intro x _; rfl
        rw [hrew, ← ih (c :> e)] at hc'
        have heq : (Quotient.mk eqSetoid c :> fun i => Quotient.mk eqSetoid (e i)) =
            (fun i => Quotient.mk eqSetoid ((c :> e) i)) := by
          funext i; cases i using Fin.cases <;> rfl
        exact ⟨Quotient.mk eqSetoid c, heq.symm ▸ hc'⟩
  -- Specialize truth lemma to sentences
  have truth_sent : ∀ (χ : Sentence ℒₛₑₜ),
      semEv V memV Fin.elim0 Empty.elim χ ↔ Rewriting.emb χ ∈ Ω := fun χ => by
    have h1 := truth (Rewriting.emb χ) Fin.elim0
    have he0 : (fun i : Fin 0 => Quotient.mk eqSetoid (Fin.elim0 i)) = Fin.elim0 :=
      Subsingleton.elim _ _
    rw [he0, semEv_emb] at h1
    have hsub : (Rew.subst (fun i : Fin 0 => &(Fin.elim0 i)) ▹ Rewriting.emb χ) =
        Rewriting.emb χ :=
      (rew_congr_fv (Rew.subst (fun i : Fin 0 => &(Fin.elim0 i))) Rew.id
        (Rewriting.emb χ) (fun i => Fin.elim0 i) (fun _ _ => rfl)).trans (rew_id_eq _)
    exact h1.trans (by rw [hsub])
  have hT : ∀ ψ ∈ T, semEv V memV Fin.elim0 Empty.elim ψ := fun ψ hψ =>
    (truth_sent ψ).mpr (hS₀Ω (Set.mem_insert_of_mem _ ⟨ψ, hψ, rfl⟩))
  have hσ_true : semEv V memV Fin.elim0 Empty.elim σ := hsem V memV hT
  have hσ_in : Rewriting.emb σ ∈ Ω := (truth_sent σ).mp hσ_true
  have hσ_neg : ∼Rewriting.emb σ ∈ Ω := hS₀Ω (Set.mem_insert _ _)
  exact maxCons_not_both hcΩ hσ_in hσ_neg

/- ## Section 3: Arbitrary ZFC Model Operations and Formula Evaluators -/

private structure ZFCModel where
  V : Type
  nonempty : Nonempty V
  mem : V → V → Prop
  sat : ∀ ψ ∈ 𝗭𝗙𝗖, semEv V mem Fin.elim0 Empty.elim ψ

private abbrev evM (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence m) : Prop :=
  semEv ℳ.V ℳ.mem e Empty.elim φ

private def subM (ℳ : ZFCModel) (x y : ℳ.V) : Prop :=
  ∀ z, ℳ.mem z x → ℳ.mem z y

private lemma evM_verum (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V) :
    evM ℳ e (⊤ : SetTheorySemisentence m) ↔ True := Iff.rfl

private lemma evM_falsum (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V) :
    evM ℳ e (⊥ : SetTheorySemisentence m) ↔ False := Iff.rfl

private lemma evM_eq (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (t u : Semiterm ℒₛₑₜ Empty m) :
    evM ℳ e (op(=).operator ![t, u]) ↔
      semTv ℳ.V e Empty.elim t = semTv ℳ.V e Empty.elim u := Iff.rfl

private lemma evM_mem (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (t u : Semiterm ℒₛₑₜ Empty m) :
    evM ℳ e (Semiformula.Operator.Mem.mem.operator ![t, u]) ↔
      ℳ.mem (semTv ℳ.V e Empty.elim t) (semTv ℳ.V e Empty.elim u) := Iff.rfl

private lemma evM_not (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence m) :
    evM ℳ e (∼φ) ↔ ¬ evM ℳ e φ := semEv_neg e Empty.elim φ

private lemma evM_and (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ ψ : SetTheorySemisentence m) :
    evM ℳ e (φ ⋏ ψ) ↔ evM ℳ e φ ∧ evM ℳ e ψ := Iff.rfl

private lemma evM_or (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ ψ : SetTheorySemisentence m) :
    evM ℳ e (φ ⋎ ψ) ↔ evM ℳ e φ ∨ evM ℳ e ψ := Iff.rfl

private lemma evM_imp (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ ψ : SetTheorySemisentence m) :
    evM ℳ e (φ 🡒 ψ) ↔ (evM ℳ e φ → evM ℳ e ψ) := semEv_imp e Empty.elim φ ψ

private lemma evM_iff (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ ψ : SetTheorySemisentence m) :
    evM ℳ e (φ 🡘 ψ) ↔ (evM ℳ e φ ↔ evM ℳ e ψ) := semEv_iff e Empty.elim φ ψ

private lemma evM_all (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence (m + 1)) :
    evM ℳ e (∀¹ φ) ↔ ∀ d : ℳ.V, evM ℳ (d :> e) φ := Iff.rfl

private lemma evM_exs (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence (m + 1)) :
    evM ℳ e (∃¹ φ) ↔ ∃ d : ℳ.V, evM ℳ (d :> e) φ := Iff.rfl

private lemma evM_ballMem (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (t : Semiterm ℒₛₑₜ Empty m) (φ : SetTheorySemisentence (m + 1)) :
    evM ℳ e (Semiformula.ballMem t φ) ↔
      ∀ x, ℳ.mem x (semTv ℳ.V e Empty.elim t) → evM ℳ (x :> e) φ := by
  unfold Semiformula.ballMem
  change (∀ x : ℳ.V, evM ℳ (x :> e)
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] 🡒 φ)) ↔ _
  refine forall_congr' fun x => ?_
  rw [evM_imp]
  change (ℳ.mem x (semTv ℳ.V (x :> e) Empty.elim (Rew.bShift t)) → _) ↔ _
  rw [semTv_bShift]

private lemma evM_bexsMem (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (t : Semiterm ℒₛₑₜ Empty m) (φ : SetTheorySemisentence (m + 1)) :
    evM ℳ e (Semiformula.bexsMem t φ) ↔
      ∃ x, ℳ.mem x (semTv ℳ.V e Empty.elim t) ∧ evM ℳ (x :> e) φ := by
  unfold Semiformula.bexsMem
  change (∃ x : ℳ.V, evM ℳ (x :> e)
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] ⋏ φ)) ↔ _
  refine exists_congr fun x => ?_
  change (ℳ.mem x (semTv ℳ.V (x :> e) Empty.elim (Rew.bShift t)) ∧ _) ↔ _
  rw [semTv_bShift]

private lemma evM_subst (ℳ : ZFCModel) {m k : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence k) (w : Fin k → Semiterm ℒₛₑₜ Empty m) :
    evM ℳ e (φ ⇜ w) ↔ evM ℳ (fun i => semTv ℳ.V e Empty.elim (w i)) φ :=
  semEv_subst e Empty.elim φ w

private lemma evM_subst1 (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence 1) (t₀ : Semiterm ℒₛₑₜ Empty m) :
    evM ℳ e (φ ⇜ ![t₀]) ↔ evM ℳ ![semTv ℳ.V e Empty.elim t₀] φ := by
  rw [evM_subst]
  exact semEv_congr φ (by funext i; fin_cases i; rfl) (fun x => x.elim)

private lemma evM_subst2 (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence 2) (t₀ t₁ : Semiterm ℒₛₑₜ Empty m) :
    evM ℳ e (φ ⇜ ![t₀, t₁]) ↔
      evM ℳ ![semTv ℳ.V e Empty.elim t₀, semTv ℳ.V e Empty.elim t₁] φ := by
  rw [evM_subst]
  exact semEv_congr φ (by funext i; fin_cases i <;> rfl) (fun x => x.elim)

private lemma evM_subst3 (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence 3) (t₀ t₁ t₂ : Semiterm ℒₛₑₜ Empty m) :
    evM ℳ e (φ ⇜ ![t₀, t₁, t₂]) ↔
      evM ℳ ![semTv ℳ.V e Empty.elim t₀, semTv ℳ.V e Empty.elim t₁,
        semTv ℳ.V e Empty.elim t₂] φ := by
  rw [evM_subst]
  exact semEv_congr φ (by funext i; fin_cases i <;> rfl) (fun x => x.elim)

private lemma evM_e0 (ℳ : ZFCModel) (e1 e2 : Fin 0 → ℳ.V) (φ : SetTheorySemisentence 0) :
    evM ℳ e1 φ ↔ evM ℳ e2 φ := by
  rw [Subsingleton.elim e1 e2]

private lemma evM_e1 (ℳ : ZFCModel) (y : ℳ.V) (e : Fin 0 → ℳ.V) (φ : SetTheorySemisentence 1) :
    evM ℳ (y :> e) φ ↔ evM ℳ ![y] φ := by
  rw [Subsingleton.elim e ![]]

/- `EvalTermAt` combinators for arbitrary `ℳ : ZFCModel` -/

private def EvalTermAt (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (Ψ : SetTheorySemisentence (m + 1)) (val : ℳ.V) : Prop :=
  ∀ y : ℳ.V, evM ℳ (y :> e) Ψ ↔ y = val

private def DefinesConst (ℳ : ZFCModel) (Ψ : SetTheorySemisentence 1) (c : ℳ.V) : Prop :=
  ∀ y : ℳ.V, evM ℳ ![y] Ψ ↔ y = c

private lemma et_bvar_succ (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V) (i : Fin m) :
    EvalTermAt ℳ e (op(=).operator (#0 :> #(i.succ) :> ![])) (e i) := by
  intro y
  rw [evM_eq]
  rfl

private lemma et_bvar1 (ℳ : ZFCModel) {m : ℕ} (a : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> e) (op(=).operator (#0 :> #1 :> ![])) a :=
  et_bvar_succ ℳ (a :> e) 0

private lemma et_bvar2 (ℳ : ZFCModel) {m : ℕ} (a b : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> e) (op(=).operator (#0 :> #2 :> ![])) b :=
  et_bvar_succ ℳ (a :> b :> e) 1

private lemma et_bvar3 (ℳ : ZFCModel) {m : ℕ} (a b c : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> c :> e) (op(=).operator (#0 :> #3 :> ![])) c :=
  et_bvar_succ ℳ (a :> b :> c :> e) 2

private lemma et_bvar4 (ℳ : ZFCModel) {m : ℕ} (a b c d : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> c :> d :> e) (op(=).operator (#0 :> #4 :> ![])) d :=
  et_bvar_succ ℳ (a :> b :> c :> d :> e) 3

private lemma et_bvar5 (ℳ : ZFCModel) {m : ℕ} (a b c d f : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> c :> d :> f :> e) (op(=).operator (#0 :> #5 :> ![])) f :=
  et_bvar_succ ℳ (a :> b :> c :> d :> f :> e) 4

private lemma et_bvar6 (ℳ : ZFCModel) {m : ℕ} (a b c d f g : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> c :> d :> f :> g :> e) (op(=).operator (#0 :> #6 :> ![])) g :=
  et_bvar_succ ℳ (a :> b :> c :> d :> f :> g :> e) 5

private lemma et_bvar7 (ℳ : ZFCModel) {m : ℕ} (a b c d f g h : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> c :> d :> f :> g :> h :> e) (op(=).operator (#0 :> #7 :> ![])) h :=
  et_bvar_succ ℳ (a :> b :> c :> d :> f :> g :> h :> e) 6

private lemma et_bvar8 (ℳ : ZFCModel) {m : ℕ} (a b c d f g h i : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> c :> d :> f :> g :> h :> i :> e)
      (op(=).operator (#0 :> #8 :> ![])) i :=
  et_bvar_succ ℳ (a :> b :> c :> d :> f :> g :> h :> i :> e) 7

private lemma et_bvar9 (ℳ : ZFCModel) {m : ℕ} (a b c d f g h i j : ℳ.V) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ (a :> b :> c :> d :> f :> g :> h :> i :> j :> e)
      (op(=).operator (#0 :> #9 :> ![])) j :=
  et_bvar_succ ℳ (a :> b :> c :> d :> f :> g :> h :> i :> j :> e) 8

private lemma ev_nestFunc0_raw (ℳ : ZFCModel) {m : ℕ} (φ : SetTheorySemisentence 1)
    (y : ℳ.V) (e : Fin m → ℳ.V) :
    evM ℳ (y :> e) (Semiformula.nestFormulaeFunc φ ![]) ↔ evM ℳ ![y] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [evM_imp, evM_verum, evM_subst]
  simp only [true_imp_iff]
  refine semEv_congr φ ?_ (fun x => x.elim)
  funext i; fin_cases i; simp [Fin.addNat]

private lemma et_const0 {ℳ : ZFCModel} {m : ℕ} {Ψ : SetTheorySemisentence 1} {c : ℳ.V}
    (hΨ : DefinesConst ℳ Ψ c) (e : Fin m → ℳ.V) :
    EvalTermAt ℳ e (Semiformula.nestFormulaeFunc Ψ ![]) c := by
  intro y
  rw [ev_nestFunc0_raw]
  exact hΨ y

private lemma ev_nestFunc1_raw {ℳ : ZFCModel} {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ℳ.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ℳ.V}
    (h₀ : EvalTermAt ℳ e Ψ₀ v₀) (y : ℳ.V) :
    evM ℳ (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀]) ↔ evM ℳ ![y, v₀] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [evM_all]
  refine (?_ : _ ↔ ∀ d₀ : ℳ.V, d₀ = v₀ → evM ℳ ![y, d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [evM_imp, evM_and, evM_verum, and_true, evM_subst, evM_subst]
  have he0 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin 1).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he1 : (fun k : Fin 2 =>
      semTv ℳ.V (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 1) :> fun i : Fin 1 => #(i.addCast m.succ)) k)) =
      ![y, d₀] := by
    funext k
    fin_cases k <;> simp [Fin.addNat, Fin.addCast]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma et_comp1 {ℳ : ZFCModel} {m : ℕ} {φ : SetTheorySemisentence 2} {G : ℳ.V → ℳ.V}
    (hφ : ∀ y x₀, evM ℳ ![y, x₀] φ ↔ y = G x₀)
    {e : Fin m → ℳ.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ℳ.V}
    (h₀ : EvalTermAt ℳ e Ψ₀ v₀) :
    EvalTermAt ℳ e (Semiformula.nestFormulaeFunc φ ![Ψ₀]) (G v₀) := by
  intro y
  rw [ev_nestFunc1_raw φ h₀ y, hφ y v₀]

private lemma ev_nestFunc2_raw {ℳ : ZFCModel} {m : ℕ} (φ : SetTheorySemisentence 3)
    {e : Fin m → ℳ.V}
    {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ℳ.V}
    (h₀ : EvalTermAt ℳ e Ψ₀ v₀) (h₁ : EvalTermAt ℳ e Ψ₁ v₁) (y : ℳ.V) :
    evM ℳ (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) ↔ evM ℳ ![y, v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [evM_all]
  refine (?_ : _ ↔ ∀ d₁ d₀ : ℳ.V, (d₀ = v₀ ∧ d₁ = v₁) → evM ℳ ![y, d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [evM_all]
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [evM_imp, evM_and, evM_and, evM_verum, and_true, evM_subst, evM_subst, evM_subst]
  have he_psi0 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he_psi1 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((1 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1]
    · simp [Fin.addNat]
  have he_phi : (fun k : Fin 3 =>
      semTv ℳ.V (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 2) :> fun i : Fin 2 => #(i.addCast m.succ)) k)) =
      ![y, d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · simp [Fin.addNat]
    · simp [Fin.addCast]
    · change semTv ℳ.V (d₀ :> d₁ :> y :> e) Empty.elim (#((1 : Fin 2).addCast m.succ)) = d₁
      simp [h1]
  rw [he_psi0, he_psi1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma et_comp2 {ℳ : ZFCModel} {m : ℕ} {φ : SetTheorySemisentence 3}
    {G : ℳ.V → ℳ.V → ℳ.V}
    (hφ : ∀ y x₀ x₁, evM ℳ ![y, x₀, x₁] φ ↔ y = G x₀ x₁)
    {e : Fin m → ℳ.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ℳ.V}
    (h₀ : EvalTermAt ℳ e Ψ₀ v₀) (h₁ : EvalTermAt ℳ e Ψ₁ v₁) :
    EvalTermAt ℳ e (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) (G v₀ v₁) := by
  intro y
  rw [ev_nestFunc2_raw φ h₀ h₁ y, hφ y v₀ v₁]

private lemma ev_nest1 {ℳ : ZFCModel} {m : ℕ} (φ : SetTheorySemisentence 1)
    {e : Fin m → ℳ.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ℳ.V}
    (h₀ : EvalTermAt ℳ e Ψ₀ v₀) :
    evM ℳ e (Semiformula.nestFormulae φ ![Ψ₀]) ↔ evM ℳ ![v₀] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [evM_all]
  refine (?_ : _ ↔ ∀ d₀ : ℳ.V, d₀ = v₀ → evM ℳ ![d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [evM_imp, evM_and, evM_verum, and_true, evM_subst, evM_subst]
  have he0 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (d₀ :> e) Empty.elim
        ((#((0 : Fin 1).addCast m) :> fun j : Fin m => #(j.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he1 : (fun k : Fin 1 =>
      semTv ℳ.V (d₀ :> e) Empty.elim (#(k.addCast m))) = ![d₀] := by
    funext k; fin_cases k; simp [Fin.addCast]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma ev_nest2 {ℳ : ZFCModel} {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ℳ.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ℳ.V}
    (h₀ : EvalTermAt ℳ e Ψ₀ v₀) (h₁ : EvalTermAt ℳ e Ψ₁ v₁) :
    evM ℳ e (Semiformula.nestFormulae φ ![Ψ₀, Ψ₁]) ↔ evM ℳ ![v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [evM_all]
  refine (?_ : _ ↔ ∀ d₁ d₀ : ℳ.V, (d₀ = v₀ ∧ d₁ = v₁) → evM ℳ ![d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [evM_all]
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [evM_imp, evM_and, evM_and, evM_verum, and_true, evM_subst, evM_subst, evM_subst]
  have he0 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (d₀ :> d₁ :> e) Empty.elim
        ((#((0 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he1 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (d₀ :> d₁ :> e) Empty.elim
        ((#((1 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1]
    · simp [Fin.addNat]
  have he_phi : (fun k : Fin 2 =>
      semTv ℳ.V (d₀ :> d₁ :> e) Empty.elim (#(k.addCast m))) = ![d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · simp [Fin.addCast]
    · change semTv ℳ.V (d₀ :> d₁ :> e) Empty.elim (#((1 : Fin 2).addCast m)) = d₁
      simp [h1]
  rw [he0, he1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma ev_faf_eq {ℳ : ZFCModel} {m : ℕ} {e : Fin m → ℳ.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ℳ.V} (h₁ : EvalTermAt ℳ e T₁ v₁) (h₂ : EvalTermAt ℳ (v₁ :> e) T₂ v₂) :
    evM ℳ e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ = v₂ := by
  rw [evM_all]
  constructor
  · intro h
    have hv1 := (evM_imp ℳ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [evM_all] at hv1
    have hv2 := (evM_imp ℳ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [evM_eq] at hv2
    exact hv2
  · intro heq d₁
    rw [evM_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [evM_all]
    intro d₂
    rw [evM_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [evM_eq]
    exact heq

private lemma ev_faf_ne {ℳ : ZFCModel} {m : ℕ} {e : Fin m → ℳ.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ℳ.V} (h₁ : EvalTermAt ℳ e T₁ v₁) (h₂ : EvalTermAt ℳ (v₁ :> e) T₂ v₂) :
    evM ℳ e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ ≠ v₂ := by
  rw [evM_all]
  constructor
  · intro h
    have hv1 := (evM_imp ℳ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [evM_all] at hv1
    have hv2 := (evM_imp ℳ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [evM_not, evM_eq] at hv2
    exact hv2
  · intro hne d₁
    rw [evM_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [evM_all]
    intro d₂
    rw [evM_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [evM_not, evM_eq]
    exact hne

private lemma ev_faf_mem {ℳ : ZFCModel} {m : ℕ} {e : Fin m → ℳ.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ℳ.V} (h₁ : EvalTermAt ℳ e T₁ v₁) (h₂ : EvalTermAt ℳ (v₁ :> e) T₂ v₂) :
    evM ℳ e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      ℳ.mem v₁ v₂ := by
  rw [evM_all]
  constructor
  · intro h
    have hv1 := (evM_imp ℳ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [evM_all] at hv1
    have hv2 := (evM_imp ℳ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [evM_mem] at hv2
    exact hv2
  · intro hmem d₁
    rw [evM_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [evM_all]
    intro d₂
    rw [evM_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [evM_mem]
    exact hmem

private lemma ev_faf_notMem {ℳ : ZFCModel} {m : ℕ} {e : Fin m → ℳ.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ℳ.V} (h₁ : EvalTermAt ℳ e T₁ v₁) (h₂ : EvalTermAt ℳ (v₁ :> e) T₂ v₂) :
    evM ℳ e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      ¬ ℳ.mem v₁ v₂ := by
  rw [evM_all]
  constructor
  · intro h
    have hv1 := (evM_imp ℳ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [evM_all] at hv1
    have hv2 := (evM_imp ℳ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [evM_not, evM_mem] at hv2
    exact hv2
  · intro hnm d₁
    rw [evM_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [evM_all]
    intro d₂
    rw [evM_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [evM_not, evM_mem]
    exact hnm

private lemma ev_faf_ball {ℳ : ZFCModel} {m : ℕ} {e : Fin m → ℳ.V}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ℳ.V}
    (h₁ : EvalTermAt ℳ e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    evM ℳ e (∀¹ (T₁ 🡒 Semiformula.ballMem (#0) φ)) ↔
      ∀ x, ℳ.mem x v₁ → evM ℳ (x :> v₁ :> e) φ := by
  rw [evM_all]
  constructor
  · intro h x hx
    have hv1 := (evM_imp ℳ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [evM_ballMem] at hv1
    exact hv1 x hx
  · intro h d₁
    rw [evM_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [evM_ballMem]
    exact h

private lemma ev_faf_bexs {ℳ : ZFCModel} {m : ℕ} {e : Fin m → ℳ.V}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ℳ.V}
    (h₁ : EvalTermAt ℳ e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    evM ℳ e (∀¹ (T₁ 🡒 Semiformula.bexsMem (#0) φ)) ↔
      ∃ x, ℳ.mem x v₁ ∧ evM ℳ (x :> v₁ :> e) φ := by
  rw [evM_all]
  constructor
  · intro h
    have hv1 := (evM_imp ℳ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [evM_bexsMem] at hv1
    exact hv1
  · intro h d₁
    rw [evM_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [evM_bexsMem]
    exact h

private lemma ev_existsUnique (ℳ : ZFCModel) {m : ℕ} (e : Fin m → ℳ.V)
    (φ : SetTheorySemisentence (m + 1)) :
    evM ℳ e (∃¹! φ) ↔ ∃! y, evM ℳ (y :> e) φ := by
  unfold Semiformula.existsUnique ExistsUnique
  rw [evM_exs]
  refine exists_congr fun y => ?_
  rw [evM_and, evM_subst, evM_all]
  have he1 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 1)) k)) = (y :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp [BinderNotation.finSuccItr]
  rw [he1]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  rw [evM_imp, evM_subst, evM_eq]
  have he2 : (fun k : Fin (m + 1) =>
      semTv ℳ.V (z :> y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 2)) k)) = (z :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp [BinderNotation.finSuccItr]
  rw [he2]
  rfl

/- Unpacking ZFC Axioms in `ℳ` -/

private lemma extM (ℳ : ZFCModel) {x y : ℳ.V} (h : ∀ z, ℳ.mem z x ↔ ℳ.mem z y) : x = y := by
  have hax := ℳ.sat Axiom.extentionality (Or.inl ZermeloFraenkel.axiom_of_extentionality)
  have hxy := hax x y
  rw [semEv_iff] at hxy
  refine hxy.mpr fun z => ?_
  rw [semEv_iff]
  exact h z

private lemma exists_emptyM (ℳ : ZFCModel) : ∃ e : ℳ.V, ∀ y, ¬ ℳ.mem y e := by
  have hax := ℳ.sat Axiom.empty (Or.inl ZermeloFraenkel.axiom_of_empty_set)
  obtain ⟨e, he⟩ := hax
  exact ⟨e, fun y => by have hy := he y; rw [semEv_neg] at hy; exact hy⟩

private noncomputable def emptyM (ℳ : ZFCModel) : ℳ.V := (exists_emptyM ℳ).choose

private lemma not_mem_emptyM (ℳ : ZFCModel) (y : ℳ.V) : ¬ ℳ.mem y (emptyM ℳ) :=
  (exists_emptyM ℳ).choose_spec y

private lemma eq_emptyM_iff (ℳ : ZFCModel) (x : ℳ.V) : x = emptyM ℳ ↔ ∀ y, ¬ ℳ.mem y x := by
  constructor
  · rintro rfl; exact not_mem_emptyM ℳ
  · intro h; exact extM ℳ fun z => ⟨fun hz => (h z hz).elim, fun hz => (not_mem_emptyM ℳ z hz).elim⟩

private lemma ev_isEmpty (ℳ : ZFCModel) (x : ℳ.V) :
    evM ℳ ![x] SetTheory.isEmpty ↔ x = emptyM ℳ := by
  unfold SetTheory.isEmpty
  rw [evM_all]
  refine (forall_congr' fun y => by rw [evM_not, evM_mem]; rfl).trans (eq_emptyM_iff ℳ x).symm

private lemma ev_isNonempty (ℳ : ZFCModel) (x : ℳ.V) :
    evM ℳ ![x] SetTheory.isNonempty ↔ ∃ y, ℳ.mem y x := by
  unfold SetTheory.isNonempty
  rw [evM_exs]
  exact exists_congr fun y => by rw [evM_mem]; rfl

private lemma ev_isSubsetOf (ℳ : ZFCModel) (x y : ℳ.V) :
    evM ℳ ![x, y] SetTheory.isSubsetOf ↔ subM ℳ x y := by
  unfold SetTheory.isSubsetOf subM
  rw [evM_ballMem]
  exact forall_congr' fun z => imp_congr Iff.rfl (by rw [evM_mem]; rfl)

private lemma exists_doubletonM (ℳ : ZFCModel) (x y : ℳ.V) :
    ∃ z : ℳ.V, ∀ w, ℳ.mem w z ↔ w = x ∨ w = y := by
  have hax := ℳ.sat Axiom.pairing (Or.inl ZermeloFraenkel.axiom_of_pairing)
  obtain ⟨z, hz⟩ := hax x y
  refine ⟨z, fun w => ?_⟩
  have hw := hz w
  rw [semEv_iff] at hw
  exact hw

private noncomputable def doubletonM (ℳ : ZFCModel) (x y : ℳ.V) : ℳ.V :=
  (exists_doubletonM ℳ x y).choose

private lemma mem_doubletonM (ℳ : ZFCModel) (x y w : ℳ.V) :
    ℳ.mem w (doubletonM ℳ x y) ↔ w = x ∨ w = y :=
  (exists_doubletonM ℳ x y).choose_spec w

private noncomputable def singletonM (ℳ : ZFCModel) (x : ℳ.V) : ℳ.V := doubletonM ℳ x x

private lemma mem_singletonM (ℳ : ZFCModel) (x w : ℳ.V) :
    ℳ.mem w (singletonM ℳ x) ↔ w = x := by
  rw [singletonM, mem_doubletonM, or_self]

private lemma exists_sUnionM (ℳ : ZFCModel) (x : ℳ.V) :
    ∃ y : ℳ.V, ∀ z, ℳ.mem z y ↔ ∃ w, ℳ.mem w x ∧ ℳ.mem z w := by
  have hax := ℳ.sat Axiom.union (Or.inl ZermeloFraenkel.axiom_of_union)
  obtain ⟨y, hy⟩ := hax x
  refine ⟨y, fun z => ?_⟩
  have hz := hy z
  rw [semEv_iff] at hz
  change (ℳ.mem z y ↔ evM ℳ (z :> y :> x :> Fin.elim0)
    (Semiformula.bexsMem (#2) (Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) at hz
  rw [evM_bexsMem] at hz
  exact hz

private noncomputable def sUnionM (ℳ : ZFCModel) (x : ℳ.V) : ℳ.V :=
  (exists_sUnionM ℳ x).choose

private lemma mem_sUnionM (ℳ : ZFCModel) (x z : ℳ.V) :
    ℳ.mem z (sUnionM ℳ x) ↔ ∃ w, ℳ.mem w x ∧ ℳ.mem z w :=
  (exists_sUnionM ℳ x).choose_spec z

private noncomputable def unionM (ℳ : ZFCModel) (x y : ℳ.V) : ℳ.V :=
  sUnionM ℳ (doubletonM ℳ x y)

private lemma mem_unionM (ℳ : ZFCModel) (x y z : ℳ.V) :
    ℳ.mem z (unionM ℳ x y) ↔ ℳ.mem z x ∨ ℳ.mem z y := by
  rw [unionM, mem_sUnionM]
  constructor
  · rintro ⟨w, hw, hzw⟩
    rcases (mem_doubletonM ℳ x y w).mp hw with rfl | rfl
    · exact Or.inl hzw
    · exact Or.inr hzw
  · rintro (hzx | hzy)
    · exact ⟨x, (mem_doubletonM ℳ x y x).mpr (Or.inl rfl), hzx⟩
    · exact ⟨y, (mem_doubletonM ℳ x y y).mpr (Or.inr rfl), hzy⟩

private noncomputable def insertM (ℳ : ZFCModel) (x y : ℳ.V) : ℳ.V :=
  unionM ℳ (singletonM ℳ x) y

private lemma mem_insertM (ℳ : ZFCModel) (x y z : ℳ.V) :
    ℳ.mem z (insertM ℳ x y) ↔ z = x ∨ ℳ.mem z y := by
  rw [insertM, mem_unionM, mem_singletonM]

private lemma sUnionM_singleton (ℳ : ZFCModel) (x : ℳ.V) :
    sUnionM ℳ (singletonM ℳ x) = x := by
  refine extM ℳ fun z => ?_
  rw [mem_sUnionM]
  constructor
  · rintro ⟨w, hw, hzw⟩
    rw [(mem_singletonM ℳ x w).mp hw] at hzw
    exact hzw
  · intro hzx
    exact ⟨x, (mem_singletonM ℳ x x).mpr rfl, hzx⟩

private lemma exists_powerM (ℳ : ZFCModel) (x : ℳ.V) :
    ∃ y : ℳ.V, ∀ z, ℳ.mem z y ↔ subM ℳ z x := by
  have hax := ℳ.sat Axiom.power (Or.inl ZermeloFraenkel.axiom_of_power_set)
  obtain ⟨y, hy⟩ := hax x
  refine ⟨y, fun z => ?_⟩
  have hz := hy z
  rw [semEv_iff] at hz
  refine hz.trans ?_
  exact (evM_subst2 ℳ _ SetTheory.isSubsetOf #0 #2).trans (ev_isSubsetOf ℳ z x)

private noncomputable def powerM (ℳ : ZFCModel) (x : ℳ.V) : ℳ.V :=
  (exists_powerM ℳ x).choose

private lemma mem_powerM (ℳ : ZFCModel) (x z : ℳ.V) :
    ℳ.mem z (powerM ℳ x) ↔ subM ℳ z x :=
  (exists_powerM ℳ x).choose_spec z

private lemma foundM (ℳ : ZFCModel) {x : ℳ.V} (hne : ∃ y, ℳ.mem y x) :
    ∃ y, ℳ.mem y x ∧ ∀ z, ℳ.mem z x → ¬ ℳ.mem z y := by
  have hax := ℳ.sat Axiom.foundation (Or.inl ZermeloFraenkel.axiom_of_foundation)
  have hx := (evM_imp ℳ _ _ _).mp (hax x)
    ((evM_subst1 ℳ _ SetTheory.isNonempty #0).mpr ((ev_isNonempty ℳ x).mpr hne))
  rw [evM_bexsMem] at hx
  obtain ⟨y, hyx, hymin⟩ := hx
  rw [evM_ballMem] at hymin
  refine ⟨y, hyx, fun z hzx => ?_⟩
  have hzy := hymin z hzx
  rw [evM_not, evM_mem] at hzy
  exact hzy

private lemma mem_irrefl (ℳ : ZFCModel) (x : ℳ.V) : ¬ ℳ.mem x x := by
  intro hxx
  obtain ⟨y, hy, hmin⟩ := foundM ℳ (x := singletonM ℳ x) ⟨x, (mem_singletonM ℳ x x).mpr rfl⟩
  rw [(mem_singletonM ℳ x y).mp hy] at hmin
  exact hmin x ((mem_singletonM ℳ x x).mpr rfl) hxx

private lemma mem_asymm (ℳ : ZFCModel) {a b : ℳ.V} (hab : ℳ.mem a b) : ¬ ℳ.mem b a := by
  intro hba
  obtain ⟨y, hy, hmin⟩ := foundM ℳ (x := doubletonM ℳ a b) ⟨a, (mem_doubletonM ℳ a b a).mpr (Or.inl rfl)⟩
  rcases (mem_doubletonM ℳ a b y).mp hy with hya | hyb
  · rw [hya] at hmin; exact hmin b ((mem_doubletonM ℳ a b b).mpr (Or.inr rfl)) hba
  · rw [hyb] at hmin; exact hmin a ((mem_doubletonM ℳ a b a).mpr (Or.inl rfl)) hab

private lemma exists_sepM (ℳ : ZFCModel) (φ : SetTheorySemiproposition 1)
    (ε : ℕ → ℳ.V) (x : ℳ.V) :
    ∃ y : ℳ.V, ∀ z, ℳ.mem z y ↔ ℳ.mem z x ∧ semEv ℳ.V ℳ.mem ![z] ε φ := by
  have hax := ℳ.sat (Axiom.separationSchema φ) (Or.inl (ZermeloFraenkel.axiom_of_separation φ))
  have hinst := semEv_univCl_mp _ hax ε
  obtain ⟨y, hy⟩ := hinst x
  refine ⟨y, fun z => ?_⟩
  have hz := hy z
  rw [semEv_iff] at hz
  change (ℳ.mem z y ↔ ℳ.mem z x ∧ semEv ℳ.V ℳ.mem (z :> y :> x :> Fin.elim0) ε (φ ⇜ ![#0])) at hz
  rw [semEv_subst] at hz
  refine hz.trans (and_congr Iff.rfl (semEv_congr φ ?_ (fun _ _ => rfl)))
  funext i; fin_cases i; rfl

private lemma exists_sepM_sent (ℳ : ZFCModel) {k : ℕ} (ψ : SetTheorySemisentence (k + 1))
    (p : Fin k → ℳ.V) (x : ℳ.V) :
    ∃ y : ℳ.V, ∀ z, ℳ.mem z y ↔ ℳ.mem z x ∧ evM ℳ (z :> p) ψ := by
  let φ : SetTheorySemiproposition 1 := (Rewriting.emb ψ) ⇜ (#0 :> fun i : Fin k => &(i.val))
  let ε : ℕ → ℳ.V := fun n => if h : n < k then p ⟨n, h⟩ else emptyM ℳ
  obtain ⟨y, hy⟩ := exists_sepM ℳ φ ε x
  refine ⟨y, fun z => (hy z).trans (and_congr Iff.rfl ?_)⟩
  dsimp only [φ]
  rw [semEv_subst, semEv_emb]
  refine semEv_congr ψ ?_ (fun a => a.elim)
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    change semTv ℳ.V ![z] ε &(j.val) = p j
    simp [ε, j.isLt]

/- Evaluators for Basic Set Operations in `ℳ` -/

private lemma ev_doubleton (ℳ : ZFCModel) (p x y : ℳ.V) :
    evM ℳ ![p, x, y] SetTheory.doubleton.dfn ↔ p = doubletonM ℳ x y := by
  unfold SetTheory.doubleton.dfn
  rw [evM_all]
  refine (forall_congr' fun z => by
    rw [evM_iff, evM_mem, evM_or, evM_eq, evM_eq]).trans ?_
  constructor
  · intro h; exact extM ℳ fun z => (h z).trans (mem_doubletonM ℳ x y z).symm
  · rintro rfl z; exact mem_doubletonM ℳ x y z

private lemma ev_singleton (ℳ : ZFCModel) (p x : ℳ.V) :
    evM ℳ ![p, x] SetTheory.singleton.dfn ↔ p = singletonM ℳ x := by
  unfold SetTheory.singleton.dfn singletonM
  exact (evM_subst3 ℳ _ SetTheory.doubleton.dfn #0 #1 #1).trans (ev_doubleton ℳ p x x)

private lemma ev_sUnion (ℳ : ZFCModel) (u x : ℳ.V) :
    evM ℳ ![u, x] SetTheory.sUnion.dfn ↔ u = sUnionM ℳ x := by
  unfold SetTheory.sUnion.dfn
  rw [evM_all]
  refine (?_ : _ ↔ ∀ z : ℳ.V, ℳ.mem z u ↔ ∃ w, ℳ.mem w x ∧ ℳ.mem z w).trans ?_
  · refine forall_congr' fun z => ?_
    rw [evM_iff, evM_mem, evM_bexsMem]
    exact iff_congr Iff.rfl (exists_congr fun w => and_congr_right fun _ => by rw [evM_mem]; rfl)
  · constructor
    · intro h; exact extM ℳ fun z => (h z).trans (mem_sUnionM ℳ x z).symm
    · rintro rfl z; exact mem_sUnionM ℳ x z

private lemma ev_union (ℳ : ZFCModel) (u x y : ℳ.V) :
    evM ℳ ![u, x, y] SetTheory.union.dfn ↔ u = unionM ℳ x y := by
  unfold SetTheory.union.dfn unionM
  rw [evM_all]
  refine (?_ : _ ↔ ∀ d : ℳ.V, d = doubletonM ℳ x y → u = sUnionM ℳ d).trans
    ⟨fun h => h (doubletonM ℳ x y) rfl, fun h d hd => hd ▸ h⟩
  refine forall_congr' fun d => ?_
  rw [evM_imp]
  exact imp_congr
    ((evM_subst3 ℳ _ SetTheory.doubleton.dfn #0 #2 #3).trans (ev_doubleton ℳ d x y))
    ((evM_subst2 ℳ _ SetTheory.sUnion.dfn #1 #0).trans (ev_sUnion ℳ u d))

private lemma ev_insert (ℳ : ZFCModel) (u x y : ℳ.V) :
    evM ℳ ![u, x, y] SetTheory.insert.dfn ↔ u = insertM ℳ x y := by
  unfold SetTheory.insert.dfn insertM
  rw [evM_all]
  refine (?_ : _ ↔ ∀ s : ℳ.V, s = singletonM ℳ x → u = unionM ℳ s y).trans
    ⟨fun h => h (singletonM ℳ x) rfl, fun h s hs => hs ▸ h⟩
  refine forall_congr' fun s => ?_
  rw [evM_imp]
  exact imp_congr
    ((evM_subst2 ℳ _ SetTheory.singleton.dfn #0 #2).trans (ev_singleton ℳ s x))
    ((evM_subst3 ℳ _ SetTheory.union.dfn #1 #0 #3).trans (ev_union ℳ u s y))

private lemma exists_sInterM (ℳ : ZFCModel) (x : ℳ.V) :
    ∃ u : ℳ.V, ∀ z, ℳ.mem z u ↔ (∃ y, ℳ.mem y x) ∧ ∀ y, ℳ.mem y x → ℳ.mem z y := by
  let ψ : SetTheorySemisentence 2 := “z x. !isNonempty x ∧ ∀ y ∈ x, z ∈ y”
  obtain ⟨u, hu⟩ := exists_sepM_sent ℳ ψ ![x] (sUnionM ℳ x)
  refine ⟨u, fun z => (hu z).trans ?_⟩
  have hψ : evM ℳ ![z, x] ψ ↔ (∃ y, ℳ.mem y x) ∧ ∀ y, ℳ.mem y x → ℳ.mem z y := by
    dsimp only [ψ]
    rw [evM_and, evM_ballMem]
    refine and_congr ((evM_subst1 ℳ _ SetTheory.isNonempty #1).trans (ev_isNonempty ℳ x)) ?_
    exact forall_congr' fun y => imp_congr Iff.rfl (by rw [evM_mem]; rfl)
  rw [hψ]
  constructor
  · exact And.right
  · rintro ⟨⟨y₀, hy₀⟩, hall⟩
    exact ⟨(mem_sUnionM ℳ x z).mpr ⟨y₀, hy₀, hall y₀ hy₀⟩, ⟨y₀, hy₀⟩, hall⟩

private noncomputable def sInterM (ℳ : ZFCModel) (x : ℳ.V) : ℳ.V :=
  (exists_sInterM ℳ x).choose

private lemma mem_sInterM (ℳ : ZFCModel) (x z : ℳ.V) :
    ℳ.mem z (sInterM ℳ x) ↔ (∃ y, ℳ.mem y x) ∧ ∀ y, ℳ.mem y x → ℳ.mem z y :=
  (exists_sInterM ℳ x).choose_spec z

private lemma ev_sInter (ℳ : ZFCModel) (u x : ℳ.V) :
    evM ℳ ![u, x] SetTheory.sInter.dfn ↔ u = sInterM ℳ x := by
  unfold SetTheory.sInter.dfn
  rw [evM_all]
  refine (?_ : _ ↔ ∀ z : ℳ.V, ℳ.mem z u ↔ (∃ y, ℳ.mem y x) ∧ ∀ y, ℳ.mem y x → ℳ.mem z y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [evM_iff, evM_mem, evM_and, evM_ballMem]
    refine iff_congr Iff.rfl (and_congr ((evM_subst1 ℳ _ SetTheory.isNonempty #2).trans
      (ev_isNonempty ℳ x)) ?_)
    exact forall_congr' fun y => imp_congr Iff.rfl (by rw [evM_mem]; rfl)
  · constructor
    · intro h; exact extM ℳ fun z => (h z).trans (mem_sInterM ℳ x z).symm
    · rintro rfl z; exact mem_sInterM ℳ x z

/- Kuratowski Pairs, Projections, and Cartesian Products in `ℳ` -/

private noncomputable def kpairM (ℳ : ZFCModel) (x y : ℳ.V) : ℳ.V :=
  doubletonM ℳ (singletonM ℳ x) (doubletonM ℳ x y)

private lemma ev_kpair (ℳ : ZFCModel) (k x y : ℳ.V) :
    evM ℳ ![k, x, y] SetTheory.kpair.dfn ↔ k = kpairM ℳ x y := by
  unfold SetTheory.kpair.dfn kpairM
  rw [evM_all]
  refine (?_ : _ ↔ ∀ x' : ℳ.V, x' = singletonM ℳ x →
      ∀ z : ℳ.V, z = doubletonM ℳ x y → k = doubletonM ℳ x' z).trans
    ⟨fun h => h (singletonM ℳ x) rfl (doubletonM ℳ x y) rfl,
     fun h x' hx' z hz => by subst hx' hz; exact h⟩
  refine forall_congr' fun x' => ?_
  rw [evM_imp, evM_all]
  refine imp_congr ((evM_subst2 ℳ _ SetTheory.singleton.dfn #0 #2).trans (ev_singleton ℳ x' x))
    (forall_congr' fun z => ?_)
  rw [evM_imp]
  exact imp_congr
    ((evM_subst3 ℳ _ SetTheory.doubleton.dfn #0 #3 #4).trans (ev_doubleton ℳ z x y))
    ((evM_subst3 ℳ _ SetTheory.doubleton.dfn #2 #1 #0).trans (ev_doubleton ℳ k x' z))

private noncomputable def pi1M (ℳ : ZFCModel) (w : ℳ.V) : ℳ.V :=
  sUnionM ℳ (sInterM ℳ w)

private lemma exists_pi2SepM (ℳ : ZFCModel) (w : ℳ.V) :
    ∃ s : ℳ.V, ∀ z, ℳ.mem z s ↔
      ℳ.mem z (sUnionM ℳ w) ∧ (ℳ.mem z (sInterM ℳ w) → sUnionM ℳ w = sInterM ℳ w) := by
  let ψ : SetTheorySemisentence 3 := “z u i. z ∈ i → u = i”
  obtain ⟨s, hs⟩ := exists_sepM_sent ℳ ψ ![sUnionM ℳ w, sInterM ℳ w] (sUnionM ℳ w)
  refine ⟨s, fun z => (hs z).trans (and_congr Iff.rfl ?_)⟩
  dsimp only [ψ]
  rw [evM_imp, evM_mem, evM_eq]; rfl

private noncomputable def pi2SepM (ℳ : ZFCModel) (w : ℳ.V) : ℳ.V :=
  (exists_pi2SepM ℳ w).choose

private lemma mem_pi2SepM (ℳ : ZFCModel) (w z : ℳ.V) :
    ℳ.mem z (pi2SepM ℳ w) ↔
      ℳ.mem z (sUnionM ℳ w) ∧ (ℳ.mem z (sInterM ℳ w) → sUnionM ℳ w = sInterM ℳ w) :=
  (exists_pi2SepM ℳ w).choose_spec z

private noncomputable def pi2M (ℳ : ZFCModel) (w : ℳ.V) : ℳ.V :=
  sUnionM ℳ (pi2SepM ℳ w)

private lemma sInterM_kpairM (ℳ : ZFCModel) (a b : ℳ.V) :
    sInterM ℳ (kpairM ℳ a b) = singletonM ℳ a := by
  refine extM ℳ fun z => ?_
  rw [mem_sInterM, mem_singletonM]
  constructor
  · rintro ⟨_, hall⟩
    exact (mem_singletonM ℳ a z).mp
      (hall (singletonM ℳ a) ((mem_doubletonM ℳ _ _ _).mpr (Or.inl rfl)))
  · rintro rfl
    refine ⟨⟨singletonM ℳ z, (mem_doubletonM ℳ _ _ _).mpr (Or.inl rfl)⟩, fun y hy => ?_⟩
    rcases (mem_doubletonM ℳ _ _ _).mp hy with rfl | rfl
    · exact (mem_singletonM ℳ z z).mpr rfl
    · exact (mem_doubletonM ℳ z b z).mpr (Or.inl rfl)

private lemma sUnionM_kpairM (ℳ : ZFCModel) (a b : ℳ.V) :
    sUnionM ℳ (kpairM ℳ a b) = doubletonM ℳ a b := by
  refine extM ℳ fun z => ?_
  rw [mem_sUnionM, mem_doubletonM]
  constructor
  · rintro ⟨w, hw, hzw⟩
    rcases (mem_doubletonM ℳ _ _ _).mp hw with rfl | rfl
    · exact Or.inl ((mem_singletonM ℳ a z).mp hzw)
    · exact (mem_doubletonM ℳ a b z).mp hzw
  · rintro (rfl | rfl)
    · exact ⟨singletonM ℳ z, (mem_doubletonM ℳ _ _ _).mpr (Or.inl rfl),
        (mem_singletonM ℳ z z).mpr rfl⟩
    · exact ⟨doubletonM ℳ a z, (mem_doubletonM ℳ _ _ _).mpr (Or.inr rfl),
        (mem_doubletonM ℳ a z z).mpr (Or.inr rfl)⟩

private lemma pi1M_kpairM (ℳ : ZFCModel) (a b : ℳ.V) :
    pi1M ℳ (kpairM ℳ a b) = a := by
  unfold pi1M
  rw [sInterM_kpairM, sUnionM_singleton]

private lemma pi2M_kpairM (ℳ : ZFCModel) (a b : ℳ.V) :
    pi2M ℳ (kpairM ℳ a b) = b := by
  unfold pi2M
  have hsep : pi2SepM ℳ (kpairM ℳ a b) = singletonM ℳ b := by
    refine extM ℳ fun z => ?_
    rw [mem_pi2SepM, sUnionM_kpairM, sInterM_kpairM, mem_doubletonM, mem_singletonM, mem_singletonM]
    by_cases hab : a = b
    · subst hab
      have hdeq : doubletonM ℳ a a = singletonM ℳ a := rfl
      simp [hdeq]
    · have hne : doubletonM ℳ a b ≠ singletonM ℳ a := by
        intro heq
        have hb : ℳ.mem b (singletonM ℳ a) := heq ▸ (mem_doubletonM ℳ a b b).mpr (Or.inr rfl)
        exact hab ((mem_singletonM ℳ a b).mp hb).symm
      simp only [hne, imp_false]
      exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left h2,
        fun hz => ⟨Or.inr hz, fun hza => hab (hza.symm.trans hz)⟩⟩
  rw [hsep, sUnionM_singleton]

private lemma kpairM_inj (ℳ : ZFCModel) {a b c d : ℳ.V}
    (h : kpairM ℳ a b = kpairM ℳ c d) : a = c ∧ b = d :=
  ⟨by rw [← pi1M_kpairM ℳ a b, h, pi1M_kpairM],
   by rw [← pi2M_kpairM ℳ a b, h, pi2M_kpairM]⟩

private lemma ev_pi1 (ℳ : ZFCModel) (p w : ℳ.V) :
    evM ℳ ![p, w] SetTheory.kpair.π₁.dfn ↔ p = pi1M ℳ w := by
  unfold SetTheory.kpair.π₁.dfn pi1M
  rw [evM_all]
  refine (?_ : _ ↔ ∀ i : ℳ.V, i = sInterM ℳ w → p = sUnionM ℳ i).trans
    ⟨fun h => h (sInterM ℳ w) rfl, fun h i hi => hi ▸ h⟩
  refine forall_congr' fun i => ?_
  rw [evM_imp]
  exact imp_congr
    ((evM_subst2 ℳ _ SetTheory.sInter.dfn #0 #2).trans (ev_sInter ℳ i w))
    ((evM_subst2 ℳ _ SetTheory.sUnion.dfn #1 #0).trans (ev_sUnion ℳ p i))

private lemma ev_pi2 (ℳ : ZFCModel) (p w : ℳ.V) :
    evM ℳ ![p, w] SetTheory.kpair.π₂.dfn ↔ p = pi2M ℳ w := by
  unfold SetTheory.kpair.π₂.dfn pi2M
  rw [evM_all]
  let u0 := sUnionM ℳ w
  let i0 := sInterM ℳ w
  let s0 := pi2SepM ℳ w
  refine (?_ : _ ↔ ∀ u : ℳ.V, u = u0 → ∀ i : ℳ.V, i = i0 →
      ∀ s : ℳ.V, (∀ z : ℳ.V, ℳ.mem z s ↔ ℳ.mem z u ∧ (ℳ.mem z i → u = i)) →
        p = sUnionM ℳ s).trans ?_
  · refine forall_congr' fun u => ?_
    rw [evM_imp, evM_all]
    refine imp_congr ((evM_subst2 ℳ _ SetTheory.sUnion.dfn #0 #2).trans (ev_sUnion ℳ u w))
      (forall_congr' fun i => ?_)
    rw [evM_imp, evM_all]
    refine imp_congr ((evM_subst2 ℳ _ SetTheory.sInter.dfn #0 #3).trans (ev_sInter ℳ i w))
      (forall_congr' fun s => ?_)
    rw [evM_imp, evM_all]
    refine imp_congr (forall_congr' fun z => ?_)
      ((evM_subst2 ℳ _ SetTheory.sUnion.dfn #3 #0).trans (ev_sUnion ℳ p s))
    rw [evM_iff, evM_mem, evM_and, evM_mem, evM_imp, evM_mem, evM_eq]; rfl
  · constructor
    · intro h
      exact h u0 rfl i0 rfl s0 (mem_pi2SepM ℳ w)
    · intro hp u hu i hi s hs
      subst hu hi
      have hseq : s = s0 := extM ℳ fun z => (hs z).trans (mem_pi2SepM ℳ w z).symm
      rw [hseq, hp]

private lemma exists_prodM (ℳ : ZFCModel) (X Y : ℳ.V) :
    ∃ p : ℳ.V, ∀ z, ℳ.mem z p ↔ ∃ x, ℳ.mem x X ∧ ∃ y, ℳ.mem y Y ∧ z = kpairM ℳ x y := by
  let ψ : SetTheorySemisentence 3 := “z X Y. ∃ x ∈ X, ∃ y ∈ Y, !kpair.dfn z x y”
  obtain ⟨p, hp⟩ := exists_sepM_sent ℳ ψ ![X, Y] (powerM ℳ (powerM ℳ (unionM ℳ X Y)))
  refine ⟨p, fun z => (hp z).trans ?_⟩
  have hψ : evM ℳ ![z, X, Y] ψ ↔ ∃ x, ℳ.mem x X ∧ ∃ y, ℳ.mem y Y ∧ z = kpairM ℳ x y := by
    dsimp only [ψ]
    rw [evM_bexsMem]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [evM_bexsMem]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    exact (evM_subst3 ℳ _ SetTheory.kpair.dfn #2 #1 #0).trans (ev_kpair ℳ z x y)
  rw [hψ]
  refine ⟨And.right, fun ⟨x, hx, y, hy, hz⟩ => ⟨?_, x, hx, y, hy, hz⟩⟩
  subst hz
  rw [mem_powerM]
  intro t ht
  rw [mem_powerM]
  intro u hu
  rcases (mem_doubletonM ℳ _ _ t).mp ht with rfl | rfl
  · rw [(mem_singletonM ℳ x u).mp hu]
    exact (mem_unionM ℳ X Y x).mpr (Or.inl hx)
  · rcases (mem_doubletonM ℳ x y u).mp hu with hux | huy
    · rw [hux]; exact (mem_unionM ℳ X Y x).mpr (Or.inl hx)
    · rw [huy]; exact (mem_unionM ℳ X Y y).mpr (Or.inr hy)

private noncomputable def prodM (ℳ : ZFCModel) (X Y : ℳ.V) : ℳ.V :=
  (exists_prodM ℳ X Y).choose

private lemma mem_prodM (ℳ : ZFCModel) (X Y z : ℳ.V) :
    ℳ.mem z (prodM ℳ X Y) ↔ ∃ x, ℳ.mem x X ∧ ∃ y, ℳ.mem y Y ∧ z = kpairM ℳ x y :=
  (exists_prodM ℳ X Y).choose_spec z

private lemma kpairM_mem_prodM (ℳ : ZFCModel) {X Y x y : ℳ.V} :
    ℳ.mem (kpairM ℳ x y) (prodM ℳ X Y) ↔ ℳ.mem x X ∧ ℳ.mem y Y := by
  rw [mem_prodM]
  constructor
  · rintro ⟨a, ha, b, hb, heq⟩
    obtain ⟨rfl, rfl⟩ := kpairM_inj ℳ heq
    exact ⟨ha, hb⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl⟩

private lemma ev_prod (ℳ : ZFCModel) (p X Y : ℳ.V) :
    evM ℳ ![p, X, Y] SetTheory.prod.dfn ↔ p = prodM ℳ X Y := by
  unfold SetTheory.prod.dfn
  rw [evM_all]
  refine (?_ : _ ↔ ∀ z : ℳ.V, ℳ.mem z p ↔ ∃ x, ℳ.mem x X ∧ ∃ y, ℳ.mem y Y ∧ z = kpairM ℳ x y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [evM_iff, evM_mem, evM_bexsMem]
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr_right fun _ => ?_)
    rw [evM_bexsMem]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    exact (evM_subst3 ℳ _ SetTheory.kpair.dfn #2 #1 #0).trans (ev_kpair ℳ z x y)
  · constructor
    · intro h; exact extM ℳ fun z => (h z).trans (mem_prodM ℳ X Y z).symm
    · rintro rfl z; exact mem_prodM ℳ X Y z

/- Successor, Finite Numerals, and `ω` in `ℳ` -/

private noncomputable def succM (ℳ : ZFCModel) (x : ℳ.V) : ℳ.V := insertM ℳ x x

private lemma mem_succM (ℳ : ZFCModel) (x z : ℳ.V) :
    ℳ.mem z (succM ℳ x) ↔ z = x ∨ ℳ.mem z x := mem_insertM ℳ x x z

private lemma succM_ne_emptyM (ℳ : ZFCModel) (x : ℳ.V) : succM ℳ x ≠ emptyM ℳ := by
  intro h
  exact not_mem_emptyM ℳ x (h ▸ (mem_succM ℳ x x).mpr (Or.inl rfl))

private lemma succM_inj (ℳ : ZFCModel) {a b : ℳ.V} (h : succM ℳ a = succM ℳ b) : a = b := by
  by_contra hne
  have ha : ℳ.mem a (succM ℳ b) := h ▸ (mem_succM ℳ a a).mpr (Or.inl rfl)
  have hb : ℳ.mem b (succM ℳ a) := h.symm ▸ (mem_succM ℳ b b).mpr (Or.inl rfl)
  have hab : ℳ.mem a b := ((mem_succM ℳ b a).mp ha).resolve_left hne
  have hba : ℳ.mem b a := ((mem_succM ℳ a b).mp hb).resolve_left (Ne.symm hne)
  exact mem_asymm ℳ hab hba

private lemma ev_succ (ℳ : ZFCModel) (y x : ℳ.V) :
    evM ℳ ![y, x] SetTheory.succ.dfn ↔ y = succM ℳ x := by
  unfold SetTheory.succ.dfn SetTheory.isSucc
  rw [evM_all]
  refine (forall_congr' fun z => by
    rw [evM_iff, evM_mem, evM_or, evM_eq, evM_mem]).trans ?_
  constructor
  · intro h; exact extM ℳ fun z => (h z).trans (mem_succM ℳ x z).symm
  · rintro rfl z; exact mem_succM ℳ x z

private noncomputable def numM (ℳ : ZFCModel) : ℕ → ℳ.V
  | 0 => emptyM ℳ
  | k + 1 => succM ℳ (numM ℳ k)

private lemma mem_numM_iff (ℳ : ZFCModel) {x : ℳ.V} {m : ℕ} :
    ℳ.mem x (numM ℳ m) ↔ ∃ k < m, x = numM ℳ k := by
  induction m with
  | zero =>
    exact ⟨fun h => (not_mem_emptyM ℳ x h).elim, fun ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    rw [numM, mem_succM, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hlt, rfl⟩

private lemma numM_lt_mem (ℳ : ZFCModel) {a b : ℕ} (h : a < b) :
    ℳ.mem (numM ℳ a) (numM ℳ b) :=
  (mem_numM_iff ℳ).mpr ⟨a, h, rfl⟩

private lemma numM_injective (ℳ : ZFCModel) : Function.Injective (numM ℳ) := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hm := numM_lt_mem ℳ hlt
    rw [← hab] at hm
    exact (mem_irrefl ℳ _ hm).elim
  · rfl
  · have hm := numM_lt_mem ℳ hgt
    rw [hab] at hm
    exact (mem_irrefl ℳ _ hm).elim

private lemma ev_IsInductive (ℳ : ZFCModel) (I : ℳ.V) :
    evM ℳ ![I] SetTheory.IsInductive.dfn ↔
      (ℳ.mem (emptyM ℳ) I ∧ ∀ y, ℳ.mem y I → ℳ.mem (succM ℳ y) I) := by
  unfold SetTheory.IsInductive.dfn
  rw [evM_and, evM_all, evM_ballMem]
  refine and_congr ?_ ?_
  · refine (?_ : _ ↔ ∀ e : ℳ.V, e = emptyM ℳ → ℳ.mem e I).trans
      ⟨fun h => h (emptyM ℳ) rfl, fun h e he => he.symm ▸ h⟩
    refine forall_congr' fun e => ?_
    rw [evM_imp, evM_mem]
    exact imp_congr ((evM_subst1 ℳ _ SetTheory.isEmpty #0).trans (ev_isEmpty ℳ e)) Iff.rfl
  · refine forall_congr' fun y => imp_congr Iff.rfl ?_
    rw [evM_all]
    refine (?_ : _ ↔ ∀ y' : ℳ.V, y' = succM ℳ y → ℳ.mem y' I).trans
      ⟨fun h => h (succM ℳ y) rfl, fun h y' hy' => hy'.symm ▸ h⟩
    refine forall_congr' fun y' => ?_
    rw [evM_imp, evM_mem]
    exact imp_congr ((evM_subst2 ℳ _ SetTheory.succ.dfn #0 #1).trans (ev_succ ℳ y' y)) Iff.rfl

private lemma exists_inductiveM (ℳ : ZFCModel) :
    ∃ I : ℳ.V, ℳ.mem (emptyM ℳ) I ∧ ∀ y, ℳ.mem y I → ℳ.mem (succM ℳ y) I := by
  have hax := ℳ.sat Axiom.infinity (Or.inl ZermeloFraenkel.axiom_of_infinity)
  obtain ⟨I, hI⟩ := hax
  refine ⟨I, ?_⟩
  exact (ev_IsInductive ℳ I).mp hI

private lemma exists_omegaM (ℳ : ZFCModel) :
    ∃ ω : ℳ.V, ∀ x, ℳ.mem x ω ↔
      ∀ I : ℳ.V, (ℳ.mem (emptyM ℳ) I ∧ ∀ y, ℳ.mem y I → ℳ.mem (succM ℳ y) I) → ℳ.mem x I := by
  obtain ⟨I₀, hI₀⟩ := exists_inductiveM ℳ
  let ψ : SetTheorySemisentence 1 := “x. ∀ I, !IsInductive.dfn I → x ∈ I”
  obtain ⟨ω, hω⟩ := exists_sepM_sent ℳ ψ ![] I₀
  refine ⟨ω, fun x => (hω x).trans ?_⟩
  have hψ : evM ℳ ![x] ψ ↔
      ∀ I : ℳ.V, (ℳ.mem (emptyM ℳ) I ∧ ∀ y, ℳ.mem y I → ℳ.mem (succM ℳ y) I) → ℳ.mem x I := by
    dsimp only [ψ]
    rw [evM_all]
    refine forall_congr' fun I => ?_
    rw [evM_imp, evM_mem]
    exact imp_congr ((evM_subst1 ℳ _ SetTheory.IsInductive.dfn #0).trans (ev_IsInductive ℳ I)) Iff.rfl
  rw [hψ]
  exact ⟨And.right, fun hall => ⟨hall I₀ hI₀, hall⟩⟩

private noncomputable def omegaM (ℳ : ZFCModel) : ℳ.V := (exists_omegaM ℳ).choose

private lemma mem_omegaM_iff (ℳ : ZFCModel) (x : ℳ.V) :
    ℳ.mem x (omegaM ℳ) ↔
      ∀ I : ℳ.V, (ℳ.mem (emptyM ℳ) I ∧ ∀ y, ℳ.mem y I → ℳ.mem (succM ℳ y) I) → ℳ.mem x I :=
  (exists_omegaM ℳ).choose_spec x

private lemma omegaM_inductive (ℳ : ZFCModel) :
    ℳ.mem (emptyM ℳ) (omegaM ℳ) ∧ ∀ y, ℳ.mem y (omegaM ℳ) → ℳ.mem (succM ℳ y) (omegaM ℳ) :=
  ⟨(mem_omegaM_iff ℳ _).mpr fun _ hI => hI.1,
   fun y hy => (mem_omegaM_iff ℳ _).mpr fun I hI => hI.2 y ((mem_omegaM_iff ℳ y).mp hy I hI)⟩

private lemma numM_mem_omegaM (ℳ : ZFCModel) (k : ℕ) : ℳ.mem (numM ℳ k) (omegaM ℳ) := by
  induction k with
  | zero => exact (omegaM_inductive ℳ).1
  | succ k ih => exact (omegaM_inductive ℳ).2 _ ih

private lemma omegaM_zero_or_succ (ℳ : ZFCModel) {w : ℳ.V} (hw : ℳ.mem w (omegaM ℳ)) :
    w = emptyM ℳ ∨ ∃ u, ℳ.mem u (omegaM ℳ) ∧ w = succM ℳ u := by
  let ψ : SetTheorySemisentence 2 := “w ω. !isEmpty w ∨ ∃ u ∈ ω, !isSucc w u”
  obtain ⟨I, hI⟩ := exists_sepM_sent ℳ ψ ![omegaM ℳ] (omegaM ℳ)
  have hψ : ∀ z, evM ℳ ![z, omegaM ℳ] ψ ↔
      z = emptyM ℳ ∨ ∃ u, ℳ.mem u (omegaM ℳ) ∧ z = succM ℳ u := by
    intro z
    dsimp only [ψ]
    rw [evM_or, evM_bexsMem]
    refine or_congr ((evM_subst1 ℳ _ SetTheory.isEmpty #0).trans (ev_isEmpty ℳ z))
      (exists_congr fun u => and_congr_right fun _ => ?_)
    exact (evM_subst2 ℳ _ SetTheory.isSucc #1 #0).trans (ev_succ ℳ z u)
  have hI_ind : ℳ.mem (emptyM ℳ) I ∧ ∀ y, ℳ.mem y I → ℳ.mem (succM ℳ y) I := by
    refine ⟨(hI _).mpr ⟨(omegaM_inductive ℳ).1, (hψ _).mpr (Or.inl rfl)⟩, fun y hy => ?_⟩
    have hyω : ℳ.mem y (omegaM ℳ) := ((hI y).mp hy).1
    exact (hI _).mpr ⟨(omegaM_inductive ℳ).2 y hyω, (hψ _).mpr (Or.inr ⟨y, hyω, rfl⟩)⟩
  exact (hψ w).mp ((hI w).mp ((mem_omegaM_iff ℳ w).mp hw I hI_ind)).2

private lemma dc_isω (ℳ : ZFCModel) : DefinesConst ℳ SetTheory.isω (omegaM ℳ) := by
  intro w
  unfold SetTheory.isω
  rw [evM_all]
  refine (?_ : _ ↔ ∀ x : ℳ.V, ℳ.mem x w ↔
      ∀ I : ℳ.V, (ℳ.mem (emptyM ℳ) I ∧ ∀ y, ℳ.mem y I → ℳ.mem (succM ℳ y) I) → ℳ.mem x I).trans ?_
  · refine forall_congr' fun x => ?_
    rw [evM_iff, evM_mem, evM_all]
    refine iff_congr Iff.rfl (forall_congr' fun I => ?_)
    rw [evM_imp, evM_mem]
    exact imp_congr ((evM_subst1 ℳ _ SetTheory.IsInductive.dfn #0).trans (ev_IsInductive ℳ I)) Iff.rfl
  · constructor
    · intro h; exact extM ℳ fun x => (h x).trans (mem_omegaM_iff ℳ x).symm
    · rintro rfl x; exact mem_omegaM_iff ℳ x

/- `range.dfn`, `function.dfn`, `IsFunction.dfn`, `value.dfn` in `ℳ` -/

private lemma exists_relRangeM (ℳ : ZFCModel) (R : ℳ.V) :
    ∃ r : ℳ.V, ∀ y, ℳ.mem y r ↔ ∃ x, ℳ.mem (kpairM ℳ x y) R := by
  let ψ : SetTheorySemisentence 2 := f“y R. ∃ x, !kpair.dfn x y ∈ R”
  obtain ⟨r, hr⟩ := exists_sepM_sent ℳ ψ ![R] (sUnionM ℳ (sUnionM ℳ R))
  refine ⟨r, fun y => (hr y).trans ?_⟩
  have hψ : evM ℳ ![y, R] ψ ↔ ∃ x, ℳ.mem (kpairM ℳ x y) R := by
    dsimp only [ψ]
    rw [evM_exs]
    refine exists_congr fun x => ?_
    exact ev_faf_mem
      (et_comp2 (ev_kpair ℳ) (et_bvar1 ℳ x _) (et_bvar2 ℳ x y _))
      (et_bvar4 ℳ _ x y R _)
  rw [hψ]
  refine ⟨And.right, fun ⟨x, hx⟩ => ⟨?_, x, hx⟩⟩
  rw [mem_sUnionM]
  refine ⟨doubletonM ℳ x y, ?_, (mem_doubletonM ℳ x y y).mpr (Or.inr rfl)⟩
  rw [mem_sUnionM]
  exact ⟨kpairM ℳ x y, hx, (mem_doubletonM ℳ _ _ _).mpr (Or.inr rfl)⟩

private noncomputable def relRangeM (ℳ : ZFCModel) (R : ℳ.V) : ℳ.V :=
  (exists_relRangeM ℳ R).choose

private lemma mem_relRangeM (ℳ : ZFCModel) (R y : ℳ.V) :
    ℳ.mem y (relRangeM ℳ R) ↔ ∃ x, ℳ.mem (kpairM ℳ x y) R :=
  (exists_relRangeM ℳ R).choose_spec y

private lemma ev_range (ℳ : ZFCModel) (r R : ℳ.V) :
    evM ℳ ![r, R] SetTheory.range.dfn ↔ r = relRangeM ℳ R := by
  unfold SetTheory.range.dfn
  change evM ℳ ![r, R] (∀¹ _) ↔ _
  rw [evM_all]
  refine (?_ : _ ↔ ∀ y : ℳ.V, ℳ.mem y r ↔ ∃ x, ℳ.mem (kpairM ℳ x y) R).trans ?_
  · refine forall_congr' fun y => ?_
    rw [evM_iff]
    refine iff_congr (ev_faf_mem (et_bvar1 ℳ y _) (et_bvar3 ℳ _ y r _)) ?_
    rw [evM_exs]
    refine exists_congr fun x => ?_
    exact ev_faf_mem
      (et_comp2 (ev_kpair ℳ) (et_bvar1 ℳ x _) (et_bvar2 ℳ x y _))
      (et_bvar5 ℳ _ x y r R _)
  · constructor
    · intro h; exact extM ℳ fun y => (h y).trans (mem_relRangeM ℳ R y).symm
    · rintro rfl y; exact mem_relRangeM ℳ R y

private lemma exists_funsM (ℳ : ZFCModel) (X Y : ℳ.V) :
    ∃ F : ℳ.V, ∀ f, ℳ.mem f F ↔
      subM ℳ f (prodM ℳ X Y) ∧ ∀ x, ℳ.mem x X → ∃! y, ℳ.mem (kpairM ℳ x y) f := by
  let ψ : SetTheorySemisentence 3 :=
    f“f X Y. f ⊆ !prod.dfn X Y ∧ ∀ x ∈ X, ∃! y, !kpair.dfn x y ∈ f”
  obtain ⟨F, hF⟩ := exists_sepM_sent ℳ ψ ![X, Y] (powerM ℳ (prodM ℳ X Y))
  refine ⟨F, fun f => (hF f).trans ?_⟩
  have hψ : evM ℳ ![f, X, Y] ψ ↔
      subM ℳ f (prodM ℳ X Y) ∧ ∀ x, ℳ.mem x X → ∃! y, ℳ.mem (kpairM ℳ x y) f := by
    dsimp only [ψ]
    rw [evM_and]
    refine and_congr ?_ ?_
    · rw [ev_nest2 SetTheory.isSubsetOf (et_bvar1 ℳ f _)
        (et_comp2 (ev_prod ℳ) (et_bvar2 ℳ f X _) (et_bvar3 ℳ f X Y _)), ev_isSubsetOf]
    · rw [ev_faf_ball (et_bvar2 ℳ f X _)]
      refine forall_congr' fun x => imp_congr Iff.rfl ?_
      rw [ev_existsUnique]
      refine existsUnique_congr fun y => ?_
      exact ev_faf_mem
        (et_comp2 (ev_kpair ℳ) (et_bvar2 ℳ y x _) (et_bvar1 ℳ y _))
        (et_bvar5 ℳ _ y x _ f _)
  rw [hψ, mem_powerM]
  exact ⟨And.right, fun ⟨h1, h2⟩ => ⟨h1, h1, h2⟩⟩

private noncomputable def funsM (ℳ : ZFCModel) (X Y : ℳ.V) : ℳ.V :=
  (exists_funsM ℳ X Y).choose

private lemma mem_funsM (ℳ : ZFCModel) (X Y f : ℳ.V) :
    ℳ.mem f (funsM ℳ X Y) ↔
      subM ℳ f (prodM ℳ X Y) ∧ ∀ x, ℳ.mem x X → ∃! y, ℳ.mem (kpairM ℳ x y) f :=
  (exists_funsM ℳ X Y).choose_spec f

private lemma ev_function (ℳ : ZFCModel) (F Y X : ℳ.V) :
    evM ℳ ![F, Y, X] SetTheory.function.dfn ↔ F = funsM ℳ X Y := by
  unfold SetTheory.function.dfn
  change evM ℳ ![F, Y, X] (∀¹ _) ↔ _
  rw [evM_all]
  refine (?_ : _ ↔ ∀ f : ℳ.V, ℳ.mem f F ↔ ℳ.mem f (funsM ℳ X Y)).trans
    ⟨fun h => extM ℳ h, fun h f => by rw [h]⟩
  refine forall_congr' fun f => ?_
  rw [evM_iff]
  refine iff_congr (ev_faf_mem (et_bvar1 ℳ f _) (et_bvar3 ℳ _ f F _)) ?_
  rw [evM_and, mem_funsM]
  refine and_congr ?_ ?_
  · rw [ev_nest2 SetTheory.isSubsetOf (et_bvar1 ℳ f _)
      (et_comp2 (ev_prod ℳ) (et_bvar4 ℳ f F Y X _) (et_bvar3 ℳ f F Y _)), ev_isSubsetOf]
  · rw [ev_faf_ball (et_bvar4 ℳ f F Y X _)]
    refine forall_congr' fun x => imp_congr Iff.rfl ?_
    rw [ev_existsUnique]
    refine existsUnique_congr fun y => ?_
    exact ev_faf_mem
      (et_comp2 (ev_kpair ℳ) (et_bvar2 ℳ y x _) (et_bvar1 ℳ y _))
      (et_bvar5 ℳ _ y x _ f _)

private lemma ev_IsFunction (ℳ : ZFCModel) (f : ℳ.V) :
    evM ℳ ![f] SetTheory.IsFunction.dfn ↔ ∃ X Y : ℳ.V, ℳ.mem f (funsM ℳ X Y) := by
  unfold SetTheory.IsFunction.dfn
  change evM ℳ ![f] (∃¹ ∃¹ _) ↔ _
  rw [evM_exs]
  refine exists_congr fun X => ?_
  rw [evM_exs]
  refine exists_congr fun Y => ?_
  exact ev_faf_mem (et_bvar3 ℳ Y X f _)
    (et_comp2 (ev_function ℳ) (et_bvar2 ℳ _ Y _) (et_bvar3 ℳ _ Y X _))

private lemma exists_appM (ℳ : ZFCModel) (f x : ℳ.V) :
    ∃ v : ℳ.V, ∀ z, ℳ.mem z v ↔
      ℳ.mem z (sUnionM ℳ (relRangeM ℳ f)) ∧ ∃ y, ℳ.mem z y ∧ ℳ.mem (kpairM ℳ x y) f := by
  let ψ : SetTheorySemisentence 3 := f“z f x. ∃ y, z ∈ y ∧ !kpair.dfn x y ∈ f”
  obtain ⟨v, hv⟩ := exists_sepM_sent ℳ ψ ![f, x] (sUnionM ℳ (relRangeM ℳ f))
  refine ⟨v, fun z => (hv z).trans (and_congr Iff.rfl ?_)⟩
  dsimp only [ψ]
  rw [evM_exs]
  refine exists_congr fun y => ?_
  rw [evM_and]
  exact and_congr
    (ev_faf_mem (et_bvar2 ℳ y z _) (et_bvar2 ℳ _ y _))
    (ev_faf_mem (et_comp2 (ev_kpair ℳ) (et_bvar4 ℳ y z f x _) (et_bvar1 ℳ y _))
      (et_bvar4 ℳ _ y z f _))

private noncomputable def appM (ℳ : ZFCModel) (f x : ℳ.V) : ℳ.V :=
  (exists_appM ℳ f x).choose

private lemma mem_appM (ℳ : ZFCModel) (f x z : ℳ.V) :
    ℳ.mem z (appM ℳ f x) ↔
      ℳ.mem z (sUnionM ℳ (relRangeM ℳ f)) ∧ ∃ y, ℳ.mem z y ∧ ℳ.mem (kpairM ℳ x y) f :=
  (exists_appM ℳ f x).choose_spec z

private lemma ev_value (ℳ : ZFCModel) (v f x : ℳ.V) :
    evM ℳ ![v, f, x] SetTheory.value.dfn ↔ v = appM ℳ f x := by
  unfold SetTheory.value.dfn
  change evM ℳ ![v, f, x] (∀¹ _) ↔ _
  rw [evM_all]
  refine (?_ : _ ↔ ∀ z : ℳ.V, ℳ.mem z v ↔
      ℳ.mem z (sUnionM ℳ (relRangeM ℳ f)) ∧ ∃ y, ℳ.mem z y ∧ ℳ.mem (kpairM ℳ x y) f).trans ?_
  · refine forall_congr' fun z => ?_
    rw [evM_iff]
    refine iff_congr (ev_faf_mem (et_bvar1 ℳ z _) (et_bvar3 ℳ _ z v _)) ?_
    rw [evM_and]
    refine and_congr ?_ ?_
    · exact ev_faf_mem (et_bvar1 ℳ z _)
        (et_comp1 (ev_sUnion ℳ) (et_comp1 (ev_range ℳ) (et_bvar4 ℳ _ z v f _)))
    · rw [evM_exs]
      refine exists_congr fun y => ?_
      rw [evM_and]
      exact and_congr
        (ev_faf_mem (et_bvar2 ℳ y z _) (et_bvar2 ℳ _ y _))
        (ev_faf_mem (et_comp2 (ev_kpair ℳ) (et_bvar5 ℳ y z v f x _) (et_bvar1 ℳ y _))
          (et_bvar5 ℳ _ y z v f _))
  · constructor
    · intro h; exact extM ℳ fun z => (h z).trans (mem_appM ℳ f x z).symm
    · rintro rfl z; exact mem_appM ℳ f x z

private lemma appM_of_mem_funsM {ℳ : ZFCModel} {X Y f x y : ℳ.V}
    (hf : ℳ.mem f (funsM ℳ X Y)) (hx : ℳ.mem x X) (hpair : ℳ.mem (kpairM ℳ x y) f) :
    appM ℳ f x = y := by
  obtain ⟨_, huniq⟩ := (mem_funsM ℳ X Y f).mp hf
  obtain ⟨y0, hy0_mem, hy0_eq⟩ := huniq x hx
  have hy_eq : y = y0 := hy0_eq y hpair
  subst hy_eq
  refine extM ℳ fun z => ?_
  rw [mem_appM]
  constructor
  · rintro ⟨_, y', hz', hp'⟩
    have rfl' : y' = y := hy0_eq y' hp'
    rwa [← rfl']
  · intro hz
    refine ⟨?_, y, hz, hy0_mem⟩
    rw [mem_sUnionM]
    exact ⟨y, (mem_relRangeM ℳ f y).mpr ⟨x, hy0_mem⟩, hz⟩

private lemma appM_mem_codomain {ℳ : ZFCModel} {X Y f x : ℳ.V}
    (hf : ℳ.mem f (funsM ℳ X Y)) (hx : ℳ.mem x X) :
    ℳ.mem (appM ℳ f x) Y := by
  obtain ⟨hsub, huniq⟩ := (mem_funsM ℳ X Y f).mp hf
  obtain ⟨y, hy, _⟩ := huniq x hx
  rw [appM_of_mem_funsM hf hx hy]
  exact ((kpairM_mem_prodM ℳ).mp (hsub _ hy)).2

private lemma funsM_ext {ℳ : ZFCModel} {X Y f1 f2 : ℳ.V}
    (hf1 : ℳ.mem f1 (funsM ℳ X Y)) (hf2 : ℳ.mem f2 (funsM ℳ X Y))
    (heq : ∀ x, ℳ.mem x X → appM ℳ f1 x = appM ℳ f2 x) : f1 = f2 := by
  obtain ⟨hsub1, huniq1⟩ := (mem_funsM ℳ X Y f1).mp hf1
  obtain ⟨hsub2, huniq2⟩ := (mem_funsM ℳ X Y f2).mp hf2
  refine extM ℳ fun p => ⟨fun hp1 => ?_, fun hp2 => ?_⟩
  · obtain ⟨x, hx, y, _, rfl⟩ := (mem_prodM ℳ X Y p).mp (hsub1 p hp1)
    have ha1 := appM_of_mem_funsM hf1 hx hp1
    obtain ⟨y2, hy2, _⟩ := huniq2 x hx
    have ha2 := appM_of_mem_funsM hf2 hx hy2
    have hy_eq : y = y2 := by rw [← ha1, heq x hx, ha2]
    rwa [hy_eq]
  · obtain ⟨x, hx, y, _, rfl⟩ := (mem_prodM ℳ X Y p).mp (hsub2 p hp2)
    have ha2 := appM_of_mem_funsM hf2 hx hp2
    obtain ⟨y1, hy1, _⟩ := huniq1 x hx
    have ha1 := appM_of_mem_funsM hf1 hx hy1
    have hy_eq : y = y1 := by rw [← ha2, ← heq x hx, ha1]
    rwa [hy_eq]

/- `Constant14` Numerals, Finite Sets, Encoded Integers, and Total Integer Succ/Pred in `ℳ` -/

private lemma dc_zero (ℳ : ZFCModel) : DefinesConst ℳ Constant14.zero (emptyM ℳ) := by
  intro z
  unfold Constant14.zero
  exact (evM_subst1 ℳ _ SetTheory.isEmpty #0).trans (ev_isEmpty ℳ z)

private lemma dc_numeral (ℳ : ZFCModel) (k : ℕ) :
    DefinesConst ℳ (Constant14.numeral k) (numM ℳ k) := by
  induction k with
  | zero => exact dc_zero ℳ
  | succ k ih =>
    intro y
    unfold Constant14.numeral numM
    exact et_comp1 (ev_succ ℳ) ih y

private lemma dc_setPair {ℳ : ZFCModel} {Ψ₁ Ψ₂ : SetTheorySemisentence 1} {v₁ v₂ : ℳ.V}
    (h₁ : DefinesConst ℳ Ψ₁ v₁) (h₂ : DefinesConst ℳ Ψ₂ v₂) :
    DefinesConst ℳ (Constant14.setPair Ψ₁ Ψ₂) (kpairM ℳ v₁ v₂) := by
  intro y
  unfold Constant14.setPair
  have h := et_comp2 (ev_kpair ℳ) (h₁ ·) (h₂ ·) y
  rwa [evM_e1] at h

private lemma dc_setTriple {ℳ : ZFCModel} {Ψ₁ Ψ₂ Ψ₃ : SetTheorySemisentence 1} {v₁ v₂ v₃ : ℳ.V}
    (h₁ : DefinesConst ℳ Ψ₁ v₁) (h₂ : DefinesConst ℳ Ψ₂ v₂) (h₃ : DefinesConst ℳ Ψ₃ v₃) :
    DefinesConst ℳ (Constant14.setTriple Ψ₁ Ψ₂ Ψ₃) (kpairM ℳ v₁ (kpairM ℳ v₂ v₃)) :=
  dc_setPair h₁ (dc_setPair h₂ h₃)

private noncomputable def listToM (ℳ : ZFCModel) : List ℳ.V → ℳ.V
  | [] => emptyM ℳ
  | x :: xs => insertM ℳ x (listToM ℳ xs)

private lemma mem_listToM (ℳ : ZFCModel) {z : ℳ.V} {xs : List ℳ.V} :
    ℳ.mem z (listToM ℳ xs) ↔ z ∈ xs := by
  induction xs with
  | nil => simp [listToM, not_mem_emptyM]
  | cons x xs ih => simp [listToM, mem_insertM, ih]

private lemma dc_finiteSet_map {ℳ : ZFCModel} {α : Type*} (l : List α)
    (fForm : α → SetTheorySemisentence 1) (fVal : α → ℳ.V)
    (hf : ∀ a, DefinesConst ℳ (fForm a) (fVal a)) :
    DefinesConst ℳ (Constant14.finiteSet (l.map fForm)) (listToM ℳ (l.map fVal)) := by
  induction l with
  | nil => exact dc_zero ℳ
  | cons a as ih =>
    intro y
    simp only [List.map_cons, Constant14.finiteSet, listToM]
    have h := et_comp2 (ev_insert ℳ) (hf a ·) (ih ·) y
    rwa [evM_e1] at h

private noncomputable def intSetM (ℳ : ZFCModel) : ℳ.V :=
  prodM ℳ (numM ℳ 2) (omegaM ℳ)

private lemma dc_integers (ℳ : ZFCModel) : DefinesConst ℳ Constant14.integers (intSetM ℳ) := by
  intro y
  unfold Constant14.integers intSetM
  exact ev_faf_eq (et_bvar1 ℳ y _)
    (et_comp2 (ev_prod ℳ) (et_const0 (dc_numeral ℳ 2) _) (et_const0 (dc_isω ℳ) _))

private noncomputable def encodeIntM (ℳ : ZFCModel) : ℤ → ℳ.V
  | Int.ofNat k => kpairM ℳ (numM ℳ 0) (numM ℳ k)
  | Int.negSucc k => kpairM ℳ (numM ℳ 1) (numM ℳ k)

private lemma encodeIntM_mem (ℳ : ZFCModel) (z : ℤ) : ℳ.mem (encodeIntM ℳ z) (intSetM ℳ) := by
  unfold intSetM
  cases z with
  | ofNat k =>
    exact (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ (by decide : 0 < 2), numM_mem_omegaM ℳ k⟩
  | negSucc k =>
    exact (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ (by decide : 1 < 2), numM_mem_omegaM ℳ k⟩

private lemma encodeIntM_injective (ℳ : ZFCModel) : Function.Injective (encodeIntM ℳ) := by
  intro z1 z2 heq
  cases z1 <;> cases z2 <;> obtain ⟨h1, h2⟩ := kpairM_inj ℳ heq
  · rw [numM_injective ℳ h2]
  · exact absurd (numM_injective ℳ h1) (by decide)
  · exact absurd (numM_injective ℳ h1) (by decide)
  · rw [numM_injective ℳ h2]

private lemma dc_integerZero (ℳ : ZFCModel) :
    DefinesConst ℳ Constant14.integerZero (encodeIntM ℳ 0) := by
  intro y
  unfold Constant14.integerZero
  exact ev_faf_eq (et_bvar1 ℳ y _)
    (et_comp2 (ev_kpair ℳ) (et_const0 (dc_numeral ℳ 0) _) (et_const0 (dc_numeral ℳ 0) _))

private noncomputable def predOmegaM (ℳ : ZFCModel) (w : ℳ.V) : ℳ.V :=
  if h : ∃ u, ℳ.mem u (omegaM ℳ) ∧ w = succM ℳ u then h.choose else emptyM ℳ

private lemma predOmegaM_succM (ℳ : ZFCModel) {u : ℳ.V} (hu : ℳ.mem u (omegaM ℳ)) :
    predOmegaM ℳ (succM ℳ u) = u := by
  have hex : ∃ v, ℳ.mem v (omegaM ℳ) ∧ succM ℳ u = succM ℳ v := ⟨u, hu, rfl⟩
  unfold predOmegaM
  rw [dif_pos hex]
  exact (succM_inj ℳ hex.choose_spec.2).symm

private lemma predOmegaM_spec (ℳ : ZFCModel) {w : ℳ.V}
    (hw : ℳ.mem w (omegaM ℳ)) (hne : w ≠ emptyM ℳ) :
    ℳ.mem (predOmegaM ℳ w) (omegaM ℳ) ∧ w = succM ℳ (predOmegaM ℳ w) := by
  have hex : ∃ u, ℳ.mem u (omegaM ℳ) ∧ w = succM ℳ u :=
    (omegaM_zero_or_succ ℳ hw).resolve_left hne
  unfold predOmegaM
  rw [dif_pos hex]
  exact hex.choose_spec

private noncomputable def intSuccM (ℳ : ZFCModel) (w : ℳ.V) : ℳ.V :=
  if ℳ.mem w (intSetM ℳ) then
    if pi1M ℳ w = numM ℳ 0 then
      kpairM ℳ (numM ℳ 0) (succM ℳ (pi2M ℳ w))
    else if pi2M ℳ w = numM ℳ 0 then
      encodeIntM ℳ 0
    else
      kpairM ℳ (numM ℳ 1) (predOmegaM ℳ (pi2M ℳ w))
  else encodeIntM ℳ 0

private noncomputable def intPredM (ℳ : ZFCModel) (w : ℳ.V) : ℳ.V :=
  if ℳ.mem w (intSetM ℳ) then
    if pi1M ℳ w = numM ℳ 0 then
      if pi2M ℳ w = numM ℳ 0 then
        encodeIntM ℳ (-1)
      else
        kpairM ℳ (numM ℳ 0) (predOmegaM ℳ (pi2M ℳ w))
    else
      kpairM ℳ (numM ℳ 1) (succM ℳ (pi2M ℳ w))
  else encodeIntM ℳ 0

private lemma mem_intSetM_cases (ℳ : ZFCModel) {w : ℳ.V} (hw : ℳ.mem w (intSetM ℳ)) :
    ∃ u, ℳ.mem u (omegaM ℳ) ∧ (w = kpairM ℳ (numM ℳ 0) u ∨ w = kpairM ℳ (numM ℳ 1) u) := by
  obtain ⟨s, hs, u, hu, rfl⟩ := (mem_prodM ℳ (numM ℳ 2) (omegaM ℳ) w).mp hw
  obtain ⟨k, hk, rfl⟩ := (mem_numM_iff ℳ).mp hs
  interval_cases k
  · exact ⟨u, hu, Or.inl rfl⟩
  · exact ⟨u, hu, Or.inr rfl⟩

private lemma intSuccM_mem (ℳ : ZFCModel) {w : ℳ.V} (hw : ℳ.mem w (intSetM ℳ)) :
    ℳ.mem (intSuccM ℳ w) (intSetM ℳ) := by
  obtain ⟨u, hu, rfl | rfl⟩ := mem_intSetM_cases ℳ hw
  · unfold intSuccM
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_pos rfl]
    exact (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ (by decide : 0 < 2), (omegaM_inductive ℳ).2 u hu⟩
  · have h10 : numM ℳ 1 ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by decide)
    unfold intSuccM
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_neg h10]
    by_cases hu0 : u = numM ℳ 0
    · rw [if_pos hu0]; exact encodeIntM_mem ℳ 0
    · rw [if_neg hu0]
      exact (kpairM_mem_prodM ℳ).mpr
        ⟨numM_lt_mem ℳ (by decide : 1 < 2), (predOmegaM_spec ℳ hu hu0).1⟩

private lemma intPredM_mem (ℳ : ZFCModel) {w : ℳ.V} (hw : ℳ.mem w (intSetM ℳ)) :
    ℳ.mem (intPredM ℳ w) (intSetM ℳ) := by
  obtain ⟨u, hu, rfl | rfl⟩ := mem_intSetM_cases ℳ hw
  · unfold intPredM
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_pos rfl]
    by_cases hu0 : u = numM ℳ 0
    · rw [if_pos hu0]; exact encodeIntM_mem ℳ (-1)
    · rw [if_neg hu0]
      exact (kpairM_mem_prodM ℳ).mpr
        ⟨numM_lt_mem ℳ (by decide : 0 < 2), (predOmegaM_spec ℳ hu hu0).1⟩
  · have h10 : numM ℳ 1 ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by decide)
    unfold intPredM
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_neg h10]
    exact (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ (by decide : 1 < 2), (omegaM_inductive ℳ).2 u hu⟩

private lemma encodeIntM_ofNat (ℳ : ZFCModel) (k : ℕ) :
    encodeIntM ℳ (Int.ofNat k) = kpairM ℳ (numM ℳ 0) (numM ℳ k) := rfl

private lemma encodeIntM_negSucc (ℳ : ZFCModel) (k : ℕ) :
    encodeIntM ℳ (Int.negSucc k) = kpairM ℳ (numM ℳ 1) (numM ℳ k) := rfl

private lemma encodeIntM_zero (ℳ : ZFCModel) :
    encodeIntM ℳ 0 = kpairM ℳ (numM ℳ 0) (numM ℳ 0) := rfl

private lemma encodeIntM_negOne (ℳ : ZFCModel) :
    encodeIntM ℳ (-1) = kpairM ℳ (numM ℳ 1) (numM ℳ 0) := rfl

private lemma intSuccM_intPredM (ℳ : ZFCModel) {w : ℳ.V} (hw : ℳ.mem w (intSetM ℳ)) :
    intSuccM ℳ (intPredM ℳ w) = w := by
  have h10 : numM ℳ 1 ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by decide)
  have hpm := intPredM_mem ℳ hw
  obtain ⟨u, hu, rfl | rfl⟩ := mem_intSetM_cases ℳ hw
  · unfold intPredM at hpm ⊢
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_pos rfl] at hpm ⊢
    by_cases hu0 : u = numM ℳ 0
    · rw [if_pos hu0] at hpm ⊢
      subst hu0
      unfold intSuccM
      rw [if_pos hpm, encodeIntM_negOne, pi1M_kpairM, pi2M_kpairM, if_neg h10, if_pos rfl]
      rfl
    · rw [if_neg hu0] at hpm ⊢
      unfold intSuccM
      rw [if_pos hpm, pi1M_kpairM, pi2M_kpairM, if_pos rfl, ← (predOmegaM_spec ℳ hu hu0).2]
  · unfold intPredM at hpm ⊢
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_neg h10] at hpm ⊢
    unfold intSuccM
    have hne : succM ℳ u ≠ numM ℳ 0 := succM_ne_emptyM ℳ u
    rw [if_pos hpm, pi1M_kpairM, pi2M_kpairM, if_neg h10, if_neg hne, predOmegaM_succM ℳ hu]

private lemma intPredM_intSuccM (ℳ : ZFCModel) {w : ℳ.V} (hw : ℳ.mem w (intSetM ℳ)) :
    intPredM ℳ (intSuccM ℳ w) = w := by
  have h10 : numM ℳ 1 ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by decide)
  have hsm := intSuccM_mem ℳ hw
  obtain ⟨u, hu, rfl | rfl⟩ := mem_intSetM_cases ℳ hw
  · unfold intSuccM at hsm ⊢
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_pos rfl] at hsm ⊢
    unfold intPredM
    have hne : succM ℳ u ≠ numM ℳ 0 := succM_ne_emptyM ℳ u
    rw [if_pos hsm, pi1M_kpairM, pi2M_kpairM, if_pos rfl, if_neg hne, predOmegaM_succM ℳ hu]
  · unfold intSuccM at hsm ⊢
    rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_neg h10] at hsm ⊢
    by_cases hu0 : u = numM ℳ 0
    · rw [if_pos hu0] at hsm ⊢
      subst hu0
      unfold intPredM
      rw [if_pos hsm, encodeIntM_zero, pi1M_kpairM, pi2M_kpairM, if_pos rfl, if_pos rfl]
      rfl
    · rw [if_neg hu0] at hsm ⊢
      unfold intPredM
      rw [if_pos hsm, pi1M_kpairM, pi2M_kpairM, if_neg h10, ← (predOmegaM_spec ℳ hu hu0).2]

private lemma intSuccM_encodeIntM (ℳ : ZFCModel) (z : ℤ) :
    intSuccM ℳ (encodeIntM ℳ z) = encodeIntM ℳ (z + 1) := by
  have hw := encodeIntM_mem ℳ z
  have h10 : numM ℳ 1 ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by decide)
  cases z with
  | ofNat k =>
    unfold intSuccM
    rw [if_pos hw, encodeIntM_ofNat, pi1M_kpairM, pi2M_kpairM, if_pos rfl]
    rfl
  | negSucc k =>
    cases k with
    | zero =>
      unfold intSuccM
      rw [if_pos hw, encodeIntM_negSucc, pi1M_kpairM, pi2M_kpairM, if_neg h10, if_pos rfl]
      rfl
    | succ k =>
      have hne : numM ℳ (k + 1) ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by omega)
      unfold intSuccM
      rw [if_pos hw, encodeIntM_negSucc, pi1M_kpairM, pi2M_kpairM, if_neg h10, if_neg hne]
      change kpairM ℳ (numM ℳ 1) (predOmegaM ℳ (succM ℳ (numM ℳ k))) = encodeIntM ℳ (Int.negSucc k)
      rw [predOmegaM_succM ℳ (numM_mem_omegaM ℳ k)]
      rfl

private lemma intPredM_encodeIntM (ℳ : ZFCModel) (z : ℤ) :
    intPredM ℳ (encodeIntM ℳ z) = encodeIntM ℳ (z - 1) := by
  have h := intPredM_intSuccM ℳ (encodeIntM_mem ℳ (z - 1))
  rw [intSuccM_encodeIntM, sub_add_cancel] at h
  exact h

private lemma ev_integerSucc (ℳ : ZFCModel) (w' w : ℳ.V) :
    evM ℳ ![w', w] Constant14.integerSucc.dfn ↔ w' = intSuccM ℳ w := by
  unfold Constant14.integerSucc.dfn
  rw [evM_or, evM_and, evM_and]
  rw [ev_faf_mem (et_bvar2 ℳ w' w _) (et_const0 (dc_integers ℳ) _),
      ev_faf_notMem (et_bvar2 ℳ w' w _) (et_const0 (dc_integers ℳ) _)]
  by_cases hw : ℳ.mem w (intSetM ℳ)
  · simp only [hw, not_true_eq_false, false_and, or_false, true_and]
    refine (?_ : _ ↔
        ((pi1M ℳ w = numM ℳ 0 ∧ w' = kpairM ℳ (numM ℳ 0) (succM ℳ (pi2M ℳ w))) ∨
          (pi1M ℳ w = numM ℳ 1 ∧
            ((pi2M ℳ w = numM ℳ 0 ∧ w' = encodeIntM ℳ 0) ∨
              ∃ m, ℳ.mem m (omegaM ℳ) ∧ pi2M ℳ w = succM ℳ m ∧
                w' = kpairM ℳ (numM ℳ 1) m)))).trans ?_
    · rw [evM_or, evM_and, evM_and, evM_or, evM_and]
      refine or_congr
        (and_congr
          (ev_faf_eq (et_comp1 (ev_pi1 ℳ) (et_bvar2 ℳ w' w _)) (et_const0 (dc_numeral ℳ 0) _))
          (ev_faf_eq (et_bvar1 ℳ w' _)
            (et_comp2 (ev_kpair ℳ) (et_const0 (dc_numeral ℳ 0) _)
              (et_comp1 (ev_succ ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar3 ℳ _ w' w _))))))
        (and_congr
          (ev_faf_eq (et_comp1 (ev_pi1 ℳ) (et_bvar2 ℳ w' w _)) (et_const0 (dc_numeral ℳ 1) _))
          (or_congr
            (and_congr
              (ev_faf_eq (et_comp1 (ev_pi2 ℳ) (et_bvar2 ℳ w' w _)) (et_const0 (dc_numeral ℳ 0) _))
              (ev_faf_eq (et_bvar1 ℳ w' _) (et_const0 (dc_integerZero ℳ) _)))
            ?_))
      rw [ev_faf_bexs (et_const0 (dc_isω ℳ) _)]
      refine exists_congr fun m => and_congr_right fun _ => ?_
      rw [evM_and]
      exact and_congr
        (ev_faf_eq (et_comp1 (ev_pi2 ℳ) (et_bvar4 ℳ m (omegaM ℳ) w' w _))
          (et_comp1 (ev_succ ℳ) (et_bvar2 ℳ _ m _)))
        (ev_faf_eq (et_bvar3 ℳ m (omegaM ℳ) w' _)
          (et_comp2 (ev_kpair ℳ) (et_const0 (dc_numeral ℳ 1) _) (et_bvar2 ℳ _ m _)))
    · have h01 : numM ℳ 0 ≠ numM ℳ 1 := fun h => absurd (numM_injective ℳ h) (by decide)
      have h10 : numM ℳ 1 ≠ numM ℳ 0 := h01.symm
      obtain ⟨u, hu, rfl | rfl⟩ := mem_intSetM_cases ℳ hw
      · unfold intSuccM
        rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_pos rfl]
        simp only [h01, false_and, or_false, true_and]
      · unfold intSuccM
        rw [if_pos hw, pi1M_kpairM, pi2M_kpairM, if_neg h10]
        simp only [h10, false_and, false_or, true_and]
        by_cases hu0 : u = numM ℳ 0
        · rw [if_pos hu0, hu0]
          have hno : ¬ ∃ m, ℳ.mem m (omegaM ℳ) ∧ numM ℳ 0 = succM ℳ m ∧
              w' = kpairM ℳ (numM ℳ 1) m := by
            rintro ⟨m, _, hm, _⟩
            exact succM_ne_emptyM ℳ m hm.symm
          simp only [true_and, hno, or_false]
        · rw [if_neg hu0]
          simp only [hu0, false_and, false_or]
          obtain ⟨hp_mem, hp_eq⟩ := predOmegaM_spec ℳ hu hu0
          constructor
          · rintro ⟨m, _, hm, rfl⟩
            have hmeq : m = predOmegaM ℳ u := succM_inj ℳ (hm.symm.trans hp_eq)
            rw [hmeq]
          · rintro rfl
            exact ⟨predOmegaM ℳ u, hp_mem, hp_eq, rfl⟩
  · simp only [hw, false_and, false_or, not_false_eq_true, true_and]
    unfold intSuccM
    rw [if_neg hw]
    exact ev_faf_eq (et_bvar1 ℳ w' _) (et_const0 (dc_integerZero ℳ) _)

private lemma ev_integerPred (ℳ : ZFCModel) (w' w : ℳ.V) :
    evM ℳ ![w', w] Constant14.integerPred.dfn ↔ w' = intPredM ℳ w := by
  unfold Constant14.integerPred.dfn
  rw [evM_or, evM_and, evM_and, evM_and]
  rw [ev_faf_mem (et_bvar2 ℳ w' w _) (et_const0 (dc_integers ℳ) _),
      ev_faf_mem (et_bvar1 ℳ w' _) (et_const0 (dc_integers ℳ) _),
      ev_nest2 Constant14.integerSucc.dfn (et_bvar2 ℳ w' w _) (et_bvar1 ℳ w' _),
      ev_faf_notMem (et_bvar2 ℳ w' w _) (et_const0 (dc_integers ℳ) _),
      ev_integerSucc]
  by_cases hw : ℳ.mem w (intSetM ℳ)
  · simp only [hw, not_true_eq_false, false_and, or_false, true_and]
    constructor
    · rintro ⟨hw', hsucc⟩
      rw [hsucc, intPredM_intSuccM ℳ hw']
    · rintro rfl
      exact ⟨intPredM_mem ℳ hw, (intSuccM_intPredM ℳ hw).symm⟩
  · simp only [hw, false_and, false_or, not_false_eq_true, true_and]
    unfold intPredM
    rw [if_neg hw]
    exact ev_faf_eq (et_bvar1 ℳ w' _) (et_const0 (dc_integerZero ℳ) _)

/- ## Section 4: Configurations, Transition Table, `nextStep`, `orbit`, and TM Simulation in `ℳ` -/

private noncomputable def cfgSetM (ℳ : ZFCModel) (N : ℕ) : ℳ.V :=
  prodM ℳ (numM ℳ N) (prodM ℳ (intSetM ℳ) (funsM ℳ (intSetM ℳ) (numM ℳ 2)))

private lemma dc_configSet (ℳ : ZFCModel) (N : ℕ) :
    DefinesConst ℳ (Constant14.configSet N) (cfgSetM ℳ N) := by
  intro y
  unfold Constant14.configSet cfgSetM
  exact ev_faf_eq (et_bvar1 ℳ y _)
    (et_comp2 (ev_prod ℳ) (et_const0 (dc_numeral ℳ N) _)
      (et_comp2 (ev_prod ℳ) (et_const0 (dc_integers ℳ) _)
        (et_comp2 (ev_function ℳ) (et_const0 (dc_numeral ℳ 2) _) (et_const0 (dc_integers ℳ) _))))

private lemma mem_cfgSetM_iff (ℳ : ZFCModel) {N : ℕ} {z : ℳ.V} :
    ℳ.mem z (cfgSetM ℳ N) ↔
      ∃ (qCode : ℕ) (posSet g : ℳ.V),
        qCode < N ∧ ℳ.mem posSet (intSetM ℳ) ∧ ℳ.mem g (funsM ℳ (intSetM ℳ) (numM ℳ 2)) ∧
          z = kpairM ℳ (numM ℳ qCode) (kpairM ℳ posSet g) := by
  unfold cfgSetM
  constructor
  · intro hz
    obtain ⟨s, hs, p, hp, rfl⟩ := (mem_prodM ℳ _ _ z).mp hz
    obtain ⟨qCode, hq, rfl⟩ := (mem_numM_iff ℳ).mp hs
    obtain ⟨posSet, hpos, g, hg, rfl⟩ := (mem_prodM ℳ _ _ p).mp hp
    exact ⟨qCode, posSet, g, hq, hpos, hg, rfl⟩
  · rintro ⟨qCode, posSet, g, hq, hpos, hg, rfl⟩
    exact (kpairM_mem_prodM ℳ).mpr
      ⟨numM_lt_mem ℳ hq, (kpairM_mem_prodM ℳ).mpr ⟨hpos, hg⟩⟩

private def entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) : SetTheorySemisentence 1 :=
  Constant14.transitionEntry t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

private noncomputable def entryValM (ℳ : ZFCModel) (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ℳ.V :=
  kpairM ℳ (kpairM ℳ (numM ℳ t.1) (numM ℳ t.2.1))
    (kpairM ℳ (numM ℳ t.2.2.1) (kpairM ℳ (numM ℳ t.2.2.2.1) (numM ℳ t.2.2.2.2)))

private lemma dc_entryForm (ℳ : ZFCModel) (t : ℕ × ℕ × ℕ × ℕ × ℕ) :
    DefinesConst ℳ (entryForm t) (entryValM ℳ t) := by
  unfold entryForm Constant14.transitionEntry entryValM
  exact dc_setPair (dc_setPair (dc_numeral ℳ _) (dc_numeral ℳ _))
    (dc_setTriple (dc_numeral ℳ _) (dc_numeral ℳ _) (dc_numeral ℳ _))

private def transTuples {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.ofFn fun q : Fin n =>
    List.ofFn fun sym : Fin 2 =>
      let o := Constant14.transitionCode M q sym
      (q.val, sym.val, o.1, o.2.1, o.2.2)).flatten ++
  List.ofFn fun sym : Fin 2 =>
    (n, sym.val, n, sym.val, Constant14.directionCode none)

private noncomputable def instrTableM (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) : ℳ.V :=
  listToM ℳ ((transTuples M).map (entryValM ℳ))

private lemma dc_instructionTable (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) :
    DefinesConst ℳ (Constant14.instructionTable M) (instrTableM ℳ M) := by
  unfold Constant14.instructionTable instrTableM
  have hmap : (transTuples M).map entryForm = Constant14.transitionEntries M := by
    simp [transTuples, Constant14.transitionEntries, entryForm, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  rw [← hmap]
  exact dc_finiteSet_map (transTuples M) entryForm (entryValM ℳ) (dc_entryForm ℳ)

private def transLookup {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode symCode : ℕ) : ℕ × ℕ × ℕ :=
  if hq : qCode < n then
    if hs : symCode < 2 then
      Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hs⟩
    else (n, 0, 1)
  else (n, symCode, 1)

private lemma transitionCode_bounds {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (q : Fin n) (sym : Fin 2) :
    let o := Constant14.transitionCode M q sym
    o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
  dsimp only [Constant14.transitionCode]
  cases M q sym with
  | none =>
    dsimp only [Constant14.directionCode]
    exact ⟨Nat.lt_succ_self n, sym.isLt, by decide⟩
  | some p =>
    rcases p with ⟨q', ⟨sym', d⟩⟩
    dsimp only
    refine ⟨?_, sym'.isLt, ?_⟩
    · cases q' with
      | none => exact Nat.lt_succ_self n
      | some qv => exact Nat.lt_succ_of_lt qv.isLt
    · cases d <;> decide

private lemma instrTableM_funs_and_app (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) :
    ℳ.mem (instrTableM ℳ M)
      (funsM ℳ (prodM ℳ (numM ℳ (n + 1)) (numM ℳ 2))
        (prodM ℳ (numM ℳ (n + 1)) (prodM ℳ (numM ℳ 2) (numM ℳ 3)))) ∧
      ∀ (qCode symCode : ℕ), qCode < n + 1 → symCode < 2 →
        appM ℳ (instrTableM ℳ M) (kpairM ℳ (numM ℳ qCode) (numM ℳ symCode)) =
          let o := transLookup M qCode symCode
          kpairM ℳ (numM ℳ o.1) (kpairM ℳ (numM ℳ o.2.1) (numM ℳ o.2.2)) := by
  have hmem_iff : ∀ p : ℳ.V, ℳ.mem p (instrTableM ℳ M) ↔
      (∃ (q : Fin n) (sym : Fin 2),
        let o := Constant14.transitionCode M q sym
        p = entryValM ℳ (q.val, sym.val, o.1, o.2.1, o.2.2)) ∨
      (∃ sym : Fin 2, p = entryValM ℳ (n, sym.val, n, sym.val, 1)) := by
    intro p
    unfold instrTableM
    rw [mem_listToM, List.mem_map]
    simp only [transTuples, List.mem_append, List.mem_flatten, List.mem_ofFn,
      Constant14.directionCode]
    constructor
    · rintro ⟨t, (⟨l, ⟨q, rfl⟩, ht⟩ | ⟨sym, rfl⟩), rfl⟩
      · obtain ⟨sym, rfl⟩ := List.mem_ofFn.mp ht
        exact Or.inl ⟨q, sym, rfl⟩
      · exact Or.inr ⟨sym, rfl⟩
    · rintro (⟨q, sym, rfl⟩ | ⟨sym, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, ⟨q, rfl⟩, List.mem_ofFn.mpr ⟨sym, rfl⟩⟩, rfl⟩
      · exact ⟨_, Or.inr ⟨sym, rfl⟩, rfl⟩
  have hfuns : ℳ.mem (instrTableM ℳ M)
      (funsM ℳ (prodM ℳ (numM ℳ (n + 1)) (numM ℳ 2))
        (prodM ℳ (numM ℳ (n + 1)) (prodM ℳ (numM ℳ 2) (numM ℳ 3)))) := by
    rw [mem_funsM]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases (hmem_iff p).mp hp with ⟨q, sym, rfl⟩ | ⟨sym, rfl⟩
      · obtain ⟨hb1, hb2, hb3⟩ := transitionCode_bounds M q sym
        exact (kpairM_mem_prodM ℳ).mpr
          ⟨(kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ (Nat.lt_succ_of_lt q.isLt), numM_lt_mem ℳ sym.isLt⟩,
           (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ hb1,
             (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ hb2, numM_lt_mem ℳ hb3⟩⟩⟩
      · exact (kpairM_mem_prodM ℳ).mpr
          ⟨(kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ (Nat.lt_succ_self n), numM_lt_mem ℳ sym.isLt⟩,
           (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ (Nat.lt_succ_self n),
             (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ sym.isLt, numM_lt_mem ℳ (by decide : 1 < 3)⟩⟩⟩
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prodM ℳ _ _ x).mp hx
      obtain ⟨qCode, hq, rfl⟩ := (mem_numM_iff ℳ).mp ha
      obtain ⟨symCode, hs, rfl⟩ := (mem_numM_iff ℳ).mp hb
      let o := transLookup M qCode symCode
      refine ⟨kpairM ℳ (numM ℳ o.1) (kpairM ℳ (numM ℳ o.2.1) (numM ℳ o.2.2)), ?_, ?_⟩
      · dsimp only
        rw [hmem_iff]
        by_cases hqn : qCode < n
        · left
          refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
          dsimp only [o, transLookup]; rw [dif_pos hqn, dif_pos hs]; rfl
        · have hqe : qCode = n := by omega
          subst qCode
          right
          refine ⟨⟨symCode, hs⟩, ?_⟩
          dsimp only [o, transLookup]; rw [dif_neg (Nat.lt_irrefl n)]; rfl
      · intro y hy
        rcases (hmem_iff _).mp hy with ⟨q, sym, heq⟩ | ⟨sym, heq⟩
        · obtain ⟨h1, rfl⟩ := kpairM_inj ℳ heq
          obtain ⟨hq1, hs1⟩ := kpairM_inj ℳ h1
          have hqc : qCode = q.val := numM_injective ℳ hq1
          have hsc : symCode = sym.val := numM_injective ℳ hs1
          subst qCode symCode
          dsimp only [o, transLookup]
          rw [dif_pos q.isLt, dif_pos sym.isLt]
        · obtain ⟨h1, rfl⟩ := kpairM_inj ℳ heq
          obtain ⟨hq1, hs1⟩ := kpairM_inj ℳ h1
          have hqc : qCode = n := numM_injective ℳ hq1
          have hsc : symCode = sym.val := numM_injective ℳ hs1
          subst qCode symCode
          dsimp only [o, transLookup]
          rw [dif_neg (Nat.lt_irrefl n)]
  refine ⟨hfuns, fun qCode symCode hq hs => ?_⟩
  have hx : ℳ.mem (kpairM ℳ (numM ℳ qCode) (numM ℳ symCode))
      (prodM ℳ (numM ℳ (n + 1)) (numM ℳ 2)) :=
    (kpairM_mem_prodM ℳ).mpr ⟨numM_lt_mem ℳ hq, numM_lt_mem ℳ hs⟩
  let o := transLookup M qCode symCode
  have hmem_pair : ℳ.mem (kpairM ℳ (kpairM ℳ (numM ℳ qCode) (numM ℳ symCode))
      (kpairM ℳ (numM ℳ o.1) (kpairM ℳ (numM ℳ o.2.1) (numM ℳ o.2.2)))) (instrTableM ℳ M) := by
    rw [hmem_iff]
    by_cases hqn : qCode < n
    · left; refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]; rw [dif_pos hqn, dif_pos hs]; rfl
    · have hqe : qCode = n := by omega
      subst qCode
      right; refine ⟨⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]; rw [dif_neg (Nat.lt_irrefl n)]; rfl
  exact appM_of_mem_funsM hfuns hx hmem_pair

/- Blank Tape and Tape Update by Separation in `ℳ` -/

private lemma exists_emptyTapeM (ℳ : ZFCModel) :
    ∃ f : ℳ.V, ∀ p, ℳ.mem p f ↔ ∃ i, ℳ.mem i (intSetM ℳ) ∧ p = kpairM ℳ i (numM ℳ 0) := by
  let ψ : SetTheorySemisentence 1 :=
    f“p. ∃ i ∈ !Constant14.integers, p = !kpair.dfn i (!(Constant14.numeral 0))”
  obtain ⟨f, hf⟩ := exists_sepM_sent ℳ ψ ![] (prodM ℳ (intSetM ℳ) (numM ℳ 2))
  refine ⟨f, fun p => (hf p).trans ?_⟩
  have hψ : evM ℳ ![p] ψ ↔ ∃ i, ℳ.mem i (intSetM ℳ) ∧ p = kpairM ℳ i (numM ℳ 0) := by
    dsimp only [ψ]
    rw [ev_faf_bexs (et_const0 (dc_integers ℳ) _)]
    refine exists_congr fun i => and_congr_right fun _ => ?_
    exact ev_faf_eq (et_bvar3 ℳ i (intSetM ℳ) p _)
      (et_comp2 (ev_kpair ℳ) (et_bvar2 ℳ _ i _) (et_const0 (dc_numeral ℳ 0) _))
  rw [hψ]
  refine ⟨And.right, fun ⟨i, hi, hp⟩ => ⟨?_, i, hi, hp⟩⟩
  subst hp
  exact (kpairM_mem_prodM ℳ).mpr ⟨hi, numM_lt_mem ℳ (by decide : 0 < 2)⟩

private noncomputable def emptyTapeM (ℳ : ZFCModel) : ℳ.V := (exists_emptyTapeM ℳ).choose

private lemma mem_emptyTapeM (ℳ : ZFCModel) (p : ℳ.V) :
    ℳ.mem p (emptyTapeM ℳ) ↔ ∃ i, ℳ.mem i (intSetM ℳ) ∧ p = kpairM ℳ i (numM ℳ 0) :=
  (exists_emptyTapeM ℳ).choose_spec p

private lemma emptyTapeM_funs_and_app (ℳ : ZFCModel) :
    ℳ.mem (emptyTapeM ℳ) (funsM ℳ (intSetM ℳ) (numM ℳ 2)) ∧
      ∀ i, ℳ.mem i (intSetM ℳ) → appM ℳ (emptyTapeM ℳ) i = numM ℳ 0 := by
  have hf : ℳ.mem (emptyTapeM ℳ) (funsM ℳ (intSetM ℳ) (numM ℳ 2)) := by
    rw [mem_funsM]
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := (mem_emptyTapeM ℳ p).mp hp
      exact (kpairM_mem_prodM ℳ).mpr ⟨hi, numM_lt_mem ℳ (by decide : 0 < 2)⟩
    · intro x hx
      refine ⟨numM ℳ 0, (mem_emptyTapeM ℳ _).mpr ⟨x, hx, rfl⟩, fun y hy => ?_⟩
      obtain ⟨i, _, heq⟩ := (mem_emptyTapeM ℳ _).mp hy
      exact (kpairM_inj ℳ heq).2
  exact ⟨hf, fun i hi => appM_of_mem_funsM hf hi ((mem_emptyTapeM ℳ _).mpr ⟨i, hi, rfl⟩)⟩

private lemma dc_emptyTape (ℳ : ZFCModel) :
    DefinesConst ℳ Constant14.emptyTape (emptyTapeM ℳ) := by
  intro f
  unfold Constant14.emptyTape
  rw [evM_and]
  rw [ev_faf_mem (et_bvar1 ℳ f _)
        (et_comp2 (ev_function ℳ) (et_const0 (dc_numeral ℳ 2) _) (et_const0 (dc_integers ℳ) _)),
      ev_faf_ball (et_const0 (dc_integers ℳ) _)]
  refine (and_congr Iff.rfl (forall_congr' fun i => imp_congr Iff.rfl
      (?_ : _ ↔ appM ℳ f i = numM ℳ 0))).trans ?_
  · exact ev_faf_eq
      (et_comp2 (ev_value ℳ) (et_bvar3 ℳ i (intSetM ℳ) f _) (et_bvar1 ℳ i _))
      (et_const0 (dc_numeral ℳ 0) _)
  · obtain ⟨he_funs, he_app⟩ := emptyTapeM_funs_and_app ℳ
    constructor
    · rintro ⟨hf, hall⟩
      exact funsM_ext hf he_funs fun w hw => (hall w hw).trans (he_app w hw).symm
    · rintro rfl
      exact ⟨he_funs, he_app⟩

private lemma exists_updateTapeM (ℳ : ZFCModel) (g posSet valSet : ℳ.V) :
    ∃ g' : ℳ.V, ∀ p, ℳ.mem p g' ↔
      ∃ i, ℳ.mem i (intSetM ℳ) ∧ ∃ v, ℳ.mem v (numM ℳ 2) ∧
        p = kpairM ℳ i v ∧ ((i = posSet ∧ v = valSet) ∨ (i ≠ posSet ∧ ℳ.mem p g)) := by
  let ψ : SetTheorySemisentence 4 :=
    f“p g pos val. ∃ i ∈ !Constant14.integers, ∃ v ∈ !(Constant14.numeral 2),
      p = !kpair.dfn i v ∧ ((i = pos ∧ v = val) ∨ (i ≠ pos ∧ p ∈ g))”
  obtain ⟨g', hg'⟩ := exists_sepM_sent ℳ ψ ![g, posSet, valSet] (prodM ℳ (intSetM ℳ) (numM ℳ 2))
  refine ⟨g', fun p => (hg' p).trans ?_⟩
  have hψ : evM ℳ ![p, g, posSet, valSet] ψ ↔
      ∃ i, ℳ.mem i (intSetM ℳ) ∧ ∃ v, ℳ.mem v (numM ℳ 2) ∧
        p = kpairM ℳ i v ∧ ((i = posSet ∧ v = valSet) ∨ (i ≠ posSet ∧ ℳ.mem p g)) := by
    dsimp only [ψ]
    rw [ev_faf_bexs (et_const0 (dc_integers ℳ) _)]
    refine exists_congr fun i => and_congr_right fun _ => ?_
    rw [ev_faf_bexs (et_const0 (dc_numeral ℳ 2) _)]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [evM_and, evM_or, evM_and, evM_and]
    refine and_congr
      (ev_faf_eq (et_bvar5 ℳ v (numM ℳ 2) i (intSetM ℳ) p _)
        (et_comp2 (ev_kpair ℳ) (et_bvar4 ℳ _ v (numM ℳ 2) i _) (et_bvar2 ℳ _ v _)))
      (or_congr
        (and_congr
          (ev_faf_eq (et_bvar3 ℳ v (numM ℳ 2) i _)
            (et_bvar8 ℳ _ v (numM ℳ 2) i (intSetM ℳ) p g posSet _))
          (ev_faf_eq (et_bvar1 ℳ v _)
            (et_bvar9 ℳ _ v (numM ℳ 2) i (intSetM ℳ) p g posSet valSet _)))
        (and_congr
          (ev_faf_ne (et_bvar3 ℳ v (numM ℳ 2) i _)
            (et_bvar8 ℳ _ v (numM ℳ 2) i (intSetM ℳ) p g posSet _))
          (ev_faf_mem (et_bvar5 ℳ v (numM ℳ 2) i (intSetM ℳ) p _)
            (et_bvar7 ℳ _ v (numM ℳ 2) i (intSetM ℳ) p g _))))
  rw [hψ]
  refine ⟨And.right, fun ⟨i, hi, v, hv, hp, hcase⟩ => ⟨?_, i, hi, v, hv, hp, hcase⟩⟩
  subst hp
  exact (kpairM_mem_prodM ℳ).mpr ⟨hi, hv⟩

private noncomputable def updateTapeM (ℳ : ZFCModel) (g posSet valSet : ℳ.V) : ℳ.V :=
  (exists_updateTapeM ℳ g posSet valSet).choose

private lemma mem_updateTapeM (ℳ : ZFCModel) (g posSet valSet p : ℳ.V) :
    ℳ.mem p (updateTapeM ℳ g posSet valSet) ↔
      ∃ i, ℳ.mem i (intSetM ℳ) ∧ ∃ v, ℳ.mem v (numM ℳ 2) ∧
        p = kpairM ℳ i v ∧ ((i = posSet ∧ v = valSet) ∨ (i ≠ posSet ∧ ℳ.mem p g)) :=
  (exists_updateTapeM ℳ g posSet valSet).choose_spec p

private lemma updateTapeM_funs_and_app {ℳ : ZFCModel} {g posSet valSet : ℳ.V}
    (hg : ℳ.mem g (funsM ℳ (intSetM ℳ) (numM ℳ 2))) (hval : ℳ.mem valSet (numM ℳ 2)) :
    ℳ.mem (updateTapeM ℳ g posSet valSet) (funsM ℳ (intSetM ℳ) (numM ℳ 2)) ∧
      ∀ w, ℳ.mem w (intSetM ℳ) →
        appM ℳ (updateTapeM ℳ g posSet valSet) w =
          if w = posSet then valSet else appM ℳ g w := by
  obtain ⟨hg_sub, hg_uniq⟩ := (mem_funsM ℳ (intSetM ℳ) (numM ℳ 2) g).mp hg
  have hf : ℳ.mem (updateTapeM ℳ g posSet valSet) (funsM ℳ (intSetM ℳ) (numM ℳ 2)) := by
    rw [mem_funsM]
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi, v, hv, rfl, _⟩ := (mem_updateTapeM ℳ g posSet valSet p).mp hp
      exact (kpairM_mem_prodM ℳ).mpr ⟨hi, hv⟩
    · intro w hw
      by_cases hwp : w = posSet
      · refine ⟨valSet, (mem_updateTapeM ℳ _ _ _ _).mpr ⟨w, hw, valSet, hval, rfl, Or.inl ⟨hwp, rfl⟩⟩,
          fun y hy => ?_⟩
        obtain ⟨i, _, v, _, heq, hcase⟩ := (mem_updateTapeM ℳ _ _ _ _).mp hy
        obtain ⟨rfl, rfl⟩ := kpairM_inj ℳ heq
        rcases hcase with ⟨_, rfl⟩ | ⟨hne, _⟩
        · rfl
        · exact (hne hwp).elim
      · obtain ⟨y0, hy0_mem, hy0_eq⟩ := hg_uniq w hw
        have hy0_cod : ℳ.mem y0 (numM ℳ 2) := ((kpairM_mem_prodM ℳ).mp (hg_sub _ hy0_mem)).2
        refine ⟨y0, (mem_updateTapeM ℳ _ _ _ _).mpr ⟨w, hw, y0, hy0_cod, rfl, Or.inr ⟨hwp, hy0_mem⟩⟩,
          fun y hy => ?_⟩
        obtain ⟨i, _, v, _, heq, hcase⟩ := (mem_updateTapeM ℳ _ _ _ _).mp hy
        obtain ⟨rfl, rfl⟩ := kpairM_inj ℳ heq
        rcases hcase with ⟨heqp, _⟩ | ⟨_, hpg⟩
        · exact (hwp heqp).elim
        · exact hy0_eq y hpg
  refine ⟨hf, fun w hw => ?_⟩
  by_cases hwp : w = posSet
  · rw [if_pos hwp]
    exact appM_of_mem_funsM hf hw
      ((mem_updateTapeM ℳ _ _ _ _).mpr ⟨w, hw, valSet, hval, rfl, Or.inl ⟨hwp, rfl⟩⟩)
  · rw [if_neg hwp]
    obtain ⟨y0, hy0_mem, _⟩ := hg_uniq w hw
    have hy0_cod : ℳ.mem y0 (numM ℳ 2) := ((kpairM_mem_prodM ℳ).mp (hg_sub _ hy0_mem)).2
    have ha1 := appM_of_mem_funsM hf hw
      ((mem_updateTapeM ℳ _ _ _ _).mpr ⟨w, hw, y0, hy0_cod, rfl, Or.inr ⟨hwp, hy0_mem⟩⟩)
    have ha2 := appM_of_mem_funsM hg hw hy0_mem
    rw [ha1, ha2]

/- One-Step Function `zfcStepFnM`, `nextStepM`, and `orbitM` in `ℳ` -/

private noncomputable def zfcStepFnM (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) (z : ℳ.V) : ℳ.V :=
  if ℳ.mem z (cfgSetM ℳ (n + 1)) then
    let qSet := pi1M ℳ z
    let posSet := pi1M ℳ (pi2M ℳ z)
    let g := pi2M ℳ (pi2M ℳ z)
    let symSet := appM ℳ g posSet
    let t := appM ℳ (instrTableM ℳ M) (kpairM ℳ qSet symSet)
    let qNext := pi1M ℳ t
    let wrSet := pi1M ℳ (pi2M ℳ t)
    let dirSet := pi2M ℳ (pi2M ℳ t)
    let posNext :=
      if dirSet = numM ℳ 0 then intPredM ℳ posSet
      else if dirSet = numM ℳ 1 then posSet
      else intSuccM ℳ posSet
    let gNext := updateTapeM ℳ g posSet wrSet
    kpairM ℳ qNext (kpairM ℳ posNext gNext)
  else emptyM ℳ

private lemma zfcStepFnM_of_cfg (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n))
    (qCode : ℕ) (posSet g : ℳ.V)
    (hq : qCode < n + 1) (hpos : ℳ.mem posSet (intSetM ℳ))
    (hg : ℳ.mem g (funsM ℳ (intSetM ℳ) (numM ℳ 2)))
    (symCode : ℕ) (hs : symCode < 2) (hsym : appM ℳ g posSet = numM ℳ symCode) :
    let o := transLookup M qCode symCode
    let posNext := if o.2.2 = 0 then intPredM ℳ posSet
      else if o.2.2 = 1 then posSet else intSuccM ℳ posSet
    zfcStepFnM ℳ M (kpairM ℳ (numM ℳ qCode) (kpairM ℳ posSet g)) =
      kpairM ℳ (numM ℳ o.1)
        (kpairM ℳ posNext (updateTapeM ℳ g posSet (numM ℳ o.2.1))) := by
  let z := kpairM ℳ (numM ℳ qCode) (kpairM ℳ posSet g)
  have hz : ℳ.mem z (cfgSetM ℳ (n + 1)) :=
    (mem_cfgSetM_iff ℳ).mpr ⟨qCode, posSet, g, hq, hpos, hg, rfl⟩
  unfold zfcStepFnM
  rw [if_pos hz]
  dsimp only
  have hp1 : pi1M ℳ z = numM ℳ qCode := pi1M_kpairM ℳ _ _
  have hp2 : pi2M ℳ z = kpairM ℳ posSet g := pi2M_kpairM ℳ _ _
  have hpos_eq : pi1M ℳ (pi2M ℳ z) = posSet := by rw [hp2, pi1M_kpairM]
  have hgv : pi2M ℳ (pi2M ℳ z) = g := by rw [hp2, pi2M_kpairM]
  obtain ⟨_, happ⟩ := instrTableM_funs_and_app ℳ M
  let o := transLookup M qCode symCode
  have ht : appM ℳ (instrTableM ℳ M)
      (kpairM ℳ (pi1M ℳ z) (appM ℳ (pi2M ℳ (pi2M ℳ z)) (pi1M ℳ (pi2M ℳ z)))) =
      kpairM ℳ (numM ℳ o.1) (kpairM ℳ (numM ℳ o.2.1) (numM ℳ o.2.2)) := by
    rw [hp1, hgv, hpos_eq, hsym]
    exact happ qCode symCode hq hs
  rw [ht, pi1M_kpairM, pi2M_kpairM, pi1M_kpairM, pi2M_kpairM, hpos_eq, hgv]
  congr 1; congr 1
  have hd0 : (numM ℳ o.2.2 = numM ℳ 0) ↔ (o.2.2 = 0) := (numM_injective ℳ).eq_iff
  have hd1 : (numM ℳ o.2.2 = numM ℳ 1) ↔ (o.2.2 = 1) := (numM_injective ℳ).eq_iff
  simp only [hd0, hd1]
  rfl

private lemma zfcStepFnM_mem_cfg (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) {z : ℳ.V} (hz : ℳ.mem z (cfgSetM ℳ (n + 1))) :
    ℳ.mem (zfcStepFnM ℳ M z) (cfgSetM ℳ (n + 1)) := by
  obtain ⟨qCode, posSet, g, hq, hpos, hg, rfl⟩ := (mem_cfgSetM_iff ℳ).mp hz
  have hsym_mem : ℳ.mem (appM ℳ g posSet) (numM ℳ 2) := appM_mem_codomain hg hpos
  obtain ⟨symCode, hs, hsym⟩ := (mem_numM_iff ℳ).mp hsym_mem
  rw [zfcStepFnM_of_cfg ℳ M qCode posSet g hq hpos hg symCode hs hsym]
  let o := transLookup M qCode symCode
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
    dsimp only [o, transLookup]
    by_cases hqn : qCode < n
    · rw [dif_pos hqn, dif_pos hs]
      exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
    · rw [dif_neg hqn]; dsimp only; exact ⟨Nat.lt_succ_self n, hs, by decide⟩
  refine (mem_cfgSetM_iff ℳ).mpr ⟨o.1, _, updateTapeM ℳ g posSet (numM ℳ o.2.1), hob.1, ?_,
    (updateTapeM_funs_and_app hg (numM_lt_mem ℳ hob.2.1)).1, rfl⟩
  split_ifs
  · exact intPredM_mem ℳ hpos
  · exact hpos
  · exact intSuccM_mem ℳ hpos

private lemma ev_nextConfig_iff (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) (z' z : ℳ.V) :
    evM ℳ ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      ℳ.mem z (cfgSetM ℳ (n + 1)) ∧ z' = zfcStepFnM ℳ M z := by
  unfold Constant14.nextConfig
  rw [evM_and, evM_and]
  rw [ev_faf_mem (et_bvar2 ℳ z' z _) (et_const0 (dc_configSet ℳ (n + 1)) _),
      ev_faf_mem (et_bvar1 ℳ z' _) (et_const0 (dc_configSet ℳ (n + 1)) _)]
  by_cases hz : ℳ.mem z (cfgSetM ℳ (n + 1))
  · simp only [hz, true_and]
    obtain ⟨qCode, posSet, g, hq, hpos, hg, rfl⟩ := (mem_cfgSetM_iff ℳ).mp hz
    let z0 := kpairM ℳ (numM ℳ qCode) (kpairM ℳ posSet g)
    have hsym_mem : ℳ.mem (appM ℳ g posSet) (numM ℳ 2) := appM_mem_codomain hg hpos
    obtain ⟨symCode, hs, hsym⟩ := (mem_numM_iff ℳ).mp hsym_mem
    let o := transLookup M qCode symCode
    have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
      dsimp only [o, transLookup]
      by_cases hqn : qCode < n
      · rw [dif_pos hqn, dif_pos hs]
        exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
      · rw [dif_neg hqn]; dsimp only; exact ⟨Nat.lt_succ_self n, hs, by decide⟩
    let tVal := kpairM ℳ (numM ℳ o.1) (kpairM ℳ (numM ℳ o.2.1) (numM ℳ o.2.2))
    let posNext := if o.2.2 = 0 then intPredM ℳ posSet
      else if o.2.2 = 1 then posSet else intSuccM ℳ posSet
    have hstep_val := zfcStepFnM_of_cfg ℳ M qCode posSet g hq hpos hg symCode hs hsym
    change zfcStepFnM ℳ M z0 = kpairM ℳ (numM ℳ o.1)
      (kpairM ℳ posNext (updateTapeM ℳ g posSet (numM ℳ o.2.1))) at hstep_val
    obtain ⟨_, happ⟩ := instrTableM_funs_and_app ℳ M
    have htVal_eq : appM ℳ (instrTableM ℳ M)
        (kpairM ℳ (pi1M ℳ z0) (appM ℳ (pi2M ℳ (pi2M ℳ z0)) (pi1M ℳ (pi2M ℳ z0)))) = tVal := by
      dsimp [z0, tVal]
      rw [pi1M_kpairM, pi2M_kpairM, pi1M_kpairM, pi2M_kpairM, hsym]
      exact happ qCode symCode hq hs
    rw [evM_exs]
    refine (and_congr Iff.rfl (exists_congr fun t => (?_ : _ ↔
        (t = tVal ∧
         pi1M ℳ z' = pi1M ℳ t ∧
         ((pi2M ℳ (pi2M ℳ t) = numM ℳ 0 ∧
             evM ℳ ![pi1M ℳ (pi2M ℳ z'), pi1M ℳ (pi2M ℳ z0)] Constant14.integerPred.dfn) ∨
           (pi2M ℳ (pi2M ℳ t) = numM ℳ 1 ∧ pi1M ℳ (pi2M ℳ z') = pi1M ℳ (pi2M ℳ z0)) ∨
           (pi2M ℳ (pi2M ℳ t) = numM ℳ 2 ∧
             evM ℳ ![pi1M ℳ (pi2M ℳ z'), pi1M ℳ (pi2M ℳ z0)] Constant14.integerSucc.dfn)) ∧
         appM ℳ (pi2M ℳ (pi2M ℳ z')) (pi1M ℳ (pi2M ℳ z0)) = pi1M ℳ (pi2M ℳ t) ∧
         ∀ k, ℳ.mem k (intSetM ℳ) → k ≠ pi1M ℳ (pi2M ℳ z0) →
           appM ℳ (pi2M ℳ (pi2M ℳ z')) k = appM ℳ (pi2M ℳ (pi2M ℳ z0)) k)))).trans ?_
    · rw [evM_and, evM_and, evM_and, evM_and]
      refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
      · rw [ev_faf_eq (et_bvar1 ℳ t _)
          (et_comp2 (ev_value ℳ) (et_const0 (dc_instructionTable ℳ M) _)
            (et_comp2 (ev_kpair ℳ)
              (et_comp1 (ev_pi1 ℳ) (et_bvar4 ℳ _ t z' z0 _))
              (et_comp2 (ev_value ℳ)
                (et_comp1 (ev_pi2 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar4 ℳ _ t z' z0 _)))
                (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar4 ℳ _ t z' z0 _)))))),
          htVal_eq]
      · exact ev_faf_eq
          (et_comp1 (ev_pi1 ℳ) (et_bvar2 ℳ t z' _))
          (et_comp1 (ev_pi1 ℳ) (et_bvar2 ℳ _ t _))
      · rw [evM_or, evM_or, evM_and, evM_and, evM_and]
        refine or_congr
          (and_congr
            (ev_faf_eq (et_comp1 (ev_pi2 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar1 ℳ t _)))
              (et_const0 (dc_numeral ℳ 0) _))
            (ev_nest2 Constant14.integerPred.dfn
              (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar2 ℳ t z' _)))
              (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar3 ℳ t z' z0 _)))))
          (or_congr
            (and_congr
              (ev_faf_eq (et_comp1 (ev_pi2 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar1 ℳ t _)))
                (et_const0 (dc_numeral ℳ 1) _))
              (ev_faf_eq
                (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar2 ℳ t z' _)))
                (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar4 ℳ _ t z' z0 _)))))
            (and_congr
              (ev_faf_eq (et_comp1 (ev_pi2 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar1 ℳ t _)))
                (et_const0 (dc_numeral ℳ 2) _))
              (ev_nest2 Constant14.integerSucc.dfn
                (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar2 ℳ t z' _)))
                (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar3 ℳ t z' z0 _))))))
      · exact ev_faf_eq
          (et_comp2 (ev_value ℳ)
            (et_comp1 (ev_pi2 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar2 ℳ t z' _)))
            (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar3 ℳ t z' z0 _))))
          (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar2 ℳ _ t _)))
      · rw [ev_faf_ball (et_const0 (dc_integers ℳ) _)]
        refine forall_congr' fun k => imp_congr Iff.rfl ?_
        rw [evM_imp]
        exact imp_congr
          (ev_faf_ne (et_bvar1 ℳ k _)
            (et_comp1 (ev_pi1 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar6 ℳ _ k (intSetM ℳ) t z' z0 _))))
          (ev_faf_eq
            (et_comp2 (ev_value ℳ)
              (et_comp1 (ev_pi2 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar4 ℳ k (intSetM ℳ) t z' _)))
              (et_bvar1 ℳ k _))
            (et_comp2 (ev_value ℳ)
              (et_comp1 (ev_pi2 ℳ) (et_comp1 (ev_pi2 ℳ) (et_bvar6 ℳ _ k (intSetM ℳ) t z' z0 _)))
              (et_bvar2 ℳ _ k _)))
    · obtain ⟨hu_funs, hu_app⟩ := updateTapeM_funs_and_app hg (numM_lt_mem ℳ hob.2.1) (posSet := posSet)
      constructor
      · rintro ⟨hz', t, rfl, hq_eq, hdir, hwr, hrest⟩
        obtain ⟨q2, pos2, g2, _, _, hg2, rfl⟩ := (mem_cfgSetM_iff ℳ).mp hz'
        dsimp [z0, tVal] at hq_eq hdir hwr hrest
        rw [pi1M_kpairM, pi1M_kpairM] at hq_eq
        rw [pi2M_kpairM, pi2M_kpairM, pi2M_kpairM, pi1M_kpairM, pi2M_kpairM, pi1M_kpairM] at hdir
        rw [pi2M_kpairM, pi2M_kpairM, pi2M_kpairM, pi1M_kpairM, pi2M_kpairM, pi1M_kpairM] at hwr
        simp only [pi2M_kpairM, pi1M_kpairM] at hrest
        rw [hstep_val, hq_eq]
        congr 1; congr 1
        · have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · have h01 : numM ℳ 0 ≠ numM ℳ 1 := fun h => absurd (numM_injective ℳ h) (by decide)
            have h02 : numM ℳ 0 ≠ numM ℳ 2 := fun h => absurd (numM_injective ℳ h) (by decide)
            simp only [true_and, h01, h02, false_and, or_false] at hdir
            rw [ev_integerPred] at hdir
            dsimp [posNext]; rw [hdv]; simpa using hdir
          · have h10 : numM ℳ 1 ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by decide)
            have h12 : numM ℳ 1 ≠ numM ℳ 2 := fun h => absurd (numM_injective ℳ h) (by decide)
            simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
            dsimp [posNext]; rw [hdv]; simpa using hdir
          · have h20 : numM ℳ 2 ≠ numM ℳ 0 := fun h => absurd (numM_injective ℳ h) (by decide)
            have h21 : numM ℳ 2 ≠ numM ℳ 1 := fun h => absurd (numM_injective ℳ h) (by decide)
            simp only [true_and, h20, h21, false_and, false_or] at hdir
            rw [ev_integerSucc] at hdir
            dsimp [posNext]; rw [hdv]; simpa using hdir
        · refine funsM_ext hg2 hu_funs fun k hk => ?_
          rw [hu_app k hk]
          by_cases hkp : k = posSet
          · rw [if_pos hkp, hkp, hwr]
          · rw [if_neg hkp, hrest k hk hkp]
      · rintro rfl
        refine ⟨zfcStepFnM_mem_cfg ℳ M hz, tVal, rfl, ?_, ?_, ?_, ?_⟩
        · rw [hstep_val]; dsimp [tVal]; rw [pi1M_kpairM, pi1M_kpairM]
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2M_kpairM, pi2M_kpairM, pi2M_kpairM, pi1M_kpairM, pi2M_kpairM, pi1M_kpairM]
          have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · left; refine ⟨rfl, ?_⟩
            rw [ev_integerPred]; dsimp [posNext]; rw [hdv]; rfl
          · right; left; refine ⟨rfl, ?_⟩
            dsimp [posNext]; rw [hdv]; rfl
          · right; right; refine ⟨rfl, ?_⟩
            rw [ev_integerSucc]; dsimp [posNext]; rw [hdv]; rfl
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2M_kpairM, pi2M_kpairM, pi2M_kpairM, pi1M_kpairM, pi2M_kpairM, pi1M_kpairM]
          rw [hu_app posSet hpos, if_pos rfl]
        · intro k hk hne
          dsimp [z0] at hne
          rw [pi2M_kpairM, pi1M_kpairM] at hne
          rw [hstep_val]; dsimp [z0]
          rw [pi2M_kpairM, pi2M_kpairM, pi2M_kpairM, pi2M_kpairM]
          rw [hu_app k hk, if_neg hne]
  · simp [hz]

private lemma exists_nextStepM (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) :
    ∃ p : ℳ.V, ∀ e, ℳ.mem e p ↔
      ∃ z, ℳ.mem z (cfgSetM ℳ (n + 1)) ∧ e = kpairM ℳ z (zfcStepFnM ℳ M z) := by
  let ψ : SetTheorySemisentence 1 :=
    f“e. ∃ z ∈ !(Constant14.configSet (n + 1)), ∃ z' ∈ !(Constant14.configSet (n + 1)),
      e = !kpair.dfn z z' ∧ !(Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) z' z”
  obtain ⟨p, hp⟩ := exists_sepM_sent ℳ ψ ![]
    (prodM ℳ (cfgSetM ℳ (n + 1)) (cfgSetM ℳ (n + 1)))
  refine ⟨p, fun e => (hp e).trans ?_⟩
  have hψ : evM ℳ ![e] ψ ↔
      ∃ z, ℳ.mem z (cfgSetM ℳ (n + 1)) ∧ e = kpairM ℳ z (zfcStepFnM ℳ M z) := by
    dsimp only [ψ]
    rw [ev_faf_bexs (et_const0 (dc_configSet ℳ (n + 1)) _)]
    refine (?_ : _ ↔ ∃ z, ℳ.mem z (cfgSetM ℳ (n + 1)) ∧
        ∃ z', ℳ.mem z' (cfgSetM ℳ (n + 1)) ∧
          e = kpairM ℳ z z' ∧ z' = zfcStepFnM ℳ M z).trans ?_
    · refine exists_congr fun z => and_congr_right fun hz => ?_
      rw [ev_faf_bexs (et_const0 (dc_configSet ℳ (n + 1)) _)]
      refine exists_congr fun z' => and_congr_right fun _ => ?_
      rw [evM_and]
      rw [ev_faf_eq (et_bvar5 ℳ z' _ z _ e _)
            (et_comp2 (ev_kpair ℳ) (et_bvar4 ℳ _ z' _ z _) (et_bvar2 ℳ _ z' _)),
          ev_nest2 (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))
            (et_bvar1 ℳ z' _) (et_bvar3 ℳ z' _ z _),
          ev_nextConfig_iff ℳ M z' z]
      exact and_congr Iff.rfl ⟨And.right, fun h => ⟨hz, h⟩⟩
    · constructor
      · rintro ⟨z, hz, z', _, rfl, rfl⟩; exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, zfcStepFnM ℳ M z, zfcStepFnM_mem_cfg ℳ M hz, rfl, rfl⟩
  rw [hψ]
  refine ⟨And.right, fun ⟨z, hz, he⟩ => ⟨?_, z, hz, he⟩⟩
  subst he
  exact (kpairM_mem_prodM ℳ).mpr ⟨hz, zfcStepFnM_mem_cfg ℳ M hz⟩

private noncomputable def nextStepM (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) : ℳ.V :=
  (exists_nextStepM ℳ M).choose

private lemma mem_nextStepM (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) (e : ℳ.V) :
    ℳ.mem e (nextStepM ℳ M) ↔
      ∃ z, ℳ.mem z (cfgSetM ℳ (n + 1)) ∧ e = kpairM ℳ z (zfcStepFnM ℳ M z) :=
  (exists_nextStepM ℳ M).choose_spec e

private lemma nextStepM_funs_and_app (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) :
    ℳ.mem (nextStepM ℳ M) (funsM ℳ (cfgSetM ℳ (n + 1)) (cfgSetM ℳ (n + 1))) ∧
      ∀ z, ℳ.mem z (cfgSetM ℳ (n + 1)) → appM ℳ (nextStepM ℳ M) z = zfcStepFnM ℳ M z := by
  have hf : ℳ.mem (nextStepM ℳ M) (funsM ℳ (cfgSetM ℳ (n + 1)) (cfgSetM ℳ (n + 1))) := by
    rw [mem_funsM]
    refine ⟨?_, ?_⟩
    · intro e he
      obtain ⟨z, hz, rfl⟩ := (mem_nextStepM ℳ M e).mp he
      exact (kpairM_mem_prodM ℳ).mpr ⟨hz, zfcStepFnM_mem_cfg ℳ M hz⟩
    · intro z hz
      refine ⟨zfcStepFnM ℳ M z, (mem_nextStepM ℳ M _).mpr ⟨z, hz, rfl⟩, fun y hy => ?_⟩
      obtain ⟨z1, _, heq⟩ := (mem_nextStepM ℳ M _).mp hy
      obtain ⟨rfl, rfl⟩ := kpairM_inj ℳ heq
      rfl
  exact ⟨hf, fun z hz => appM_of_mem_funsM hf hz ((mem_nextStepM ℳ M _).mpr ⟨z, hz, rfl⟩)⟩

private lemma dc_nextStep (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) :
    DefinesConst ℳ (Constant14.nextStep (n + 1) (Constant14.instructionTable M))
      (nextStepM ℳ M) := by
  intro p
  unfold Constant14.nextStep
  change evM ℳ ![p] (∀¹ _) ↔ _
  rw [evM_all]
  refine (?_ : _ ↔ ∀ e : ℳ.V, ℳ.mem e p ↔ ℳ.mem e (nextStepM ℳ M)).trans
    ⟨fun h => extM ℳ h, fun h e => by rw [h]⟩
  refine forall_congr' fun e => ?_
  rw [evM_iff]
  refine iff_congr (ev_faf_mem (et_bvar1 ℳ e _) (et_bvar3 ℳ _ e p _)) ?_
  rw [ev_faf_bexs (et_const0 (dc_configSet ℳ (n + 1)) _), mem_nextStepM]
  refine (?_ : _ ↔ ∃ z, ℳ.mem z (cfgSetM ℳ (n + 1)) ∧
      ∃ z', ℳ.mem z' (cfgSetM ℳ (n + 1)) ∧ e = kpairM ℳ z z' ∧ z' = zfcStepFnM ℳ M z).trans ?_
  · refine exists_congr fun z => and_congr_right fun hz => ?_
    rw [ev_faf_bexs (et_const0 (dc_configSet ℳ (n + 1)) _)]
    refine exists_congr fun z' => and_congr_right fun _ => ?_
    rw [evM_and]
    rw [ev_faf_eq (et_bvar5 ℳ z' _ z _ e _)
          (et_comp2 (ev_kpair ℳ) (et_bvar4 ℳ _ z' _ z _) (et_bvar2 ℳ _ z' _)),
        ev_nest2 (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))
          (et_bvar1 ℳ z' _) (et_bvar3 ℳ z' _ z _),
        ev_nextConfig_iff ℳ M z' z]
    exact and_congr Iff.rfl ⟨And.right, fun h => ⟨hz, h⟩⟩
  · constructor
    · rintro ⟨z, hz, z', _, rfl, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, zfcStepFnM ℳ M z, zfcStepFnM_mem_cfg ℳ M hz, rfl, rfl⟩

private noncomputable def initConfigM (ℳ : ZFCModel) : ℳ.V :=
  kpairM ℳ (numM ℳ 0) (kpairM ℳ (encodeIntM ℳ 0) (emptyTapeM ℳ))

private lemma dc_initialConfig (ℳ : ZFCModel) :
    DefinesConst ℳ Constant14.initialConfig (initConfigM ℳ) := by
  intro z
  unfold Constant14.initialConfig initConfigM
  exact ev_faf_eq (et_bvar1 ℳ z _)
    (et_comp2 (ev_kpair ℳ) (et_const0 (dc_numeral ℳ 0) _)
      (et_comp2 (ev_kpair ℳ) (et_const0 (dc_integerZero ℳ) _) (et_const0 (dc_emptyTape ℳ) _)))

private lemma exists_orbitM (ℳ : ZFCModel) {f x0 B : ℳ.V}
    (hx0 : ℳ.mem x0 B) (hclosed : ∀ y, ℳ.mem y B → ℳ.mem (appM ℳ f y) B) :
    ∃ O : ℳ.V, ∀ z, ℳ.mem z O ↔
      ∀ A : ℳ.V, (ℳ.mem x0 A ∧ ∀ y, ℳ.mem y A → ℳ.mem (appM ℳ f y) A) → ℳ.mem z A := by
  let ψ : SetTheorySemisentence 3 :=
    f“z f x0. ∀ A, (x0 ∈ A ∧ ∀ y ∈ A, !value.dfn f y ∈ A) → z ∈ A”
  obtain ⟨O, hO⟩ := exists_sepM_sent ℳ ψ ![f, x0] B
  refine ⟨O, fun z => (hO z).trans ?_⟩
  have hψ : evM ℳ ![z, f, x0] ψ ↔
      ∀ A : ℳ.V, (ℳ.mem x0 A ∧ ∀ y, ℳ.mem y A → ℳ.mem (appM ℳ f y) A) → ℳ.mem z A := by
    dsimp only [ψ]
    rw [evM_all]
    refine forall_congr' fun A => ?_
    rw [evM_imp, evM_and]
    refine imp_congr (and_congr ?_ ?_) (ev_faf_mem (et_bvar2 ℳ A z _) (et_bvar2 ℳ _ A _))
    · exact ev_faf_mem (et_bvar4 ℳ A z f x0 _) (et_bvar2 ℳ _ A _)
    · rw [ev_faf_ball (et_bvar1 ℳ A _)]
      refine forall_congr' fun y => imp_congr Iff.rfl ?_
      exact ev_faf_mem
        (et_comp2 (ev_value ℳ) (et_bvar5 ℳ y A A z f _) (et_bvar1 ℳ y _))
        (et_bvar4 ℳ _ y A A _)
  rw [hψ]
  exact ⟨And.right, fun hall => ⟨hall B ⟨hx0, hclosed⟩, hall⟩⟩

private lemma ev_orbit_iff (ℳ : ZFCModel) {f x0 B O : ℳ.V}
    (hf : ℳ.mem f (funsM ℳ B B)) (hx0 : ℳ.mem x0 B) :
    evM ℳ ![O, f, x0] Constant14.orbit ↔
      O = (exists_orbitM ℳ hx0 (fun _ hy => appM_mem_codomain hf hy)).choose := by
  let O0 := (exists_orbitM ℳ hx0 (fun _ hy => appM_mem_codomain hf hy)).choose
  have hO0 : ∀ z, ℳ.mem z O0 ↔
      ∀ A : ℳ.V, (ℳ.mem x0 A ∧ ∀ y, ℳ.mem y A → ℳ.mem (appM ℳ f y) A) → ℳ.mem z A :=
    (exists_orbitM ℳ hx0 (fun _ hy => appM_mem_codomain hf hy)).choose_spec
  unfold Constant14.orbit
  rw [evM_and]
  have hfn : evM ℳ ![O, f, x0]
      (Semiformula.nestFormulae SetTheory.IsFunction.dfn ![op(=).operator (#0 :> #2 :> ![])]) := by
    rw [ev_nest1 SetTheory.IsFunction.dfn (et_bvar2 ℳ O f _), ev_IsFunction]
    exact ⟨B, B, hf⟩
  simp only [hfn, true_and]
  rw [evM_all]
  refine (forall_congr' fun z => ?_).trans ⟨fun h => extM ℳ h, fun h z => by rw [h]⟩
  rw [evM_iff]
  refine iff_congr (ev_faf_mem (et_bvar1 ℳ z _) (et_bvar3 ℳ _ z O _)) ?_
  rw [evM_all, hO0 z]
  refine forall_congr' fun A => ?_
  rw [evM_imp, evM_and]
  refine imp_congr (and_congr ?_ ?_) (ev_faf_mem (et_bvar2 ℳ A z _) (et_bvar2 ℳ _ A _))
  · exact ev_faf_mem (et_bvar5 ℳ A z O f x0 _) (et_bvar2 ℳ _ A _)
  · rw [ev_faf_ball (et_bvar1 ℳ A _)]
    refine forall_congr' fun y => imp_congr Iff.rfl ?_
    exact ev_faf_mem
      (et_comp2 (ev_value ℳ) (et_bvar6 ℳ y A A z O f _) (et_bvar1 ℳ y _))
      (et_bvar4 ℳ _ y A A _)

/- Meta-Induction Simulation of Halting Machines in `ℳ` -/

private abbrev ExtCfg (n : ℕ) := Option (Fin n) × ℤ × Tape (Fin 2)

private def extInit (n : ℕ) [NeZero n] : ExtCfg n :=
  (some 0, 0, Tape.mk₁ [])

private def extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ExtCfg n → ExtCfg n
  | (none, pos, T) => (none, pos, T)
  | (some q, pos, T) =>
    match M q T.head with
    | none => (none, pos, T)
    | some (q', Stmt.write sym d) =>
      let pos' := match d with
        | Dir.left => pos - 1
        | Dir.right => pos + 1
      (q', pos', (T.write sym).move d)

private lemma blank_tape_nth (i : ℤ) : (Tape.mk₁ ([] : List (Fin 2))).nth i = 0 := by
  cases i with
  | ofNat k =>
    cases k <;> simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]
  | negSucc k =>
    simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]

private lemma sim_invariant (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    let c := (extStep M)^[k] (extInit n)
    ∃ g : ℳ.V, ℳ.mem g (funsM ℳ (intSetM ℳ) (numM ℳ 2)) ∧
      (appM ℳ (nextStepM ℳ M))^[k] (initConfigM ℳ) =
        kpairM ℳ (numM ℳ (Constant14.stateCode c.1)) (kpairM ℳ (encodeIntM ℳ c.2.1) g) ∧
      ∀ m : ℤ, appM ℳ g (encodeIntM ℳ m) = numM ℳ (c.2.2.nth (m - c.2.1)).val := by
  induction k with
  | zero =>
    obtain ⟨he_funs, he_app⟩ := emptyTapeM_funs_and_app ℳ
    refine ⟨emptyTapeM ℳ, he_funs, rfl, fun m => ?_⟩
    dsimp [extInit]
    rw [he_app _ (encodeIntM_mem ℳ m), blank_tape_nth]
    rfl
  | succ k ih =>
    rcases hext : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
    rw [hext] at ih
    obtain ⟨g, hg, hcfg, happ⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hext, hcfg]
    have hsym : appM ℳ g (encodeIntM ℳ pos) = numM ℳ T.head.val := by
      have h := happ pos
      rw [sub_self] at h
      exact h
    obtain ⟨_, hstep_app⟩ := nextStepM_funs_and_app ℳ M
    cases qOpt with
    | none =>
      have hmem_cfg : ℳ.mem (kpairM ℳ (numM ℳ n) (kpairM ℳ (encodeIntM ℳ pos) g))
          (cfgSetM ℳ (n + 1)) :=
        (mem_cfgSetM_iff ℳ).mpr ⟨n, encodeIntM ℳ pos, g, Nat.lt_succ_self n, encodeIntM_mem ℳ pos, hg, rfl⟩
      dsimp only [Constant14.stateCode, extStep]
      rw [hstep_app _ hmem_cfg,
        zfcStepFnM_of_cfg ℳ M n (encodeIntM ℳ pos) g (Nat.lt_succ_self n)
          (encodeIntM_mem ℳ pos) hg T.head.val T.head.isLt hsym]
      have hlu : transLookup M n T.head.val = (n, T.head.val, 1) := by
        unfold transLookup; rw [dif_neg (Nat.lt_irrefl n)]
      rw [hlu]
      dsimp only
      have h10 : (1 : ℕ) ≠ 0 := by decide
      simp only [h10, ↓reduceIte]
      obtain ⟨hu_funs, hu_app⟩ := updateTapeM_funs_and_app hg (numM_lt_mem ℳ T.head.isLt)
        (posSet := encodeIntM ℳ pos)
      refine ⟨updateTapeM ℳ g (encodeIntM ℳ pos) (numM ℳ T.head.val), hu_funs, rfl, fun m => ?_⟩
      rw [hu_app _ (encodeIntM_mem ℳ m)]
      by_cases hmp : m = pos
      · subst hmp; rw [if_pos rfl, sub_self]; rfl
      · rw [if_neg (fun h => hmp (encodeIntM_injective ℳ h)), happ m]
    | some q =>
      have hmem_cfg : ℳ.mem (kpairM ℳ (numM ℳ q.val) (kpairM ℳ (encodeIntM ℳ pos) g))
          (cfgSetM ℳ (n + 1)) :=
        (mem_cfgSetM_iff ℳ).mpr ⟨q.val, encodeIntM ℳ pos, g, Nat.lt_succ_of_lt q.isLt,
          encodeIntM_mem ℳ pos, hg, rfl⟩
      dsimp only [Constant14.stateCode]
      rw [hstep_app _ hmem_cfg,
        zfcStepFnM_of_cfg ℳ M q.val (encodeIntM ℳ pos) g (Nat.lt_succ_of_lt q.isLt)
          (encodeIntM_mem ℳ pos) hg T.head.val T.head.isLt hsym]
      have hlu : transLookup M q.val T.head.val = Constant14.transitionCode M q T.head := by
        unfold transLookup; rw [dif_pos q.isLt, dif_pos T.head.isLt]
      rw [hlu]
      cases hM : M q T.head with
      | none =>
        rw [Constant14.transitionCode, extStep, hM]
        dsimp only [Constant14.directionCode, Constant14.stateCode]
        have h10 : (1 : ℕ) ≠ 0 := by decide
        simp only [h10, ↓reduceIte]
        obtain ⟨hu_funs, hu_app⟩ := updateTapeM_funs_and_app hg (numM_lt_mem ℳ T.head.isLt)
          (posSet := encodeIntM ℳ pos)
        refine ⟨updateTapeM ℳ g (encodeIntM ℳ pos) (numM ℳ T.head.val), hu_funs, rfl, fun m => ?_⟩
        rw [hu_app _ (encodeIntM_mem ℳ m)]
        by_cases hmp : m = pos
        · subst hmp; rw [if_pos rfl, sub_self]; rfl
        · rw [if_neg (fun h => hmp (encodeIntM_injective ℳ h)), happ m]
      | some out =>
        rcases out with ⟨q', ⟨sym, d⟩⟩
        obtain ⟨hu_funs, hu_app⟩ := updateTapeM_funs_and_app hg (numM_lt_mem ℳ sym.isLt)
          (posSet := encodeIntM ℳ pos)
        cases d with
        | left =>
          rw [Constant14.transitionCode, extStep, hM]
          dsimp only [Constant14.directionCode]
          simp only [↓reduceIte, intPredM_encodeIntM]
          refine ⟨updateTapeM ℳ g (encodeIntM ℳ pos) (numM ℳ sym.val), hu_funs, rfl, fun m => ?_⟩
          rw [hu_app _ (encodeIntM_mem ℳ m), Tape.move_left_nth]
          have hidx : m - (pos - 1) - 1 = m - pos := by omega
          rw [hidx, Tape.write_nth]
          by_cases hmp : m = pos
          · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
          · have hne1 : encodeIntM ℳ m ≠ encodeIntM ℳ pos := fun h => hmp (encodeIntM_injective ℳ h)
            have hne2 : m - pos ≠ 0 := by omega
            rw [if_neg hne1, if_neg hne2, happ m]
        | right =>
          rw [Constant14.transitionCode, extStep, hM]
          dsimp only [Constant14.directionCode]
          have h20 : (2 : ℕ) ≠ 0 := by decide
          have h21 : (2 : ℕ) ≠ 1 := by decide
          simp only [h20, h21, ↓reduceIte, intSuccM_encodeIntM]
          refine ⟨updateTapeM ℳ g (encodeIntM ℳ pos) (numM ℳ sym.val), hu_funs, rfl, fun m => ?_⟩
          rw [hu_app _ (encodeIntM_mem ℳ m), Tape.move_right_nth]
          have hidx : m - (pos + 1) + 1 = m - pos := by omega
          rw [hidx, Tape.write_nth]
          by_cases hmp : m = pos
          · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
          · have hne1 : encodeIntM ℳ m ≠ encodeIntM ℳ pos := fun h => hmp (encodeIntM_injective ℳ h)
            have hne2 : m - pos ≠ 0 := by omega
            rw [if_neg hne1, if_neg hne2, happ m]

private lemma multiStep_rel_extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    match M.multiStep (Machine.init []) k with
    | none => ((extStep M)^[k] (extInit n)).1 = none
    | some cfg => ((extStep M)^[k] (extInit n)).1 = cfg.q ∧
        ((extStep M)^[k] (extInit n)).2.2 = cfg.tape := by
  induction k with
  | zero =>
    simp [Machine.multiStep_zero, Machine.init, Fin.default_eq_zero, extInit]
  | succ k ih =>
    rw [Machine.multiStep_succ, Function.iterate_succ_apply']
    rcases hext : (extStep M)^[k] (extInit n) with ⟨c1, posk, cT⟩
    rw [hext] at ih
    cases hmk : M.multiStep (Machine.init []) k with
    | none =>
      rw [hmk] at ih
      dsimp only at ih
      subst ih
      rfl
    | some cfg =>
      rw [hmk] at ih
      rcases cfg with ⟨qOpt, Tk⟩
      dsimp only at ih
      obtain ⟨rfl, rfl⟩ := ih
      cases c1 with
      | none =>
        simp [Machine.step, extStep]
      | some qk =>
        simp only [Option.bind_some, Machine.step]
        cases hMq : M qk cT.head with
        | none =>
          simp [hMq, extStep]
        | some out =>
          rcases out with ⟨q', ⟨sym, d⟩⟩
          simp [hMq, extStep]

private lemma semEv_halts_of_multiStep_none (ℳ : ZFCModel) {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) (k : ℕ) (hk : M.multiStep (Machine.init []) k = none) :
    evM ℳ Fin.elim0 (Constant14.halts M) := by
  have hrel := multiStep_rel_extStep M k
  rw [hk] at hrel
  obtain ⟨g, hg, hcfg, _⟩ := sim_invariant ℳ M k
  rw [hrel] at hcfg
  dsimp only [Constant14.stateCode] at hcfg
  let pos := ((extStep M)^[k] (extInit n)).2.1
  let Fstep := nextStepM ℳ M
  let x0 := initConfigM ℳ
  have hF_funs : ℳ.mem Fstep (funsM ℳ (cfgSetM ℳ (n + 1)) (cfgSetM ℳ (n + 1))) :=
    (nextStepM_funs_and_app ℳ M).1
  have hx0_mem : ℳ.mem x0 (cfgSetM ℳ (n + 1)) :=
    (mem_cfgSetM_iff ℳ).mpr ⟨0, encodeIntM ℳ 0, emptyTapeM ℳ, Nat.zero_lt_succ n,
      encodeIntM_mem ℳ 0, (emptyTapeM_funs_and_app ℳ).1, rfl⟩
  let O0 := (exists_orbitM ℳ hx0_mem (fun _ hy => appM_mem_codomain hF_funs hy)).choose
  have hO0 : ∀ z, ℳ.mem z O0 ↔
      ∀ A : ℳ.V, (ℳ.mem x0 A ∧ ∀ y, ℳ.mem y A → ℳ.mem (appM ℳ Fstep y) A) → ℳ.mem z A :=
    (exists_orbitM ℳ hx0_mem (fun _ hy => appM_mem_codomain hF_funs hy)).choose_spec
  have hiter_in_O0 : ∀ j : ℕ, ℳ.mem ((appM ℳ Fstep)^[j] x0) O0 := by
    intro j
    rw [hO0]
    intro A ⟨hx0A, hclA⟩
    induction j with
    | zero => exact hx0A
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hclA _ ih
  have htarget_in_O0 : ℳ.mem (kpairM ℳ (numM ℳ n) (kpairM ℳ (encodeIntM ℳ pos) g)) O0 := by
    rw [← hcfg]
    exact hiter_in_O0 k
  rw [evM_e0 ℳ Fin.elim0 ![]]
  unfold Constant14.halts
  rw [ev_faf_bexs (et_const0 (dc_integers ℳ) ![])]
  refine ⟨encodeIntM ℳ pos, encodeIntM_mem ℳ pos, ?_⟩
  rw [ev_faf_bexs
    (et_comp2 (ev_function ℳ) (et_const0 (dc_numeral ℳ 2) _) (et_const0 (dc_integers ℳ) _))]
  refine ⟨g, hg, ?_⟩
  have h_orbit_eval : EvalTermAt ℳ
      (kpairM ℳ (numM ℳ n) (kpairM ℳ (encodeIntM ℳ pos) g) :> g :>
        funsM ℳ (intSetM ℳ) (numM ℳ 2) :> encodeIntM ℳ pos :> intSetM ℳ :> ![])
      (Semiformula.nestFormulaeFunc Constant14.orbit
        (Semiformula.nestFormulaeFunc (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ![] :>
          Semiformula.nestFormulaeFunc Constant14.initialConfig ![] :> ![]))
      O0 := by
    intro O
    rw [ev_nestFunc2_raw Constant14.orbit
      (et_const0 (dc_nextStep ℳ M) _) (et_const0 (dc_initialConfig ℳ) _) O]
    exact ev_orbit_iff ℳ hF_funs hx0_mem
  exact (ev_faf_mem
    (et_comp2 (ev_kpair ℳ) (et_const0 (dc_numeral ℳ n) _)
      (et_comp2 (ev_kpair ℳ) (et_bvar3 ℳ g _ (encodeIntM ℳ pos) _) (et_bvar1 ℳ g _)))
    h_orbit_eval).mpr htarget_in_O0

private theorem provable_halts_of_multiStep_none {n : ℕ} [NeZero n]
    (M : Machine (Fin 2) (Fin n)) (k : ℕ) (hk : M.multiStep (Machine.init []) k = none) :
    FFL.Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M) :=
  completeness_set 𝗭𝗙𝗖
    (fun φ hφ => Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ))
    (Constant14.halts M)
    (fun V hne memV hsat => semEv_halts_of_multiStep_none ⟨V, hne, memV, hsat⟩ M k hk)

end C14H2Proof

theorem OMA.solution : OMA.R_Constant14_c14_ge_5_R1.H2 :=
  fun M h => C14H2Proof.provable_halts_of_multiStep_none M 108 h
