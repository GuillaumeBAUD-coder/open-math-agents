import OMAStatements.S_arxiv_1902_01106

open OMA.S_arxiv_1902_01106

namespace OMA.P_arxiv_1902_01106

/-- The counterexample S4 formula `A := □((P ∧ ¬□P) → P) → ¬□(P ∧ ¬□P)`. -/
private def counterA : S4Form :=
  .imp (.box (.imp (.conj (.atom 0) (.neg (.box (.atom 0)))) (.atom 0)))
       (.neg (.box (.conj (.atom 0) (.neg (.box (.atom 0))))))

/-- The LP realization `B := y:(P ∧ ¬(y·x):P → P) → ¬x:(P ∧ ¬(y·x):P)`. -/
private def counterB : LPForm :=
  let t : LPTerm := .app (.var 1) (.var 0)
  let phi : LPForm := .conj (.atom 0) (.neg (.just t (.atom 0)))
  .imp (.just (.var 1) (.imp phi (.atom 0))) (.neg (.just (.var 0) phi))

private lemma counterB_forget : counterB.forget = counterA := rfl

/-- `counterA` is provable in G3s (standard proof of `¬□(P ∧ ¬□P)`, weakened with the antecedent). -/
private def counterA_g3s : G3s 0 {counterA} := by
  let P : S4Form := .atom 0
  let phi : S4Form := .conj P (.neg (.box P))
  let hyp : S4Form := .box (.imp phi P)
  change G3s 0 {.imp hyp (.neg (.box phi))}
  refine G3s.impR ?_
  rw [show (hyp ::ₘ (0 : Multiset S4Form)) = {hyp} from rfl]
  refine G3s.negR ?_
  -- Goal: `G3s (box phi ::ₘ {hyp}) 0`
  refine G3s.boxL ?_
  refine G3s.conjL ?_
  -- Goal: `G3s (P ::ₘ neg (box P) ::ₘ box phi ::ₘ {hyp}) 0`
  -- Move `neg (box P)` to the front to apply `negL`
  have h1 : P ::ₘ .neg (.box P) ::ₘ .box phi ::ₘ ({hyp} : Multiset S4Form) =
      .neg (.box P) ::ₘ P ::ₘ .box phi ::ₘ {hyp} := Multiset.cons_swap _ _ _
  rw [h1]
  refine G3s.negL ?_
  -- Goal: `G3s (P ::ₘ box phi ::ₘ {hyp}) {box P}`
  have h2 : P ::ₘ .box phi ::ₘ ({hyp} : Multiset S4Form) =
      {P, hyp} + ({phi} : Multiset S4Form).map S4Form.box := by
    simp only [Multiset.map_singleton, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
    exact congrArg (P ::ₘ ·) (Multiset.pair_comm _ _)
  have h3 : (.box P ::ₘ (0 : Multiset S4Form)) =
      .box P ::ₘ ((0 : Multiset S4Form).map S4Form.dia + 0) := by simp
  rw [h2, h3]
  refine G3s.boxR ?_
  -- Premise: `G3s ({phi}.map box) (P ::ₘ 0)` = `G3s {box phi} {P}`
  simp only [Multiset.map_singleton, Multiset.map_zero]
  refine G3s.boxL ?_
  refine G3s.conjL ?_
  exact G3s.ax 0 _ _

/-- Empty constant specification is trivially non-self-referential. -/
private lemma empty_not_selfRef : ¬ IsSelfRefCS (∅ : Set (ℕ × LPForm)) := by
  rintro ⟨c, hc⟩
  cases hc with
  | single h => obtain ⟨_, hmem, _⟩ := h; exact hmem
  | tail _ h => obtain ⟨_, hmem, _⟩ := h; exact hmem

/-- `counterB` is provable in `LP₀ = LP(∅)`. -/
private lemma counterB_lp0 : LPProv (∅ : Set (ℕ × LPForm)) counterB := by
  let x : LPTerm := .var 0
  let y : LPTerm := .var 1
  let t : LPTerm := .app y x
  let P : LPForm := .atom 0
  let phi : LPForm := .conj P (.neg (.just t P))
  let F1 : LPForm := .imp (.just y (.imp phi P)) (.imp (.just x phi) (.just t P))
  let F2 : LPForm := .imp (.just x phi) phi
  let B : LPForm := .imp (.just y (.imp phi P)) (.neg (.just x phi))
  have h1 : LPProv ∅ F1 := LPProv.ax (IsLPAxiom.a2 y x phi P)
  have h2 : LPProv ∅ F2 := LPProv.ax (IsLPAxiom.a1 x phi)
  have htaut : IsPropTaut (.imp F1 (.imp F2 B)) := by
    intro va vj
    simp only [F1, F2, B, phi, P, LPForm.propEval]
    cases vj y (.imp (.conj (.atom 0) (.neg (.just t (.atom 0)))) (.atom 0)) <;>
      cases vj x (.conj (.atom 0) (.neg (.just t (.atom 0)))) <;>
      cases vj t (.atom 0) <;>
      cases va 0 <;> rfl
  exact LPProv.mp (LPProv.mp (LPProv.ax (IsLPAxiom.a0 htaut)) h1) h2

/-- Soundness valuation `v₀` for the 1-world reflexive-transitive Kripke model `W = {w}, R = {(w,w)}, val(P) = ∅`. -/
private def v0 : S4Form → Bool
  | .bot => false
  | .atom _ => false
  | .neg A => !v0 A
  | .conj A B => v0 A && v0 B
  | .disj A B => v0 A || v0 B
  | .imp A B => !v0 A || v0 B
  | .box A => v0 A
  | .dia A => v0 A

/-- Soundness of annotated G3s with respect to the 1-world S4 Kripke model `v₀`. -/
private lemma annG3s_sound_v0 {ι : Type} {Γ Δ : Multiset (AnnS4Form ι)} (T : AnnG3s Γ Δ) :
    (∃ F ∈ Γ, v0 F.erase = false) ∨ (∃ F ∈ Δ, v0 F.erase = true) := by
  induction T with
  | ax p Γ Δ =>
    left; exact ⟨.atom p, Multiset.mem_cons_self _ _, rfl⟩
  | botL Γ Δ =>
    left; exact ⟨.bot, Multiset.mem_cons_self _ _, rfl⟩
  | @negL A Γ Δ _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · left; exact ⟨F, Multiset.mem_cons_of_mem hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv; left; exact ⟨.neg A, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · right; exact ⟨F, hF', hFv⟩
  | @negR A Γ Δ _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv; right; exact ⟨.neg A, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · left; exact ⟨F, hF', hFv⟩
    · right; exact ⟨F, Multiset.mem_cons_of_mem hF, hFv⟩
  | @conjL A B Γ Δ _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF1
      · rw [hFA] at hFv; left; exact ⟨.conj A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · rcases Multiset.mem_cons.mp hF1 with hFB | hF2
        · rw [hFB] at hFv; left; exact ⟨.conj A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
        · left; exact ⟨F, Multiset.mem_cons_of_mem hF2, hFv⟩
    · right; exact ⟨F, hF, hFv⟩
  | @conjR A B Γ Δ _ _ ih1 ih2 =>
    rcases ih1 with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · left; exact ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv
        rcases ih2 with ⟨G, hG, hGv⟩ | ⟨G, hG, hGv⟩
        · left; exact ⟨G, hG, hGv⟩
        · rcases Multiset.mem_cons.mp hG with hGB | hG'
          · rw [hGB] at hGv; right; exact ⟨.conj A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv, hGv]⟩
          · right; exact ⟨G, Multiset.mem_cons_of_mem hG', hGv⟩
      · right; exact ⟨F, Multiset.mem_cons_of_mem hF', hFv⟩
  | @disjL A B Γ Δ _ _ ih1 ih2 =>
    rcases ih1 with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv
        rcases ih2 with ⟨G, hG, hGv⟩ | ⟨G, hG, hGv⟩
        · rcases Multiset.mem_cons.mp hG with hGB | hG'
          · rw [hGB] at hGv; left; exact ⟨.disj A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv, hGv]⟩
          · left; exact ⟨G, Multiset.mem_cons_of_mem hG', hGv⟩
        · right; exact ⟨G, hG, hGv⟩
      · left; exact ⟨F, Multiset.mem_cons_of_mem hF', hFv⟩
    · right; exact ⟨F, hF, hFv⟩
  | @disjR A B Γ Δ _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · left; exact ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF1
      · rw [hFA] at hFv; right; exact ⟨.disj A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · rcases Multiset.mem_cons.mp hF1 with hFB | hF2
        · rw [hFB] at hFv; right; exact ⟨.disj A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
        · right; exact ⟨F, Multiset.mem_cons_of_mem hF2, hFv⟩
  | @impL A B Γ Δ _ _ ih1 ih2 =>
    rcases ih1 with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · left; exact ⟨F, Multiset.mem_cons_of_mem hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv
        rcases ih2 with ⟨G, hG, hGv⟩ | ⟨G, hG, hGv⟩
        · rcases Multiset.mem_cons.mp hG with hGB | hG'
          · rw [hGB] at hGv; left; exact ⟨.imp A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv, hGv]⟩
          · left; exact ⟨G, Multiset.mem_cons_of_mem hG', hGv⟩
        · right; exact ⟨G, hG, hGv⟩
      · right; exact ⟨F, hF', hFv⟩
  | @impR A B Γ Δ _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv; right; exact ⟨.imp A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · left; exact ⟨F, hF', hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFB | hF'
      · rw [hFB] at hFv; right; exact ⟨.imp A B, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · right; exact ⟨F, Multiset.mem_cons_of_mem hF', hFv⟩
  | @boxL i A Γ Δ _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF1
      · rw [hFA] at hFv; left; exact ⟨.box i A, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · left; exact ⟨F, hF1, hFv⟩
    · right; exact ⟨F, hF, hFv⟩
  | @boxR i A Γ Γ' Δ Δ' _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · left; exact ⟨F, Multiset.mem_add.mpr (Or.inr hF), hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv; right; exact ⟨.box i A, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · right; exact ⟨F, Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inl hF')), hFv⟩
  | @diaL A Γ Γ' Δ Δ' _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF'
      · rw [hFA] at hFv; left; exact ⟨.dia A, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · left; exact ⟨F, Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inr hF')), hFv⟩
    · right; exact ⟨F, Multiset.mem_add.mpr (Or.inl hF), hFv⟩
  | @diaR A Γ Δ _ ih =>
    rcases ih with ⟨F, hF, hFv⟩ | ⟨F, hF, hFv⟩
    · left; exact ⟨F, hF, hFv⟩
    · rcases Multiset.mem_cons.mp hF with hFA | hF1
      · rw [hFA] at hFv; right; exact ⟨.dia A, Multiset.mem_cons_self _ _, by simp [AnnS4Form.erase, v0, hFv]⟩
      · right; exact ⟨F, hF1, hFv⟩

/-- Separating valuation `v₁`: sets `P ↦ true`, `□P ↦ false`, and every other `□F ↦ v₁ F`.
Falsifies `counterA`, is preserved upward by every G3s rule except `(⊃□)`, and forces
every `(⊃□)` rule on a falsified sequent to be `□₄ P` with `□₃(P ∧ ¬□₄P)` in its premise! -/
private def v1 : S4Form → Bool
  | .bot => false
  | .atom _ => true
  | .neg A => !v1 A
  | .conj A B => v1 A && v1 B
  | .disj A B => v1 A || v1 B
  | .imp A B => !v1 A || v1 B
  | .box A => if A = .atom 0 then false else v1 A
  | .dia A => v1 A

/-- Any annotated formula whose erasure is `counterA` has exact shape parametrized by 4 labels. -/
private lemma ann_shape_of_erase_counterA {ι : Type} {A_ann : AnnS4Form ι}
    (h : A_ann.erase = counterA) :
    ∃ i₁ i₂ i₃ i₄ : ι,
      A_ann =
        .imp (.box i₁ (.imp (.conj (.atom 0) (.neg (.box i₂ (.atom 0)))) (.atom 0)))
             (.neg (.box i₃ (.conj (.atom 0) (.neg (.box i₄ (.atom 0)))))) := by
  cases A_ann with
  | imp L R =>
    simp only [AnnS4Form.erase, counterA, S4Form.imp.injEq] at h
    rcases h with ⟨hL, hR⟩
    cases L with
    | box i₁ L1 =>
      simp only [AnnS4Form.erase, S4Form.box.injEq] at hL
      cases L1 with
      | imp L1a L1b =>
        simp only [AnnS4Form.erase, S4Form.imp.injEq] at hL
        rcases hL with ⟨hL1a, hL1b⟩
        cases L1a with
        | conj C1 C2 =>
          simp only [AnnS4Form.erase, S4Form.conj.injEq] at hL1a
          rcases hL1a with ⟨hC1, hC2⟩
          cases C1 with
          | atom p1 =>
            simp only [AnnS4Form.erase, S4Form.atom.injEq] at hC1; subst hC1
            cases C2 with
            | neg N2 =>
              simp only [AnnS4Form.erase, S4Form.neg.injEq] at hC2
              cases N2 with
              | box i₂ B2 =>
                simp only [AnnS4Form.erase, S4Form.box.injEq] at hC2
                cases B2 with
                | atom p2 =>
                  simp only [AnnS4Form.erase, S4Form.atom.injEq] at hC2; subst hC2
                  cases L1b with
                  | atom p3 =>
                    simp only [AnnS4Form.erase, S4Form.atom.injEq] at hL1b; subst hL1b
                    cases R with
                    | neg R1 =>
                      simp only [AnnS4Form.erase, S4Form.neg.injEq] at hR
                      cases R1 with
                      | box i₃ R2 =>
                        simp only [AnnS4Form.erase, S4Form.box.injEq] at hR
                        cases R2 with
                        | conj D1 D2 =>
                          simp only [AnnS4Form.erase, S4Form.conj.injEq] at hR
                          rcases hR with ⟨hD1, hD2⟩
                          cases D1 with
                          | atom p4 =>
                            simp only [AnnS4Form.erase, S4Form.atom.injEq] at hD1; subst hD1
                            cases D2 with
                            | neg N4 =>
                              simp only [AnnS4Form.erase, S4Form.neg.injEq] at hD2
                              cases N4 with
                              | box i₄ B4 =>
                                simp only [AnnS4Form.erase, S4Form.box.injEq] at hD2
                                cases B4 with
                                | atom p5 =>
                                  simp only [AnnS4Form.erase, S4Form.atom.injEq] at hD2; subst hD2
                                  exact ⟨i₁, i₂, i₃, i₄, rfl⟩
                                | _ => simp [AnnS4Form.erase] at hD2
                              | _ => simp [AnnS4Form.erase] at hD2
                            | _ => simp [AnnS4Form.erase] at hD2
                          | _ => simp [AnnS4Form.erase] at hD1
                        | _ => simp [AnnS4Form.erase] at hR
                      | _ => simp [AnnS4Form.erase] at hR
                    | _ => simp [AnnS4Form.erase] at hR
                  | _ => simp [AnnS4Form.erase] at hL1b
                | _ => simp [AnnS4Form.erase] at hC2
              | _ => simp [AnnS4Form.erase] at hC2
            | _ => simp [AnnS4Form.erase] at hC2
          | _ => simp [AnnS4Form.erase] at hC1
        | _ => simp [AnnS4Form.erase] at hL1a
      | _ => simp [AnnS4Form.erase] at hL
    | _ => simp [AnnS4Form.erase] at hL
  | _ => simp [AnnS4Form.erase, counterA] at h

/-- Positive subformulas of the annotated `counterA(i₁, i₂, i₃, i₄)` (the only ones that can appear on the RHS). -/
private def IsPosSub {ι : Type} (i₁ i₂ i₃ i₄ : ι) (F : AnnS4Form ι) : Prop :=
  let P : AnnS4Form ι := .atom 0
  let phi2 : AnnS4Form ι := .conj P (.neg (.box i₂ P))
  let phi4 : AnnS4Form ι := .conj P (.neg (.box i₄ P))
  F = .imp (.box i₁ (.imp phi2 P)) (.neg (.box i₃ phi4)) ∨
  F = .neg (.box i₃ phi4) ∨
  F = phi2 ∨
  F = P ∨
  F = .neg (.box i₂ P) ∨
  F = .box i₄ P

/-- Negative subformulas of the annotated `counterA(i₁, i₂, i₃, i₄)` (the only ones that can appear on the LHS). -/
private def IsNegSub {ι : Type} (i₁ i₂ i₃ i₄ : ι) (F : AnnS4Form ι) : Prop :=
  let P : AnnS4Form ι := .atom 0
  let phi2 : AnnS4Form ι := .conj P (.neg (.box i₂ P))
  let phi4 : AnnS4Form ι := .conj P (.neg (.box i₄ P))
  F = .box i₁ (.imp phi2 P) ∨
  F = .imp phi2 P ∨
  F = P ∨
  F = .box i₂ P ∨
  F = .box i₃ phi4 ∨
  F = phi4 ∨
  F = .neg (.box i₄ P)

/-- Core inductive invariant: any annotated G3s proof of a polarity-valid sequent falsified by `v₁`
must contain a `(⊃ □)` step with `LeftPrehist T i₄ i₄`! -/
private lemma leftPrehist_self_of_falsified {ι : Type} (i₁ i₂ i₃ i₄ : ι)
    {Γ Δ : Multiset (AnnS4Form ι)} (T : AnnG3s Γ Δ)
    (hΓ : ∀ F ∈ Γ, IsNegSub i₁ i₂ i₃ i₄ F)
    (hΔ : ∀ F ∈ Δ, IsPosSub i₁ i₂ i₃ i₄ F)
    (hvΓ : ∀ F ∈ Γ, v1 F.erase = true)
    (hvΔ : ∀ F ∈ Δ, v1 F.erase = false) :
    LeftPrehist T i₄ i₄ := by
  induction T with
  | ax p Γ Δ =>
    have h1 := hvΓ (.atom p) (Multiset.mem_cons_self _ _)
    have h2 := hvΔ (.atom p) (Multiset.mem_cons_self _ _)
    simp [AnnS4Form.erase, v1] at h2
  | botL Γ Δ =>
    have h1 := hvΓ .bot (Multiset.mem_cons_self _ _)
    simp [AnnS4Form.erase, v1] at h1
  | @negL A Γ Δ d ih =>
    have hneg := hΓ (.neg A) (Multiset.mem_cons_self _ _)
    have hApos : IsPosSub i₁ i₂ i₃ i₄ A := by
      rcases hneg with h | h | h | h | h | h | h <;> cases h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    have hvA : v1 A.erase = false := by
      have h1 := hvΓ (.neg A) (Multiset.mem_cons_self _ _)
      simpa [AnnS4Form.erase, v1] using h1
    exact ih
      (fun F hF => hΓ F (Multiset.mem_cons_of_mem hF))
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hApos; exact hΔ F hF')
      (fun F hF => hvΓ F (Multiset.mem_cons_of_mem hF))
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvA; exact hvΔ F hF')
  | @negR A Γ Δ d ih =>
    have hneg := hΔ (.neg A) (Multiset.mem_cons_self _ _)
    have hAneg : IsNegSub i₁ i₂ i₃ i₄ A := by
      rcases hneg with h | h | h | h | h | h <;> cases h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    have hvA : v1 A.erase = true := by
      have h1 := hvΔ (.neg A) (Multiset.mem_cons_self _ _)
      simpa [AnnS4Form.erase, v1] using h1
    exact ih
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAneg; exact hΓ F hF')
      (fun F hF => hΔ F (Multiset.mem_cons_of_mem hF))
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvA; exact hvΓ F hF')
      (fun F hF => hvΔ F (Multiset.mem_cons_of_mem hF))
  | @conjL A B Γ Δ d ih =>
    have hconj := hΓ (.conj A B) (Multiset.mem_cons_self _ _)
    have hAB : IsNegSub i₁ i₂ i₃ i₄ A ∧ IsNegSub i₁ i₂ i₃ i₄ B := by
      rcases hconj with h | h | h | h | h | h | h <;> cases h
      exact ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩
    have hvAB : v1 A.erase = true ∧ v1 B.erase = true := by
      have h1 := hvΓ (.conj A B) (Multiset.mem_cons_self _ _)
      simpa [AnnS4Form.erase, v1] using h1
    exact ih
      (fun F hF => by
        rcases Multiset.mem_cons.mp hF with rfl | hF1
        · exact hAB.1
        · rcases Multiset.mem_cons.mp hF1 with rfl | hF2
          · exact hAB.2
          · exact hΓ F (Multiset.mem_cons_of_mem hF2))
      hΔ
      (fun F hF => by
        rcases Multiset.mem_cons.mp hF with rfl | hF1
        · exact hvAB.1
        · rcases Multiset.mem_cons.mp hF1 with rfl | hF2
          · exact hvAB.2
          · exact hvΓ F (Multiset.mem_cons_of_mem hF2))
      hvΔ
  | @conjR A B Γ Δ d₁ d₂ ih1 ih2 =>
    have hconj := hΔ (.conj A B) (Multiset.mem_cons_self _ _)
    have hAB : IsPosSub i₁ i₂ i₃ i₄ A ∧ IsPosSub i₁ i₂ i₃ i₄ B := by
      rcases hconj with h | h | h | h | h | h <;> cases h
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    have hvAB : v1 A.erase = false ∨ v1 B.erase = false := by
      have h1 := hvΔ (.conj A B) (Multiset.mem_cons_self _ _)
      simp only [AnnS4Form.erase, v1, Bool.and_eq_false_iff] at h1
      exact h1
    rcases hvAB with hvA | hvB
    · left
      exact ih1 hΓ
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAB.1; exact hΔ F (Multiset.mem_cons_of_mem hF'))
        hvΓ
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvA; exact hvΔ F (Multiset.mem_cons_of_mem hF'))
    · right
      exact ih2 hΓ
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAB.2; exact hΔ F (Multiset.mem_cons_of_mem hF'))
        hvΓ
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvB; exact hvΔ F (Multiset.mem_cons_of_mem hF'))
  | @disjL A B Γ Δ _ _ _ _ =>
    have hdisj := hΓ (.disj A B) (Multiset.mem_cons_self _ _)
    rcases hdisj with h | h | h | h | h | h | h <;> cases h
  | @disjR A B Γ Δ _ _ =>
    have hdisj := hΔ (.disj A B) (Multiset.mem_cons_self _ _)
    rcases hdisj with h | h | h | h | h | h <;> cases h
  | @impL A B Γ Δ d₁ d₂ ih1 ih2 =>
    have himp := hΓ (.imp A B) (Multiset.mem_cons_self _ _)
    have hAB : IsPosSub i₁ i₂ i₃ i₄ A ∧ IsNegSub i₁ i₂ i₃ i₄ B := by
      rcases himp with h | h | h | h | h | h | h <;> cases h
      exact ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inl rfl))⟩
    have hvAB : v1 A.erase = false ∨ v1 B.erase = true := by
      have h1 := hvΓ (.imp A B) (Multiset.mem_cons_self _ _)
      simp only [AnnS4Form.erase, v1, Bool.or_eq_true, Bool.not_eq_true'] at h1
      exact h1
    rcases hvAB with hvA | hvB
    · left
      exact ih1
        (fun F hF => hΓ F (Multiset.mem_cons_of_mem hF))
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAB.1; exact hΔ F hF')
        (fun F hF => hvΓ F (Multiset.mem_cons_of_mem hF))
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvA; exact hvΔ F hF')
    · right
      exact ih2
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAB.2; exact hΓ F (Multiset.mem_cons_of_mem hF'))
        hΔ
        (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvB; exact hvΓ F (Multiset.mem_cons_of_mem hF'))
        hvΔ
  | @impR A B Γ Δ d ih =>
    have himp := hΔ (.imp A B) (Multiset.mem_cons_self _ _)
    have hAB : IsNegSub i₁ i₂ i₃ i₄ A ∧ IsPosSub i₁ i₂ i₃ i₄ B := by
      rcases himp with h | h | h | h | h | h <;> cases h
      exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
    have hvAB : v1 A.erase = true ∧ v1 B.erase = false := by
      have h1 := hvΔ (.imp A B) (Multiset.mem_cons_self _ _)
      simp only [AnnS4Form.erase, v1, Bool.or_eq_false_iff, Bool.not_eq_false'] at h1
      exact h1
    exact ih
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAB.1; exact hΓ F hF')
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAB.2; exact hΔ F (Multiset.mem_cons_of_mem hF'))
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvAB.1; exact hvΓ F hF')
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvAB.2; exact hvΔ F (Multiset.mem_cons_of_mem hF'))
  | @boxL j A Γ Δ d ih =>
    have hbox := hΓ (.box j A) (Multiset.mem_cons_self _ _)
    have hAneg : IsNegSub i₁ i₂ i₃ i₄ A := by
      rcases hbox with h | h | h | h | h | h | h <;> cases h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have hvA : v1 A.erase = true := by
      have h1 := hvΓ (.box j A) (Multiset.mem_cons_self _ _)
      simp only [AnnS4Form.erase, v1] at h1
      by_cases heq : A.erase = .atom 0
      · rw [if_pos heq] at h1; cases h1
      · rwa [if_neg heq] at h1
    exact ih
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hAneg; exact hΓ F hF')
      hΔ
      (fun F hF => by rcases Multiset.mem_cons.mp hF with rfl | hF'; exact hvA; exact hvΓ F hF')
      hvΔ
  | @boxR j A Γ Γ' Δ Δ' d _ =>
    -- The principal formula `box j A` is a positive subformula of `counterA`, so `j = i₄` and `A = atom 0`!
    have hbox := hΔ (.box j A) (Multiset.mem_cons_self _ _)
    have hjA : j = i₄ ∧ A = .atom 0 := by
      rcases hbox with h | h | h | h | h | h <;> cases h
      exact ⟨rfl, rfl⟩
    rcases hjA with ⟨hj, rfl⟩
    subst hj
    -- No `dia` formulas exist in `IsPosSub`, so `Δ = 0`!
    have hΔ0 : Δ = 0 := by
      by_contra hne
      obtain ⟨D, hD⟩ := Multiset.exists_mem_of_ne_zero hne
      have hdia := hΔ (.dia D) (Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inl (Multiset.mem_map_of_mem _ hD))))
      rcases hdia with h | h | h | h | h | h <;> cases h
    -- Check whether `box i₃ phi4` appears in `Γ.map box`!
    let phi4 : AnnS4Form ι := .conj (.atom 0) (.neg (.box j (.atom 0)))
    let F3 : AnnS4Form ι := .box i₃ phi4
    by_cases hF3 : F3 ∈ Γ.map fun p => AnnS4Form.box p.1 p.2
    · left
      refine ⟨rfl, F3, hF3, ?_⟩
      simp [F3, phi4, AnnS4Form.hasBoxLabel]
    · -- Otherwise every formula in `Γ.map box` must be `box i₁ (phi2 → P)`, which is TRUE under `v0`!
      exfalso
      rcases annG3s_sound_v0 d with ⟨F, hF, hFv0⟩ | ⟨F, hF, hFv0⟩
      · have hFneg := hΓ F (Multiset.mem_add.mpr (Or.inr hF))
        have hFv1 := hvΓ F (Multiset.mem_add.mpr (Or.inr hF))
        obtain ⟨⟨pj, pA⟩, _, rfl⟩ := Multiset.mem_map.mp hF
        rcases hFneg with h | h | h | h | h | h | h <;> cases h
        · -- `F = box i₁ (phi2 → P)` has `v0 F.erase = true`, contradicting `hFv0`!
          simp [AnnS4Form.erase, v0] at hFv0
        · -- `F = box i₂ P` has `v1 F.erase = false`, contradicting `hFv1`!
          simp [AnnS4Form.erase, v1] at hFv1
        · -- `F = box i₃ phi4` contradicts `hF3`!
          exact hF3 hF
      · rw [hΔ0, Multiset.map_zero] at hF
        rcases Multiset.mem_cons.mp hF with rfl | hF'
        · simp [AnnS4Form.erase, v0] at hFv0
        · exact Multiset.notMem_zero F hF'
  | @diaL A Γ Γ' Δ Δ' _ _ =>
    have hdia := hΓ (.dia A) (Multiset.mem_cons_self _ _)
    rcases hdia with h | h | h | h | h | h | h <;> cases h
  | @diaR A Γ Δ _ _ =>
    have hdia := hΔ (.dia A) (Multiset.mem_cons_self _ _)
    rcases hdia with h | h | h | h | h | h <;> cases h

private theorem main_proof :
    ∃ (A : S4Form) (B : LPForm) (CS : Set (ℕ × LPForm)),
      Nonempty (G3s 0 {A}) ∧
      B.forget = A ∧
      ¬ IsSelfRefCS CS ∧
      LPProv CS B ∧
      ∀ {ι : Type} (A_ann : AnnS4Form ι),
        A_ann.erase = A →
        ∀ (T : AnnG3s 0 {A_ann}), HasLeftPrehistCycle T ∧ HasPrehistCycle T := by
  refine ⟨counterA, counterB, ∅, ⟨counterA_g3s⟩, counterB_forget, empty_not_selfRef, counterB_lp0, ?_⟩
  intro ι A_ann herase T
  obtain ⟨i₁, i₂, i₃, i₄, rfl⟩ := ann_shape_of_erase_counterA herase
  have hL : LeftPrehist T i₄ i₄ :=
    leftPrehist_self_of_falsified i₁ i₂ i₃ i₄ T
      (fun _ h => absurd h (Multiset.notMem_zero _))
      (fun F h => by
        rw [Multiset.mem_singleton.mp h]
        exact Or.inl rfl)
      (fun _ h => absurd h (Multiset.notMem_zero _))
      (fun F h => by
        rw [Multiset.mem_singleton.mp h]
        rfl)
  exact ⟨⟨i₄, Relation.TransGen.single hL⟩, ⟨i₄, Relation.TransGen.single (Or.inl hL)⟩⟩

end OMA.P_arxiv_1902_01106

theorem OMA.solution : type_of% @OMA.S_arxiv_1902_01106.main :=
  OMA.P_arxiv_1902_01106.main_proof
