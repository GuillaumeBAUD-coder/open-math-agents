import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Prod.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Filter

namespace Conj11

def move (s : ℕ) (v : ℕ × ℕ) : ℕ × ℕ := (s + v.2, v.1)

def choose (friendly : Bool) (u v : ℕ × ℕ) : ℕ × ℕ :=
  if u.1 < v.1 then v else if v.1 < u.1 then u
  else if friendly then (u.1, max u.2 v.2) else (u.1, min u.2 v.2)

def outcome (a b : ℕ) (c₁ c₂ : Bool) (h : ℕ) : ℕ × ℕ :=
  if h < a then (0, 0) else
    let u := move a (if h - a < h then outcome a b c₂ c₁ (h-a) else (0, 0))
    if h < b then u else
      choose c₁ u (move b (if h - b < h then outcome a b c₂ c₁ (h-b) else (0, 0)))
termination_by h

theorem outcome_of_lt (a b h : ℕ) (c₁ c₂ : Bool) (hh : h < a) :
    outcome a b c₁ c₂ h = (0, 0) := by
  rw [outcome]
  simp only [hh, ↓reduceIte]

theorem outcome_of_one (a b h : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hah : a ≤ h) (hhb : h < b) :
    outcome a b c₁ c₂ h = move a (outcome a b c₂ c₁ (h-a)) := by
  rw [outcome]
  have hs : h - a < h := by omega
  simp only [Nat.not_lt.mpr hah, hhb, hs, ↓reduceIte]

theorem outcome_of_two (a b h : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hb : 0 < b) (hah : a ≤ h) (hbh : b ≤ h) :
    outcome a b c₁ c₂ h =
      choose c₁ (move a (outcome a b c₂ c₁ (h-a)))
        (move b (outcome a b c₂ c₁ (h-b))) := by
  rw [outcome]
  have hsa : h - a < h := by omega
  have hsb : h - b < h := by omega
  simp only [Nat.not_lt.mpr hah, Nat.not_lt.mpr hbh, hsa, hsb, ↓reduceIte]

end Conj11


namespace Conj13

open Conj11

/-- Definition 2 specialized to three ordered positive actions. -/
def outcome (a b c : ℕ) (c₁ c₂ : Bool) (h : ℕ) : ℕ × ℕ :=
  if h < a then (0, 0) else
    let u := move a (if h-a < h then outcome a b c c₂ c₁ (h-a) else (0,0))
    if h < b then u else
      let v := choose c₁ u (move b
        (if h-b < h then outcome a b c c₂ c₁ (h-b) else (0,0)))
      if h < c then v else
        choose c₁ v (move c
          (if h-c < h then outcome a b c c₂ c₁ (h-c) else (0,0)))
termination_by h

theorem outcome_of_lt (a b c h : ℕ) (c₁ c₂ : Bool) (hh : h < a) :
    outcome a b c c₁ c₂ h = (0,0) := by
  rw [outcome]
  simp only [hh, ↓reduceIte]

theorem outcome_of_one (a b c h : ℕ) (c₁ c₂ : Bool)
    (ha : 0<a) (hah : a≤h) (hhb : h<b) :
    outcome a b c c₁ c₂ h = move a (outcome a b c c₂ c₁ (h-a)) := by
  rw [outcome]
  have hs : h-a<h := by omega
  simp only [Nat.not_lt.mpr hah,hhb,hs,↓reduceIte]

theorem outcome_of_two (a b c h : ℕ) (c₁ c₂ : Bool)
    (ha : 0<a) (hb : 0<b) (hah : a≤h) (hbh : b≤h) (hhc : h<c) :
    outcome a b c c₁ c₂ h =
      choose c₁ (move a (outcome a b c c₂ c₁ (h-a)))
        (move b (outcome a b c c₂ c₁ (h-b))) := by
  rw [outcome]
  have hsa : h-a<h := by omega
  have hsb : h-b<h := by omega
  simp only [Nat.not_lt.mpr hah,Nat.not_lt.mpr hbh,hhc,hsa,hsb,↓reduceIte]

theorem outcome_of_three (a b c h : ℕ) (c₁ c₂ : Bool)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hah : a≤h) (hbh : b≤h) (hch : c≤h) :
    outcome a b c c₁ c₂ h =
      choose c₁
        (choose c₁ (move a (outcome a b c c₂ c₁ (h-a)))
          (move b (outcome a b c c₂ c₁ (h-b))))
        (move c (outcome a b c c₂ c₁ (h-c))) := by
  rw [outcome]
  have hsa : h-a<h := by omega
  have hsb : h-b<h := by omega
  have hsc : h-c<h := by omega
  simp only [Nat.not_lt.mpr hah,Nat.not_lt.mpr hbh,Nat.not_lt.mpr hch,
    hsa,hsb,hsc,↓reduceIte]

end Conj13

namespace OMA.S_arxiv_2510_24280

/-- One application of the recurrence of Definition 2 at heap `h`, for a mover who is friendly
(`friendly = true`) or antagonistic, where `prev k` is the outcome at the smaller heap `k`, seen from the
player who moves there. The result is (mover's total, other player's total). -/
def step (S : Finset ℕ) (friendly : Bool) (h : ℕ) (prev : ℕ → ℕ × ℕ) : ℕ × ℕ :=
  let moves := S.filter (fun s => s ≤ h)
  let mine : ℕ → ℕ := fun s => s + (prev (h - s)).2
  let theirs : ℕ → ℕ := fun s => (prev (h - s)).1
  let best := moves.sup mine
  let ties := moves.filter (fun s => mine s = best)
  (best,
    if friendly then ties.sup theirs
    else if hne : ties.Nonempty then ties.inf' hne theirs else 0)

/-- The outcome `o_X(h)` of the source: (total of the player to move, total of the other player) at heap
`h`, the player to move following convention `c₁` and the other player `c₂`. -/
def outcome (S : Finset ℕ) (c₁ c₂ : Bool) (h : ℕ) : ℕ × ℕ :=
  step S c₁ h (fun k => if _ : k < h then outcome S c₂ c₁ k else (0, 0))
termination_by h

end OMA.S_arxiv_2510_24280

namespace Conj13GenericModelBridge

open Conj11

def AtMost (friendly : Bool) (p q : ℕ × ℕ) : Prop :=
  p.1 ≤ q.1 ∧ (p.1 = q.1 → if friendly then p.2 ≤ q.2 else q.2 ≤ p.2)

theorem atMost_trans (friendly : Bool) (p q r : ℕ × ℕ)
    (hpq : AtMost friendly p q) (hqr : AtMost friendly q r) :
    AtMost friendly p r := by
  rcases hpq with ⟨h₁,h₂⟩
  rcases hqr with ⟨h₃,h₄⟩
  refine ⟨h₁.trans h₃, ?_⟩
  intro h
  have hp : p.1 = q.1 := by omega
  have hq : q.1 = r.1 := by omega
  cases friendly <;> simp_all <;> omega

theorem choose_eq_or (friendly : Bool) (u v : ℕ × ℕ) :
    choose friendly u v = u ∨ choose friendly u v = v := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> simp only [choose, Bool.false_eq_true,
    ↓reduceIte, max_def, min_def]
  all_goals split_ifs <;> simp_all
  all_goals omega

theorem atMost_choose_left (friendly : Bool) (u v : ℕ × ℕ) :
    AtMost friendly u (choose friendly u v) := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> simp only [AtMost, choose, Bool.false_eq_true,
    ↓reduceIte, max_def, min_def]
  all_goals split_ifs <;> simp_all <;> omega

theorem atMost_choose_right (friendly : Bool) (u v : ℕ × ℕ) :
    AtMost friendly v (choose friendly u v) := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> simp only [AtMost, choose, Bool.false_eq_true,
    ↓reduceIte, max_def, min_def]
  all_goals split_ifs <;> simp_all <;> omega

theorem step_eq_of_best (S : Finset ℕ) (friendly : Bool) (h : ℕ)
    (prev : ℕ → ℕ × ℕ) (w : ℕ × ℕ)
    (hw : ∃ s ∈ S, s ≤ h ∧ move s (prev (h-s)) = w)
    (hbest : ∀ s ∈ S, s ≤ h → AtMost friendly (move s (prev (h-s))) w) :
    OMA.S_arxiv_2510_24280.step S friendly h prev = w := by
  classical
  let moves := S.filter (fun s => s ≤ h)
  let mine := fun s => s + (prev (h-s)).2
  let theirs := fun s => (prev (h-s)).1
  have hsup : moves.sup mine = w.1 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro s hs
      rcases Finset.mem_filter.mp hs with ⟨hs,hh⟩
      exact (hbest s hs hh).1
    · rcases hw with ⟨s,hs,hh,he⟩
      have hm : s ∈ moves := Finset.mem_filter.mpr ⟨hs,hh⟩
      have he₁ : mine s = w.1 := congrArg Prod.fst he
      rw [← he₁]
      exact Finset.le_sup hm
  let ties := moves.filter (fun s => mine s = moves.sup mine)
  have hne : ties.Nonempty := by
    rcases hw with ⟨s,hs,hh,he⟩
    refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hs,hh⟩, ?_⟩⟩
    rw [hsup]
    exact congrArg Prod.fst he
  have hsecond : (if friendly then ties.sup theirs else
      if ht : ties.Nonempty then ties.inf' ht theirs else 0) = w.2 := by
    cases hf : friendly
    · simp only [Bool.false_eq_true, ↓reduceIte, dif_pos hne]
      apply le_antisymm
      · rcases hw with ⟨s,hs,hh,he⟩
        have hm : s ∈ ties := Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hs,hh⟩, by rw [hsup]; exact congrArg Prod.fst he⟩
        have he₂ : theirs s = w.2 := congrArg Prod.snd he
        rw [← he₂]
        exact Finset.inf'_le theirs hm
      · apply Finset.le_inf'
        intro s hs
        rcases Finset.mem_filter.mp hs with ⟨hm,he⟩
        rcases Finset.mem_filter.mp hm with ⟨hs,hh⟩
        have he' : (move s (prev (h-s))).1 = w.1 := by simpa [mine, move, hsup] using he
        simpa [hf, theirs, move] using (hbest s hs hh).2 he'
    · simp only [↓reduceIte]
      apply le_antisymm
      · apply Finset.sup_le
        intro s hs
        rcases Finset.mem_filter.mp hs with ⟨hm,he⟩
        rcases Finset.mem_filter.mp hm with ⟨hs,hh⟩
        have he' : (move s (prev (h-s))).1 = w.1 := by simpa [mine, move, hsup] using he
        simpa [hf, theirs, move] using (hbest s hs hh).2 he'
      · rcases hw with ⟨s,hs,hh,he⟩
        have hm : s ∈ ties := Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hs,hh⟩, by rw [hsup]; exact congrArg Prod.fst he⟩
        have he₂ : theirs s = w.2 := congrArg Prod.snd he
        rw [← he₂]
        exact Finset.le_sup hm
  change (moves.sup mine, if friendly then ties.sup theirs else
    if ht : ties.Nonempty then ties.inf' ht theirs else 0) = w
  exact Prod.ext hsup hsecond

theorem atMost_refl (friendly : Bool) (p : ℕ × ℕ) : AtMost friendly p p := by
  simp [AtMost]

theorem step_eq_zero (S : Finset ℕ) (friendly : Bool) (h : ℕ)
    (prev : ℕ → ℕ × ℕ) (hlegal : ∀ s ∈ S, h < s) :
    OMA.S_arxiv_2510_24280.step S friendly h prev = (0,0) := by
  have hm : S.filter (fun s => s ≤ h) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs
    exact Nat.not_le.mpr (hlegal s hs)
  simp [OMA.S_arxiv_2510_24280.step, hm]

theorem step_two (a b h : ℕ) (hab : a < b) (friendly : Bool)
    (prev : ℕ → ℕ × ℕ) :
    OMA.S_arxiv_2510_24280.step {a,b} friendly h prev =
      if h < a then (0,0) else
        if h < b then move a (prev (h-a)) else
          choose friendly (move a (prev (h-a))) (move b (prev (h-b))) := by
  by_cases hha : h < a
  · rw [if_pos hha]
    apply step_eq_zero
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> omega
  rw [if_neg hha]
  by_cases hhb : h < b
  · rw [if_pos hhb]
    apply step_eq_of_best
    · exact ⟨a, by simp, by omega, rfl⟩
    · intro s hs hsh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact atMost_refl _ _
      · omega
  · rw [if_neg hhb]
    apply step_eq_of_best
    · rcases choose_eq_or friendly (move a (prev (h-a))) (move b (prev (h-b))) with he | he
      · exact ⟨a, by simp, by omega, he.symm⟩
      · exact ⟨b, by simp, by omega, he.symm⟩
    · intro s hs _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact atMost_choose_left _ _ _
      · exact atMost_choose_right _ _ _

theorem step_three (a b c h : ℕ) (hab : a < b) (hbc : b < c)
    (friendly : Bool) (prev : ℕ → ℕ × ℕ) :
    OMA.S_arxiv_2510_24280.step {a,b,c} friendly h prev =
      if h < a then (0,0) else
        if h < b then move a (prev (h-a)) else
          if h < c then choose friendly (move a (prev (h-a))) (move b (prev (h-b)))
          else choose friendly
            (choose friendly (move a (prev (h-a))) (move b (prev (h-b))))
            (move c (prev (h-c))) := by
  by_cases hha : h < a
  · rw [if_pos hha]
    apply step_eq_zero
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> omega
  rw [if_neg hha]
  by_cases hhb : h < b
  · rw [if_pos hhb]
    apply step_eq_of_best
    · exact ⟨a, by simp, by omega, rfl⟩
    · intro s hs hsh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact atMost_refl _ _
      · omega
      · omega
  rw [if_neg hhb]
  by_cases hhc : h < c
  · rw [if_pos hhc]
    apply step_eq_of_best
    · rcases choose_eq_or friendly (move a (prev (h-a))) (move b (prev (h-b))) with he | he
      · exact ⟨a, by simp, by omega, he.symm⟩
      · exact ⟨b, by simp, by omega, he.symm⟩
    · intro s hs hsh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact atMost_choose_left _ _ _
      · exact atMost_choose_right _ _ _
      · omega
  rw [if_neg hhc]
  apply step_eq_of_best
  · rcases choose_eq_or friendly
      (choose friendly (move a (prev (h-a))) (move b (prev (h-b))))
      (move c (prev (h-c))) with he | he
    · rcases choose_eq_or friendly (move a (prev (h-a))) (move b (prev (h-b))) with he' | he'
      · exact ⟨a, by simp, by omega, (he.trans he').symm⟩
      · exact ⟨b, by simp, by omega, (he.trans he').symm⟩
    · exact ⟨c, by simp, by omega, he.symm⟩
  · intro s hs _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact atMost_trans _ _ _ _ (atMost_choose_left _ _ _) (atMost_choose_left _ _ _)
    · exact atMost_trans _ _ _ _ (atMost_choose_right _ _ _) (atMost_choose_left _ _ _)
    · exact atMost_choose_right _ _ _

theorem outcome_two_eq (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (h : ℕ) (c₁ c₂ : Bool) :
    OMA.S_arxiv_2510_24280.outcome {a,b} c₁ c₂ h =
      Conj11.outcome a b c₁ c₂ h := by
  induction h using Nat.strong_induction_on generalizing c₁ c₂ with
  | h h ih =>
    rw [OMA.S_arxiv_2510_24280.outcome, step_two a b h hab]
    by_cases hha : h < a
    · rw [if_pos hha, Conj11.outcome_of_lt a b h c₁ c₂ hha]
    rw [if_neg hha]
    have hah : a ≤ h := by omega
    have hsa : h-a < h := by omega
    have hpa : (if h-a < h then
        OMA.S_arxiv_2510_24280.outcome {a,b} c₂ c₁ (h-a) else (0,0)) =
        Conj11.outcome a b c₂ c₁ (h-a) := by
      rw [if_pos hsa]
      exact ih _ hsa _ _
    by_cases hhb : h < b
    · rw [if_pos hhb, Conj11.outcome_of_one a b h c₁ c₂ ha hah hhb]
      exact congrArg (move a) hpa
    · rw [if_neg hhb, Conj11.outcome_of_two a b h c₁ c₂ ha (by omega) hah (by omega)]
      have hsb : h-b < h := by omega
      have hpb : (if h-b < h then
          OMA.S_arxiv_2510_24280.outcome {a,b} c₂ c₁ (h-b) else (0,0)) =
          Conj11.outcome a b c₂ c₁ (h-b) := by
        rw [if_pos hsb]
        exact ih _ hsb _ _
      simp only [dif_pos hsa, dif_pos hsb, ih (h-a) hsa c₂ c₁, ih (h-b) hsb c₂ c₁]

theorem outcome_three_eq (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h : ℕ) (c₁ c₂ : Bool) :
    OMA.S_arxiv_2510_24280.outcome {a,b,c} c₁ c₂ h =
      Conj13.outcome a b c c₁ c₂ h := by
  induction h using Nat.strong_induction_on generalizing c₁ c₂ with
  | h h ih =>
    rw [OMA.S_arxiv_2510_24280.outcome, step_three a b c h hab hbc]
    by_cases hha : h < a
    · rw [if_pos hha, Conj13.outcome_of_lt a b c h c₁ c₂ hha]
    rw [if_neg hha]
    have hah : a ≤ h := by omega
    have hsa : h-a < h := by omega
    have hpa : (if h-a < h then
        OMA.S_arxiv_2510_24280.outcome {a,b,c} c₂ c₁ (h-a) else (0,0)) =
        Conj13.outcome a b c c₂ c₁ (h-a) := by
      rw [if_pos hsa]
      exact ih _ hsa _ _
    by_cases hhb : h < b
    · rw [if_pos hhb, Conj13.outcome_of_one a b c h c₁ c₂ ha hah hhb]
      exact congrArg (move a) hpa
    rw [if_neg hhb]
    have hbh : b ≤ h := by omega
    have hsb : h-b < h := by omega
    have hpb : (if h-b < h then
        OMA.S_arxiv_2510_24280.outcome {a,b,c} c₂ c₁ (h-b) else (0,0)) =
        Conj13.outcome a b c c₂ c₁ (h-b) := by
      rw [if_pos hsb]
      exact ih _ hsb _ _
    by_cases hhc : h < c
    · rw [if_pos hhc, Conj13.outcome_of_two a b c h c₁ c₂ ha (by omega) hah hbh hhc]
      simp only [dif_pos hsa, dif_pos hsb, ih (h-a) hsa c₂ c₁, ih (h-b) hsb c₂ c₁]
    · rw [if_neg hhc, Conj13.outcome_of_three a b c h c₁ c₂ ha (by omega) (by omega)
        hah hbh (by omega)]
      have hsc : h-c < h := by omega
      have hpc : (if h-c < h then
          OMA.S_arxiv_2510_24280.outcome {a,b,c} c₂ c₁ (h-c) else (0,0)) =
          Conj13.outcome a b c c₂ c₁ (h-c) := by
        rw [if_pos hsc]
        exact ih _ hsc _ _
      simp only [dif_pos hsa, dif_pos hsb, dif_pos hsc, ih (h-a) hsa c₂ c₁,
        ih (h-b) hsb c₂ c₁, ih (h-c) hsc c₂ c₁]

end Conj13GenericModelBridge





namespace Conj14

/-- Explicit lower-cell vector for the additive three-action game. -/
def lower (a b t r : ℕ) : ℕ × ℕ :=
  let q := r/a
  let u := q-t
  (t*(a+b)+a*((u+1)/2),t*b+a*min t q+a*(u/2))

/-- Profile-independent early vector; the domain is stated in the theorems. -/
def early (a b t r : ℕ) : ℕ × ℕ :=
  if r<b then lower a b t r
  else if r<a+b then
    ((t+1)*b+(if (t+1)*a≤r then (t+1)*a-b else 0),t*(a+b))
  else Conj11.move (a+b) (lower a b t (r-(a+b)))

end Conj14


namespace Conj14Lower

open Conj11 Conj14

theorem sub_self_div (a r : ℕ) (ha : 0<a) (har : a≤r) :
    (r-a)/a = r/a-1 := by
  have h : (r-a)/a+1 = r/a := by
    rw [←Nat.add_div_right _ ha, Nat.sub_add_cancel har]
  rw [←h, Nat.add_sub_cancel]

theorem choose_absorb (friendly : Bool) (u w : ℕ × ℕ)
    (hu : u=w ∨ u.1<w.1) : choose friendly u w = w := by
  rcases hu with rfl | hu
  · cases friendly <;> simp [choose]
  · simp [choose, hu]

theorem lower_double_move (a b k r : ℕ) (ha : 0<a) (har : a≤r) :
    move (a+b) (move (a+b) (lower a b k (r-a))) = lower a b (k+1) r := by
  have hd := sub_self_div a r ha har
  have hq : 0 < r/a := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_div_iff_mul_le ha).mpr (by simpa using har))
  have hu : (r-a)/a-k = r/a-(k+1) := by omega
  have hm : 1+min k ((r-a)/a) = min (k+1) (r/a) := by omega
  have hma := congrArg (fun z => a*z) hm
  apply Prod.ext
  · simp only [move, lower]
    rw [hu]
    ring
  · simp only [move, lower]
    rw [hu]
    nlinarith only [hma]

theorem c_candidate (a b k r : ℕ) (ha : 0<a) (_hab : a<b)
    (hdom : (k+1)*a<b) (_hr : r<b) :
    move (a+b) (early a b k (b+r)) = lower a b (k+1) r := by
  by_cases hra : r<a
  · have hz : (k+1)*a-b=0 := by omega
    simp only [early, show ¬b+r<b by omega, ↓reduceIte,
      show b+r<a+b by omega, hz, ite_self]
    simp only [lower, Nat.div_eq_of_lt hra, Nat.zero_sub, zero_add, Nat.zero_div,
      Nat.min_zero, Nat.mul_zero, add_zero, move]
    apply Prod.ext <;> ring
  · have hs : b+r-(a+b)=r-a := by omega
    simp only [early, show ¬b+r<b by omega, show ¬b+r<a+b by omega, ↓reduceIte, hs]
    exact lower_double_move a b k r ha (by omega)

theorem b_candidate (a b k r : ℕ) (ha : 0<a) (_hab : a<b) (_hr : r<b) :
    move b (early a b k (a+b+r)) = lower a b (k+1) r ∨
      (move b (early a b k (a+b+r))).1 < (lower a b (k+1) r).1 := by
  have he : early a b k (a+b+r) = move (a+b) (lower a b k r) := by
    simp [early, show ¬a+b+r<b by omega, show ¬a+b+r<a+b by omega]
  rw [he]
  by_cases hq : r/a < k+1
  · right
    have hu : r/a-k=0 := by omega
    have hv : r/a-(k+1)=0 := by omega
    simp only [move, lower, hu, hv, zero_add, Nat.zero_div,
      Nat.mul_zero, add_zero]
    nlinarith only [ha]
  · have hm : min k (r/a)=k := by omega
    have hn : min (k+1) (r/a)=k+1 := by omega
    have hu : r/a-k=(r/a-(k+1))+1 := by omega
    by_cases hp : ((r/a-(k+1))+2)/2=((r/a-(k+1))+1)/2+1
    · left
      have hf : ((r/a-(k+1))+1)/2=(r/a-(k+1))/2 := by omega
      apply Prod.ext
      · simp only [move, lower, hm, hn, hu]
        rw [show (r/a-(k+1))+1+1=(r/a-(k+1))+2 by omega, hp]
        ring
      · simp only [move, lower, hm, hn, hu]
        rw [hf]
        ring
    · right
      have hf : ((r/a-(k+1))+2)/2=((r/a-(k+1))+1)/2 := by omega
      simp only [move, lower, hm, hn, hu]
      rw [show (r/a-(k+1))+1+1=(r/a-(k+1))+2 by omega, hf]
      nlinarith only [ha]

theorem a_stay_candidate (a b t r : ℕ) (ha : 0<a) (_ht : 0<t) (har : a≤r) :
    move a (lower a b t (r-a)) = lower a b t r ∨
      (move a (lower a b t (r-a))).1 < (lower a b t r).1 := by
  have hd := sub_self_div a r ha har
  have hq : 0<r/a :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_div_iff_mul_le ha).mpr (by simpa using har))
  by_cases hqt : r/a<t
  · right
    have hm : min t (r/a)=r/a := by omega
    have hn : min t (r/a-1)=r/a-1 := by omega
    have hu : r/a-t=0 := by omega
    have hv : r/a-1-t=0 := by omega
    have he : a*(r/a-1)+a=a*(r/a) := by
      calc
        _ = a*((r/a-1)+1) := by ring
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1≤r/a)]
    have hl : a*(r/a)<a*t := Nat.mul_lt_mul_of_pos_left hqt ha
    simp only [move, lower, hd, hm, hn, hu, hv, zero_add, Nat.zero_div, Nat.mul_zero, add_zero]
    norm_num only
    nlinarith only [he,hl]
  by_cases heq : r/a=t
  · left
    have hm : min t (r/a-1)=t-1 := by omega
    have hn : min t (r/a)=t := by omega
    have hu : r/a-t=0 := by omega
    have hv : r/a-1-t=0 := by omega
    have he : a*(t-1)+a=a*t := by
      calc
        _ = a*((t-1)+1) := by ring
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1≤t)]
    apply Prod.ext
    · simp only [move, lower, hd, hm, hn, hu, hv, zero_add, Nat.zero_div, Nat.mul_zero, add_zero]
      norm_num only
      nlinarith only [he]
    · simp only [move, lower, hd, hm, hn, hu, hv, zero_add, Nat.zero_div, Nat.mul_zero, add_zero]
      ring
  · left
    have hm : min t (r/a-1)=t := by omega
    have hn : min t (r/a)=t := by omega
    have hc : 1+(r/a-1-t)/2=(r/a-t+1)/2 := by omega
    have hf : (r/a-1-t+1)/2=(r/a-t)/2 := by omega
    have hc' := congrArg (fun z => a*z) hc
    apply Prod.ext
    · simp only [move, lower, hd, hm, hn]
      nlinarith only [hc']
    · simp only [move, lower, hd, hm, hn]
      rw [hf]
      ring

theorem a_cross_candidate (a b k r : ℕ) (_ha : 0<a) (hab : a<b) (hra : r<a) :
    (move a (early a b k (a+2*b+r-a))).1 < (lower a b (k+1) r).1 := by
  have hz : a+2*b+r-a-(a+b)=b+r-a := by omega
  have he : early a b k (a+2*b+r-a) = move (a+b) (lower a b k (b+r-a)) := by
    simp only [early, show ¬a+2*b+r-a<b by omega,
      show ¬a+2*b+r-a<a+b by omega, ↓reduceIte, hz]
  rw [he]
  have hceil (q j : ℕ) : (q-j+1)/2 ≤ q := by omega
  have hq := hceil ((b+r-a)/a) k
  have hmul := Nat.mul_le_mul_left a hq
  have hdiv : a*((b+r-a)/a) ≤ b+r-a := Nat.mul_div_le _ _
  have hsum : a+(b+r-a)=b+r := by omega
  simp only [move, lower, Nat.div_eq_of_lt hra, Nat.zero_sub, zero_add, Nat.zero_div,
    Nat.mul_zero, add_zero]
  norm_num only
  nlinarith only [hmul,hdiv,hsum,hra]

theorem lower_step (a b t r : ℕ) (friendly : Bool)
    (ha : 0<a) (hab : a<b) (ht : 0<t) (hdom : t*a<b) (hr : r<b) :
    choose friendly
      (choose friendly
        (move a (if r<a then early a b (t-1) (a+2*b+r-a) else early a b t (r-a)))
        (move b (early a b (t-1) (a+b+r))))
      (move (a+b) (early a b (t-1) (b+r))) = lower a b t r := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp only [Nat.succ_sub_one]
  rw [c_candidate a b k r ha hab hdom hr]
  have ha' : move a (if r<a then early a b k (a+2*b+r-a) else early a b (k+1) (r-a)) =
      lower a b (k+1) r ∨
      (move a (if r<a then early a b k (a+2*b+r-a) else early a b (k+1) (r-a))).1 <
        (lower a b (k+1) r).1 := by
    by_cases hra : r<a
    · rw [if_pos hra]
      exact Or.inr (a_cross_candidate a b k r ha hab hra)
    · rw [if_neg hra]
      have he : early a b (k+1) (r-a)=lower a b (k+1) (r-a) := by
        simp [early, show r-a<b by omega]
      rw [he]
      exact a_stay_candidate a b (k+1) r ha (by omega) (by omega)
  have hb' := b_candidate a b k r ha hab hr
  rcases Conj13GenericModelBridge.choose_eq_or friendly
    (move a (if r<a then early a b k (a+2*b+r-a) else early a b (k+1) (r-a)))
    (move b (early a b k (a+b+r))) with he | he
  · rw [he]
    exact choose_absorb friendly _ _ ha'
  · rw [he]
    exact choose_absorb friendly _ _ hb'

end Conj14Lower





namespace Conj14Cut

open Conj11 Conj14

lemma choose_eq_left_of_atMost (friendly : Bool) (u v : ℕ × ℕ)
    (h : Conj13GenericModelBridge.AtMost friendly v u) : choose friendly u v = u := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> simp only [Conj13GenericModelBridge.AtMost, choose,
    Bool.false_eq_true, ↓reduceIte] at *
  all_goals split_ifs <;> simp_all [min_def,max_def] <;> omega

lemma choose_repeat_left (friendly : Bool) (u v : ℕ × ℕ) :
    choose friendly (choose friendly u v) u = choose friendly u v := by
  exact choose_eq_left_of_atMost friendly (choose friendly u v) u
    (Conj13GenericModelBridge.atMost_choose_left friendly u v)

lemma choose_same_other_le (friendly : Bool) (x y z : ℕ) (hxy : x ≤ y) :
    choose friendly (x,z) (y,z) = (y,z) := by
  by_cases hlt : x < y
  · simp [choose,hlt]
  have he : x=y := by omega
  subst y
  simp [choose]

lemma choose_same_other_ge (friendly : Bool) (x y z : ℕ) (hyx : y ≤ x) :
    choose friendly (x,z) (y,z) = (x,z) := by
  by_cases hlt : y < x
  · simp [choose,hlt,show ¬ x<y by omega]
  have he : x=y := by omega
  subst y
  simp [choose]

lemma cut_a_candidate (a b t r : ℕ) (ha : 0<a) (hab : a<b)
    (hta : t*a<b) (hbr : b≤r) (hrc : r<a+b) :
    move a (early a b t (r-a)) =
      (t*(a+b)+a*((r/a-t+1)/2),t*(a+b)+a*((r/a-t)/2)) := by
  have har : a≤r := by omega
  have hl : r-a<b := by omega
  have hq : t≤r/a := (Nat.le_div_iff_mul_le ha).2 (by omega)
  have hdiv : (r-a)/a = r/a-1 := by
    have h := Nat.div_eq_sub_div ha har
    rw [h,Nat.add_sub_cancel]
  simp only [early,if_pos hl,lower,hdiv]
  by_cases he : r/a=t
  · have ht : 0<t := by
      have h := Nat.div_eq_sub_div ha har
      omega
    have hsub : t-1-t=0 := by omega
    have hmin : min t (t-1)=t-1 := Nat.min_eq_right (by omega)
    rw [he]
    simp only [hsub,hmin,Nat.sub_self,Nat.zero_add,Nat.zero_div,
      Nat.mul_zero,Nat.add_zero,Nat.reduceDiv]
    have hp := congrArg (fun v : ℕ => a*v) (show t-1+1=t by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hp
    apply Prod.ext
    · dsimp [move]
      simp only [Nat.mul_add]
      nlinarith
    · dsimp [move]
  · have hqt : t<r/a := by omega
    have hmin : min t (r/a-1)=t := Nat.min_eq_left (by omega)
    have hhalf : (r/a-1-t+1)/2=(r/a-t)/2 := by omega
    have hother : 1+(r/a-1-t)/2=(r/a-t+1)/2 := by omega
    simp only [hmin,hhalf]
    have hp := congrArg (fun v : ℕ => a*v) hother
    simp only [Nat.mul_add,Nat.mul_one] at hp
    apply Prod.ext
    · dsimp [move]
      simp only [Nat.mul_add]
      nlinarith
    · dsimp [move]

lemma cut_b_candidate (a b t r : ℕ) (_ha : 0<a) (hab : a<b)
    (hbr : b≤r) (hrc : r<a+b) :
    move b (early a b t (r-b)) = ((t+1)*b,t*(a+b)) := by
  have hl : r-b<b := by omega
  have hdiv : (r-b)/a=0 := Nat.div_eq_of_lt (by omega)
  simp only [early,if_pos hl,lower,hdiv,Nat.zero_sub,Nat.zero_add,
    Nat.zero_div,Nat.mul_zero,Nat.min_zero,Nat.add_zero,Nat.reduceDiv]
  apply Prod.ext
  · dsimp [move]
    ring
  · rfl

lemma cut_c_candidate (a b t r : ℕ) (ha : 0<a) (hab : a<b)
    (ht : 0<t) (hta : t*a<b) (hbr : b≤r) (_hrc : r<a+b) :
    move (a+b) (early a b (t-1) (b+r)) =
      (t*(a+b)+a*((r/a-t+1)/2),t*(a+b)+a*((r/a-t)/2)) := by
  have hlow : ¬ b+r<b := by omega
  have hcut : ¬ b+r<a+b := by omega
  have hres : b+r-(a+b)=r-a := by omega
  have har : a≤r := by omega
  have hq : t≤r/a := (Nat.le_div_iff_mul_le ha).2 (by omega)
  have hdiv : (r-a)/a=r/a-1 := by
    have h := Nat.div_eq_sub_div ha har
    omega
  have hmin : min (t-1) (r/a-1)=t-1 := Nat.min_eq_left (by omega)
  have hsub : r/a-1-(t-1)=r/a-t := by omega
  simp only [early,if_neg hlow,if_neg hcut,hres,lower,hdiv,hmin,hsub]
  have hp := congrArg (fun v : ℕ => v*(a+b)) (show t-1+1=t by omega)
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_add] at hp
  apply Prod.ext <;> dsimp [move]
  · nlinarith
  · nlinarith

lemma cut_choose (a b t r : ℕ) (friendly : Bool) (ha : 0<a) (_hab : a<b)
    (hta : t*a<b) (hbr : b≤r) (hrc : r<a+b) :
    choose friendly
      (t*(a+b)+a*((r/a-t+1)/2),t*(a+b)+a*((r/a-t)/2))
      ((t+1)*b,t*(a+b)) = early a b t r := by
  have hq : t≤r/a := (Nat.le_div_iff_mul_le ha).2 (by omega)
  let k := r/a-t
  have hqsum : r/a=t+k := by dsimp [k]; omega
  have hbound := Nat.mul_div_le r a
  have hupp := Nat.lt_mul_div_succ r ha
  rw [hqsum,Nat.mul_add] at hbound hupp
  change choose friendly
    (t*(a+b)+a*((k+1)/2),t*(a+b)+a*(k/2))
    ((t+1)*b,t*(a+b)) = early a b t r
  by_cases hk0 : k=0
  · have hf : ¬ (t+1)*a≤r := by rw [hk0] at hupp; nlinarith
    have hearly : early a b t r=((t+1)*b,t*(a+b)) := by
      simp only [early,if_neg (show ¬r<b by omega),if_pos hrc,if_neg hf,Nat.add_zero]
    rw [hk0,hearly]
    norm_num only [Nat.mul_one,Nat.mul_zero,Nat.add_zero]
    have hfirst : t*(a+b)<(t+1)*b := by nlinarith
    exact choose_same_other_le friendly _ _ _ hfirst.le
  by_cases hk1 : k=1
  · have hi : (t+1)*a≤r := by rw [hk1] at hbound; nlinarith
    have hearly : early a b t r=
        ((t+1)*b+((t+1)*a-b),t*(a+b)) := by
      simp only [early,if_neg (show ¬r<b by omega),if_pos hrc,if_pos hi]
    rw [hk1,hearly]
    norm_num only [Nat.mul_one,Nat.mul_zero,Nat.add_zero]
    by_cases hdelta : (t+1)*a≤b
    · rw [Nat.sub_eq_zero_of_le hdelta,Nat.add_zero]
      have hfirst : t*(a+b)+a≤(t+1)*b := by nlinarith
      exact choose_same_other_le friendly _ _ _ hfirst
    · have hd : b≤(t+1)*a := by omega
      have hdsub := Nat.sub_add_cancel hd
      have hz : (t+1)*b+((t+1)*a-b)=t*(a+b)+a := by nlinarith
      rw [hz]
      have hfirst : (t+1)*b≤t*(a+b)+a := by nlinarith
      exact choose_same_other_ge friendly _ _ _ hfirst
  · have hk : 2≤k := by omega
    have hhalf : a*((k+1)/2)≤a*(k-1) := Nat.mul_le_mul_left a (by omega)
    have hp := congrArg (fun v : ℕ => a*v) (show k-1+1=k by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hp
    have htwo := Nat.mul_le_mul_left a hk
    have hdelta : (t+1)*a≤b := by nlinarith
    have hearly : early a b t r=((t+1)*b,t*(a+b)) := by
      simp only [early,if_neg (show ¬r<b by omega),if_pos hrc,
        Nat.sub_eq_zero_of_le hdelta,ite_self,Nat.add_zero]
    have hfirst : t*(a+b)+a*((k+1)/2)<(t+1)*b := by nlinarith
    rw [hearly]
    simp only [choose,hfirst,↓reduceIte]

theorem cut_step (a b t r : ℕ) (friendly : Bool)
    (ha : 0<a) (hab : a<b) (ht : 0<t) (hta : t*a<b)
    (hbr : b≤r) (hrc : r<a+b) :
    choose friendly
      (choose friendly (move a (early a b t (r-a))) (move b (early a b t (r-b))))
      (move (a+b) (early a b (t-1) (b+r))) = early a b t r := by
  rw [cut_a_candidate a b t r ha hab hta hbr hrc,
    cut_b_candidate a b t r ha hab hbr hrc,
    cut_c_candidate a b t r ha hab ht hta hbr hrc,choose_repeat_left]
  exact cut_choose a b t r friendly ha hab hta hbr hrc

theorem cut_step_zero (a b r : ℕ) (friendly : Bool)
    (ha : 0<a) (hab : a<b) (hbr : b≤r) (hrc : r<a+b) :
    choose friendly (move a (early a b 0 (r-a))) (move b (early a b 0 (r-b))) =
      early a b 0 r := by
  have hta : 0*a<b := by omega
  rw [cut_a_candidate a b 0 r ha hab hta hbr hrc,
    cut_b_candidate a b 0 r ha hab hbr hrc]
  exact cut_choose a b 0 r friendly ha hab hta hbr hrc

end Conj14Cut


namespace Conj14Upper

open Conj11 Conj14

theorem choose_right (friendly : Bool) (u v : ℕ×ℕ)
    (h : Conj13GenericModelBridge.AtMost friendly u v) : choose friendly u v=v := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> simp only [Conj13GenericModelBridge.AtMost,choose,
    Bool.false_eq_true,↓reduceIte] at *
  all_goals split_ifs <;> simp_all [min_def,max_def] <;> omega

theorem choose_absorb (friendly : Bool) (u v z : ℕ×ℕ)
    (hu : choose friendly u z=z) (hv : choose friendly v z=z) :
    choose friendly (choose friendly u v) z=z := by
  rcases Conj13GenericModelBridge.choose_eq_or friendly u v with h|h
  · rw [h]; exact hu
  · rw [h]; exact hv

theorem upper_a_strict (a b t r : ℕ) (ha : 0<a) (hab : a<b)
    (hta : t*a<b) (hcr : a+b≤r) (hrL : r<a+2*b) :
    (move a (early a b t (r-a))).1 < (early a b t r).1 := by
  let z : ℕ := r-(a+b)
  have hz : z<b := by dsimp [z]; omega
  have hrz : r=a+b+z := by dsimp [z]; omega
  have hrr : ¬r<b := by omega
  have hrc : ¬r<a+b := by omega
  have hchild : ¬r-a<b := by omega
  by_cases hza : z<a
  · have hcut : r-a<a+b := by omega
    have hzero : z/a=0 := Nat.div_eq_of_lt hza
    simp only [early,if_neg hrr,if_neg hrc,if_neg hchild,if_pos hcut,
      move,lower,show r-(a+b)=z from rfl,hzero,Nat.zero_sub,Nat.min_zero,
      Nat.zero_add,Nat.div_eq_of_lt (by omega : 1<2),Nat.mul_zero,Nat.add_zero]
    nlinarith
  · have hupper : ¬r-a<a+b := by omega
    have hrem : r-a-(a+b)=z-a := by omega
    have hdiv : (z-a)/a=z/a-1 := by simpa using Nat.sub_mul_div z a 1
    simp only [early,if_neg hrr,if_neg hrc,if_neg hchild,if_neg hupper,move,
      lower,show r-(a+b)=z from rfl,hrem,hdiv]
    by_cases hqt : z/a≤t
    · have hzsub : z/a-t=0 := by omega
      have hsub : z/a-1-t=0 := by omega
      simp only [hzsub,hsub,Nat.min_eq_right hqt,Nat.zero_add,
        Nat.div_eq_of_lt (by omega : 1<2),Nat.mul_zero,Nat.add_zero]
      nlinarith [Nat.zero_le (a*(z/a))]
    · have hmin : min t (z/a)=t := Nat.min_eq_left (by omega)
      have hsub : z/a-1-t+1=z/a-t := by omega
      simp only [hmin,hsub]
      nlinarith


theorem upper_b_compare (a b t r : ℕ) (ha : 0<a) (_hab : a<b)
    (_hta : t*a<b) (hcr : a+b≤r) (hrL : r<a+2*b)
    (hextra : 2*b≤r → (t+1)*a≤b) :
    (move b (early a b t (r-b))).1≤(early a b t r).1 ∧
      ((move b (early a b t (r-b))).1=(early a b t r).1 →
        (move b (early a b t (r-b))).2=(early a b t r).2) := by
  let z : ℕ := r-(a+b)
  have hz : z<b := by dsimp [z]; omega
  have hrz : r=a+b+z := by dsimp [z]; omega
  have hrr : ¬r<b := by omega
  have hrc : ¬r<a+b := by omega
  by_cases hr2 : r<2*b
  · have hlow : r-b<b := by omega
    have hrem : r-b=z+a := by omega
    have hdiv : (r-b)/a=z/a+1 := by rw [hrem,Nat.add_div_right z ha]
    simp only [early,if_neg hrr,if_neg hrc,if_pos hlow,lower,move,hdiv,
      show r-(a+b)=z from rfl]
    by_cases hqt : z/a<t
    · have hsub : z/a-t=0 := by omega
      have hsub' : z/a+1-t=0 := by omega
      have hmin : min t (z/a)=z/a := Nat.min_eq_right (by omega)
      have hmin' : min t (z/a+1)=z/a+1 := Nat.min_eq_right (by omega)
      simp only [hsub,hsub',hmin,hmin',Nat.zero_add,
        Nat.div_eq_of_lt (by omega : 1<2),Nat.mul_zero,Nat.add_zero]
      constructor
      · nlinarith
      · intro _; trivial
    · let u : ℕ := z/a-t
      have hmin : min t (z/a)=t := Nat.min_eq_left (by omega)
      have hmin' : min t (z/a+1)=t := Nat.min_eq_left (by omega)
      have hsub : z/a+1-t=u+1 := by dsimp [u]; omega
      simp only [hmin,hmin',hsub,show z/a-t=u from rfl]
      have hhalf : (u+1)/2≤u/2+1 := by omega
      have hmul := Nat.mul_le_mul_left a hhalf
      constructor
      · nlinarith
      · intro he
        have hehalf : u/2+1=(u+1)/2 := by
          apply Nat.mul_left_cancel ha
          nlinarith
        have heopp : (u+1+1)/2=(u+1)/2 := by omega
        rw [heopp]
  · have h2r : 2*b≤r := by omega
    have hta' := hextra h2r
    have hcutlo : ¬r-b<b := by omega
    have hcut : r-b<a+b := by omega
    have hbump : (t+1)*a-b=0 := by omega
    have htq : t≤z/a := (Nat.le_div_iff_mul_le ha).2 (by dsimp [z]; nlinarith)
    have hmin : min t (z/a)=t := Nat.min_eq_left htq
    simp only [early,if_neg hrr,if_neg hrc,if_neg hcutlo,if_pos hcut,hbump,
      ite_self,Nat.add_zero,move,lower,show r-(a+b)=z from rfl,hmin]
    have hstrict : b+t*(a+b)<a+b+(t*b+a*t+a*((z/a-t)/2)) := by
      nlinarith [Nat.zero_le (a*((z/a-t)/2))]
    exact ⟨hstrict.le,fun he => False.elim (Nat.ne_of_lt hstrict he)⟩

theorem upper_step (a b t r : ℕ) (friendly : Bool) (ha : 0<a) (hab : a<b)
    (hta : t*a<b) (hcr : a+b≤r) (hrL : r<a+2*b)
    (hextra : 2*b≤r → (t+1)*a≤b) :
    choose friendly
      (choose friendly (move a (early a b t (r-a))) (move b (early a b t (r-b))))
      (move (a+b) (early a b t (r-(a+b))))=early a b t r := by
  have hlow : r-(a+b)<b := by omega
  have hsupply : move (a+b) (early a b t (r-(a+b)))=early a b t r := by
    simp only [early,if_neg (show ¬r<b by omega),if_neg (show ¬r<a+b by omega),
      if_pos hlow]
  rw [hsupply]
  apply choose_absorb
  · apply choose_right
    have h := upper_a_strict a b t r ha hab hta hcr hrL
    refine ⟨h.le,?_⟩
    intro he
    exact False.elim (Nat.ne_of_lt h he)
  · apply choose_right
    obtain ⟨hown,heq⟩ := upper_b_compare a b t r ha hab hta hcr hrL hextra
    refine ⟨hown,?_⟩
    intro he
    rw [heq he]
    cases friendly <;> simp

end Conj14Upper


namespace Conj14Early

open Conj11 Conj14

theorem predecessor_mul (t x : ℕ) (ht : 0<t) : (t-1)*x+x=t*x := by
  have h : t-1+1=t := by omega
  calc
    _ = (t-1+1)*x := by ring
    _ = _ := by rw [h]

theorem lower_zero_step (a b r : ℕ) (ha : 0<a) (har : a≤r) :
    move a (lower a b 0 (r-a))=lower a b 0 r := by
  have hq : 0<r/a := (Nat.le_div_iff_mul_le ha).2 (by omega)
  have hdiv : (r-a)/a=r/a-1 := by simpa using Nat.sub_mul_div r a 1
  have he₁ : r/a-1+1=r/a := by omega
  have he₂ : 1+(r/a-1)/2=(r/a+1)/2 := by omega
  simp only [lower,hdiv,Nat.zero_mul,Nat.zero_add,Nat.sub_zero,Nat.zero_min,
    Nat.mul_zero,Nat.add_zero,move,he₁]
  apply Prod.ext
  · dsimp only
    nlinarith
  · rfl

theorem outcome_eq_early_of_steps (a b : ℕ) (ha : 0<a) (hab : a<b)
    (hlo : ∀ t r f,0<t → t*a<b → r<b →
      choose f
        (choose f
          (move a (if r<a then early a b (t-1) (a+2*b+r-a) else early a b t (r-a)))
          (move b (early a b (t-1) (a+b+r))))
        (move (a+b) (early a b (t-1) (b+r)))=lower a b t r)
    (hcut : ∀ t r f,0<t → t*a<b → b≤r → r<a+b →
      choose f
        (choose f (move a (early a b t (r-a))) (move b (early a b t (r-b))))
        (move (a+b) (early a b (t-1) (b+r)))=early a b t r)
    (hcut0 : ∀ r f,b≤r → r<a+b →
      choose f (move a (early a b 0 (r-a))) (move b (early a b 0 (r-b)))=early a b 0 r)
    (hup : ∀ t r f,t*a<b → a+b≤r → r<a+2*b → (2*b≤r → (t+1)*a≤b) →
      choose f
        (choose f (move a (early a b t (r-a))) (move b (early a b t (r-b))))
        (move (a+b) (early a b t (r-(a+b))))=early a b t r) :
    ∀ h t r,h=t*(a+2*b)+r → r<a+2*b → t*a<b → (2*b≤r → (t+1)*a≤b) →
      ∀ c₁ c₂,Conj13.outcome a b (a+b) c₁ c₂ h=early a b t r := by
  have hb : 0<b := by omega
  have hc : 0<a+b := by omega
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro t r hh hrL hta hextra c₁ c₂
    have hget (s : ℕ) (hs : 0<s) (hsc : s≤a+b) (hsh : s≤h) :
        Conj13.outcome a b (a+b) c₂ c₁ (h-s)=
          if r<s then early a b (t-1) (a+2*b+r-s) else early a b t (r-s) := by
      by_cases hrs : r<s
      · rw [if_pos hrs]
        have ht : 0<t := by
          by_contra hn
          have ht0 : t=0 := by omega
          have hh' : h=r := by simpa [ht0] using hh
          omega
        have hp := predecessor_mul t (a+2*b) ht
        have hpa := Nat.mul_le_mul_right a (show t-1≤t by omega)
        have hts : t-1+1=t := by omega
        apply ih (h-s) (by omega) (t-1) (a+2*b+r-s) (by omega) (by omega)
          (by omega) (fun _ => by rw [hts]; exact hta.le) c₂ c₁
      · rw [if_neg hrs]
        apply ih (h-s) (by omega) t (r-s) (by omega) (by omega) hta
          (fun h2 => hextra (by omega)) c₂ c₁
    by_cases hrlow : r<b
    · by_cases ht0 : t=0
      · have hhr : h=r := by simpa [ht0] using hh
        rw [ht0,hhr]
        by_cases hra : r<a
        · rw [Conj13.outcome_of_lt a b (a+b) r c₁ c₂ hra]
          simp [early,hrlow,lower,Nat.div_eq_of_lt hra]
        · have har : a≤r := by omega
          rw [Conj13.outcome_of_one a b (a+b) r c₁ c₂ ha har hrlow]
          rw [ih (r-a) (by omega) 0 (r-a) (by simp) (by omega) (by omega)
            (fun h2 => by omega) c₂ c₁]
          have hpa : early a b 0 (r-a)=lower a b 0 (r-a) := by
            simp only [early,if_pos (show r-a<b by omega)]
          rw [hpa]
          have hpr : early a b 0 r=lower a b 0 r := by simp only [early,if_pos hrlow]
          rw [hpr]
          exact lower_zero_step a b r ha har
      · have ht : 0<t := by omega
        have hp := predecessor_mul t (a+2*b) ht
        have hch : a+b≤h := by omega
        rw [Conj13.outcome_of_three a b (a+b) h c₁ c₂ ha hb hc (by omega) (by omega) hch,
          hget a ha (by omega) (by omega),hget b hb (by omega) (by omega),
          hget (a+b) hc (by omega) hch]
        have hbrem : a+2*b+r-b=a+b+r := by omega
        have hcrem : a+2*b+r-(a+b)=b+r := by omega
        simp only [if_pos hrlow,if_pos (show r<a+b by omega),hbrem,hcrem]
        have hpr : early a b t r=lower a b t r := by simp only [early,if_pos hrlow]
        rw [hpr]
        exact hlo t r c₁ ht hta hrlow
    · have hbr : b≤r := by omega
      by_cases hrc : r<a+b
      · by_cases ht0 : t=0
        · have hhr : h=r := by simpa [ht0] using hh
          rw [ht0,hhr]
          rw [Conj13.outcome_of_two a b (a+b) r c₁ c₂ ha hb (by omega) hbr hrc,
            ih (r-a) (by omega) 0 (r-a) (by simp) (by omega) (by omega)
              (fun h2 => by omega) c₂ c₁,
            ih (r-b) (by omega) 0 (r-b) (by simp) (by omega) (by omega)
              (fun h2 => by omega) c₂ c₁]
          exact hcut0 r c₁ hbr hrc
        · have ht : 0<t := by omega
          have hp := predecessor_mul t (a+2*b) ht
          have hch : a+b≤h := by omega
          rw [Conj13.outcome_of_three a b (a+b) h c₁ c₂ ha hb hc (by omega) (by omega) hch,
            hget a ha (by omega) (by omega),hget b hb (by omega) (by omega),
            hget (a+b) hc (by omega) hch]
          have hcrem : a+2*b+r-(a+b)=b+r := by omega
          simp only [if_neg (show ¬r<a by omega),if_neg hrlow,if_pos hrc,hcrem]
          exact hcut t r c₁ ht hta hbr hrc
      · have hcr : a+b≤r := by omega
        have hch : a+b≤h := by omega
        rw [Conj13.outcome_of_three a b (a+b) h c₁ c₂ ha hb hc (by omega) (by omega) hch,
          hget a ha (by omega) (by omega),hget b hb (by omega) (by omega),
          hget (a+b) hc (by omega) hch]
        simp only [if_neg (show ¬r<a by omega),if_neg hrlow,if_neg hrc]
        exact hup t r c₁ hta hcr hrL hextra


theorem nondiv_parameters (a b : ℕ) (ha : 0<a) (hab : a<b) (hdiv : ¬a∣b) :
    ∃ n : ℕ,0<n ∧ n*a<b ∧ b<(n+1)*a := by
  let n : ℕ := b/a
  have hn : 0<n := (Nat.le_div_iff_mul_le ha).2 (by omega)
  have hle : n*a≤b := Nat.div_mul_le_self b a
  have hne : n*a≠b := by
    intro he
    apply hdiv
    exact ⟨n,by simpa [Nat.mul_comm] using he.symm⟩
  refine ⟨n,hn,by omega,?_⟩
  simpa [n,Nat.mul_comm] using Nat.lt_mul_div_succ b ha

end Conj14Early


namespace Conj14Early

/-- The actual profile-independent early formula; all cell identities are proved. -/
theorem outcome_eq_early (a b t r : ℕ) (ha : 0<a) (hab : a<b)
    (hrL : r<a+2*b) (hta : t*a<b) (hextra : 2*b≤r → (t+1)*a≤b)
    (c₁ c₂ : Bool) :
    Conj13.outcome a b (a+b) c₁ c₂ (t*(a+2*b)+r)=Conj14.early a b t r := by
  exact outcome_eq_early_of_steps a b ha hab
    (fun t r f ht hdom hr => Conj14Lower.lower_step a b t r f ha hab ht hdom hr)
    (fun t r f ht hdom hbr hrc => Conj14Cut.cut_step a b t r f ha hab ht hdom hbr hrc)
    (fun r f hbr hrc => Conj14Cut.cut_step_zero a b r f ha hab hbr hrc)
    (fun t r f hdom hcr hrL hex => Conj14Upper.upper_step a b t r f ha hab hdom hcr hrL hex)
    (t*(a+2*b)+r) t r rfl hrL hta hextra c₁ c₂

end Conj14Early


namespace Conj14Integer

open Conj11

/-- Equal-total alternatives have no genuine secondary preference. -/
theorem choose_independent_of_convention (u v : ℕ × ℕ) (friendly : Bool)
    (htotal : u.1 + u.2 = v.1 + v.2) :
    choose friendly u v = choose true u v := by
  by_cases huv : u.1 < v.1
  · simp [choose, huv]
  by_cases hvu : v.1 < u.1
  · simp [choose, huv, hvu]
  have heq : u = v := by
    apply Prod.ext <;> omega
  subst v
  cases friendly <;> simp [choose]

theorem choose_preserves_total (u v : ℕ × ℕ) (friendly : Bool) (h : ℕ)
    (hu : u.1 + u.2 = h) (hv : v.1 + v.2 = h) :
    (choose friendly u v).1 + (choose friendly u v).2 = h := by
  by_cases huv : u.1 < v.1
  · simpa [choose, huv] using hv
  by_cases hvu : v.1 < u.1
  · simpa [choose, huv, hvu] using hu
  have heq : u = v := by
    apply Prod.ext <;> omega
  subst v
  cases friendly <;> simpa [choose] using hu

lemma mod_sub_of_dvd (a s h : ℕ) (hs : s ≤ h) (hdvd : a ∣ s) :
    (h - s) % a = h % a := by
  have hm := congrArg (fun z : ℕ => z % a) (Nat.sub_add_cancel hs)
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.add_zero, Nat.mod_mod] at hm
  exact hm

lemma move_total (a s h : ℕ) (v : ℕ × ℕ) (hs : s ≤ h) (hdvd : a ∣ s)
    (hv : v.1 + v.2 = (h-s) - (h-s) % a) :
    (move s v).1 + (move s v).2 = h - h % a := by
  have hm := mod_sub_of_dvd a s h hs hdvd
  have hr := Nat.mod_le (h-s) a
  rw [hm] at hv hr
  dsimp [move]
  omega

/-- If the least move divides every move, all profiles coincide and all
available pebbles except the invariant remainder are consumed. -/
theorem outcome_independent_and_total (a b c : ℕ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (habdiv : a ∣ b) (hacdiv : a ∣ c) :
    ∀ h : ℕ,
      (∀ c₁ c₂ : Bool, Conj13.outcome a b c c₁ c₂ h =
        Conj13.outcome a b c true true h) ∧
      (Conj13.outcome a b c true true h).1 +
        (Conj13.outcome a b c true true h).2 = h - h % a := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hha : h < a
    · constructor
      · intro c₁ c₂
        rw [Conj13.outcome_of_lt a b c h c₁ c₂ hha,
          Conj13.outcome_of_lt a b c h true true hha]
      · rw [Conj13.outcome_of_lt a b c h true true hha]
        simp [Nat.mod_eq_of_lt hha]
    · have hah : a ≤ h := by omega
      obtain ⟨heqa, hsuma⟩ := ih (h-a) (by omega)
      let u := move a (Conj13.outcome a b c true true (h-a))
      have hu : u.1 + u.2 = h - h % a :=
        move_total a a h _ hah (dvd_refl a) hsuma
      by_cases hhb : h < b
      · have hstep (c₁ c₂ : Bool) : Conj13.outcome a b c c₁ c₂ h = u := by
          rw [Conj13.outcome_of_one a b c h c₁ c₂ ha hah hhb, heqa c₂ c₁]
        constructor
        · intro c₁ c₂
          rw [hstep c₁ c₂, hstep true true]
        · rw [hstep true true]
          exact hu
      · have hbh : b ≤ h := by omega
        obtain ⟨heqb, hsumb⟩ := ih (h-b) (by omega)
        let v := move b (Conj13.outcome a b c true true (h-b))
        have hv : v.1 + v.2 = h - h % a :=
          move_total a b h _ hbh habdiv hsumb
        by_cases hhc : h < c
        · have hstep (c₁ c₂ : Bool) :
              Conj13.outcome a b c c₁ c₂ h = choose c₁ u v := by
            rw [Conj13.outcome_of_two a b c h c₁ c₂ ha (by omega) hah hbh hhc,
              heqa c₂ c₁, heqb c₂ c₁]
          constructor
          · intro c₁ c₂
            rw [hstep c₁ c₂, hstep true true]
            exact choose_independent_of_convention u v c₁ (hu.trans hv.symm)
          · rw [hstep true true]
            exact choose_preserves_total u v true (h-h%a) hu hv
        · have hch : c ≤ h := by omega
          obtain ⟨heqc, hsumc⟩ := ih (h-c) (by omega)
          let z := move c (Conj13.outcome a b c true true (h-c))
          have hz : z.1 + z.2 = h - h % a :=
            move_total a c h _ hch hacdiv hsumc
          have hw : (choose true u v).1 + (choose true u v).2 = h - h % a :=
            choose_preserves_total u v true (h-h%a) hu hv
          have hstep (c₁ c₂ : Bool) : Conj13.outcome a b c c₁ c₂ h =
              choose c₁ (choose c₁ u v) z := by
            rw [Conj13.outcome_of_three a b c h c₁ c₂ ha (by omega) (by omega)
              hah hbh hch, heqa c₂ c₁, heqb c₂ c₁, heqc c₂ c₁]
          constructor
          · intro c₁ c₂
            rw [hstep c₁ c₂, hstep true true,
              choose_independent_of_convention u v c₁ (hu.trans hv.symm)]
            exact choose_independent_of_convention (choose true u v) z c₁ (hw.trans hz.symm)
          · rw [hstep true true]
            exact choose_preserves_total (choose true u v) z true (h-h%a) hw hz

theorem outcome_total (a b c h : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (habdiv : a ∣ b) (hacdiv : a ∣ c) :
    (Conj13.outcome a b c c₁ c₂ h).1 + (Conj13.outcome a b c c₁ c₂ h).2 = h-h%a := by
  obtain ⟨heq, hsum⟩ := outcome_independent_and_total a b c ha hab hbc habdiv hacdiv h
  rw [heq c₁ c₂]
  exact hsum

/-- The integer-ratio direction of Conjecture14 in the specialized recurrence. -/
theorem no_discrepancy_of_dvd (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hdiv : a ∣ b) :
    ∀ h : ℕ, Conj13.outcome a b (a+b) true true h =
      Conj13.outcome a b (a+b) false false h := by
  intro h
  obtain ⟨heq, _⟩ := outcome_independent_and_total a b (a+b) ha hab (by omega)
    hdiv (Nat.dvd_add (dvd_refl a) hdiv) h
  exact (heq false false).symm

/-- The integer-ratio direction in the exact approved finite-set recurrence. -/
theorem generic_no_discrepancy_of_dvd (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hdiv : a ∣ b) :
    ∀ h : ℕ, OMA.S_arxiv_2510_24280.outcome {a,b,a+b} true true h =
      OMA.S_arxiv_2510_24280.outcome {a,b,a+b} false false h := by
  intro h
  rw [Conj13GenericModelBridge.outcome_three_eq a b (a+b) ha hab (by omega),
    Conj13GenericModelBridge.outcome_three_eq a b (a+b) ha hab (by omega)]
  exact no_discrepancy_of_dvd a b ha hab hdiv h

end Conj14Integer


namespace Conj14Assembly

open Conj11 Conj14

def Core (a b : ℕ) : Prop :=
  ∀ (t r : ℕ) (c₁ c₂ : Bool), r<a+2*b → t*a<b →
    (2*b≤r → (t+1)*a≤b) →
    Conj13.outcome a b (a+b) c₁ c₂ (t*(a+2*b)+r) = early a b t r

theorem all_conventions_before (a b n h : ℕ) (ha : 0<a) (_hab : a<b)
    (hna : n*a<b) (hcore : Core a b) (hh : h<n*(a+2*b)+2*b) (c₁ c₂ : Bool) :
    Conj13.outcome a b (a+b) c₁ c₂ h = Conj13.outcome a b (a+b) true true h := by
  let L := a+2*b
  let t := h/L
  let r := h%L
  have hL : 0<L := by dsimp [L]; omega
  have hr : r<L := Nat.mod_lt _ hL
  have hrep : h=t*L+r := by
    dsimp [t,r]
    simpa [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div h L).symm
  have hbig : h<(n+1)*L := by
    change h<n*L+2*b at hh
    calc
      h<n*L+2*b := hh
      _<n*L+L := by dsimp [L]; omega
      _=(n+1)*L := by ring
  have htn : t≤n := by
    have hx := (Nat.div_lt_iff_lt_mul hL).mpr hbig
    dsimp [t]
    omega
  have ht : t*a<b := (Nat.mul_le_mul_right a htn).trans_lt hna
  have hlast : 2*b≤r → (t+1)*a≤b := by
    intro hlarge
    have htn' : t<n := by
      by_contra hnot
      have hteq : t=n := by omega
      rw [hteq] at hrep
      change h<n*L+2*b at hh
      omega
    exact (Nat.mul_le_mul_right a (show t+1≤n by omega)).trans hna.le
  rw [hrep,hcore t r c₁ c₂ hr ht hlast,hcore t r true true hr ht hlast]

theorem endpoint_profile (a b n : ℕ) (ha : 0<a) (hab : a<b) (hn : 0<n)
    (hna : n*a<b) (hupper : b<(n+1)*a) (hcore : Core a b) (c₁ c₂ : Bool) :
    let H := n*(a+2*b)+2*b
    Conj13.outcome a b (a+b) c₁ c₂ H =
      (n*(a+b)+b, if c₁ then (n+1)*b else n*(a+b)) := by
  dsimp only
  let H := n*(a+2*b)+2*b
  have hb : 0<b := by omega
  have hdiv : b/a=n := by
    have hlo := (Nat.le_div_iff_mul_le ha).mpr hna.le
    have hhi := (Nat.div_lt_iff_lt_mul ha).mpr hupper
    omega
  have hsubdiv : (b-a)/a=n-1 := by
    simpa only [Nat.mul_one,hdiv] using (Nat.sub_mul_div b a 1)
  have htwodiv : (b-2*a)/a=n-2 := by
    simpa only [Nat.mul_comm a 2,hdiv] using (Nat.sub_mul_div b a 2)
  have hcalc : n*b+a*(n-1)=n*(a+b)-a := by
    have hn1 : n-1+1=n := by omega
    have hx : a*(n-1)+a=n*a := by
      calc
        _=a*(n-1+1) := by ring
        _=_ := by rw [hn1]; ring
    have hy : n*(a+b)=n*b+n*a := by ring
    omega
  have hchildb (d₁ d₂ : Bool) :
      Conj13.outcome a b (a+b) d₁ d₂ (H-b)=((n+1)*b,n*(a+b)) := by
    have he : H-b=n*(a+2*b)+b := by dsimp [H]; omega
    rw [he,hcore n b d₁ d₂ (by omega) hna (by omega)]
    simp [early,show b<a+b by omega,show ¬(n+1)*a≤b by omega]
  have hchildc (d₁ d₂ : Bool) :
      Conj13.outcome a b (a+b) d₁ d₂ (H-(a+b))=(n*(a+b),n*(a+b)-a) := by
    have he : H-(a+b)=n*(a+2*b)+(b-a) := by dsimp [H]; omega
    have hr : b-a<b := by omega
    rw [he,hcore n (b-a) d₁ d₂ (by omega) hna (by omega)]
    simp only [early,if_pos hr,lower,hsubdiv,Nat.sub_eq_zero_of_le (Nat.sub_le n 1),
      Nat.min_eq_right (Nat.sub_le n 1)]
    norm_num only
    exact Prod.ext (by ring) hcalc
  have hchilda (d₁ d₂ : Bool) :
      (Conj13.outcome a b (a+b) d₁ d₂ (H-a)).2=n*(a+b) := by
    have he : H-a=n*(a+2*b)+(2*b-a) := by dsimp [H]; omega
    rw [he,hcore n (2*b-a) d₁ d₂ (by omega) hna (by omega)]
    by_cases hr : 2*b-a<a+b
    · simp [early,show ¬2*b-a<b by omega,hr]
    · have hz : 2*b-a-(a+b)=b-2*a := by omega
      simp only [early,show ¬2*b-a<b by omega,hr,↓reduceIte,move,lower,hz,
        htwodiv,Nat.sub_eq_zero_of_le (Nat.sub_le n 2)]
      norm_num
  have hlegal : a+b≤H := by dsimp [H]; omega
  have hown : (a+b)+(n*(a+b)-a)=n*(a+b)+b := by
    have hx := Nat.mul_le_mul_right (a+b) (show 1≤n by omega)
    simp only [one_mul] at hx
    omega
  have hopp : n*(a+b)<(n+1)*b := by nlinarith only [hna]
  rw [Conj13.outcome_of_three a b (a+b) H c₁ c₂ ha hb (by omega)
    (by omega) (by omega) hlegal,hchildb,hchildc]
  have haown : (move a (Conj13.outcome a b (a+b) c₂ c₁ (H-a))).1 <
      (move b ((n+1)*b,n*(a+b))).1 := by
    simp only [move]
    rw [hchilda]
    omega
  unfold choose
  rw [if_pos haown]
  simp only [move,hown]
  cases c₁ <;> simp [Nat.max_eq_left hopp.le,Nat.min_eq_right hopp.le,Nat.add_comm]

theorem endpoint_outcomes (a b n : ℕ) (ha : 0<a) (hab : a<b) (hn : 0<n)
    (hna : n*a<b) (hupper : b<(n+1)*a) (hcore : Core a b) :
    let H := n*(a+2*b)+2*b
    Conj13.outcome a b (a+b) true true H=(n*(a+b)+b,(n+1)*b) ∧
      Conj13.outcome a b (a+b) false false H=(n*(a+b)+b,n*(a+b)) := by
  constructor
  · simpa using endpoint_profile a b n ha hab hn hna hupper hcore true true
  · simpa using endpoint_profile a b n ha hab hn hna hupper hcore false false

theorem first_discrepancy (a b n : ℕ) (ha : 0<a) (hab : a<b) (hn : 0<n)
    (hna : n*a<b) (hupper : b<(n+1)*a) (hcore : Core a b) :
    IsLeast {h : ℕ | Conj13.outcome a b (a+b) true true h ≠
      Conj13.outcome a b (a+b) false false h} (n*(a+2*b)+2*b) := by
  have he := endpoint_outcomes a b n ha hab hn hna hupper hcore
  dsimp only at he
  constructor
  · intro hsame
    rw [he.1,he.2] at hsame
    have hs := congrArg Prod.snd hsame
    simp only at hs
    nlinarith only [hna,hs]
  · intro h hdis
    by_contra hnot
    have hh : h<n*(a+2*b)+2*b := by omega
    exact hdis (all_conventions_before a b n h ha hab hna hcore hh false false).symm

end Conj14Assembly


namespace Conj14Complete

/-- The early-profile hypothesis is proved from the actual three-action recurrence. -/
theorem core_proved (a b : ℕ) (ha : 0<a) (hab : a<b) : Conj14Assembly.Core a b := by
  intro t r c₁ c₂ hr hta hextra
  exact Conj14Early.outcome_eq_early a b t r ha hab hr hta hextra c₁ c₂

theorem all_conventions_before (a b n h : ℕ) (ha : 0<a) (hab : a<b)
    (hna : n*a<b) (hh : h<n*(a+2*b)+2*b) (c₁ c₂ : Bool) :
    Conj13.outcome a b (a+b) c₁ c₂ h=Conj13.outcome a b (a+b) true true h :=
  Conj14Assembly.all_conventions_before a b n h ha hab hna (core_proved a b ha hab) hh c₁ c₂

theorem endpoint_profile (a b n : ℕ) (ha : 0<a) (hab : a<b) (hn : 0<n)
    (hna : n*a<b) (hupper : b<(n+1)*a) (c₁ c₂ : Bool) :
    Conj13.outcome a b (a+b) c₁ c₂ (n*(a+2*b)+2*b)=
      (n*(a+b)+b,if c₁ then (n+1)*b else n*(a+b)) :=
  Conj14Assembly.endpoint_profile a b n ha hab hn hna hupper (core_proved a b ha hab) c₁ c₂

theorem first_discrepancy (a b n : ℕ) (ha : 0<a) (hab : a<b) (hn : 0<n)
    (hna : n*a<b) (hupper : b<(n+1)*a) :
    IsLeast {h : ℕ | Conj13.outcome a b (a+b) true true h≠
      Conj13.outcome a b (a+b) false false h} (n*(a+2*b)+2*b) :=
  Conj14Assembly.first_discrepancy a b n ha hab hn hna hupper (core_proved a b ha hab)

theorem discrepancy_iff_not_dvd (a b : ℕ) (ha : 0<a) (hab : a<b) :
    (∃ h : ℕ,Conj13.outcome a b (a+b) true true h≠
      Conj13.outcome a b (a+b) false false h) ↔ ¬a∣b := by
  constructor
  · rintro ⟨h,hdis⟩ hdiv
    exact hdis (Conj14Integer.no_discrepancy_of_dvd a b ha hab hdiv h)
  · intro hdiv
    obtain ⟨n,hn,hna,hupper⟩ := Conj14Early.nondiv_parameters a b ha hab hdiv
    exact ⟨n*(a+2*b)+2*b,(first_discrepancy a b n ha hab hn hna hupper).1⟩

theorem discrepancy_iff_not_dvd_generic (a b : ℕ) (ha : 0<a) (hab : a<b) :
    (∃ h : ℕ,OMA.S_arxiv_2510_24280.outcome {a,b,a+b} true true h≠
      OMA.S_arxiv_2510_24280.outcome {a,b,a+b} false false h) ↔ ¬a∣b := by
  simpa only [Conj13GenericModelBridge.outcome_three_eq a b (a+b) ha hab (by omega)] using
    discrepancy_iff_not_dvd a b ha hab

theorem first_discrepancy_generic (a b n : ℕ) (ha : 0<a) (hab : a<b) (hn : 0<n)
    (hna : n*a<b) (hupper : b<(n+1)*a) :
    IsLeast {h : ℕ | OMA.S_arxiv_2510_24280.outcome {a,b,a+b} true true h≠
      OMA.S_arxiv_2510_24280.outcome {a,b,a+b} false false h}
      ((n+2)*b+n*(a+b)) := by
  have heq : (n+2)*b+n*(a+b)=n*(a+2*b)+2*b := by ring
  rw [heq]
  simpa only [Conj13GenericModelBridge.outcome_three_eq a b (a+b) ha hab (by omega)] using
    first_discrepancy a b n ha hab hn hna hupper

theorem endpoint_profile_generic (a b n : ℕ) (ha : 0<a) (hab : a<b) (hn : 0<n)
    (hna : n*a<b) (hupper : b<(n+1)*a) (c₁ c₂ : Bool) :
    OMA.S_arxiv_2510_24280.outcome {a,b,a+b} c₁ c₂ ((n+2)*b+n*(a+b))=
      (n*(a+b)+b,if c₁ then (n+1)*b else n*(a+b)) := by
  have heq : (n+2)*b+n*(a+b)=n*(a+2*b)+2*b := by ring
  rw [heq,Conj13GenericModelBridge.outcome_three_eq a b (a+b) ha hab (by omega)]
  exact endpoint_profile a b n ha hab hn hna hupper c₁ c₂

/-- Complete original Conjecture 14: the iff and the least distinguishing heap,
including existence of the positive interval index n. -/
theorem conjecture_14_generic (a b : ℕ) (ha : 0<a) (hab : a<b) :
    ((∃ h : ℕ,OMA.S_arxiv_2510_24280.outcome {a,b,a+b} true true h≠
      OMA.S_arxiv_2510_24280.outcome {a,b,a+b} false false h) ↔ ¬a∣b) ∧
    (¬a∣b → ∃ n : ℕ,0<n ∧ n*a<b ∧ b<(n+1)*a ∧
      IsLeast {h : ℕ | OMA.S_arxiv_2510_24280.outcome {a,b,a+b} true true h≠
        OMA.S_arxiv_2510_24280.outcome {a,b,a+b} false false h}
        ((n+2)*b+n*(a+b))) := by
  refine ⟨discrepancy_iff_not_dvd_generic a b ha hab,?_⟩
  intro hdiv
  obtain ⟨n,hn,hna,hupper⟩ := Conj14Early.nondiv_parameters a b ha hab hdiv
  exact ⟨n,hn,hna,hupper,first_discrepancy_generic a b n ha hab hn hna hupper⟩

end Conj14Complete
