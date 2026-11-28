import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Prod.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

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


namespace Conj13Boundary
open Conj11

lemma choose_eq_left_or_right (friendly : Bool) (u v : ℕ × ℕ) :
    choose friendly u v = u ∨ choose friendly u v = v := by
  unfold choose
  split_ifs with h₁ h₂ hf
  · exact Or.inr rfl
  · exact Or.inl rfl
  · have he : u.1 = v.1 := by omega
    by_cases hsec : u.2 ≤ v.2
    · right
      apply Prod.ext
      · exact he
      · exact Nat.max_eq_right hsec
    · left
      apply Prod.ext
      · rfl
      · exact Nat.max_eq_left (by omega)
  · have he : u.1 = v.1 := by omega
    by_cases hsec : u.2 ≤ v.2
    · left
      apply Prod.ext
      · rfl
      · exact Nat.min_eq_left hsec
    · right
      apply Prod.ext
      · exact he
      · exact Nat.min_eq_right (by omega)

lemma choose_first_ge_right (friendly : Bool) (u v : ℕ × ℕ) :
    v.1 ≤ (choose friendly u v).1 := by
  unfold choose
  split_ifs <;> simp_all

theorem outcome_budget (a b h : ℕ) (c₁ c₂ : Bool) (ha : 0 < a) (hab : a < b) :
    (outcome a b c₁ c₂ h).1 + (outcome a b c₁ c₂ h).2 ≤ h := by
  induction h using Nat.strong_induction_on generalizing c₁ c₂ with
  | h h ih =>
    by_cases hlt : h < a
    · rw [outcome_of_lt a b h c₁ c₂ hlt]
      simp
    · have hah : a ≤ h := by omega
      have hca := ih (h - a) (by omega) c₂ c₁
      by_cases hhb : h < b
      · rw [outcome_of_one a b h c₁ c₂ ha hah hhb]
        dsimp [move]
        omega
      · have hbh : b ≤ h := by omega
        have hcb := ih (h - b) (by omega) c₂ c₁
        rw [outcome_of_two a b h c₁ c₂ ha (by omega) hah hbh]
        rcases choose_eq_left_or_right c₁ (move a (outcome a b c₂ c₁ (h - a)))
          (move b (outcome a b c₂ c₁ (h - b))) with he | he
        · rw [he]
          dsimp [move]
          omega
        · rw [he]
          dsimp [move]
          omega

theorem outcome_first_ge_b (a b h : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hab : a < b) (hb : b ≤ h) :
    b ≤ (outcome a b c₁ c₂ h).1 := by
  rw [outcome_of_two a b h c₁ c₂ ha (by omega) (by omega) hb]
  have h := choose_first_ge_right c₁ (move a (outcome a b c₂ c₁ (h - a)))
    (move b (outcome a b c₂ c₁ (h - b)))
  dsimp [move] at h ⊢
  omega

theorem outcome_singleton_decomp (a b q t : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (ht : t < a) (hh : a * q + t < b) :
    outcome a b c₁ c₂ (a * q + t) = (a * ((q + 1) / 2), a * (q / 2)) := by
  induction q generalizing t c₁ c₂ with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [outcome_of_lt a b t c₁ c₂ ht]
    norm_num
  | succ q ih =>
    have he : a * (q + 1) + t - a = a * q + t := by
      rw [Nat.mul_succ]
      omega
    have hh' : a * q + t < b := by
      rw [Nat.mul_succ] at hh
      omega
    have hah : a ≤ a * (q + 1) + t := by
      rw [Nat.mul_succ]
      omega
    rw [outcome_of_one a b _ c₁ c₂ ha hah hh, he, ih t c₂ c₁ ht hh']
    have hdiv : (q + 1 + 1) / 2 = q / 2 + 1 := by omega
    rw [hdiv]
    apply Prod.ext
    · dsimp [move]
      ring
    · rfl

theorem outcome_below_b (a b h : ℕ) (c₁ c₂ : Bool) (ha : 0 < a) (hh : h < b) :
    outcome a b c₁ c₂ h = (a * ((h / a + 1) / 2), a * ((h / a) / 2)) := by
  have he : a * (h / a) + h % a = h := by
    have h := Nat.mod_add_div h a
    omega
  have hdecomp := outcome_singleton_decomp a b (h / a) (h % a) c₁ c₂ ha
    (Nat.mod_lt h ha) (by omega)
  simpa only [he] using hdecomp

end Conj13Boundary

namespace Conj13Boundary
open Conj11

lemma staircase_comparison (a r v : ℕ) (ha : 0 < a) (hrv : r ≤ v) :
    r + a * ((v / a) / 2) ≤ v + a * ((r / a + 1) / 2) ∧
      (r + a * ((v / a) / 2) = v + a * ((r / a + 1) / 2) →
        v = r ∧ a * ((r / a + 1) / 2) = a * ((r / a) / 2)) := by
  have hquot : r / a ≤ v / a := Nat.div_le_div_right hrv
  by_cases heq : v / a = r / a
  · have hprod : a * ((r / a) / 2) ≤ a * ((r / a + 1) / 2) :=
      Nat.mul_le_mul_left a (by omega)
    constructor
    · simpa only [heq] using Nat.add_le_add hrv hprod
    · intro he
      have he' : r + a * ((r / a) / 2) = v + a * ((r / a + 1) / 2) := by
        simpa only [heq] using he
      exact ⟨by omega, by omega⟩
  · have hquotlt : r / a < v / a := by omega
    have hcoef : a * ((r / a) / 2 + 1) ≤ a * ((v / a + 1) / 2) :=
      Nat.mul_le_mul_left a (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hcoef
    have hrdiv : (r / a) / 2 + (r / a + 1) / 2 = r / a := by omega
    have hvdiv : (v / a) / 2 + (v / a + 1) / 2 = v / a := by omega
    have hrsplit := congrArg (fun q : ℕ => a * q) hrdiv
    have hvsplit := congrArg (fun q : ℕ => a * q) hvdiv
    rw [Nat.mul_add] at hrsplit hvsplit
    have hrmod := Nat.mod_add_div r a
    have hvmod := Nat.mod_add_div v a
    have hrlt := Nat.mod_lt r ha
    have hstrict : r + a * ((v / a) / 2) < v + a * ((r / a + 1) / 2) := by omega
    exact ⟨hstrict.le, fun he => False.elim (by omega)⟩

lemma boundary_of_selected_move (a b r u s : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hab : a < b) (hr : r < b) (hu : b + r ≤ u) (hs : s ≤ b)
    (hmove : outcome a b c₁ c₂ u = move s (outcome a b c₂ c₁ (u - s))) :
    r + (outcome a b c₁ c₂ u).1 ≤ u + (outcome a b c₁ c₂ r).1 ∧
      (r + (outcome a b c₁ c₂ u).1 = u + (outcome a b c₁ c₂ r).1 →
        (outcome a b c₁ c₂ u).2 = (outcome a b c₁ c₂ r).2) := by
  let v := u - s
  have hvge : r ≤ v := by dsimp [v]; omega
  have huadd : u = s + v := by dsimp [v]; omega
  have hbudget := outcome_budget a b v c₂ c₁ ha hab
  by_cases hvb : b ≤ v
  · have hfirst := outcome_first_ge_b a b v c₂ c₁ ha hab hvb
    have hstrict : r + (outcome a b c₁ c₂ u).1 < u + (outcome a b c₁ c₂ r).1 := by
      rw [hmove]
      change r + (s + (outcome a b c₂ c₁ v).2) < u + (outcome a b c₁ c₂ r).1
      omega
    exact ⟨hstrict.le, fun he => False.elim (by omega)⟩
  · have hvrange : v < b := by omega
    have hrform := outcome_below_b a b r c₁ c₂ ha hr
    have hvform := outcome_below_b a b v c₂ c₁ ha hvrange
    have hstair := staircase_comparison a r v ha hvge
    have hcomp : r + (outcome a b c₂ c₁ v).2 ≤ v + (outcome a b c₁ c₂ r).1 := by
      rw [hrform, hvform]
      exact hstair.1
    constructor
    · rw [hmove]
      change r + (s + (outcome a b c₂ c₁ v).2) ≤ u + (outcome a b c₁ c₂ r).1
      omega
    · intro he
      have hecomp : r + a * ((v / a) / 2) = v + a * ((r / a + 1) / 2) := by
        rw [hmove] at he
        change r + (s + (outcome a b c₂ c₁ v).2) = u + (outcome a b c₁ c₂ r).1 at he
        rw [hrform, hvform] at he
        dsimp only at he
        omega
      obtain ⟨hvr, hsame⟩ := hstair.2 hecomp
      rw [hmove]
      change (outcome a b c₂ c₁ v).1 = (outcome a b c₁ c₂ r).2
      rw [hrform, hvform, hvr]
      exact hsame

theorem boundary_own_and_other (a b r u : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hab : a < b) (hr : r < b) (hu : b + r ≤ u) :
    r + (outcome a b c₁ c₂ u).1 ≤ u + (outcome a b c₁ c₂ r).1 ∧
      (r + (outcome a b c₁ c₂ u).1 = u + (outcome a b c₁ c₂ r).1 →
        (outcome a b c₁ c₂ u).2 = (outcome a b c₁ c₂ r).2) := by
  have htwo := outcome_of_two a b u c₁ c₂ ha (by omega) (by omega) (by omega)
  rcases choose_eq_left_or_right c₁ (move a (outcome a b c₂ c₁ (u - a)))
    (move b (outcome a b c₂ c₁ (u - b))) with he | he
  · exact boundary_of_selected_move a b r u a c₁ c₂ ha hab hr hu hab.le (htwo.trans he)
  · exact boundary_of_selected_move a b r u b c₁ c₂ ha hab hr hu le_rfl (htwo.trans he)

theorem boundary_own (a b r u : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hab : a < b) (hr : r < b) (hu : b + r ≤ u) :
    r + (outcome a b c₁ c₂ u).1 ≤ u + (outcome a b c₁ c₂ r).1 :=
  (boundary_own_and_other a b r u c₁ c₂ ha hab hr hu).1

theorem boundary_other_of_eq (a b r u : ℕ) (c₁ c₂ : Bool)
    (ha : 0 < a) (hab : a < b) (hr : r < b) (hu : b + r ≤ u)
    (he : r + (outcome a b c₁ c₂ u).1 = u + (outcome a b c₁ c₂ r).1) :
    (outcome a b c₁ c₂ u).2 = (outcome a b c₁ c₂ r).2 :=
  (boundary_own_and_other a b r u c₁ c₂ ha hab hr hu).2 he

end Conj13Boundary


namespace Conj13Extension

open Conj11

def addPair (n : ℕ) (u : ℕ × ℕ) : ℕ × ℕ := (n+u.1,n+u.2)

theorem choose_mem (friendly : Bool) (u v : ℕ × ℕ) :
    choose friendly u v = u ∨ choose friendly u v = v := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> simp only [choose, Bool.false_eq_true, ↓reduceIte]
  all_goals (split_ifs <;> simp_all [min_def,max_def]); omega

theorem choose_eq_right_of_compare (friendly : Bool) (u v : ℕ × ℕ)
    (hown : u.1≤v.1)
    (hother : u.1=v.1 → if friendly then u.2≤v.2 else v.2≤u.2) :
    choose friendly u v = v := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> simp only [choose, Bool.false_eq_true, ↓reduceIte] at *
  all_goals split_ifs <;> simp_all [min_def,max_def] <;> omega

theorem choose_absorb (friendly : Bool) (u v z : ℕ × ℕ)
    (hu : choose friendly u z=z) (hv : choose friendly v z=z) :
    choose friendly (choose friendly u v) z=z := by
  rcases choose_mem friendly u v with h|h
  · rw [h]; exact hu
  · rw [h]; exact hv

theorem choose_addPair (friendly : Bool) (n : ℕ) (u v : ℕ × ℕ) :
    choose friendly (addPair n u) (addPair n v)=addPair n (choose friendly u v) := by
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  cases friendly <;> by_cases h₁ : u₁<v₁ <;> by_cases h₂ : v₁<u₁ <;>
    by_cases h₃ : u₂≤v₂ <;> simp [choose,addPair,h₁,h₂,h₃,min_def,max_def]

theorem choose_self (friendly : Bool) (u : ℕ × ℕ) : choose friendly u u=u := by
  simp [choose]

def extension (a b c q r : ℕ) (c₁ c₂ : Bool) : ℕ × ℕ :=
  if r<c then addPair (q*c) (Conj11.outcome a b c₁ c₂ r)
  else ((q+1)*c+(Conj11.outcome a b c₂ c₁ (r-c)).2,
    q*c+(Conj11.outcome a b c₂ c₁ (r-c)).1)

theorem mul_predecessor (q c : ℕ) (hq : 0<q) :
    q*c=(q-1)*c+c := by
  conv_lhs => rw [show q=q-1+1 by omega]
  rw [Nat.add_mul,one_mul]

theorem outcome_below_c (a b c h : ℕ) (ha : 0<a) (hab : a<b)
    (hbc : b<c) (hhc : h<c) (c₁ c₂ : Bool) :
    Conj13.outcome a b c c₁ c₂ h=Conj11.outcome a b c₁ c₂ h := by
  induction h using Nat.strong_induction_on generalizing c₁ c₂ with
  | h h ih =>
    by_cases hha : h<a
    · rw [Conj13.outcome_of_lt _ _ _ _ _ _ hha,
        Conj11.outcome_of_lt _ _ _ _ _ hha]
    have hah : a≤h := by omega
    by_cases hhb : h<b
    · rw [Conj13.outcome_of_one _ _ _ _ _ _ ha hah hhb,
        Conj11.outcome_of_one _ _ _ _ _ ha hah hhb,
        ih (h-a) (by omega) (by omega)]
    have hbh : b≤h := by omega
    rw [Conj13.outcome_of_two _ _ _ _ _ _ ha (by omega) hah hbh hhc,
      Conj11.outcome_of_two _ _ _ _ _ ha (by omega) hah hbh,
      ih (h-a) (by omega) (by omega),ih (h-b) (by omega) (by omega)]


theorem outcome_formula_of_boundary (a b c : ℕ) (ha : 0<a) (hab : a<b)
    (hdom : 2*b≤c)
    (hbudget : ∀ h c₁ c₂, (Conj11.outcome a b c₁ c₂ h).1+
      (Conj11.outcome a b c₁ c₂ h).2≤h)
    (hfirst : ∀ h c₁ c₂, b≤h → b≤(Conj11.outcome a b c₁ c₂ h).1)
    (hboundary : ∀ r u c₁ c₂, r<b → b+r≤u →
      r+(Conj11.outcome a b c₁ c₂ u).1≤u+(Conj11.outcome a b c₁ c₂ r).1 ∧
      (r+(Conj11.outcome a b c₁ c₂ u).1=u+(Conj11.outcome a b c₁ c₂ r).1 →
        (Conj11.outcome a b c₁ c₂ u).2=(Conj11.outcome a b c₁ c₂ r).2)) :
    ∀ h q r, r<2*c → h=q*(2*c)+r → ∀ c₁ c₂,
      Conj13.outcome a b c c₁ c₂ h=extension a b c q r c₁ c₂ := by
  have hb : 0<b := by omega
  have hc : 0<c := by omega
  have hbc : b<c := by omega
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro q r hr hh c₁ c₂
    by_cases hrc : r<c
    · by_cases hq : q=0
      · subst q
        have her : h=r := by simpa using hh
        rw [her,outcome_below_c a b c r ha hab hbc hrc c₁ c₂]
        simp [extension,hrc,addPair]
      have hqp : 0<q := by omega
      have hqadd : q-1+1=q := by omega
      have hqc := mul_predecessor q c hqp
      have hq2c := mul_predecessor q (2*c) hqp
      have hch : c≤h := by omega
      let Z : ℕ×ℕ := addPair (q*c) (Conj11.outcome a b c₁ c₂ r)
      have hcm : move c (Conj13.outcome a b c c₂ c₁ (h-c))=Z := by
        rw [ih (h-c) (by omega) (q-1) (c+r) (by omega) (by omega) c₂ c₁]
        simp only [extension,if_neg (show ¬c+r<c by omega),Nat.add_sub_cancel_left,hqadd,
          move,Z,addPair]
        apply Prod.ext
        all_goals dsimp only
        all_goals omega
      have hbad (s : ℕ) (hs : s≤b) (hrs : r<s) :
          choose c₁ (move s (Conj13.outcome a b c c₂ c₁ (h-s))) Z=Z := by
        let u : ℕ := c+r-s
        have hu : u<c := by dsimp [u]; omega
        have hbu : b+r≤u := by dsimp [u]; omega
        have hru : r<b := by omega
        have hbnd := hboundary r u c₁ c₂ hru hbu
        have hsum : s+u=c+r := by dsimp [u]; omega
        rw [ih (h-s) (by omega) (q-1) (c+u) (by omega) (by dsimp [u]; omega) c₂ c₁]
        simp only [extension,if_neg (show ¬c+u<c by omega),Nat.add_sub_cancel_left,hqadd]
        apply choose_eq_right_of_compare
        · dsimp only [move,Z,addPair]
          omega
        · intro he
          have heq : r+(Conj11.outcome a b c₁ c₂ u).1=
              u+(Conj11.outcome a b c₁ c₂ r).1 := by
            dsimp only [move,Z,addPair] at he
            omega
          have he₂ := hbnd.2 heq
          dsimp only [move,Z,addPair]
          rw [he₂]
          cases c₁ <;> simp
      rw [show extension a b c q r c₁ c₂=Z by simp [extension,hrc,Z]]
      rw [Conj13.outcome_of_three a b c h c₁ c₂ ha hb hc (by omega) (by omega) hch,hcm]
      change choose c₁
        (choose c₁ (move a (Conj13.outcome a b c c₂ c₁ (h-a)))
          (move b (Conj13.outcome a b c c₂ c₁ (h-b)))) Z=Z
      by_cases hbr : b≤r
      · have har : a≤r := by omega
        rw [ih (h-a) (by omega) q (r-a) (by omega) (by omega) c₂ c₁,
          ih (h-b) (by omega) q (r-b) (by omega) (by omega) c₂ c₁]
        have hma : move a (extension a b c q (r-a) c₂ c₁)=
            addPair (q*c) (move a (Conj11.outcome a b c₂ c₁ (r-a))) := by
          simp only [extension,if_pos (show r-a<c by omega),move,addPair]
          apply Prod.ext
          all_goals dsimp only
          all_goals omega
        have hmb : move b (extension a b c q (r-b) c₂ c₁)=
            addPair (q*c) (move b (Conj11.outcome a b c₂ c₁ (r-b))) := by
          simp only [extension,if_pos (show r-b<c by omega),move,addPair]
          apply Prod.ext
          all_goals dsimp only
          all_goals omega
        rw [hma,hmb,choose_addPair,
          ←Conj11.outcome_of_two a b r c₁ c₂ ha hb har hbr]
        exact choose_self c₁ Z
      · have hrb : r<b := by omega
        have hB := hbad b (by omega) hrb
        by_cases har : a≤r
        · have hma : move a (Conj13.outcome a b c c₂ c₁ (h-a))=Z := by
            rw [ih (h-a) (by omega) q (r-a) (by omega) (by omega) c₂ c₁]
            dsimp only [Z]
            rw [Conj11.outcome_of_one a b r c₁ c₂ ha har hrb]
            simp only [extension,if_pos (show r-a<c by omega),move,addPair]
            apply Prod.ext
            all_goals dsimp only
            all_goals omega
          apply choose_absorb
          · rw [hma]; exact choose_self c₁ Z
          · exact hB
        · exact choose_absorb c₁ _ _ Z (hbad a (by omega) (by omega)) hB
    · have hcr : c≤r := by omega
      let z : ℕ := r-c
      have hz : z<c := by dsimp [z]; omega
      have hrz : r=c+z := by dsimp [z]; omega
      let Z : ℕ×ℕ := ((q+1)*c+(Conj11.outcome a b c₂ c₁ z).2,
        q*c+(Conj11.outcome a b c₂ c₁ z).1)
      have hcm : move c (Conj13.outcome a b c c₂ c₁ (h-c))=Z := by
        rw [ih (h-c) (by omega) q z (by omega) (by dsimp [z]; omega) c₂ c₁]
        simp only [extension,if_pos hz,move,addPair,Z,Nat.add_mul,one_mul]
        apply Prod.ext
        all_goals dsimp only
        all_goals omega
      have hbad (s : ℕ) (hs₀ : 0<s) (hs : s≤b) :
          choose c₁ (move s (Conj13.outcome a b c c₂ c₁ (h-s))) Z=Z := by
        have hown : (move s (Conj13.outcome a b c c₂ c₁ (h-s))).1<Z.1 := by
          by_cases hsz : s≤z
          · rw [ih (h-s) (by omega) q (c+(z-s)) (by omega) (by omega) c₂ c₁]
            have he : (c+(z-s))-c=z-s := by omega
            simp only [extension,if_neg (show ¬c+(z-s)<c by omega),he,move,Z]
            have hbud := hbudget (z-s) c₁ c₂
            have heqc : (q+1)*c=q*c+c := by rw [Nat.add_mul,one_mul]
            omega
          · let u : ℕ := c+z-s
            have hu : u<c := by dsimp [u]; omega
            have hbu : b≤u := by dsimp [u]; omega
            rw [ih (h-s) (by omega) q u (by omega) (by dsimp [u]; omega) c₂ c₁]
            simp only [extension,if_pos hu,move,addPair,Z]
            have hbud := hbudget u c₂ c₁
            have hfst := hfirst u c₂ c₁ hbu
            have hsum : s+u=c+z := by dsimp [u]; omega
            have heqc : (q+1)*c=q*c+c := by rw [Nat.add_mul,one_mul]
            omega
        apply choose_eq_right_of_compare c₁ _ Z hown.le
        intro he
        exact False.elim (Nat.ne_of_lt hown he)
      rw [show extension a b c q r c₁ c₂=Z by simp [extension,hrc,Z,z]]
      rw [Conj13.outcome_of_three a b c h c₁ c₂ ha hb hc (by omega) (by omega) (by omega),hcm]
      change choose c₁
        (choose c₁ (move a (Conj13.outcome a b c c₂ c₁ (h-a)))
          (move b (Conj13.outcome a b c c₂ c₁ (h-b)))) Z=Z
      exact choose_absorb c₁ _ _ Z (hbad a ha (by omega)) (hbad b hb (by omega))

end Conj13Extension


namespace Conj13Complete

open Conj13Extension

/-- Exact all-profile dominant-extension formula, with no auxiliary premise. -/
theorem exact_outcome_formula (a b c h q r : ℕ)
    (ha : 0<a) (hab : a<b) (hdom : 2*b≤c)
    (hr : r<2*c) (hh : h=q*(2*c)+r) (c₁ c₂ : Bool) :
    Conj13.outcome a b c c₁ c₂ h=extension a b c q r c₁ c₂ := by
  apply outcome_formula_of_boundary a b c ha hab hdom
    (fun h c₁ c₂ => Conj13Boundary.outcome_budget a b h c₁ c₂ ha hab)
    (fun h c₁ c₂ hb => Conj13Boundary.outcome_first_ge_b a b h c₁ c₂ ha hab hb)
    (fun r u c₁ c₂ hr hu => Conj13Boundary.boundary_own_and_other a b r u c₁ c₂ ha hab hr hu)
    h q r hr hh c₁ c₂

/-- Conjecture 13 of arXiv:2510.24280v2, with the original three-action order. -/
theorem conjecture_13 (a b c : ℕ) (ha : 0<a) (hab : a<b) (_hbc : b<c)
    (hdom : 2*b≤c)
    (hsmall : ∀ h,Conj11.outcome a b true true h=Conj11.outcome a b false false h) :
    ∀ h,Conj13.outcome a b c true true h=Conj13.outcome a b c false false h := by
  intro h
  have hc : 0<c := by omega
  let q : ℕ := h/(2*c)
  let r : ℕ := h%(2*c)
  have hr : r<2*c := Nat.mod_lt h (by omega)
  have hh : h=q*(2*c)+r := by
    dsimp [q,r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod h (2*c)).symm
  rw [exact_outcome_formula a b c h q r ha hab hdom hr hh true true,
    exact_outcome_formula a b c h q r ha hab hdom hr hh false false]
  unfold extension
  split_ifs
  · rw [hsmall r]
  · rw [hsmall (r-c)]

/-- All profiles have a two-largest-moves affine period from the initial heap. -/
theorem periodic_affine_outcome (a b c h : ℕ) (ha : 0<a) (hab : a<b)
    (hdom : 2*b≤c) (c₁ c₂ : Bool) :
    Conj13.outcome a b c c₁ c₂ (h+2*c)=
      addPair c (Conj13.outcome a b c c₁ c₂ h) := by
  have hc : 0<c := by omega
  let q : ℕ := h/(2*c)
  let r : ℕ := h%(2*c)
  have hr : r<2*c := Nat.mod_lt h (by omega)
  have hh : h=q*(2*c)+r := by
    dsimp [q,r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod h (2*c)).symm
  have hh' : h+2*c=(q+1)*(2*c)+r := by
    rw [Nat.add_mul,one_mul]
    omega
  rw [exact_outcome_formula a b c (h+2*c) (q+1) r ha hab hdom hr hh' c₁ c₂,
    exact_outcome_formula a b c h q r ha hab hdom hr hh c₁ c₂]
  unfold extension
  split_ifs <;> simp only [addPair,Nat.add_mul,one_mul]
  all_goals
    apply Prod.ext
    all_goals dsimp only
    all_goals omega

end Conj13Complete


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






namespace Conj13Complete

/-- The dominant extension formula in the approved finite-set model. -/
theorem exact_outcome_formula_generic (a b c h q r : ℕ)
    (ha : 0<a) (hab : a<b) (hbc : b<c) (hdom : 2*b≤c)
    (hr : r<2*c) (hh : h=q*(2*c)+r) (c₁ c₂ : Bool) :
    OMA.S_arxiv_2510_24280.outcome {a,b,c} c₁ c₂ h=
      if r<c then Conj13Extension.addPair (q*c)
        (OMA.S_arxiv_2510_24280.outcome {a,b} c₁ c₂ r)
      else ((q+1)*c+(OMA.S_arxiv_2510_24280.outcome {a,b} c₂ c₁ (r-c)).2,
        q*c+(OMA.S_arxiv_2510_24280.outcome {a,b} c₂ c₁ (r-c)).1) := by
  rw [Conj13GenericModelBridge.outcome_three_eq a b c ha hab hbc]
  simpa only [Conj13Extension.extension,
    Conj13GenericModelBridge.outcome_two_eq a b ha hab] using
    exact_outcome_formula a b c h q r ha hab hdom hr hh c₁ c₂

/-- Original Conjecture 13 in the exact approved finite-set recurrence. -/
theorem conjecture_13_generic (a b c : ℕ) (ha : 0<a) (hab : a<b) (hbc : b<c)
    (hdom : 2*b≤c)
    (hsmall : ∀ h,OMA.S_arxiv_2510_24280.outcome {a,b} true true h=
      OMA.S_arxiv_2510_24280.outcome {a,b} false false h) :
    ∀ h,OMA.S_arxiv_2510_24280.outcome {a,b,c} true true h=
      OMA.S_arxiv_2510_24280.outcome {a,b,c} false false h := by
  have hsmall' : ∀ h,Conj11.outcome a b true true h=Conj11.outcome a b false false h := by
    intro h
    simpa only [Conj13GenericModelBridge.outcome_two_eq a b ha hab] using hsmall h
  intro h
  rw [Conj13GenericModelBridge.outcome_three_eq a b c ha hab hbc,
    Conj13GenericModelBridge.outcome_three_eq a b c ha hab hbc]
  exact conjecture_13 a b c ha hab hbc hdom hsmall' h

/-- The affine period in the approved finite-set game model. -/
theorem periodic_affine_outcome_generic (a b c h : ℕ) (ha : 0<a) (hab : a<b)
    (hbc : b<c) (hdom : 2*b≤c) (c₁ c₂ : Bool) :
    OMA.S_arxiv_2510_24280.outcome {a,b,c} c₁ c₂ (h+2*c)=
      Conj13Extension.addPair c (OMA.S_arxiv_2510_24280.outcome {a,b,c} c₁ c₂ h) := by
  rw [Conj13GenericModelBridge.outcome_three_eq a b c ha hab hbc,
    Conj13GenericModelBridge.outcome_three_eq a b c ha hab hbc]
  exact periodic_affine_outcome a b c h ha hab hdom c₁ c₂

end Conj13Complete
