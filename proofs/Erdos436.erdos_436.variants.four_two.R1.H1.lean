import OMAReductions.R_Erdos436_erdos_436_variants_four_two_R1
import Mathlib

/-! A verified decision-tree certificate for the finite search in step `H1`. -/

inductive T where
| l (n : ℕ)
| n (q : ℕ) (a b c d : T)
open T

def upd (f : ℕ → ZMod 4) (q : ℕ) (x : ZMod 4) : ℕ → ZMod 4 :=
  fun p => if p = q then x else f p
def csum (f : ℕ → ZMod 4) (n : ℕ) : ZMod 4 := (n.primeFactorsList.map f).sum
def keysin (ks : List ℕ) (n : ℕ) : Bool :=
  n.primeFactorsList.all fun q => decide (q ∈ ks)
def leafok (ks : List ℕ) (f : ℕ → ZMod 4) (n : ℕ) : Bool :=
  decide (1 ≤ n ∧ n ≤ 1224) &&
    (keysin ks n && (keysin ks (n+1) &&
      (decide (csum f n = 0) && decide (csum f (n+1) = 0))))
def valid (ks : List ℕ) (f : ℕ → ZMod 4) : T → Bool
  | l m => leafok ks f m
  | n q a b c d =>
      valid (q::ks) (upd f q 0) a &&
        (valid (q::ks) (upd f q 1) b &&
          (valid (q::ks) (upd f q 2) c && valid (q::ks) (upd f q 3) d))
def ev (w : ℕ → ZMod 4) : T → ℕ
  | l m => m
  | n q a b c d =>
      if w q = 0 then ev w a else if w q = 1 then ev w b else
      if w q = 2 then ev w c else ev w d

def agr (w : ℕ → ZMod 4) (ks : List ℕ) (f : ℕ → ZMod 4) : Prop :=
  ∀ q ∈ ks, f q = w q
def good (w : ℕ → ZMod 4) (n : ℕ) : Prop :=
  n ∈ Finset.Icc 1 1224 ∧ (n.primeFactorsList.map w).sum = 0 ∧
    ((n+1).primeFactorsList.map w).sum = 0

lemma z4 : ∀ x : ZMod 4, x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by decide

lemma agrc (w : ℕ → ZMod 4) (ks : List ℕ) (f : ℕ → ZMod 4) (q : ℕ) (x : ZMod 4)
    (h : agr w ks f) (hq : w q = x) : agr w (q::ks) (upd f q x) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [upd,hq]
  · by_cases e : p=q
    · subst p; simp [upd,hq]
    · simp [upd,e,h p hp]

lemma mapeq (w : ℕ → ZMod 4) (ks : List ℕ) (f : ℕ → ZMod 4) (n : ℕ)
    (hk : keysin ks n = true) (h : agr w ks f) :
    n.primeFactorsList.map f = n.primeFactorsList.map w := by
  apply List.map_congr_left
  intro q hq
  exact h q (of_decide_eq_true ((List.all_eq_true.mp hk) q hq))

lemma leafsound (w : ℕ → ZMod 4) (ks : List ℕ) (f : ℕ → ZMod 4) (n : ℕ)
    (hok : leafok ks f n = true) (ha : agr w ks f) : good w n := by
  have h0 := Bool.and_eq_true_iff.mp hok
  have hbnd := of_decide_eq_true h0.1
  have h1 := Bool.and_eq_true_iff.mp h0.2
  have hk1 := h1.1
  have h2 := Bool.and_eq_true_iff.mp h1.2
  have hk2 := h2.1
  have h3 := Bool.and_eq_true_iff.mp h2.2
  have hs1f := of_decide_eq_true h3.1
  have hs2f := of_decide_eq_true h3.2
  have mn1 := mapeq w ks f n hk1 ha
  have mn2 := mapeq w ks f (n+1) hk2 ha
  have hs1 : csum w n = 0 := by
    rw [csum,← mn1]
    exact hs1f
  have hs2 : csum w (n+1) = 0 := by
    rw [csum,← mn2]
    exact hs2f
  exact ⟨Finset.mem_Icc.2 hbnd,hs1,hs2⟩

theorem sound (w : ℕ → ZMod 4) : ∀ t ks f, valid ks f t = true → agr w ks f → good w (ev w t) := by
  intro t
  induction t with
  | l m =>
      intro ks f hv ha
      exact leafsound w ks f m hv ha
  | n q a b c d iha ihb ihc ihd =>
      intro ks f hv ha
      have h0 := Bool.and_eq_true_iff.mp hv
      have h1 := Bool.and_eq_true_iff.mp h0.2
      have h2 := Bool.and_eq_true_iff.mp h1.2
      rcases z4 (w q) with hq | hq | hq | hq
      · have ha' := agrc w ks f q 0 ha hq
        have hg := iha (q::ks) (upd f q 0) h0.1 ha'
        simpa [ev,hq] using hg
      · have ha' := agrc w ks f q 1 ha hq
        have hg := ihb (q::ks) (upd f q 1) h1.1 ha'
        simpa [ev,hq,(show (1:ZMod 4)≠0 by decide)] using hg
      · have ha' := agrc w ks f q 2 ha hq
        have hg := ihc (q::ks) (upd f q 2) h2.1 ha'
        simpa [ev,hq,(show (2:ZMod 4)≠0 by decide),(show (2:ZMod 4)≠1 by decide)] using hg
      · have ha' := agrc w ks f q 3 ha hq
        have hg := ihd (q::ks) (upd f q 3) h2.2 ha'
        simpa [ev,hq,(show (3:ZMod 4)≠0 by decide),(show (3:ZMod 4)≠1 by decide),(show (3:ZMod 4)≠2 by decide)] using hg


def tree : T := n 2 (l 1) (n 3 (n 5 (l 15) (n 7 (l 48) (n 11 (l 99) (n 13 (l 39) (n 17 (l 16) (l 1224) (l 935) (l 119)) (l 168) (l 26)) (l 120) (l 55)) (l 27) (n 11 (l 99) (n 13 (l 13) (l 104) (l 728) (l 26)) (l 120) (n 13 (l 13) (l 104) (l 728) (l 26)))) (n 7 (l 20) (n 11 (n 13 (l 143) (l 363) (l 168) (l 25)) (n 13 (l 168) (l 675) (l 168) (l 25)) (l 55) (n 13 (l 168) (l 143) (l 65) (l 25))) (l 27) (l 224)) (l 9)) (n 5 (l 24) (n 7 (n 11 (n 13 (l 90) (n 17 (l 16) (l 135) (l 255) (l 374)) (l 77) (l 39)) (n 13 (l 90) (n 17 (l 16) (l 135) (l 255) (l 220)) (l 168) (l 39)) (l 99) (l 54)) (n 11 (l 440) (n 13 (n 17 (l 16) (l 135) (l 169) (l 84)) (l 350) (l 195) (l 39)) (l 99) (l 54)) (n 11 (l 175) (l 384) (l 99) (l 54)) (l 35)) (l 24) (l 15)) (n 5 (l 80) (n 7 (n 11 (l 11) (n 13 (l 12) (l 675) (l 39) (l 65)) (n 13 (l 12) (l 675) (l 39) (l 675)) (n 13 (l 12) (l 143) (l 39) (l 675))) (n 11 (l 11) (n 13 (l 12) (l 104) (l 39) (l 65)) (n 13 (l 12) (l 104) (l 39) (l 675)) (l 55)) (n 11 (l 11) (n 13 (l 12) (l 675) (l 39) (l 65)) (n 13 (l 12) (l 77) (l 39) (l 675)) (l 21)) (n 11 (l 11) (n 13 (l 12) (l 77) (l 39) (l 65)) (n 13 (l 12) (l 195) (l 39) (l 675)) (n 13 (l 12) (l 143) (l 39) (l 363)))) (l 15) (l 9)) (n 5 (l 5) (l 15) (n 7 (l 6) (l 20) (l 35) (n 11 (l 120) (n 13 (l 13) (l 104) (n 17 (l 16) (l 51) (l 84) (l 33)) (l 25)) (l 44) (l 440))) (n 7 (l 6) (l 35) (n 11 (l 10) (n 13 (l 168) (l 104) (l 168) (n 17 (l 16) (l 135) (l 153) (l 33))) (l 99) (n 13 (l 168) (l 104) (l 168) (l 351))) (l 224)))) (n 3 (l 3) (n 5 (l 4) (n 7 (l 49) (n 11 (l 120) (l 440) (l 98) (n 13 (l 168) (l 77) (l 168) (l 64))) (l 49) (n 11 (l 120) (l 440) (l 21) (n 13 (n 17 (l 16) (l 119) (l 33) (l 50)) (n 17 (l 16) (l 119) (l 33) (l 50)) (l 324) (l 64)))) (n 7 (n 11 (l 10) (n 13 (l 324) (l 195) (l 25) (l 39)) (l 99) (n 13 (l 324) (l 195) (l 25) (l 39))) (n 11 (l 10) (n 13 (l 168) (n 17 (l 16) (l 255) (l 153) (n 19 (l 18) (l 285) (l 399) (n 23 (n 29 (n 31 (n 37 (l 666) (l 221) (l 296) (l 1035)) (l 186) (l 154) (l 92)) (n 31 (n 37 (n 41 (l 40) (l 245) (l 81) (l 123)) (l 221) (l 296) (l 406)) (l 186) (l 154) (l 92)) (l 57) (l 203)) (l 391) (l 45) (l 160)))) (l 25) (l 39)) (l 98) (n 13 (l 168) (l 77) (l 25) (l 39))) (l 63) (n 11 (l 10) (n 13 (l 324) (l 77) (l 25) (l 39)) (l 21) (n 13 (l 324) (n 17 (l 16) (l 255) (l 33) (l 594)) (l 25) (l 39)))) (l 15)) (n 5 (l 4) (n 7 (l 6) (n 11 (l 98) (n 13 (l 675) (l 728) (l 104) (l 64)) (l 384) (l 54)) (l 49) (l 35)) (l 9) (n 7 (l 6) (l 35) (l 49) (n 11 (l 98) (l 54) (l 384) (n 13 (l 675) (l 64) (l 104) (l 728))))) (n 5 (l 4) (l 15) (n 7 (n 11 (l 10) (n 13 (l 324) (l 39) (l 25) (l 195)) (l 99) (n 13 (l 324) (l 39) (l 25) (l 195))) (n 11 (l 10) (n 13 (l 324) (l 39) (l 25) (n 17 (l 16) (l 594) (l 33) (l 255))) (l 21) (n 13 (l 324) (l 39) (l 25) (l 77))) (l 63) (n 11 (l 10) (n 13 (l 168) (l 39) (l 25) (l 77)) (l 98) (n 13 (l 168) (l 39) (l 25) (n 17 (l 16) (n 19 (l 18) (n 23 (n 29 (n 31 (n 37 (l 666) (l 1035) (l 296) (l 221)) (l 92) (l 154) (l 186)) (l 203) (l 57) (n 31 (n 37 (n 41 (l 40) (l 123) (l 81) (l 245)) (l 406) (l 296) (l 221)) (l 92) (l 154) (l 186))) (l 160) (l 45) (l 391)) (l 399) (l 285)) (l 153) (l 255))))) (n 7 (l 49) (n 11 (l 120) (n 13 (n 17 (l 16) (l 50) (l 33) (l 119)) (l 64) (l 324) (n 17 (l 16) (l 50) (l 33) (l 119))) (l 21) (l 440)) (l 49) (n 11 (l 120) (n 13 (l 168) (l 64) (l 168) (l 77)) (l 98) (l 440))))) (n 3 (n 5 (l 15) (l 9) (n 7 (l 20) (l 224) (l 27) (n 11 (n 13 (l 143) (l 25) (l 168) (l 363)) (n 13 (l 168) (l 25) (l 65) (l 143)) (l 55) (n 13 (l 168) (l 25) (l 168) (l 675)))) (n 7 (l 48) (n 11 (l 99) (n 13 (l 13) (l 26) (l 728) (l 104)) (l 120) (n 13 (l 13) (l 26) (l 728) (l 104))) (l 27) (n 11 (l 99) (l 55) (l 120) (n 13 (l 39) (l 26) (l 168) (n 17 (l 16) (l 119) (l 935) (l 1224)))))) (n 5 (l 5) (n 7 (l 6) (l 224) (n 11 (l 10) (n 13 (l 168) (l 351) (l 168) (l 104)) (l 99) (n 13 (l 168) (n 17 (l 16) (l 33) (l 153) (l 135)) (l 168) (l 104))) (l 35)) (n 7 (l 6) (n 11 (l 120) (l 440) (l 44) (n 13 (l 13) (l 25) (n 17 (l 16) (l 33) (l 84) (l 51)) (l 104))) (l 35) (l 20)) (l 15)) (n 5 (l 80) (l 9) (l 15) (n 7 (n 11 (l 11) (n 13 (l 12) (l 675) (l 39) (l 143)) (n 13 (l 12) (l 675) (l 39) (l 675)) (n 13 (l 12) (l 65) (l 39) (l 675))) (n 11 (l 11) (n 13 (l 12) (l 363) (l 39) (l 143)) (n 13 (l 12) (l 675) (l 39) (l 195)) (n 13 (l 12) (l 65) (l 39) (l 77))) (n 11 (l 11) (l 21) (n 13 (l 12) (l 675) (l 39) (l 77)) (n 13 (l 12) (l 65) (l 39) (l 675))) (n 11 (l 11) (l 55) (n 13 (l 12) (l 675) (l 39) (l 104)) (n 13 (l 12) (l 65) (l 39) (l 104))))) (n 5 (l 24) (l 15) (l 24) (n 7 (n 11 (n 13 (l 90) (l 39) (l 77) (n 17 (l 16) (l 374) (l 255) (l 135))) (l 54) (l 99) (n 13 (l 90) (l 39) (l 168) (n 17 (l 16) (l 220) (l 255) (l 135)))) (l 35) (n 11 (l 175) (l 54) (l 99) (l 384)) (n 11 (l 440) (l 54) (l 99) (n 13 (n 17 (l 16) (l 84) (l 169) (l 135)) (l 39) (l 195) (l 350))))))

set_option maxRecDepth 100000 in
theorem vtree : valid [] (fun _ => 0) tree = true := by
  simp [valid,leafok,csum,keysin,tree,upd]
  repeat constructor

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1 := by
  intro w
  exact ⟨ev w tree,sound w tree [] (fun _ => 0) vtree (by intro q h; simp at h)⟩
