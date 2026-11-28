import OMAReductions.R_Erdos436_erdos_436_variants_four_two_R1
import Mathlib

/-! A verified decision-tree certificate for the finite search in step `H1`. -/
-- Decision tree and checker from PR #16230 by Bondyboy2001; leaves written as numerals.

inductive T where
| l (n : ℕ)
| n (q : ℕ) (a b c d : T)
open T
instance {m : ℕ} : OfNat T m := ⟨l m⟩

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


def tree : T := n 2 1 (n 3 (n 5 15 (n 7 48 (n 11 99 (n 13 39 (n 17 16 1224 935 119) 168 26) 120 55) 27 (n 11 99 (n 13 13 104 728 26) 120 (n 13 13 104 728 26))) (n 7 20 (n 11 (n 13 143 363 168 25) (n 13 168 675 168 25) 55 (n 13 168 143 65 25)) 27 224) 9) (n 5 24 (n 7 (n 11 (n 13 90 (n 17 16 135 255 374) 77 39) (n 13 90 (n 17 16 135 255 220) 168 39) 99 54) (n 11 440 (n 13 (n 17 16 135 169 84) 350 195 39) 99 54) (n 11 175 384 99 54) 35) 24 15) (n 5 80 (n 7 (n 11 11 (n 13 12 675 39 65) (n 13 12 675 39 675) (n 13 12 143 39 675)) (n 11 11 (n 13 12 104 39 65) (n 13 12 104 39 675) 55) (n 11 11 (n 13 12 675 39 65) (n 13 12 77 39 675) 21) (n 11 11 (n 13 12 77 39 65) (n 13 12 195 39 675) (n 13 12 143 39 363))) 15 9) (n 5 5 15 (n 7 6 20 35 (n 11 120 (n 13 13 104 (n 17 16 51 84 33) 25) 44 440)) (n 7 6 35 (n 11 10 (n 13 168 104 168 (n 17 16 135 153 33)) 99 (n 13 168 104 168 351)) 224))) (n 3 3 (n 5 4 (n 7 49 (n 11 120 440 98 (n 13 168 77 168 64)) 49 (n 11 120 440 21 (n 13 (n 17 16 119 33 50) (n 17 16 119 33 50) 324 64))) (n 7 (n 11 10 (n 13 324 195 25 39) 99 (n 13 324 195 25 39)) (n 11 10 (n 13 168 (n 17 16 255 153 (n 19 18 285 399 (n 23 (n 29 (n 31 (n 37 666 221 296 1035) 186 154 92) (n 31 (n 37 (n 41 40 245 81 123) 221 296 406) 186 154 92) 57 203) 391 45 160))) 25 39) 98 (n 13 168 77 25 39)) 63 (n 11 10 (n 13 324 77 25 39) 21 (n 13 324 (n 17 16 255 33 594) 25 39))) 15) (n 5 4 (n 7 6 (n 11 98 (n 13 675 728 104 64) 384 54) 49 35) 9 (n 7 6 35 49 (n 11 98 54 384 (n 13 675 64 104 728)))) (n 5 4 15 (n 7 (n 11 10 (n 13 324 39 25 195) 99 (n 13 324 39 25 195)) (n 11 10 (n 13 324 39 25 (n 17 16 594 33 255)) 21 (n 13 324 39 25 77)) 63 (n 11 10 (n 13 168 39 25 77) 98 (n 13 168 39 25 (n 17 16 (n 19 18 (n 23 (n 29 (n 31 (n 37 666 1035 296 221) 92 154 186) 203 57 (n 31 (n 37 (n 41 40 123 81 245) 406 296 221) 92 154 186)) 160 45 391) 399 285) 153 255)))) (n 7 49 (n 11 120 (n 13 (n 17 16 50 33 119) 64 324 (n 17 16 50 33 119)) 21 440) 49 (n 11 120 (n 13 168 64 168 77) 98 440)))) (n 3 (n 5 15 9 (n 7 20 224 27 (n 11 (n 13 143 25 168 363) (n 13 168 25 65 143) 55 (n 13 168 25 168 675))) (n 7 48 (n 11 99 (n 13 13 26 728 104) 120 (n 13 13 26 728 104)) 27 (n 11 99 55 120 (n 13 39 26 168 (n 17 16 119 935 1224))))) (n 5 5 (n 7 6 224 (n 11 10 (n 13 168 351 168 104) 99 (n 13 168 (n 17 16 33 153 135) 168 104)) 35) (n 7 6 (n 11 120 440 44 (n 13 13 25 (n 17 16 33 84 51) 104)) 35 20) 15) (n 5 80 9 15 (n 7 (n 11 11 (n 13 12 675 39 143) (n 13 12 675 39 675) (n 13 12 65 39 675)) (n 11 11 (n 13 12 363 39 143) (n 13 12 675 39 195) (n 13 12 65 39 77)) (n 11 11 21 (n 13 12 675 39 77) (n 13 12 65 39 675)) (n 11 11 55 (n 13 12 675 39 104) (n 13 12 65 39 104)))) (n 5 24 15 24 (n 7 (n 11 (n 13 90 39 77 (n 17 16 374 255 135)) 54 99 (n 13 90 39 168 (n 17 16 220 255 135))) 35 (n 11 175 54 99 384) (n 11 440 54 99 (n 13 (n 17 16 84 169 135) 39 195 350)))))

set_option maxRecDepth 100000 in
theorem vtree : valid [] (fun _ => 0) tree = true := by
  decide +kernel

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1 := by
  intro w
  exact ⟨ev w tree,sound w tree [] (fun _ => 0) vtree (by intro q h; simp at h)⟩
