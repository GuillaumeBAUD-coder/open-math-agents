import OMAStatements.S_oeis_a132297
import Mathlib

/-!
# Binary Markov type counts

A profile records the multiplicities of the four adjacent pairs in a binary
word. The two switch directions alternate. For a positive number of switches,
their multiplicities determine the orientation up to parity, and the remaining
positions may be distributed freely between 00 and 11. The two constant words
supply the profiles with no switches.

The formulas are those of Colin Barker in OEIS A132297.
-/

namespace OMA.Markov
open OMA.S_oeis_a132297 Finset

def compat : Bool → Profile → Prop
  | false, p => p.oz ≤ p.zo ∧ p.zo ≤ p.oz+1 ∧ (p.zo=0 → p.oo=0)
  | true, p => p.zo ≤ p.oz ∧ p.oz ≤ p.zo+1 ∧ (p.oz=0 → p.zz=0)

def size (p : Profile) := p.zz + p.zo + p.oz + p.oo

lemma walk_spec (w : List Bool) (b : Bool) :
    size (walk b w) = w.length ∧ compat b (walk b w) := by
  induction w generalizing b with
  | nil => cases b <;> simp [walk, size, compat]
  | cons h w ih =>
    have hf := ih false
    have ht := ih true
    cases b <;> cases h <;> simp_all [walk, compat, size] <;> omega

/-- Remove a stay at the current symbol, or switch if there are no stays left there. -/
lemma build_walk (m : ℕ) (b : Bool) (a u v d : ℕ) (len : a+u+v+d = m)
    (h : compat b ⟨a,u,v,d⟩) : ∃ w, walk b w = ⟨a,u,v,d⟩ := by
  induction m generalizing b a u v d with
  | zero =>
    obtain ⟨rfl,rfl,rfl,rfl⟩ : a=0 ∧ u=0 ∧ v=0 ∧ d=0 := by omega
    exact ⟨[],rfl⟩
  | succ m ih =>
    cases b
    · simp only [compat] at h
      cases a with
      | succ a =>
        obtain ⟨w, hw⟩ := ih false a u v d (by omega) h
        exact ⟨false::w, by simp [walk,hw]⟩
      | zero =>
        obtain ⟨u,rfl⟩ : ∃ z, u = z+1 := by exact ⟨u-1,by omega⟩
        obtain ⟨w, hw⟩ := ih true 0 u v d (by omega) (by simp [compat]; omega)
        exact ⟨true::w, by simp [walk,hw]⟩
    · simp only [compat] at h
      cases d with
      | succ d =>
        obtain ⟨w, hw⟩ := ih true a u v d (by omega) h
        exact ⟨false::w, by simp [walk,hw]⟩
      | zero =>
        obtain ⟨v,rfl⟩ : ∃ z, v = z+1 := by exact ⟨v-1,by omega⟩
        obtain ⟨w, hw⟩ := ih false a u v 0 (by omega) (by simp [compat]; omega)
        exact ⟨true::w, by simp [walk,hw]⟩

lemma mem_profiles (m : ℕ) (p : Profile) :
    p ∈ profiles m ↔ size p = m ∧ (compat false p ∨ compat true p) := by
  constructor
  · intro hp
    obtain ⟨⟨b,f⟩, _, rfl⟩ := mem_image.mp hp
    obtain ⟨hl, hc⟩ := walk_spec (List.ofFn f) b
    exact ⟨by simpa using hl, by cases b <;> tauto⟩
  · rintro ⟨hl, hc⟩
    obtain ⟨b,hb⟩ : ∃ b, compat b p := by
      rcases hc with h | h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    obtain ⟨a,u,v,d⟩ := p
    obtain ⟨w,hw⟩ := build_walk m b a u v d hl hb
    have hlen : w.length = m := by rw [← (walk_spec w b).1, hw]; exact hl
    clear hl
    subst m
    exact mem_image.mpr ⟨(b,w.get),mem_univ _,by simpa using hw⟩

/-- Positive-switch profiles, indexed by the number of 00 stays and the
orientation of the unmatched switch when the number of switches is odd. -/
def entry (m i : ℕ) (p : ℕ × ℕ) : Profile :=
  let s := i + 1
  let u := s/2 + p.2
  ⟨p.1, u, s-u, m-s-p.1⟩

def layer (m i : ℕ) := ((range (m-i)) ×ˢ (range (1+(i+1)%2))).image (entry m i)

lemma mem_layer {m i : ℕ} {p : Profile} :
    p ∈ layer m i ↔ size p = m ∧ p.zo+p.oz = i+1 ∧
      p.zo ≤ p.oz+1 ∧ p.oz ≤ p.zo+1 := by
  obtain ⟨a,u,v,d⟩ := p
  simp only [layer, mem_image, mem_product, mem_range, size]
  constructor
  · rintro ⟨⟨z,j⟩,⟨ha,hj⟩,he⟩
    simp only [entry, Profile.mk.injEq] at he
    dsimp at ha hj
    omega
  · rintro ⟨hl,hs,h1,h2⟩
    refine ⟨(a,u-(i+1)/2), ⟨by omega,by omega⟩, ?_⟩
    simp [entry, Profile.mk.injEq]
    omega

lemma card_layer (m i : ℕ) :
    (layer m i).card = (m-i)*(1+(i+1)%2) := by
  unfold layer
  rw [card_image_of_injOn, card_product, card_range, card_range]
  intro a _ b _ h
  exact Prod.ext (congrArg Profile.zz h) (Nat.add_left_cancel (congrArg Profile.zo h))

def constantProfiles (m : ℕ) : Finset Profile := {⟨m,0,0,0⟩,⟨0,0,0,m⟩}

lemma mem_constant {p : Profile} {m : ℕ} :
    p ∈ constantProfiles m ↔ p = ⟨m,0,0,0⟩ ∨ p = ⟨0,0,0,m⟩ := by
  simp [constantProfiles]

lemma partition (m : ℕ) :
    profiles m = constantProfiles m ∪ (range m).biUnion (layer m) := by
  ext p
  obtain ⟨a,u,v,d⟩ := p
  rw [mem_profiles, mem_union, mem_constant, mem_biUnion]
  simp only [mem_range, mem_layer, size, compat, Profile.mk.injEq]
  constructor
  · rintro ⟨hl,h⟩
    by_cases hzero : u+v=0
    · left; omega
    · right; exact ⟨u+v-1, by omega, hl, by omega, by omega, by omega⟩
  · rintro (hc | ⟨i,hi,hl,hs,h1,h2⟩) <;> omega

lemma card_profiles (m : ℕ) (hm : 0 < m) :
    (profiles m).card = 2 + ∑ i ∈ range m, (m-i)*(1+(i+1)%2) := by
  have disj : Disjoint (constantProfiles m) ((range m).biUnion (layer m)) := by
    rw [disjoint_left]
    intro p hp hq
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    have hs := (mem_layer.mp hi).2.1
    rcases mem_constant.mp hp with rfl | rfl <;> simp at hs
  have separate : (range m : Set ℕ).PairwiseDisjoint (layer m) := by
    intro i _ j _ hne
    rw [Function.onFun, disjoint_left]
    intro p hp hq
    exact hne (by have := (mem_layer.mp hp).2.1; have := (mem_layer.mp hq).2.1; omega)
  have cc : (constantProfiles m).card = 2 := by
    simp [constantProfiles, hm.ne', Profile.mk.injEq]
  rw [partition, card_union_of_disjoint disj, cc, card_biUnion separate]
  simp only [card_layer]

def count (m : ℕ) := ∑ i ∈ range m, (m-i)*(1+(i+1)%2)

/-- Adding two positions preserves the parity weights and adds two initial layers. -/
lemma count_step (m : ℕ) : count (m+2) = count m + 3*m+5 := by
  unfold count
  rw [sum_range_succ', sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  have hs (j : ℕ) : (j+1+1+1)%2 = (j+1)%2 := by omega
  simp_rw [hs]
  omega

lemma term_step (j : ℕ) : term (j+4) = term (j+2) + 3*j+8 := by
  have h (t : ℕ) : term (t+2) = 2 + count (t+1) := by
    unfold term
    rw [if_pos (by omega), show t+2-1=t+1 by omega]
    exact card_profiles _ (by omega)
  rw [show j+4=j+2+2 by omega, h, h]
  have hh := count_step (j+1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hh ⊢
  omega

lemma small : term 0 = 0 ∧ term 1 = 0 ∧ term 2 = 4 ∧ term 3 = 7 ∧ term 4 = 12 ∧ term 5 = 18 := by
  decide

lemma formula (j : ℕ) : 8*(term (j+2) : ℤ) =
    15+(-1)^(j+2)-4*((j:ℤ)+2)+6*((j:ℤ)+2)^2 := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num [small.2.2.1]
  | one => norm_num [small.2.2.2.1]
  | more j ih _ =>
    rw [show j+2+2 = j+4 by omega, term_step]
    push_cast
    simp only [show j+4 = (j+2)+2 by omega, pow_add, neg_one_sq] at *
    linarith only [ih]

lemma recurrence (k : ℕ) :
    term (k+6)+2*term (k+3) = 2*term (k+5)+term (k+2) := by
  have h₁ := term_step k
  have h₂ := term_step (k+1)
  have h₃ := term_step (k+2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h₁ h₂ h₃
  omega

open PowerSeries

lemma generating :
    (1-2*X+2*X^3-X^4)*series = 4*X^2-X^3-2*X^4+2*X^5 := by
  have c2 : (2 : PowerSeries ℚ) = C 2 := (map_ofNat C 2).symm
  have c4 : (4 : PowerSeries ℚ) = C 4 := (map_ofNat C 4).symm
  ext n
  simp only [sub_mul,add_mul,one_mul,mul_assoc, c2,c4,map_sub,map_add,coeff_C_mul,
    coeff_X_pow_mul',coeff_X_pow,series,coeff_mk]
  by_cases hn : n < 6
  · obtain ⟨h0,h1,h2,h3,h4,h5⟩ := small
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5]
  · obtain ⟨k,rfl⟩ : ∃ k, n=k+6 := ⟨n-6,by omega⟩
    simp only [if_pos (by omega : 3 ≤ k+6), if_pos (by omega : 4 ≤ k+6),
      if_neg (by omega : ¬ k+6 = 2), if_neg (by omega : ¬ k+6 = 3),
      if_neg (by omega : ¬ k+6 = 4), if_neg (by omega : ¬ k+6 = 5)]
    norm_num
    rw [show k+6-3 = k+3 by omega, show k+6-4 = k+2 by omega]
    have hr : (term (k+6) : ℚ) + 2*term (k+3) = 2*term (k+5)+term (k+2) := by
      exact_mod_cast recurrence k
    linarith

end OMA.Markov

theorem OMA.solution : type_of% @OMA.S_oeis_a132297.main := by
  refine ⟨?_, OMA.Markov.recurrence, OMA.Markov.generating⟩
  intro n hn
  obtain ⟨j,rfl⟩ : ∃ j, n=j+2 := ⟨n-2,by omega⟩
  simpa using OMA.Markov.formula j
