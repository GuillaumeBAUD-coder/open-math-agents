import FormalConjectures.GreensOpenProblems.«14»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-! Exact mixed van der Waerden numbers as tabulated by Ahmed, Kullmann and Snevily,
https://arxiv.org/abs/1102.5433, Appendix A.
The order and certificate bridge below are adapted from Dominic
Dabish’s Apache-2.0 Green14 proofs, revision 013a0f04de0057d2bd1034c7cc4caf10ac8dc2cf
of https://github.com/DomTheDeveloper/formal-conjectures. Credit: @Deldor14. -/

open Set
open scoped Classical

namespace Green14

theorem mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) :
    N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x ↦ ⟨x, x.2.1, x.2.2.trans hMN⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Icc 1 N ↦ (z : Nat)) h⟩
  let restricted : Icc 1 M → Fin 2 := fun x ↦ coloring (emb x)
  rcases hM restricted with hzero | hone
  · left
    rcases hzero with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

/-- One bad coloring of `{1, ..., N}` proves the numerical lower bound
`W(k,r) ≥ N+1`. -/
theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

end Green14

open Set
open scoped Classical

namespace Green14.FunctionCertificateBridge

/-- Bit i of starts m d j records that i through i+j*d all belong to m. -/
private def starts (m d : Nat) : Nat → Nat
  | 0 => m
  | j+1 => starts m d j &&& (m >>> ((j+1)*d))

private theorem start_bit {m d a j : Nat}
    (h : ∀ i ≤ j, m.testBit (a + i*d) = true) :
    (starts m d j).testBit a = true := by
  induction j with
  | zero => simpa [starts] using h 0 le_rfl
  | succ j ih =>
    simp only [starts, Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (Nat.le_succ_of_le hi), by simpa [Nat.add_comm] using h (j+1) le_rfl⟩

private def clear (N k m : Nat) : Bool :=
  (List.range ((N-1)/(k-1))).all fun d => starts m (d+1) (k-1) == 0

private lemma mismatch {N k m : Nat} (hk : 2 ≤ k) (hc : clear N k m = true)
    {a d : Nat} (hd : 0 < d) (he : a + (k-1)*d < N) :
    ∃ i < k, m.testBit (a+i*d) = false := by
  by_contra! h
  have hmul : d*(k-1) ≤ N-1 := by rw [Nat.mul_comm]; omega
  have hle := (Nat.le_div_iff_mul_le (show 0 < k-1 by omega)).mpr hmul
  have hz := List.all_eq_true.mp hc (d-1) (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq, Nat.sub_add_cancel (show 1 ≤ d by omega)] at hz
  have H := start_bit (a := a) (j := k-1) (m := m) (d := d) (by
    intro i hi
    simpa using h i (by omega))
  simp [hz] at H

def boolColor : Bool → Fin 2
  | false => 0
  | true => 1

lemma boolColor_injective : Function.Injective boolColor := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolColor]

def certificateColoring (N : Nat) (coloring : Nat → Bool) : Icc 1 N → Fin 2 :=
  fun x => boolColor (coloring (x.1 - 1))

private lemma mem_coe_finset_set_iff {N : Nat} {s : Finset (Icc 1 N)} {z : Nat} :
    z ∈ ({(x : Nat) | x ∈ s} : Set Nat) ↔ ∃ x ∈ s, (x : Nat) = z := by
  simp

lemma no_monoAP_of_hasAP_eq_false
    {N k mask : Nat} {coloring : Nat → Bool} {color : Bool}
    (hk : 2 ≤ k) (hcheck : clear N k mask = true)
    (hmask : ∀ i < N, coloring i = color → mask.testBit i = true) :
    ¬ ∃ s : Finset (Icc 1 N),
        ({(x : Nat) | x ∈ s}).IsAPOfLength k ∧
          ∀ x ∈ s, certificateColoring N coloring x = boolColor color := by
  rintro ⟨s, hAP, hmono⟩
  rcases hAP with ⟨start, step, hWith⟩
  let T : Set Nat := {(x : Nat) | x ∈ s}
  have hT : T.IsAPOfLengthWith k start step := hWith
  have term_mem (i : Nat) (hi : i < k) : start + i * step ∈ T := by
    rw [hT.2]
    refine ⟨i, ?_, ?_⟩
    · exact_mod_cast hi
    · simp
  have start_mem : start ∈ T := by simpa using term_mem 0 (by omega)
  have last_mem : start + (k - 1) * step ∈ T := term_mem (k - 1) (by omega)
  rcases (mem_coe_finset_set_iff.mp start_mem) with ⟨x0, hx0s, hx0⟩
  rcases (mem_coe_finset_set_iff.mp last_mem) with ⟨xlast, hxlasts, hxlast⟩
  have hstart_lo : 1 ≤ start := by simpa [hx0] using x0.2.1
  have hstart_hi : start ≤ N := by simpa [hx0] using x0.2.2
  have hlast_hi : start + (k - 1) * step ≤ N := by simpa [hxlast] using xlast.2.2
  have hstep_pos : 0 < step := by
    by_contra hnot
    have hstep : step = 0 := Nat.eq_zero_of_not_pos hnot
    have hTsingle : T = {start} := by
      rw [hT.2]
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        simp [hstep]
      · intro hz
        have hz' : z = start := by simpa using hz
        subst z
        refine ⟨0, ?_, by simp [hstep]⟩
        exact_mod_cast (show 0 < k by omega)
    have hcard : (k : ℕ∞) = 1 := by
      rw [← hT.1, hTsingle]
      simp
    have : k = 1 := by exact_mod_cast hcard
    omega
  have hend0 : start - 1 + (k - 1) * step < N := by omega
  obtain ⟨i, hi, hmismatch⟩ :=
    mismatch hk hcheck hstep_pos hend0
  have hiterm : start + i * step ∈ T := term_mem i hi
  rcases (mem_coe_finset_set_iff.mp hiterm) with ⟨x, hxs, hx⟩
  have hxindex : x.1 - 1 = start - 1 + i * step := by
    have hxval : x.1 = start + i * step := hx
    omega
  have hcolor := hmono x hxs
  have hbool : coloring (start - 1 + i * step) = color := by
    apply boolColor_injective
    simpa [certificateColoring, hxindex] using hcolor
  have hbound := Nat.mul_le_mul_right step (show i ≤ k-1 by omega)
  have ht := hmask _ (by omega) hbool
  simp_all

end Green14.FunctionCertificateBridge

open Green14.FunctionCertificateBridge
namespace OMA.VDW
open Set Green14
lemma progression_at {N k a d : Nat} (hd : 0 < d)
    (c : Icc 1 N → Fin 2) (color : Fin 2)
    (bound : ∀ i : Fin k, a+i.val*d < N)
    (mono : ∀ (i : Fin k) (hi : a+i.val*d < N), c ⟨a+i.val*d+1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val*d + 1
  have inj : Function.Injective value := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (by simpa [value] using h)
  let point : Fin k ↪ Icc 1 N := ⟨fun i => ⟨value i, by
    have := bound i
    dsimp [value]
    constructor <;> omega⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  let s := Finset.univ.map point
  have eqs : ({(z : Nat) | z ∈ s} : Set Nat) = range value := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨point i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a+1,d,?_,?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]; omega⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)
end OMA.VDW

/-! ## A lane-parallel DPLL refutation, evaluated by the kernel

Positions `0, …, 97-1` stand for `1, …, 97`. A partial colouring is a pair of bit masks `(T, F)`
(`true` = colour 1, `false` = colour 0). Many partial colourings (lanes) are packed into one number,
lane `l` occupying bits `l*194 …`, so every bitwise operation acts on all of them at once.
`go` branches on the variables of a fixed order, propagates the forced values, and drops the lanes
that became contradictory. Every lane that survives is consistent with any good colouring that its
parent was consistent with; so if no lane survives, no good colouring exists. -/

namespace OMA.VDWL

noncomputable def ft3 (F D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun d acc =>
      let a := Nat.shiftLeft F (d+1)
      let b := Nat.shiftRight F (d+1)
      Nat.lor (Nat.lor (Nat.lor (Nat.land a (Nat.shiftLeft a (d+1)))
        (Nat.land b (Nat.shiftRight b (d+1)))) (Nat.land a b)) acc) D

noncomputable def run (T d S m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (2^S - 1) (fun i acc => Nat.land acc (Nat.shiftRight T (i*d))) m

noncomputable def ffj (T d S J : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.lor (Nat.land (Nat.shiftLeft (run T d S j) (j*d))
      (Nat.shiftRight (run T d S (10-1-j)) d)) acc) J

noncomputable def ffr (T S D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun d acc => Nat.lor (ffj T (d+1) S 10) acc) D

noncomputable def prop (S M fuel : Nat) : Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun T F => (T, F))
    (fun _ rec T F =>
      let nT := Nat.lor T (Nat.land (ft3 F 48) M)
      let nF := Nat.lor F (Nat.land (ffr T S 10) M)
      cond (Nat.beq nT T && Nat.beq nF F) (T, F) (rec nT nF)) fuel

structure St where
  T : Nat
  F : Nat
  M : Nat
  L : Nat

def lo (s : St) (h : Nat) : St := ⟨s.T % 2^(h*194), s.F % 2^(h*194), s.M % 2^(h*194), h⟩
def hi (s : St) (h : Nat) : St :=
  ⟨Nat.shiftRight s.T (h*194), Nat.shiftRight s.F (h*194), Nat.shiftRight s.M (h*194), s.L - h⟩
def comb (a b : St) : St :=
  ⟨Nat.lor a.T (Nat.shiftLeft b.T (a.L*194)), Nat.lor a.F (Nat.shiftLeft b.F (a.L*194)),
    Nat.lor a.M (Nat.shiftLeft b.M (a.L*194)), a.L + b.L⟩

noncomputable def compact (fuel : Nat) : St → St :=
  Nat.rec (motive := fun _ => St → St) (fun s => s)
    (fun _ rec s =>
      cond (Nat.beq s.L 0) ⟨0, 0, 0, 0⟩ <|
      cond (Nat.beq s.L 1) (cond (Nat.beq (Nat.land s.T s.F) 0) s ⟨0, 0, 0, 0⟩) <|
      comb (rec (lo s (s.L / 2))) (rec (hi s (s.L / 2)))) fuel

noncomputable def step (v : Nat) (s : St) : St :=
  let LW := s.L * 194
  let V := Nat.shiftLeft (Nat.xor s.M (Nat.land s.M (Nat.shiftLeft s.M 1))) v
  let T1 := Nat.lor (Nat.lor s.T V) (Nat.shiftLeft s.T LW)
  let F1 := Nat.lor s.F (Nat.shiftLeft (Nat.lor s.F V) LW)
  let M1 := Nat.lor s.M (Nat.shiftLeft s.M LW)
  let p := prop (2*LW + 194) M1 97 T1 F1
  compact 64 ⟨p.1, p.2, M1, 2 * s.L⟩

noncomputable def go (l : List Nat) : St → St :=
  List.rec (motive := fun _ => St → St) (fun s => s)
    (fun v _ rec s => cond (Nat.blt v 97) (rec (step v s)) s) l

def init : St := ⟨0, 0, 2 ^ 97 - 1, 1⟩

def sub (s : St) (a : Nat) : St :=
  ⟨(s.T >>> (a*194)) % 2^194, (s.F >>> (a*194)) % 2^194, (s.M >>> (a*194)) % 2^194, 1⟩


/-! ## Soundness -/

def Good (c : Nat → Bool) : Prop :=
  (∀ a d, 0 < d → a + 2*d < 97 → c a = true ∨ c (a+d) = true ∨ c (a+2*d) = true) ∧
  (∀ a d, 0 < d → a + (10-1)*d < 97 → ∃ i < 10, c (a+i*d) = false)

def Cons (c : Nat → Bool) (T F l : Nat) : Prop :=
  ∀ x < 97, (T.testBit (l*194 + x) = true → c x = true) ∧ (F.testBit (l*194 + x) = true → c x = false)

def MaskOK (M L : Nat) : Prop := ∀ p, M.testBit p = true ↔ (p < L*194 ∧ p % 194 < 97)

def Inv (s : St) : Prop :=
  MaskOK s.M s.L ∧ (∀ p, s.T.testBit p = true → s.M.testBit p = true) ∧
    (∀ p, s.F.testBit p = true → s.M.testBit p = true)

theorem tlor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_lor x y i
theorem tland (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_land x y i
theorem txor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) := Nat.testBit_xor x y i
theorem tshl (x n i : Nat) : (Nat.shiftLeft x n).testBit i = (decide (i ≥ n) && x.testBit (i - n)) :=
  Nat.testBit_shiftLeft x
theorem tshr (x n i : Nat) : (Nat.shiftRight x n).testBit i = x.testBit (n + i) := Nat.testBit_shiftRight x

theorem consT {c : Nat → Bool} {T F l y q : Nat} (h : Cons c T F l) (hy : y < 97) (hq : q = l*194 + y)
    (hb : T.testBit q = true) : c y = true := by
  subst hq; exact (h y hy).1 hb

theorem consF {c : Nat → Bool} {T F l y q : Nat} (h : Cons c T F l) (hy : y < 97) (hq : q = l*194 + y)
    (hb : F.testBit q = true) : c y = false := by
  subst hq; exact (h y hy).2 hb

theorem ft3_sound {c : Nat → Bool} (hg : Good c) {M L T F l x : Nat} (hM : MaskOK M L)
    (hF : ∀ p, F.testBit p = true → M.testBit p = true) (hc : Cons c T F l) (hx : x < 97) :
    ∀ D, D ≤ 48 → (ft3 F D).testBit (l*194 + x) = true → c x = true := by
  have lanepos : ∀ q, F.testBit q = true → q % 194 < 97 := fun q h => ((hM q).1 (hF q h)).2
  intro D
  induction D with
  | zero => intro _ h; simp [ft3] at h
  | succ D ih =>
    intro hD h
    have e : ft3 F (D+1) = Nat.lor (Nat.lor (Nat.lor (Nat.land (Nat.shiftLeft F (D+1))
        (Nat.shiftLeft (Nat.shiftLeft F (D+1)) (D+1)))
        (Nat.land (Nat.shiftRight F (D+1)) (Nat.shiftRight (Nat.shiftRight F (D+1)) (D+1))))
        (Nat.land (Nat.shiftLeft F (D+1)) (Nat.shiftRight F (D+1)))) (ft3 F D) := rfl
    rw [e] at h
    simp only [tlor, tland, tshl, tshr, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    by_contra hne
    have hcx : c x = false := by simpa using hne
    rcases h with ((⟨⟨h1, h2⟩, h3, h4, h5⟩ | ⟨h1, h2⟩) | ⟨⟨h1, h2⟩, h3⟩) | h
    · -- x-2d, x-d in F
      have l4 := lanepos _ h5
      have l2 := lanepos _ h2
      have c1 := consF hc (y := x - (D+1)) (by omega) (by omega) h2
      have c2 := consF hc (y := x - 2*(D+1)) (by omega) (by omega) h5
      have := hg.1 (x - 2*(D+1)) (D+1) (by omega) (by omega)
      rw [show x - 2*(D+1) + (D+1) = x - (D+1) by omega, show x - 2*(D+1) + 2*(D+1) = x by omega] at this
      simp_all
    · -- x+d, x+2d in F
      have l1 := lanepos _ h1
      have l2 := lanepos _ h2
      have c1 := consF hc (y := x + (D+1)) (by omega) (by omega) h1
      have c2 := consF hc (y := x + 2*(D+1)) (by omega) (by omega) h2
      have := hg.1 x (D+1) (by omega) (by omega)
      rw [show x + 2*(D+1) = x + 2*(D+1) from rfl] at this
      simp_all
    · -- x-d, x+d in F
      have l2 := lanepos _ h2
      have l3 := lanepos _ h3
      have c1 := consF hc (y := x - (D+1)) (by omega) (by omega) h2
      have c2 := consF hc (y := x + (D+1)) (by omega) (by omega) h3
      have := hg.1 (x - (D+1)) (D+1) (by omega) (by omega)
      rw [show x - (D+1) + (D+1) = x by omega, show x - (D+1) + 2*(D+1) = x + (D+1) by omega] at this
      simp_all
    · exact hne (ih (by omega) h)

theorem run_bit {T d S : Nat} : ∀ m q, (run T d S m).testBit q = true → ∀ i < m, T.testBit (i*d + q) = true := by
  intro m
  induction m with
  | zero => intro q _ i hi; omega
  | succ m ih =>
    intro q h i hi
    have e : run T d S (m+1) = Nat.land (run T d S m) (Nat.shiftRight T (m*d)) := rfl
    rw [e, tland, tshr, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ih q h.1 i hi
    · subst hi; exact h.2

theorem ffj_bit {T d S p : Nat} : ∀ J, (ffj T d S J).testBit p = true →
    ∃ j < J, (Nat.shiftLeft (run T d S j) (j*d)).testBit p = true ∧
      (Nat.shiftRight (run T d S (10-1-j)) d).testBit p = true := by
  intro J
  induction J with
  | zero => intro h; simp [ffj] at h
  | succ J ih =>
    intro h
    have e : ffj T d S (J+1) = Nat.lor (Nat.land (Nat.shiftLeft (run T d S J) (J*d))
      (Nat.shiftRight (run T d S (10-1-J)) d)) (ffj T d S J) := rfl
    rw [e, tlor, tland, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · exact ⟨J, by omega, h.1, h.2⟩
    · obtain ⟨j, hj, h1, h2⟩ := ih h
      exact ⟨j, by omega, h1, h2⟩

theorem ffr_bit {T S p : Nat} : ∀ D, (ffr T S D).testBit p = true →
    ∃ d, 0 < d ∧ d ≤ D ∧ (ffj T d S 10).testBit p = true := by
  intro D
  induction D with
  | zero => intro h; simp [ffr] at h
  | succ D ih =>
    intro h
    have e : ffr T S (D+1) = Nat.lor (ffj T (D+1) S 10) (ffr T S D) := rfl
    rw [e, tlor, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨D+1, by omega, le_rfl, h⟩
    · obtain ⟨d, h0, hd, h1⟩ := ih h
      exact ⟨d, h0, by omega, h1⟩

theorem ffr_sound {c : Nat → Bool} (hg : Good c) {M L T F l x S : Nat} (hM : MaskOK M L)
    (hT : ∀ p, T.testBit p = true → M.testBit p = true) (hc : Cons c T F l) (hx : x < 97)
    (h : (ffr T S 10).testBit (l*194 + x) = true) : c x = false := by
  have lanepos : ∀ q, T.testBit q = true → q % 194 < 97 := fun q h => ((hM q).1 (hT q h)).2
  obtain ⟨d, hd0, hdD, h⟩ := ffr_bit 10 h
  obtain ⟨j, hj, hl, hr⟩ := ffj_bit 10 h
  rw [tshl, Bool.and_eq_true, decide_eq_true_eq] at hl
  rw [tshr] at hr
  have L := run_bit j _ hl.2
  have Rt := run_bit _ _ hr
  have hEd : (10-1)*d ≤ 97 - 1 := by
    have := Nat.mul_le_mul_left (10-1) hdD
    omega
  have hjd : j*d ≤ (10-1)*d := Nat.mul_le_mul_right d (by omega)
  -- the start of the progression lies in the lane
  have hjx : j*d ≤ x := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0; simp
    · have b0 := L 0 hj0
      simp only [Nat.zero_mul, Nat.zero_add] at b0
      have := lanepos _ b0
      omega
  -- every member but x is true
  have left : ∀ i < j, c (x - j*d + i*d) = true := by
    intro i hi
    have b := L i hi
    have hid : i*d + d ≤ j*d := by
      have := Nat.mul_le_mul_right d (show i + 1 ≤ j by omega)
      simpa [Nat.add_mul] using this
    have := lanepos _ b
    exact consT hc (by omega) (by omega) b
  have right : ∀ i < 10-1-j, c (x + (i+1)*d) = true := by
    intro i hi
    have b := Rt i hi
    have hid : (i+1)*d ≤ (10-1)*d := Nat.mul_le_mul_right d (by omega)
    have hid' : (i+1)*d = i*d + d := by rw [Nat.add_mul, Nat.one_mul]
    have := lanepos _ b
    exact consT hc (by omega) (by omega) b
  by_contra hne
  have hcx : c x = true := by simpa using hne
  have hend : x - j*d + (10-1)*d < 97 := by
    rcases Nat.lt_or_ge j (10-1) with hj1 | hj1
    · have b := right (10-2-j) (by omega)
      have e1 : (10-2-j+1)*d + j*d = (10-1)*d := by
        rw [← Nat.add_mul]; congr 1; omega
      by_contra hc'
      have hb := Rt (10-2-j) (by omega)
      have := lanepos _ hb
      have hid : (10-2-j)*d + d = (10-2-j+1)*d := by rw [Nat.add_mul, Nat.one_mul]
      omega
    · have : j = 10-1 := by omega
      subst this; omega
  obtain ⟨i, hi, hci⟩ := hg.2 (x - j*d) d hd0 hend
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := left i hij; simp_all
  · subst hij
    rw [show x - i*d + i*d = x by omega] at hci
    simp_all
  · have e : x - j*d + i*d = x + (i - j - 1 + 1)*d := by
      have : i*d = j*d + (i-j-1+1)*d := by rw [← Nat.add_mul]; congr 1; omega
      omega
    have := right (i-j-1) (by omega)
    rw [e] at hci
    simp_all

theorem prop_sound {c : Nat → Bool} (hg : Good c) {M L S l : Nat} (hM : MaskOK M L) :
    ∀ fuel T F, (∀ p, T.testBit p = true → M.testBit p = true) →
      (∀ p, F.testBit p = true → M.testBit p = true) → Cons c T F l →
      (∀ p, (prop S M fuel T F).1.testBit p = true → M.testBit p = true) ∧
      (∀ p, (prop S M fuel T F).2.testBit p = true → M.testBit p = true) ∧
      Cons c (prop S M fuel T F).1 (prop S M fuel T F).2 l := by
  intro fuel
  induction fuel with
  | zero => intro T F hT hF hc; exact ⟨hT, hF, hc⟩
  | succ n ih =>
    intro T F hT hF hc
    have hT' : ∀ p, (Nat.lor T (Nat.land (ft3 F 48) M)).testBit p = true → M.testBit p = true := by
      intro p hp
      rw [tlor, tland, Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with hp | hp
      · exact hT p hp
      · exact hp.2
    have hF' : ∀ p, (Nat.lor F (Nat.land (ffr T S 10) M)).testBit p = true → M.testBit p = true := by
      intro p hp
      rw [tlor, tland, Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with hp | hp
      · exact hF p hp
      · exact hp.2
    have hc' : Cons c (Nat.lor T (Nat.land (ft3 F 48) M)) (Nat.lor F (Nat.land (ffr T S 10) M)) l := by
      intro x hx
      constructor
      · intro hb
        rw [tlor, tland, Bool.or_eq_true, Bool.and_eq_true] at hb
        rcases hb with hb | hb
        · exact (hc x hx).1 hb
        · exact ft3_sound hg hM hF hc hx 48 le_rfl hb.1
      · intro hb
        rw [tlor, tland, Bool.or_eq_true, Bool.and_eq_true] at hb
        rcases hb with hb | hb
        · exact (hc x hx).2 hb
        · exact ffr_sound hg hM hT hc hx hb.1
    show (∀ p, (cond (_ && _) (T, F) (prop S M n _ _)).1.testBit p = true → M.testBit p = true) ∧
      (∀ p, (cond (_ && _) (T, F) (prop S M n _ _)).2.testBit p = true → M.testBit p = true) ∧
      Cons c (cond (_ && _) (T, F) (prop S M n _ _)).1 (cond (_ && _) (T, F) (prop S M n _ _)).2 l
    cases (Nat.beq (Nat.lor T (Nat.land (ft3 F 48) M)) T && Nat.beq (Nat.lor F (Nat.land (ffr T S 10) M)) F)
    · exact ih _ _ hT' hF' hc'
    · exact ⟨hT, hF, hc⟩

/-- Lanes of a packed number. -/
theorem testBit_mod_pow {x k i : Nat} : (x % 2^k).testBit i = (decide (i < k) && x.testBit i) :=
  Nat.testBit_mod_two_pow x k i

theorem beq_t {a b : Nat} (h : a = b) : Nat.beq a b = true := by subst h; exact Nat.beq_refl a
theorem beq_f {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem inv_zero : Inv ⟨0, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro p; simp
  · intro p h; simp at h
  · intro p h; simp at h

theorem lo_inv {s : St} (hs : Inv s) {h : Nat} (hh : h ≤ s.L) : Inv (lo s h) := by
  obtain ⟨hM, hT, hF⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro p
    show (s.M % 2^(h*194)).testBit p = true ↔ (p < h*194 ∧ p % 194 < 97)
    rw [testBit_mod_pow, Bool.and_eq_true, decide_eq_true_eq, hM p]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, by omega, h3⟩
  · intro p hp
    have hp' : (s.T % 2^(h*194)).testBit p = true := hp
    show (s.M % 2^(h*194)).testBit p = true
    rw [testBit_mod_pow, Bool.and_eq_true] at hp' ⊢
    exact ⟨hp'.1, hT p hp'.2⟩
  · intro p hp
    have hp' : (s.F % 2^(h*194)).testBit p = true := hp
    show (s.M % 2^(h*194)).testBit p = true
    rw [testBit_mod_pow, Bool.and_eq_true] at hp' ⊢
    exact ⟨hp'.1, hF p hp'.2⟩

theorem hi_inv {s : St} (hs : Inv s) {h : Nat} (hh : h ≤ s.L) : Inv (hi s h) := by
  obtain ⟨hM, hT, hF⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro p
    show (Nat.shiftRight s.M (h*194)).testBit p = true ↔ (p < (s.L - h)*194 ∧ p % 194 < 97)
    rw [tshr, hM]
    omega
  · intro p hp
    have hp' : (Nat.shiftRight s.T (h*194)).testBit p = true := hp
    show (Nat.shiftRight s.M (h*194)).testBit p = true
    rw [tshr] at hp' ⊢; exact hT _ hp'
  · intro p hp
    have hp' : (Nat.shiftRight s.F (h*194)).testBit p = true := hp
    show (Nat.shiftRight s.M (h*194)).testBit p = true
    rw [tshr] at hp' ⊢; exact hF _ hp'

theorem lo_cons {c : Nat → Bool} {s : St} {h l : Nat} (hc : Cons c s.T s.F l) (hl : l < h) :
    Cons c (lo s h).T (lo s h).F l := by
  intro x hx
  have hlt : l*194 + x < h*194 := by omega
  constructor
  · intro hb
    have hb' : (s.T % 2^(h*194)).testBit (l*194+x) = true := hb
    rw [testBit_mod_pow, Bool.and_eq_true] at hb'
    exact (hc x hx).1 hb'.2
  · intro hb
    have hb' : (s.F % 2^(h*194)).testBit (l*194+x) = true := hb
    rw [testBit_mod_pow, Bool.and_eq_true] at hb'
    exact (hc x hx).2 hb'.2

theorem hi_cons {c : Nat → Bool} {s : St} {h l : Nat} (hc : Cons c s.T s.F l) (hl : h ≤ l) :
    Cons c (hi s h).T (hi s h).F (l - h) := by
  intro x hx
  have he : h*194 + ((l-h)*194 + x) = l*194 + x := by omega
  constructor
  · intro hb
    have hb' : (Nat.shiftRight s.T (h*194)).testBit ((l-h)*194+x) = true := hb
    rw [tshr, he] at hb'
    exact (hc x hx).1 hb'
  · intro hb
    have hb' : (Nat.shiftRight s.F (h*194)).testBit ((l-h)*194+x) = true := hb
    rw [tshr, he] at hb'
    exact (hc x hx).2 hb'

theorem comb_inv {a b : St} (ha : Inv a) (hb : Inv b) : Inv (comb a b) := by
  obtain ⟨haM, haT, haF⟩ := ha
  obtain ⟨hbM, hbT, hbF⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · intro p
    show (Nat.lor a.M (Nat.shiftLeft b.M (a.L*194))).testBit p = true ↔ (p < (a.L + b.L)*194 ∧ p % 194 < 97)
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, haM, hbM]
    omega
  · intro p hp
    have hp' : (Nat.lor a.T (Nat.shiftLeft b.T (a.L*194))).testBit p = true := hp
    show (Nat.lor a.M (Nat.shiftLeft b.M (a.L*194))).testBit p = true
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true] at hp' ⊢
    rcases hp' with hp' | hp'
    · exact Or.inl (haT p hp')
    · exact Or.inr ⟨hp'.1, hbT _ hp'.2⟩
  · intro p hp
    have hp' : (Nat.lor a.F (Nat.shiftLeft b.F (a.L*194))).testBit p = true := hp
    show (Nat.lor a.M (Nat.shiftLeft b.M (a.L*194))).testBit p = true
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true] at hp' ⊢
    rcases hp' with hp' | hp'
    · exact Or.inl (haF p hp')
    · exact Or.inr ⟨hp'.1, hbF _ hp'.2⟩

theorem comb_lo {c : Nat → Bool} {a b : St} {l : Nat} (hl : l < a.L) (hc : Cons c a.T a.F l) :
    Cons c (comb a b).T (comb a b).F l := by
  intro x hx
  have hlt : l*194 + x < a.L*194 := by omega
  constructor
  · intro hb
    have hb' : (Nat.lor a.T (Nat.shiftLeft b.T (a.L*194))).testBit (l*194+x) = true := hb
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb'
    rcases hb' with hb' | hb'
    · exact (hc x hx).1 hb'
    · omega
  · intro hb
    have hb' : (Nat.lor a.F (Nat.shiftLeft b.F (a.L*194))).testBit (l*194+x) = true := hb
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb'
    rcases hb' with hb' | hb'
    · exact (hc x hx).2 hb'
    · omega

theorem comb_hi {c : Nat → Bool} {a b : St} {l : Nat} (ha : Inv a) (hc : Cons c b.T b.F l) :
    Cons c (comb a b).T (comb a b).F (a.L + l) := by
  obtain ⟨haM, haT, haF⟩ := ha
  intro x hx
  have he : (a.L + l)*194 + x - a.L*194 = l*194 + x := by omega
  constructor
  · intro hb
    have hb' : (Nat.lor a.T (Nat.shiftLeft b.T (a.L*194))).testBit ((a.L+l)*194+x) = true := hb
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb'
    rcases hb' with hb' | hb'
    · have := ((haM _).1 (haT _ hb')).1; omega
    · rw [he] at hb'; exact (hc x hx).1 hb'.2
  · intro hb
    have hb' : (Nat.lor a.F (Nat.shiftLeft b.F (a.L*194))).testBit ((a.L+l)*194+x) = true := hb
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb'
    rcases hb' with hb' | hb'
    · have := ((haM _).1 (haF _ hb')).1; omega
    · rw [he] at hb'; exact (hc x hx).2 hb'.2

theorem compact_succ (n : Nat) (s : St) : compact (n+1) s =
    (cond (Nat.beq s.L 0) ⟨0, 0, 0, 0⟩ <|
      cond (Nat.beq s.L 1) (cond (Nat.beq (Nat.land s.T s.F) 0) s ⟨0, 0, 0, 0⟩) <|
      comb (compact n (lo s (s.L / 2))) (compact n (hi s (s.L / 2)))) := rfl

theorem compact_inv : ∀ fuel (s : St), Inv s → Inv (compact fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro s hs; exact hs
  | succ n ih =>
    intro s hs
    rw [compact_succ]
    cases Nat.beq s.L 0
    · cases Nat.beq s.L 1
      · exact comb_inv (ih _ (lo_inv hs (by omega))) (ih _ (hi_inv hs (by omega)))
      · cases Nat.beq (Nat.land s.T s.F) 0
        · exact inv_zero
        · exact hs
    · exact inv_zero

theorem compact_cons {c : Nat → Bool} : ∀ fuel (s : St), Inv s → ∀ l < s.L, Cons c s.T s.F l →
    ∃ l' < (compact fuel s).L, Cons c (compact fuel s).T (compact fuel s).F l' := by
  intro fuel
  induction fuel with
  | zero => intro s _ l hl hc; exact ⟨l, hl, hc⟩
  | succ n ih =>
    intro s hs l hl hc
    rw [compact_succ, beq_f (show s.L ≠ 0 by omega), cond_false]
    by_cases hL1 : s.L = 1
    · rw [beq_t hL1, cond_true]
      have hz : Nat.beq (Nat.land s.T s.F) 0 = true := by
        apply beq_t
        apply Nat.eq_of_testBit_eq
        intro p
        rw [tland, Nat.zero_testBit]
        cases h1 : s.T.testBit p <;> cases h2 : s.F.testBit p <;> simp
        have hm := (hs.1 p).1 (hs.2.1 p h1)
        have hl0 : l = 0 := by omega
        subst hl0
        have hp : p < 97 := by omega
        have a1 := (hc p hp).1 (by simpa using h1)
        have a2 := (hc p hp).2 (by simpa using h2)
        simp_all
      rw [hz, cond_true]
      exact ⟨l, hl, hc⟩
    · rw [beq_f hL1, cond_false]
      rcases Nat.lt_or_ge l (s.L / 2) with hlh | hlh
      · obtain ⟨l', hl', hc'⟩ := ih _ (lo_inv hs (by omega)) l hlh (lo_cons hc hlh)
        exact ⟨l', by show l' < _ + _; omega, comb_lo hl' hc'⟩
      · obtain ⟨l', hl', hc'⟩ := ih _ (hi_inv hs (by omega)) (l - s.L / 2)
          (by show l - s.L / 2 < s.L - s.L / 2; omega) (hi_cons hc hlh)
        exact ⟨_ + l', by show _ + l' < _ + _; omega,
          comb_hi (compact_inv n _ (lo_inv hs (by omega))) hc'⟩

end OMA.VDWL

namespace OMA.VDWL

theorem step_eq (v : Nat) (s : St) : step v s =
    compact 64 ⟨(prop (2*(s.L * 194) + 194) (Nat.lor s.M (Nat.shiftLeft s.M (s.L * 194))) 97
        (Nat.lor (Nat.lor s.T (Nat.shiftLeft (Nat.xor s.M (Nat.land s.M (Nat.shiftLeft s.M 1))) v))
          (Nat.shiftLeft s.T (s.L * 194)))
        (Nat.lor s.F (Nat.shiftLeft (Nat.lor s.F (Nat.shiftLeft (Nat.xor s.M (Nat.land s.M (Nat.shiftLeft s.M 1))) v))
          (s.L * 194)))).1,
      (prop (2*(s.L * 194) + 194) (Nat.lor s.M (Nat.shiftLeft s.M (s.L * 194))) 97
        (Nat.lor (Nat.lor s.T (Nat.shiftLeft (Nat.xor s.M (Nat.land s.M (Nat.shiftLeft s.M 1))) v))
          (Nat.shiftLeft s.T (s.L * 194)))
        (Nat.lor s.F (Nat.shiftLeft (Nat.lor s.F (Nat.shiftLeft (Nat.xor s.M (Nat.land s.M (Nat.shiftLeft s.M 1))) v))
          (s.L * 194)))).2,
      Nat.lor s.M (Nat.shiftLeft s.M (s.L * 194)), 2 * s.L⟩ := rfl

theorem V_bit {M L : Nat} (hM : MaskOK M L) (v q : Nat) (hv : v < 97) :
    (Nat.shiftLeft (Nat.xor M (Nat.land M (Nat.shiftLeft M 1))) v).testBit q = true ↔
      (v ≤ q ∧ q - v < L*194 ∧ (q - v) % 194 = 0) := by
  rw [tshl, txor, tland, tshl]
  cases h1 : M.testBit (q - v) <;> cases h2 : M.testBit (q - v - 1) <;>
    have e1 := hM (q - v) <;> have e2 := hM (q - v - 1) <;> simp_all <;> omega

theorem step_sound {c : Nat → Bool} (hg : Good c) {v : Nat} (hv : v < 97) {s : St} (hs : Inv s)
    {l : Nat} (hl : l < s.L) (hc : Cons c s.T s.F l) :
    Inv (step v s) ∧ ∃ l' < (step v s).L, Cons c (step v s).T (step v s).F l' := by
  obtain ⟨hM, hT, hF⟩ := hs
  have hTl : ∀ p, s.T.testBit p = true → p < s.L*194 ∧ p % 194 < 97 := fun p h => (hM p).1 (hT p h)
  have hFl : ∀ p, s.F.testBit p = true → p < s.L*194 ∧ p % 194 < 97 := fun p h => (hM p).1 (hF p h)
  have hV := V_bit hM v
  rw [step_eq]
  generalize Nat.shiftLeft (Nat.xor s.M (Nat.land s.M (Nat.shiftLeft s.M 1))) v = V at hV
  have hM1 : MaskOK (Nat.lor s.M (Nat.shiftLeft s.M (s.L * 194))) (2 * s.L) := by
    intro p
    rw [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hM, hM]
    omega
  have hT1 : ∀ p, (Nat.lor (Nat.lor s.T V) (Nat.shiftLeft s.T (s.L * 194))).testBit p = true →
      (Nat.lor s.M (Nat.shiftLeft s.M (s.L * 194))).testBit p = true := by
    intro p hp
    rw [hM1]
    rw [tlor, tlor, tshl, Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases hp with (hp | hp) | hp
    · have := hTl p hp; omega
    · have := (hV p hv).1 hp; omega
    · have := hTl _ hp.2; omega
  have hF1 : ∀ p, (Nat.lor s.F (Nat.shiftLeft (Nat.lor s.F V) (s.L * 194))).testBit p = true →
      (Nat.lor s.M (Nat.shiftLeft s.M (s.L * 194))).testBit p = true := by
    intro p hp
    rw [hM1]
    simp only [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases hp with hp | ⟨hp0, hp | hp⟩
    · have := hFl p hp; omega
    · have := hFl _ hp; omega
    · have := (hV _ hv).1 hp; omega
  have hc1 : ∃ l1 < 2 * s.L, Cons c (Nat.lor (Nat.lor s.T V) (Nat.shiftLeft s.T (s.L * 194)))
      (Nat.lor s.F (Nat.shiftLeft (Nat.lor s.F V) (s.L * 194))) l1 := by
    cases hcv : c v
    · refine ⟨s.L + l, by omega, ?_⟩
      intro x hx
      constructor
      · intro hb
        rw [tlor, tlor, tshl, Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
        rcases hb with (hb | hb) | hb
        · have := hTl _ hb; omega
        · have := (hV _ hv).1 hb; omega
        · exact consT hc hx (by omega) hb.2
      · intro hb
        simp only [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
        rcases hb with hb | ⟨hb0, hb | hb⟩
        · have := hFl _ hb; omega
        · exact consF hc hx (by omega) hb
        · have := (hV _ hv).1 hb
          have : x = v := by omega
          subst this; exact hcv
    · refine ⟨l, by omega, ?_⟩
      intro x hx
      constructor
      · intro hb
        rw [tlor, tlor, tshl, Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
        rcases hb with (hb | hb) | hb
        · exact (hc x hx).1 hb
        · have := (hV _ hv).1 hb
          have : x = v := by omega
          subst this; exact hcv
        · omega
      · intro hb
        simp only [tlor, tshl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
        rcases hb with hb | ⟨hb0, hb | hb⟩
        · exact (hc x hx).2 hb
        · omega
        · omega
  obtain ⟨l1, hl1, hc1⟩ := hc1
  obtain ⟨hpT, hpF, hpc⟩ := prop_sound hg hM1 (S := 2*(s.L * 194) + 194) 97 _ _ hT1 hF1 hc1
  have hI : Inv ⟨_, _, Nat.lor s.M (Nat.shiftLeft s.M (s.L * 194)), 2 * s.L⟩ := ⟨hM1, hpT, hpF⟩
  exact ⟨compact_inv 64 _ hI, compact_cons 64 _ hI l1 hl1 hpc⟩

theorem go_sound {c : Nat → Bool} (hg : Good c) : ∀ (o : List Nat) (s : St), Inv s → ∀ l < s.L,
    Cons c s.T s.F l → Inv (go o s) ∧ ∃ l' < (go o s).L, Cons c (go o s).T (go o s).F l' := by
  intro o
  induction o with
  | nil => intro s hs l hl hc; exact ⟨hs, l, hl, hc⟩
  | cons v vs ih =>
    intro s hs l hl hc
    show Inv (cond (Nat.blt v 97) (go vs (step v s)) s) ∧
      ∃ l' < (cond (Nat.blt v 97) (go vs (step v s)) s).L,
        Cons c (cond (Nat.blt v 97) (go vs (step v s)) s).T (cond (Nat.blt v 97) (go vs (step v s)) s).F l'
    cases hb : Nat.blt v 97
    · exact ⟨hs, l, hl, hc⟩
    · have hv : v < 97 := Nat.blt_eq.mp hb
      obtain ⟨hs', l', hl', hc'⟩ := step_sound hg hv hs hl hc
      exact ih _ hs' l' hl' hc'

theorem inv_init : Inv init := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    show (2 ^ 97 - 1).testBit p = true ↔ _
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    show p < 97 ↔ p < 1 * 194 ∧ p % 194 < 97
    omega
  · intro p h; simp [init] at h
  · intro p h; simp [init] at h

theorem cons_init (c : Nat → Bool) : Cons c init.T init.F 0 := by
  intro x _
  constructor
  · intro h; simp [init] at h
  · intro h; simp [init] at h

theorem sub_inv {s : St} (hs : Inv s) {a : Nat} (ha : a < s.L) : Inv (sub s a) := by
  obtain ⟨hM, hT, hF⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro p
    show ((s.M >>> (a*194)) % 2^194).testBit p = true ↔ (p < 1*194 ∧ p % 194 < 97)
    rw [testBit_mod_pow, Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_eq, hM]
    omega
  · intro p hp
    have hp' : ((s.T >>> (a*194)) % 2^194).testBit p = true := hp
    show ((s.M >>> (a*194)) % 2^194).testBit p = true
    rw [testBit_mod_pow, Nat.testBit_shiftRight, Bool.and_eq_true] at hp' ⊢
    exact ⟨hp'.1, hT _ hp'.2⟩
  · intro p hp
    have hp' : ((s.F >>> (a*194)) % 2^194).testBit p = true := hp
    show ((s.M >>> (a*194)) % 2^194).testBit p = true
    rw [testBit_mod_pow, Nat.testBit_shiftRight, Bool.and_eq_true] at hp' ⊢
    exact ⟨hp'.1, hF _ hp'.2⟩

theorem sub_cons {c : Nat → Bool} {s : St} {a : Nat} (hc : Cons c s.T s.F a) :
    Cons c (sub s a).T (sub s a).F 0 := by
  intro x hx
  constructor
  · intro hb
    have hb' : ((s.T >>> (a*194)) % 2^194).testBit (0*194 + x) = true := hb
    rw [testBit_mod_pow, Nat.testBit_shiftRight, Bool.and_eq_true] at hb'
    exact consT hc hx (by omega) hb'.2
  · intro hb
    have hb' : ((s.F >>> (a*194)) % 2^194).testBit (0*194 + x) = true := hb
    rw [testBit_mod_pow, Nat.testBit_shiftRight, Bool.and_eq_true] at hb'
    exact consF hc hx (by omega) hb'.2

def Ref (s : St) : Prop := ∀ c, Good c → Inv s → ∀ l < s.L, Cons c s.T s.F l → False

theorem ref_go {o : List Nat} {s : St} (h : Nat.beq (go o s).L 0 = true) : Ref s := by
  intro c hg hs l hl hc
  obtain ⟨_, l', hl', _⟩ := go_sound hg o s hs l hl hc
  have := Nat.eq_of_beq_eq_true h
  omega

theorem ref_split {o : List Nat} {s : St} {K : Nat} (hK : (go o s).L ≤ K)
    (h : ∀ l < K, Ref (sub (go o s) l)) : Ref s := by
  intro c hg hs l hl hc
  obtain ⟨hs', l', hl', hc'⟩ := go_sound hg o s hs l hl hc
  exact h l' (by omega) c hg (sub_inv hs' hl') 0 (by show 0 < 1; omega) (sub_cons hc')

theorem upd {P : Nat → Prop} {k : Nat} (h : ∀ l < k, P l) (hk : P k) : ∀ l < k + 1, P l := by
  intro l hl
  rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
  · exact h l hl
  · subst hl; exact hk

theorem up0 {P : Nat → Prop} : ∀ l < 0, P l := fun l h => absurd h (Nat.not_lt_zero l)

def o0_3 : List Nat := [48, 47, 49]
def o3_6 : List Nat := [46, 50, 45]
def o6_9 : List Nat := [51, 44, 52]
def o9_12 : List Nat := [43, 53, 42]
def o12_97 : List Nat := [54, 41, 55, 40, 56, 39, 57, 38, 58, 37, 59, 36, 60, 35, 61, 34, 62, 33, 63, 32, 64, 31, 65, 30, 66, 29, 67, 28, 68, 27, 69, 26, 70, 25, 71, 24, 72, 23, 73, 22, 74, 21, 75, 20, 76, 19, 77, 18, 78, 17, 79, 16, 80, 15, 81, 14, 82, 13, 83, 12, 84, 11, 85, 10, 86, 9, 87, 8, 88, 7, 89, 6, 90, 5, 91, 4, 92, 3, 93, 2, 94, 1, 95, 0, 96]
def o9_97 : List Nat := [43, 53, 42, 54, 41, 55, 40, 56, 39, 57, 38, 58, 37, 59, 36, 60, 35, 61, 34, 62, 33, 63, 32, 64, 31, 65, 30, 66, 29, 67, 28, 68, 27, 69, 26, 70, 25, 71, 24, 72, 23, 73, 22, 74, 21, 75, 20, 76, 19, 77, 18, 78, 17, 79, 16, 80, 15, 81, 14, 82, 13, 83, 12, 84, 11, 85, 10, 86, 9, 87, 8, 88, 7, 89, 6, 90, 5, 91, 4, 92, 3, 93, 2, 94, 1, 95, 0, 96]
def o6_97 : List Nat := [51, 44, 52, 43, 53, 42, 54, 41, 55, 40, 56, 39, 57, 38, 58, 37, 59, 36, 60, 35, 61, 34, 62, 33, 63, 32, 64, 31, 65, 30, 66, 29, 67, 28, 68, 27, 69, 26, 70, 25, 71, 24, 72, 23, 73, 22, 74, 21, 75, 20, 76, 19, 77, 18, 78, 17, 79, 16, 80, 15, 81, 14, 82, 13, 83, 12, 84, 11, 85, 10, 86, 9, 87, 8, 88, 7, 89, 6, 90, 5, 91, 4, 92, 3, 93, 2, 94, 1, 95, 0, 96]
def o12_15 : List Nat := [54, 41, 55]
def o15_97 : List Nat := [40, 56, 39, 57, 38, 58, 37, 59, 36, 60, 35, 61, 34, 62, 33, 63, 32, 64, 31, 65, 30, 66, 29, 67, 28, 68, 27, 69, 26, 70, 25, 71, 24, 72, 23, 73, 22, 74, 21, 75, 20, 76, 19, 77, 18, 78, 17, 79, 16, 80, 15, 81, 14, 82, 13, 83, 12, 84, 11, 85, 10, 86, 9, 87, 8, 88, 7, 89, 6, 90, 5, 91, 4, 92, 3, 93, 2, 94, 1, 95, 0, 96]
noncomputable def X0 : St := go o0_3 (init)
noncomputable def X1 : St := go o3_6 (sub X0 0)
noncomputable def X2 : St := go o6_9 (sub X1 0)
noncomputable def X3 : St := go o9_12 (sub X2 0)
noncomputable def X6 : St := go o9_12 (sub X2 1)
noncomputable def X15 : St := go o9_12 (sub X2 2)
noncomputable def X22 : St := go o9_12 (sub X2 3)
noncomputable def X28 : St := go o9_12 (sub X2 4)
noncomputable def X35 : St := go o9_12 (sub X2 5)
noncomputable def X42 : St := go o6_9 (sub X1 1)
noncomputable def X43 : St := go o9_12 (sub X42 0)
noncomputable def X59 : St := go o6_9 (sub X1 2)
noncomputable def X60 : St := go o9_12 (sub X59 0)
noncomputable def X69 : St := go o9_12 (sub X59 1)
noncomputable def X82 : St := go o6_9 (sub X1 3)
noncomputable def X89 : St := go o6_9 (sub X1 4)
noncomputable def X90 : St := go o9_12 (sub X89 0)
noncomputable def X100 : St := go o9_12 (sub X89 2)
noncomputable def X106 : St := go o9_12 (sub X89 4)
noncomputable def X118 : St := go o6_9 (sub X1 5)
noncomputable def X119 : St := go o9_12 (sub X118 0)
noncomputable def X131 : St := go o6_9 (sub X1 6)
noncomputable def X139 : St := go o3_6 (sub X0 1)
noncomputable def X140 : St := go o6_9 (sub X139 0)
noncomputable def X141 : St := go o9_12 (sub X140 0)
noncomputable def X142 : St := go o12_15 (sub X141 0)
noncomputable def X159 : St := go o6_9 (sub X139 1)
noncomputable def X160 : St := go o9_12 (sub X159 0)
noncomputable def X170 : St := go o6_9 (sub X139 2)
noncomputable def X171 : St := go o9_12 (sub X170 0)
noncomputable def X181 : St := go o6_9 (sub X139 3)
noncomputable def X187 : St := go o3_6 (sub X0 2)
noncomputable def X188 : St := go o6_9 (sub X187 0)
noncomputable def X189 : St := go o9_12 (sub X188 0)
noncomputable def X190 : St := go o12_15 (sub X189 0)
noncomputable def X213 : St := go o6_9 (sub X187 1)
noncomputable def X214 : St := go o9_12 (sub X213 0)
noncomputable def X230 : St := go o6_9 (sub X187 2)
noncomputable def X235 : St := go o6_9 (sub X187 4)
noncomputable def X245 : St := go o3_6 (sub X0 3)
noncomputable def X246 : St := go o6_9 (sub X245 0)
noncomputable def X247 : St := go o9_12 (sub X246 0)
noncomputable def X262 : St := go o3_6 (sub X0 4)
noncomputable def X263 : St := go o6_9 (sub X262 0)
noncomputable def X264 : St := go o9_12 (sub X263 0)
noncomputable def X281 : St := go o6_9 (sub X262 2)
noncomputable def X282 : St := go o9_12 (sub X281 0)
noncomputable def X295 : St := go o6_9 (sub X262 4)
noncomputable def X307 : St := go o3_6 (sub X0 5)
noncomputable def X308 : St := go o6_9 (sub X307 0)
noncomputable def X309 : St := go o9_12 (sub X308 0)
noncomputable def X324 : St := go o3_6 (sub X0 6)
noncomputable def X325 : St := go o6_9 (sub X324 0)
noncomputable def X326 : St := go o9_12 (sub X325 0)
theorem R4 : Ref (sub X3 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R5 : Ref (sub X3 1) := ref_go (o := o12_97) (by decide +kernel)
theorem C3_0 : ∀ l < 0, Ref (sub X3 l) := up0
theorem C3_1 : ∀ l < 1, Ref (sub X3 l) := upd C3_0 R4
theorem C3_2 : ∀ l < 2, Ref (sub X3 l) := upd C3_1 R5
theorem K3 : X3.L ≤ 2 := by decide +kernel
theorem R3 : Ref (sub X2 0) := ref_split (o := o9_12) K3 C3_2
theorem R7 : Ref (sub X6 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R8 : Ref (sub X6 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R9 : Ref (sub X6 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R10 : Ref (sub X6 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R11 : Ref (sub X6 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R12 : Ref (sub X6 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R13 : Ref (sub X6 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R14 : Ref (sub X6 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C6_0 : ∀ l < 0, Ref (sub X6 l) := up0
theorem C6_1 : ∀ l < 1, Ref (sub X6 l) := upd C6_0 R7
theorem C6_2 : ∀ l < 2, Ref (sub X6 l) := upd C6_1 R8
theorem C6_3 : ∀ l < 3, Ref (sub X6 l) := upd C6_2 R9
theorem C6_4 : ∀ l < 4, Ref (sub X6 l) := upd C6_3 R10
theorem C6_5 : ∀ l < 5, Ref (sub X6 l) := upd C6_4 R11
theorem C6_6 : ∀ l < 6, Ref (sub X6 l) := upd C6_5 R12
theorem C6_7 : ∀ l < 7, Ref (sub X6 l) := upd C6_6 R13
theorem C6_8 : ∀ l < 8, Ref (sub X6 l) := upd C6_7 R14
theorem K6 : X6.L ≤ 8 := by decide +kernel
theorem R6 : Ref (sub X2 1) := ref_split (o := o9_12) K6 C6_8
theorem R16 : Ref (sub X15 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R17 : Ref (sub X15 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R18 : Ref (sub X15 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R19 : Ref (sub X15 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R20 : Ref (sub X15 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R21 : Ref (sub X15 5) := ref_go (o := o12_97) (by decide +kernel)
theorem C15_0 : ∀ l < 0, Ref (sub X15 l) := up0
theorem C15_1 : ∀ l < 1, Ref (sub X15 l) := upd C15_0 R16
theorem C15_2 : ∀ l < 2, Ref (sub X15 l) := upd C15_1 R17
theorem C15_3 : ∀ l < 3, Ref (sub X15 l) := upd C15_2 R18
theorem C15_4 : ∀ l < 4, Ref (sub X15 l) := upd C15_3 R19
theorem C15_5 : ∀ l < 5, Ref (sub X15 l) := upd C15_4 R20
theorem C15_6 : ∀ l < 6, Ref (sub X15 l) := upd C15_5 R21
theorem K15 : X15.L ≤ 6 := by decide +kernel
theorem R15 : Ref (sub X2 2) := ref_split (o := o9_12) K15 C15_6
theorem R23 : Ref (sub X22 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R24 : Ref (sub X22 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R25 : Ref (sub X22 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R26 : Ref (sub X22 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R27 : Ref (sub X22 4) := ref_go (o := o12_97) (by decide +kernel)
theorem C22_0 : ∀ l < 0, Ref (sub X22 l) := up0
theorem C22_1 : ∀ l < 1, Ref (sub X22 l) := upd C22_0 R23
theorem C22_2 : ∀ l < 2, Ref (sub X22 l) := upd C22_1 R24
theorem C22_3 : ∀ l < 3, Ref (sub X22 l) := upd C22_2 R25
theorem C22_4 : ∀ l < 4, Ref (sub X22 l) := upd C22_3 R26
theorem C22_5 : ∀ l < 5, Ref (sub X22 l) := upd C22_4 R27
theorem K22 : X22.L ≤ 5 := by decide +kernel
theorem R22 : Ref (sub X2 3) := ref_split (o := o9_12) K22 C22_5
theorem R29 : Ref (sub X28 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R30 : Ref (sub X28 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R31 : Ref (sub X28 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R32 : Ref (sub X28 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R33 : Ref (sub X28 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R34 : Ref (sub X28 5) := ref_go (o := o12_97) (by decide +kernel)
theorem C28_0 : ∀ l < 0, Ref (sub X28 l) := up0
theorem C28_1 : ∀ l < 1, Ref (sub X28 l) := upd C28_0 R29
theorem C28_2 : ∀ l < 2, Ref (sub X28 l) := upd C28_1 R30
theorem C28_3 : ∀ l < 3, Ref (sub X28 l) := upd C28_2 R31
theorem C28_4 : ∀ l < 4, Ref (sub X28 l) := upd C28_3 R32
theorem C28_5 : ∀ l < 5, Ref (sub X28 l) := upd C28_4 R33
theorem C28_6 : ∀ l < 6, Ref (sub X28 l) := upd C28_5 R34
theorem K28 : X28.L ≤ 6 := by decide +kernel
theorem R28 : Ref (sub X2 4) := ref_split (o := o9_12) K28 C28_6
theorem R36 : Ref (sub X35 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R37 : Ref (sub X35 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R38 : Ref (sub X35 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R39 : Ref (sub X35 3) := ref_go (o := o12_97) (by decide +kernel)
theorem C35_0 : ∀ l < 0, Ref (sub X35 l) := up0
theorem C35_1 : ∀ l < 1, Ref (sub X35 l) := upd C35_0 R36
theorem C35_2 : ∀ l < 2, Ref (sub X35 l) := upd C35_1 R37
theorem C35_3 : ∀ l < 3, Ref (sub X35 l) := upd C35_2 R38
theorem C35_4 : ∀ l < 4, Ref (sub X35 l) := upd C35_3 R39
theorem K35 : X35.L ≤ 4 := by decide +kernel
theorem R35 : Ref (sub X2 5) := ref_split (o := o9_12) K35 C35_4
theorem R40 : Ref (sub X2 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R41 : Ref (sub X2 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C2_0 : ∀ l < 0, Ref (sub X2 l) := up0
theorem C2_1 : ∀ l < 1, Ref (sub X2 l) := upd C2_0 R3
theorem C2_2 : ∀ l < 2, Ref (sub X2 l) := upd C2_1 R6
theorem C2_3 : ∀ l < 3, Ref (sub X2 l) := upd C2_2 R15
theorem C2_4 : ∀ l < 4, Ref (sub X2 l) := upd C2_3 R22
theorem C2_5 : ∀ l < 5, Ref (sub X2 l) := upd C2_4 R28
theorem C2_6 : ∀ l < 6, Ref (sub X2 l) := upd C2_5 R35
theorem C2_7 : ∀ l < 7, Ref (sub X2 l) := upd C2_6 R40
theorem C2_8 : ∀ l < 8, Ref (sub X2 l) := upd C2_7 R41
theorem K2 : X2.L ≤ 8 := by decide +kernel
theorem R2 : Ref (sub X1 0) := ref_split (o := o6_9) K2 C2_8
theorem R44 : Ref (sub X43 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R45 : Ref (sub X43 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R46 : Ref (sub X43 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R47 : Ref (sub X43 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R48 : Ref (sub X43 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R49 : Ref (sub X43 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R50 : Ref (sub X43 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R51 : Ref (sub X43 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C43_0 : ∀ l < 0, Ref (sub X43 l) := up0
theorem C43_1 : ∀ l < 1, Ref (sub X43 l) := upd C43_0 R44
theorem C43_2 : ∀ l < 2, Ref (sub X43 l) := upd C43_1 R45
theorem C43_3 : ∀ l < 3, Ref (sub X43 l) := upd C43_2 R46
theorem C43_4 : ∀ l < 4, Ref (sub X43 l) := upd C43_3 R47
theorem C43_5 : ∀ l < 5, Ref (sub X43 l) := upd C43_4 R48
theorem C43_6 : ∀ l < 6, Ref (sub X43 l) := upd C43_5 R49
theorem C43_7 : ∀ l < 7, Ref (sub X43 l) := upd C43_6 R50
theorem C43_8 : ∀ l < 8, Ref (sub X43 l) := upd C43_7 R51
theorem K43 : X43.L ≤ 8 := by decide +kernel
theorem R43 : Ref (sub X42 0) := ref_split (o := o9_12) K43 C43_8
theorem R52 : Ref (sub X42 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R53 : Ref (sub X42 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R54 : Ref (sub X42 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R55 : Ref (sub X42 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R56 : Ref (sub X42 5) := ref_go (o := o9_97) (by decide +kernel)
theorem R57 : Ref (sub X42 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R58 : Ref (sub X42 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C42_0 : ∀ l < 0, Ref (sub X42 l) := up0
theorem C42_1 : ∀ l < 1, Ref (sub X42 l) := upd C42_0 R43
theorem C42_2 : ∀ l < 2, Ref (sub X42 l) := upd C42_1 R52
theorem C42_3 : ∀ l < 3, Ref (sub X42 l) := upd C42_2 R53
theorem C42_4 : ∀ l < 4, Ref (sub X42 l) := upd C42_3 R54
theorem C42_5 : ∀ l < 5, Ref (sub X42 l) := upd C42_4 R55
theorem C42_6 : ∀ l < 6, Ref (sub X42 l) := upd C42_5 R56
theorem C42_7 : ∀ l < 7, Ref (sub X42 l) := upd C42_6 R57
theorem C42_8 : ∀ l < 8, Ref (sub X42 l) := upd C42_7 R58
theorem K42 : X42.L ≤ 8 := by decide +kernel
theorem R42 : Ref (sub X1 1) := ref_split (o := o6_9) K42 C42_8
theorem R61 : Ref (sub X60 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R62 : Ref (sub X60 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R63 : Ref (sub X60 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R64 : Ref (sub X60 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R65 : Ref (sub X60 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R66 : Ref (sub X60 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R67 : Ref (sub X60 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R68 : Ref (sub X60 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C60_0 : ∀ l < 0, Ref (sub X60 l) := up0
theorem C60_1 : ∀ l < 1, Ref (sub X60 l) := upd C60_0 R61
theorem C60_2 : ∀ l < 2, Ref (sub X60 l) := upd C60_1 R62
theorem C60_3 : ∀ l < 3, Ref (sub X60 l) := upd C60_2 R63
theorem C60_4 : ∀ l < 4, Ref (sub X60 l) := upd C60_3 R64
theorem C60_5 : ∀ l < 5, Ref (sub X60 l) := upd C60_4 R65
theorem C60_6 : ∀ l < 6, Ref (sub X60 l) := upd C60_5 R66
theorem C60_7 : ∀ l < 7, Ref (sub X60 l) := upd C60_6 R67
theorem C60_8 : ∀ l < 8, Ref (sub X60 l) := upd C60_7 R68
theorem K60 : X60.L ≤ 8 := by decide +kernel
theorem R60 : Ref (sub X59 0) := ref_split (o := o9_12) K60 C60_8
theorem R70 : Ref (sub X69 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R71 : Ref (sub X69 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R72 : Ref (sub X69 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R73 : Ref (sub X69 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R74 : Ref (sub X69 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R75 : Ref (sub X69 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R76 : Ref (sub X69 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R77 : Ref (sub X69 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C69_0 : ∀ l < 0, Ref (sub X69 l) := up0
theorem C69_1 : ∀ l < 1, Ref (sub X69 l) := upd C69_0 R70
theorem C69_2 : ∀ l < 2, Ref (sub X69 l) := upd C69_1 R71
theorem C69_3 : ∀ l < 3, Ref (sub X69 l) := upd C69_2 R72
theorem C69_4 : ∀ l < 4, Ref (sub X69 l) := upd C69_3 R73
theorem C69_5 : ∀ l < 5, Ref (sub X69 l) := upd C69_4 R74
theorem C69_6 : ∀ l < 6, Ref (sub X69 l) := upd C69_5 R75
theorem C69_7 : ∀ l < 7, Ref (sub X69 l) := upd C69_6 R76
theorem C69_8 : ∀ l < 8, Ref (sub X69 l) := upd C69_7 R77
theorem K69 : X69.L ≤ 8 := by decide +kernel
theorem R69 : Ref (sub X59 1) := ref_split (o := o9_12) K69 C69_8
theorem R78 : Ref (sub X59 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R79 : Ref (sub X59 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R80 : Ref (sub X59 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R81 : Ref (sub X59 5) := ref_go (o := o9_97) (by decide +kernel)
theorem C59_0 : ∀ l < 0, Ref (sub X59 l) := up0
theorem C59_1 : ∀ l < 1, Ref (sub X59 l) := upd C59_0 R60
theorem C59_2 : ∀ l < 2, Ref (sub X59 l) := upd C59_1 R69
theorem C59_3 : ∀ l < 3, Ref (sub X59 l) := upd C59_2 R78
theorem C59_4 : ∀ l < 4, Ref (sub X59 l) := upd C59_3 R79
theorem C59_5 : ∀ l < 5, Ref (sub X59 l) := upd C59_4 R80
theorem C59_6 : ∀ l < 6, Ref (sub X59 l) := upd C59_5 R81
theorem K59 : X59.L ≤ 6 := by decide +kernel
theorem R59 : Ref (sub X1 2) := ref_split (o := o6_9) K59 C59_6
theorem R83 : Ref (sub X82 0) := ref_go (o := o9_97) (by decide +kernel)
theorem R84 : Ref (sub X82 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R85 : Ref (sub X82 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R86 : Ref (sub X82 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R87 : Ref (sub X82 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R88 : Ref (sub X82 5) := ref_go (o := o9_97) (by decide +kernel)
theorem C82_0 : ∀ l < 0, Ref (sub X82 l) := up0
theorem C82_1 : ∀ l < 1, Ref (sub X82 l) := upd C82_0 R83
theorem C82_2 : ∀ l < 2, Ref (sub X82 l) := upd C82_1 R84
theorem C82_3 : ∀ l < 3, Ref (sub X82 l) := upd C82_2 R85
theorem C82_4 : ∀ l < 4, Ref (sub X82 l) := upd C82_3 R86
theorem C82_5 : ∀ l < 5, Ref (sub X82 l) := upd C82_4 R87
theorem C82_6 : ∀ l < 6, Ref (sub X82 l) := upd C82_5 R88
theorem K82 : X82.L ≤ 6 := by decide +kernel
theorem R82 : Ref (sub X1 3) := ref_split (o := o6_9) K82 C82_6
theorem R91 : Ref (sub X90 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R92 : Ref (sub X90 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R93 : Ref (sub X90 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R94 : Ref (sub X90 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R95 : Ref (sub X90 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R96 : Ref (sub X90 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R97 : Ref (sub X90 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R98 : Ref (sub X90 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C90_0 : ∀ l < 0, Ref (sub X90 l) := up0
theorem C90_1 : ∀ l < 1, Ref (sub X90 l) := upd C90_0 R91
theorem C90_2 : ∀ l < 2, Ref (sub X90 l) := upd C90_1 R92
theorem C90_3 : ∀ l < 3, Ref (sub X90 l) := upd C90_2 R93
theorem C90_4 : ∀ l < 4, Ref (sub X90 l) := upd C90_3 R94
theorem C90_5 : ∀ l < 5, Ref (sub X90 l) := upd C90_4 R95
theorem C90_6 : ∀ l < 6, Ref (sub X90 l) := upd C90_5 R96
theorem C90_7 : ∀ l < 7, Ref (sub X90 l) := upd C90_6 R97
theorem C90_8 : ∀ l < 8, Ref (sub X90 l) := upd C90_7 R98
theorem K90 : X90.L ≤ 8 := by decide +kernel
theorem R90 : Ref (sub X89 0) := ref_split (o := o9_12) K90 C90_8
theorem R99 : Ref (sub X89 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R101 : Ref (sub X100 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R102 : Ref (sub X100 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R103 : Ref (sub X100 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R104 : Ref (sub X100 3) := ref_go (o := o12_97) (by decide +kernel)
theorem C100_0 : ∀ l < 0, Ref (sub X100 l) := up0
theorem C100_1 : ∀ l < 1, Ref (sub X100 l) := upd C100_0 R101
theorem C100_2 : ∀ l < 2, Ref (sub X100 l) := upd C100_1 R102
theorem C100_3 : ∀ l < 3, Ref (sub X100 l) := upd C100_2 R103
theorem C100_4 : ∀ l < 4, Ref (sub X100 l) := upd C100_3 R104
theorem K100 : X100.L ≤ 4 := by decide +kernel
theorem R100 : Ref (sub X89 2) := ref_split (o := o9_12) K100 C100_4
theorem R105 : Ref (sub X89 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R107 : Ref (sub X106 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R108 : Ref (sub X106 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R109 : Ref (sub X106 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R110 : Ref (sub X106 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R111 : Ref (sub X106 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R112 : Ref (sub X106 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R113 : Ref (sub X106 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R114 : Ref (sub X106 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C106_0 : ∀ l < 0, Ref (sub X106 l) := up0
theorem C106_1 : ∀ l < 1, Ref (sub X106 l) := upd C106_0 R107
theorem C106_2 : ∀ l < 2, Ref (sub X106 l) := upd C106_1 R108
theorem C106_3 : ∀ l < 3, Ref (sub X106 l) := upd C106_2 R109
theorem C106_4 : ∀ l < 4, Ref (sub X106 l) := upd C106_3 R110
theorem C106_5 : ∀ l < 5, Ref (sub X106 l) := upd C106_4 R111
theorem C106_6 : ∀ l < 6, Ref (sub X106 l) := upd C106_5 R112
theorem C106_7 : ∀ l < 7, Ref (sub X106 l) := upd C106_6 R113
theorem C106_8 : ∀ l < 8, Ref (sub X106 l) := upd C106_7 R114
theorem K106 : X106.L ≤ 8 := by decide +kernel
theorem R106 : Ref (sub X89 4) := ref_split (o := o9_12) K106 C106_8
theorem R115 : Ref (sub X89 5) := ref_go (o := o9_97) (by decide +kernel)
theorem R116 : Ref (sub X89 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R117 : Ref (sub X89 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C89_0 : ∀ l < 0, Ref (sub X89 l) := up0
theorem C89_1 : ∀ l < 1, Ref (sub X89 l) := upd C89_0 R90
theorem C89_2 : ∀ l < 2, Ref (sub X89 l) := upd C89_1 R99
theorem C89_3 : ∀ l < 3, Ref (sub X89 l) := upd C89_2 R100
theorem C89_4 : ∀ l < 4, Ref (sub X89 l) := upd C89_3 R105
theorem C89_5 : ∀ l < 5, Ref (sub X89 l) := upd C89_4 R106
theorem C89_6 : ∀ l < 6, Ref (sub X89 l) := upd C89_5 R115
theorem C89_7 : ∀ l < 7, Ref (sub X89 l) := upd C89_6 R116
theorem C89_8 : ∀ l < 8, Ref (sub X89 l) := upd C89_7 R117
theorem K89 : X89.L ≤ 8 := by decide +kernel
theorem R89 : Ref (sub X1 4) := ref_split (o := o6_9) K89 C89_8
theorem R120 : Ref (sub X119 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R121 : Ref (sub X119 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R122 : Ref (sub X119 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R123 : Ref (sub X119 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R124 : Ref (sub X119 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R125 : Ref (sub X119 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R126 : Ref (sub X119 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R127 : Ref (sub X119 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C119_0 : ∀ l < 0, Ref (sub X119 l) := up0
theorem C119_1 : ∀ l < 1, Ref (sub X119 l) := upd C119_0 R120
theorem C119_2 : ∀ l < 2, Ref (sub X119 l) := upd C119_1 R121
theorem C119_3 : ∀ l < 3, Ref (sub X119 l) := upd C119_2 R122
theorem C119_4 : ∀ l < 4, Ref (sub X119 l) := upd C119_3 R123
theorem C119_5 : ∀ l < 5, Ref (sub X119 l) := upd C119_4 R124
theorem C119_6 : ∀ l < 6, Ref (sub X119 l) := upd C119_5 R125
theorem C119_7 : ∀ l < 7, Ref (sub X119 l) := upd C119_6 R126
theorem C119_8 : ∀ l < 8, Ref (sub X119 l) := upd C119_7 R127
theorem K119 : X119.L ≤ 8 := by decide +kernel
theorem R119 : Ref (sub X118 0) := ref_split (o := o9_12) K119 C119_8
theorem R128 : Ref (sub X118 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R129 : Ref (sub X118 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R130 : Ref (sub X118 3) := ref_go (o := o9_97) (by decide +kernel)
theorem C118_0 : ∀ l < 0, Ref (sub X118 l) := up0
theorem C118_1 : ∀ l < 1, Ref (sub X118 l) := upd C118_0 R119
theorem C118_2 : ∀ l < 2, Ref (sub X118 l) := upd C118_1 R128
theorem C118_3 : ∀ l < 3, Ref (sub X118 l) := upd C118_2 R129
theorem C118_4 : ∀ l < 4, Ref (sub X118 l) := upd C118_3 R130
theorem K118 : X118.L ≤ 4 := by decide +kernel
theorem R118 : Ref (sub X1 5) := ref_split (o := o6_9) K118 C118_4
theorem R132 : Ref (sub X131 0) := ref_go (o := o9_97) (by decide +kernel)
theorem R133 : Ref (sub X131 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R134 : Ref (sub X131 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R135 : Ref (sub X131 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R136 : Ref (sub X131 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R137 : Ref (sub X131 5) := ref_go (o := o9_97) (by decide +kernel)
theorem C131_0 : ∀ l < 0, Ref (sub X131 l) := up0
theorem C131_1 : ∀ l < 1, Ref (sub X131 l) := upd C131_0 R132
theorem C131_2 : ∀ l < 2, Ref (sub X131 l) := upd C131_1 R133
theorem C131_3 : ∀ l < 3, Ref (sub X131 l) := upd C131_2 R134
theorem C131_4 : ∀ l < 4, Ref (sub X131 l) := upd C131_3 R135
theorem C131_5 : ∀ l < 5, Ref (sub X131 l) := upd C131_4 R136
theorem C131_6 : ∀ l < 6, Ref (sub X131 l) := upd C131_5 R137
theorem K131 : X131.L ≤ 6 := by decide +kernel
theorem R131 : Ref (sub X1 6) := ref_split (o := o6_9) K131 C131_6
theorem R138 : Ref (sub X1 7) := ref_go (o := o6_97) (by decide +kernel)
theorem C1_0 : ∀ l < 0, Ref (sub X1 l) := up0
theorem C1_1 : ∀ l < 1, Ref (sub X1 l) := upd C1_0 R2
theorem C1_2 : ∀ l < 2, Ref (sub X1 l) := upd C1_1 R42
theorem C1_3 : ∀ l < 3, Ref (sub X1 l) := upd C1_2 R59
theorem C1_4 : ∀ l < 4, Ref (sub X1 l) := upd C1_3 R82
theorem C1_5 : ∀ l < 5, Ref (sub X1 l) := upd C1_4 R89
theorem C1_6 : ∀ l < 6, Ref (sub X1 l) := upd C1_5 R118
theorem C1_7 : ∀ l < 7, Ref (sub X1 l) := upd C1_6 R131
theorem C1_8 : ∀ l < 8, Ref (sub X1 l) := upd C1_7 R138
theorem K1 : X1.L ≤ 8 := by decide +kernel
theorem R1 : Ref (sub X0 0) := ref_split (o := o3_6) K1 C1_8
theorem R143 : Ref (sub X142 0) := ref_go (o := o15_97) (by decide +kernel)
theorem R144 : Ref (sub X142 1) := ref_go (o := o15_97) (by decide +kernel)
theorem R145 : Ref (sub X142 2) := ref_go (o := o15_97) (by decide +kernel)
theorem R146 : Ref (sub X142 3) := ref_go (o := o15_97) (by decide +kernel)
theorem R147 : Ref (sub X142 4) := ref_go (o := o15_97) (by decide +kernel)
theorem R148 : Ref (sub X142 5) := ref_go (o := o15_97) (by decide +kernel)
theorem C142_0 : ∀ l < 0, Ref (sub X142 l) := up0
theorem C142_1 : ∀ l < 1, Ref (sub X142 l) := upd C142_0 R143
theorem C142_2 : ∀ l < 2, Ref (sub X142 l) := upd C142_1 R144
theorem C142_3 : ∀ l < 3, Ref (sub X142 l) := upd C142_2 R145
theorem C142_4 : ∀ l < 4, Ref (sub X142 l) := upd C142_3 R146
theorem C142_5 : ∀ l < 5, Ref (sub X142 l) := upd C142_4 R147
theorem C142_6 : ∀ l < 6, Ref (sub X142 l) := upd C142_5 R148
theorem K142 : X142.L ≤ 6 := by decide +kernel
theorem R142 : Ref (sub X141 0) := ref_split (o := o12_15) K142 C142_6
theorem R149 : Ref (sub X141 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R150 : Ref (sub X141 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R151 : Ref (sub X141 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R152 : Ref (sub X141 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R153 : Ref (sub X141 5) := ref_go (o := o12_97) (by decide +kernel)
theorem C141_0 : ∀ l < 0, Ref (sub X141 l) := up0
theorem C141_1 : ∀ l < 1, Ref (sub X141 l) := upd C141_0 R142
theorem C141_2 : ∀ l < 2, Ref (sub X141 l) := upd C141_1 R149
theorem C141_3 : ∀ l < 3, Ref (sub X141 l) := upd C141_2 R150
theorem C141_4 : ∀ l < 4, Ref (sub X141 l) := upd C141_3 R151
theorem C141_5 : ∀ l < 5, Ref (sub X141 l) := upd C141_4 R152
theorem C141_6 : ∀ l < 6, Ref (sub X141 l) := upd C141_5 R153
theorem K141 : X141.L ≤ 6 := by decide +kernel
theorem R141 : Ref (sub X140 0) := ref_split (o := o9_12) K141 C141_6
theorem R154 : Ref (sub X140 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R155 : Ref (sub X140 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R156 : Ref (sub X140 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R157 : Ref (sub X140 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R158 : Ref (sub X140 5) := ref_go (o := o9_97) (by decide +kernel)
theorem C140_0 : ∀ l < 0, Ref (sub X140 l) := up0
theorem C140_1 : ∀ l < 1, Ref (sub X140 l) := upd C140_0 R141
theorem C140_2 : ∀ l < 2, Ref (sub X140 l) := upd C140_1 R154
theorem C140_3 : ∀ l < 3, Ref (sub X140 l) := upd C140_2 R155
theorem C140_4 : ∀ l < 4, Ref (sub X140 l) := upd C140_3 R156
theorem C140_5 : ∀ l < 5, Ref (sub X140 l) := upd C140_4 R157
theorem C140_6 : ∀ l < 6, Ref (sub X140 l) := upd C140_5 R158
theorem K140 : X140.L ≤ 6 := by decide +kernel
theorem R140 : Ref (sub X139 0) := ref_split (o := o6_9) K140 C140_6
theorem R161 : Ref (sub X160 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R162 : Ref (sub X160 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R163 : Ref (sub X160 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R164 : Ref (sub X160 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R165 : Ref (sub X160 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R166 : Ref (sub X160 5) := ref_go (o := o12_97) (by decide +kernel)
theorem C160_0 : ∀ l < 0, Ref (sub X160 l) := up0
theorem C160_1 : ∀ l < 1, Ref (sub X160 l) := upd C160_0 R161
theorem C160_2 : ∀ l < 2, Ref (sub X160 l) := upd C160_1 R162
theorem C160_3 : ∀ l < 3, Ref (sub X160 l) := upd C160_2 R163
theorem C160_4 : ∀ l < 4, Ref (sub X160 l) := upd C160_3 R164
theorem C160_5 : ∀ l < 5, Ref (sub X160 l) := upd C160_4 R165
theorem C160_6 : ∀ l < 6, Ref (sub X160 l) := upd C160_5 R166
theorem K160 : X160.L ≤ 6 := by decide +kernel
theorem R160 : Ref (sub X159 0) := ref_split (o := o9_12) K160 C160_6
theorem R167 : Ref (sub X159 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R168 : Ref (sub X159 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R169 : Ref (sub X159 3) := ref_go (o := o9_97) (by decide +kernel)
theorem C159_0 : ∀ l < 0, Ref (sub X159 l) := up0
theorem C159_1 : ∀ l < 1, Ref (sub X159 l) := upd C159_0 R160
theorem C159_2 : ∀ l < 2, Ref (sub X159 l) := upd C159_1 R167
theorem C159_3 : ∀ l < 3, Ref (sub X159 l) := upd C159_2 R168
theorem C159_4 : ∀ l < 4, Ref (sub X159 l) := upd C159_3 R169
theorem K159 : X159.L ≤ 4 := by decide +kernel
theorem R159 : Ref (sub X139 1) := ref_split (o := o6_9) K159 C159_4
theorem R172 : Ref (sub X171 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R173 : Ref (sub X171 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R174 : Ref (sub X171 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R175 : Ref (sub X171 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R176 : Ref (sub X171 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R177 : Ref (sub X171 5) := ref_go (o := o12_97) (by decide +kernel)
theorem C171_0 : ∀ l < 0, Ref (sub X171 l) := up0
theorem C171_1 : ∀ l < 1, Ref (sub X171 l) := upd C171_0 R172
theorem C171_2 : ∀ l < 2, Ref (sub X171 l) := upd C171_1 R173
theorem C171_3 : ∀ l < 3, Ref (sub X171 l) := upd C171_2 R174
theorem C171_4 : ∀ l < 4, Ref (sub X171 l) := upd C171_3 R175
theorem C171_5 : ∀ l < 5, Ref (sub X171 l) := upd C171_4 R176
theorem C171_6 : ∀ l < 6, Ref (sub X171 l) := upd C171_5 R177
theorem K171 : X171.L ≤ 6 := by decide +kernel
theorem R171 : Ref (sub X170 0) := ref_split (o := o9_12) K171 C171_6
theorem R178 : Ref (sub X170 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R179 : Ref (sub X170 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R180 : Ref (sub X170 3) := ref_go (o := o9_97) (by decide +kernel)
theorem C170_0 : ∀ l < 0, Ref (sub X170 l) := up0
theorem C170_1 : ∀ l < 1, Ref (sub X170 l) := upd C170_0 R171
theorem C170_2 : ∀ l < 2, Ref (sub X170 l) := upd C170_1 R178
theorem C170_3 : ∀ l < 3, Ref (sub X170 l) := upd C170_2 R179
theorem C170_4 : ∀ l < 4, Ref (sub X170 l) := upd C170_3 R180
theorem K170 : X170.L ≤ 4 := by decide +kernel
theorem R170 : Ref (sub X139 2) := ref_split (o := o6_9) K170 C170_4
theorem R182 : Ref (sub X181 0) := ref_go (o := o9_97) (by decide +kernel)
theorem R183 : Ref (sub X181 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R184 : Ref (sub X181 2) := ref_go (o := o9_97) (by decide +kernel)
theorem C181_0 : ∀ l < 0, Ref (sub X181 l) := up0
theorem C181_1 : ∀ l < 1, Ref (sub X181 l) := upd C181_0 R182
theorem C181_2 : ∀ l < 2, Ref (sub X181 l) := upd C181_1 R183
theorem C181_3 : ∀ l < 3, Ref (sub X181 l) := upd C181_2 R184
theorem K181 : X181.L ≤ 3 := by decide +kernel
theorem R181 : Ref (sub X139 3) := ref_split (o := o6_9) K181 C181_3
theorem R185 : Ref (sub X139 4) := ref_go (o := o6_97) (by decide +kernel)
theorem R186 : Ref (sub X139 5) := ref_go (o := o6_97) (by decide +kernel)
theorem C139_0 : ∀ l < 0, Ref (sub X139 l) := up0
theorem C139_1 : ∀ l < 1, Ref (sub X139 l) := upd C139_0 R140
theorem C139_2 : ∀ l < 2, Ref (sub X139 l) := upd C139_1 R159
theorem C139_3 : ∀ l < 3, Ref (sub X139 l) := upd C139_2 R170
theorem C139_4 : ∀ l < 4, Ref (sub X139 l) := upd C139_3 R181
theorem C139_5 : ∀ l < 5, Ref (sub X139 l) := upd C139_4 R185
theorem C139_6 : ∀ l < 6, Ref (sub X139 l) := upd C139_5 R186
theorem K139 : X139.L ≤ 6 := by decide +kernel
theorem R139 : Ref (sub X0 1) := ref_split (o := o3_6) K139 C139_6
theorem R191 : Ref (sub X190 0) := ref_go (o := o15_97) (by decide +kernel)
theorem R192 : Ref (sub X190 1) := ref_go (o := o15_97) (by decide +kernel)
theorem R193 : Ref (sub X190 2) := ref_go (o := o15_97) (by decide +kernel)
theorem R194 : Ref (sub X190 3) := ref_go (o := o15_97) (by decide +kernel)
theorem R195 : Ref (sub X190 4) := ref_go (o := o15_97) (by decide +kernel)
theorem R196 : Ref (sub X190 5) := ref_go (o := o15_97) (by decide +kernel)
theorem R197 : Ref (sub X190 6) := ref_go (o := o15_97) (by decide +kernel)
theorem R198 : Ref (sub X190 7) := ref_go (o := o15_97) (by decide +kernel)
theorem C190_0 : ∀ l < 0, Ref (sub X190 l) := up0
theorem C190_1 : ∀ l < 1, Ref (sub X190 l) := upd C190_0 R191
theorem C190_2 : ∀ l < 2, Ref (sub X190 l) := upd C190_1 R192
theorem C190_3 : ∀ l < 3, Ref (sub X190 l) := upd C190_2 R193
theorem C190_4 : ∀ l < 4, Ref (sub X190 l) := upd C190_3 R194
theorem C190_5 : ∀ l < 5, Ref (sub X190 l) := upd C190_4 R195
theorem C190_6 : ∀ l < 6, Ref (sub X190 l) := upd C190_5 R196
theorem C190_7 : ∀ l < 7, Ref (sub X190 l) := upd C190_6 R197
theorem C190_8 : ∀ l < 8, Ref (sub X190 l) := upd C190_7 R198
theorem K190 : X190.L ≤ 8 := by decide +kernel
theorem R190 : Ref (sub X189 0) := ref_split (o := o12_15) K190 C190_8
theorem R199 : Ref (sub X189 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R200 : Ref (sub X189 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R201 : Ref (sub X189 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R202 : Ref (sub X189 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R203 : Ref (sub X189 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R204 : Ref (sub X189 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R205 : Ref (sub X189 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C189_0 : ∀ l < 0, Ref (sub X189 l) := up0
theorem C189_1 : ∀ l < 1, Ref (sub X189 l) := upd C189_0 R190
theorem C189_2 : ∀ l < 2, Ref (sub X189 l) := upd C189_1 R199
theorem C189_3 : ∀ l < 3, Ref (sub X189 l) := upd C189_2 R200
theorem C189_4 : ∀ l < 4, Ref (sub X189 l) := upd C189_3 R201
theorem C189_5 : ∀ l < 5, Ref (sub X189 l) := upd C189_4 R202
theorem C189_6 : ∀ l < 6, Ref (sub X189 l) := upd C189_5 R203
theorem C189_7 : ∀ l < 7, Ref (sub X189 l) := upd C189_6 R204
theorem C189_8 : ∀ l < 8, Ref (sub X189 l) := upd C189_7 R205
theorem K189 : X189.L ≤ 8 := by decide +kernel
theorem R189 : Ref (sub X188 0) := ref_split (o := o9_12) K189 C189_8
theorem R206 : Ref (sub X188 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R207 : Ref (sub X188 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R208 : Ref (sub X188 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R209 : Ref (sub X188 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R210 : Ref (sub X188 5) := ref_go (o := o9_97) (by decide +kernel)
theorem R211 : Ref (sub X188 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R212 : Ref (sub X188 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C188_0 : ∀ l < 0, Ref (sub X188 l) := up0
theorem C188_1 : ∀ l < 1, Ref (sub X188 l) := upd C188_0 R189
theorem C188_2 : ∀ l < 2, Ref (sub X188 l) := upd C188_1 R206
theorem C188_3 : ∀ l < 3, Ref (sub X188 l) := upd C188_2 R207
theorem C188_4 : ∀ l < 4, Ref (sub X188 l) := upd C188_3 R208
theorem C188_5 : ∀ l < 5, Ref (sub X188 l) := upd C188_4 R209
theorem C188_6 : ∀ l < 6, Ref (sub X188 l) := upd C188_5 R210
theorem C188_7 : ∀ l < 7, Ref (sub X188 l) := upd C188_6 R211
theorem C188_8 : ∀ l < 8, Ref (sub X188 l) := upd C188_7 R212
theorem K188 : X188.L ≤ 8 := by decide +kernel
theorem R188 : Ref (sub X187 0) := ref_split (o := o6_9) K188 C188_8
theorem R215 : Ref (sub X214 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R216 : Ref (sub X214 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R217 : Ref (sub X214 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R218 : Ref (sub X214 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R219 : Ref (sub X214 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R220 : Ref (sub X214 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R221 : Ref (sub X214 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R222 : Ref (sub X214 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C214_0 : ∀ l < 0, Ref (sub X214 l) := up0
theorem C214_1 : ∀ l < 1, Ref (sub X214 l) := upd C214_0 R215
theorem C214_2 : ∀ l < 2, Ref (sub X214 l) := upd C214_1 R216
theorem C214_3 : ∀ l < 3, Ref (sub X214 l) := upd C214_2 R217
theorem C214_4 : ∀ l < 4, Ref (sub X214 l) := upd C214_3 R218
theorem C214_5 : ∀ l < 5, Ref (sub X214 l) := upd C214_4 R219
theorem C214_6 : ∀ l < 6, Ref (sub X214 l) := upd C214_5 R220
theorem C214_7 : ∀ l < 7, Ref (sub X214 l) := upd C214_6 R221
theorem C214_8 : ∀ l < 8, Ref (sub X214 l) := upd C214_7 R222
theorem K214 : X214.L ≤ 8 := by decide +kernel
theorem R214 : Ref (sub X213 0) := ref_split (o := o9_12) K214 C214_8
theorem R223 : Ref (sub X213 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R224 : Ref (sub X213 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R225 : Ref (sub X213 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R226 : Ref (sub X213 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R227 : Ref (sub X213 5) := ref_go (o := o9_97) (by decide +kernel)
theorem R228 : Ref (sub X213 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R229 : Ref (sub X213 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C213_0 : ∀ l < 0, Ref (sub X213 l) := up0
theorem C213_1 : ∀ l < 1, Ref (sub X213 l) := upd C213_0 R214
theorem C213_2 : ∀ l < 2, Ref (sub X213 l) := upd C213_1 R223
theorem C213_3 : ∀ l < 3, Ref (sub X213 l) := upd C213_2 R224
theorem C213_4 : ∀ l < 4, Ref (sub X213 l) := upd C213_3 R225
theorem C213_5 : ∀ l < 5, Ref (sub X213 l) := upd C213_4 R226
theorem C213_6 : ∀ l < 6, Ref (sub X213 l) := upd C213_5 R227
theorem C213_7 : ∀ l < 7, Ref (sub X213 l) := upd C213_6 R228
theorem C213_8 : ∀ l < 8, Ref (sub X213 l) := upd C213_7 R229
theorem K213 : X213.L ≤ 8 := by decide +kernel
theorem R213 : Ref (sub X187 1) := ref_split (o := o6_9) K213 C213_8
theorem R231 : Ref (sub X230 0) := ref_go (o := o9_97) (by decide +kernel)
theorem R232 : Ref (sub X230 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R233 : Ref (sub X230 2) := ref_go (o := o9_97) (by decide +kernel)
theorem C230_0 : ∀ l < 0, Ref (sub X230 l) := up0
theorem C230_1 : ∀ l < 1, Ref (sub X230 l) := upd C230_0 R231
theorem C230_2 : ∀ l < 2, Ref (sub X230 l) := upd C230_1 R232
theorem C230_3 : ∀ l < 3, Ref (sub X230 l) := upd C230_2 R233
theorem K230 : X230.L ≤ 3 := by decide +kernel
theorem R230 : Ref (sub X187 2) := ref_split (o := o6_9) K230 C230_3
theorem R234 : Ref (sub X187 3) := ref_go (o := o6_97) (by decide +kernel)
theorem R236 : Ref (sub X235 0) := ref_go (o := o9_97) (by decide +kernel)
theorem R237 : Ref (sub X235 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R238 : Ref (sub X235 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R239 : Ref (sub X235 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R240 : Ref (sub X235 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R241 : Ref (sub X235 5) := ref_go (o := o9_97) (by decide +kernel)
theorem R242 : Ref (sub X235 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R243 : Ref (sub X235 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C235_0 : ∀ l < 0, Ref (sub X235 l) := up0
theorem C235_1 : ∀ l < 1, Ref (sub X235 l) := upd C235_0 R236
theorem C235_2 : ∀ l < 2, Ref (sub X235 l) := upd C235_1 R237
theorem C235_3 : ∀ l < 3, Ref (sub X235 l) := upd C235_2 R238
theorem C235_4 : ∀ l < 4, Ref (sub X235 l) := upd C235_3 R239
theorem C235_5 : ∀ l < 5, Ref (sub X235 l) := upd C235_4 R240
theorem C235_6 : ∀ l < 6, Ref (sub X235 l) := upd C235_5 R241
theorem C235_7 : ∀ l < 7, Ref (sub X235 l) := upd C235_6 R242
theorem C235_8 : ∀ l < 8, Ref (sub X235 l) := upd C235_7 R243
theorem K235 : X235.L ≤ 8 := by decide +kernel
theorem R235 : Ref (sub X187 4) := ref_split (o := o6_9) K235 C235_8
theorem R244 : Ref (sub X187 5) := ref_go (o := o6_97) (by decide +kernel)
theorem C187_0 : ∀ l < 0, Ref (sub X187 l) := up0
theorem C187_1 : ∀ l < 1, Ref (sub X187 l) := upd C187_0 R188
theorem C187_2 : ∀ l < 2, Ref (sub X187 l) := upd C187_1 R213
theorem C187_3 : ∀ l < 3, Ref (sub X187 l) := upd C187_2 R230
theorem C187_4 : ∀ l < 4, Ref (sub X187 l) := upd C187_3 R234
theorem C187_5 : ∀ l < 5, Ref (sub X187 l) := upd C187_4 R235
theorem C187_6 : ∀ l < 6, Ref (sub X187 l) := upd C187_5 R244
theorem K187 : X187.L ≤ 6 := by decide +kernel
theorem R187 : Ref (sub X0 2) := ref_split (o := o3_6) K187 C187_6
theorem R248 : Ref (sub X247 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R249 : Ref (sub X247 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R250 : Ref (sub X247 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R251 : Ref (sub X247 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R252 : Ref (sub X247 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R253 : Ref (sub X247 5) := ref_go (o := o12_97) (by decide +kernel)
theorem C247_0 : ∀ l < 0, Ref (sub X247 l) := up0
theorem C247_1 : ∀ l < 1, Ref (sub X247 l) := upd C247_0 R248
theorem C247_2 : ∀ l < 2, Ref (sub X247 l) := upd C247_1 R249
theorem C247_3 : ∀ l < 3, Ref (sub X247 l) := upd C247_2 R250
theorem C247_4 : ∀ l < 4, Ref (sub X247 l) := upd C247_3 R251
theorem C247_5 : ∀ l < 5, Ref (sub X247 l) := upd C247_4 R252
theorem C247_6 : ∀ l < 6, Ref (sub X247 l) := upd C247_5 R253
theorem K247 : X247.L ≤ 6 := by decide +kernel
theorem R247 : Ref (sub X246 0) := ref_split (o := o9_12) K247 C247_6
theorem R254 : Ref (sub X246 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R255 : Ref (sub X246 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R256 : Ref (sub X246 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R257 : Ref (sub X246 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R258 : Ref (sub X246 5) := ref_go (o := o9_97) (by decide +kernel)
theorem C246_0 : ∀ l < 0, Ref (sub X246 l) := up0
theorem C246_1 : ∀ l < 1, Ref (sub X246 l) := upd C246_0 R247
theorem C246_2 : ∀ l < 2, Ref (sub X246 l) := upd C246_1 R254
theorem C246_3 : ∀ l < 3, Ref (sub X246 l) := upd C246_2 R255
theorem C246_4 : ∀ l < 4, Ref (sub X246 l) := upd C246_3 R256
theorem C246_5 : ∀ l < 5, Ref (sub X246 l) := upd C246_4 R257
theorem C246_6 : ∀ l < 6, Ref (sub X246 l) := upd C246_5 R258
theorem K246 : X246.L ≤ 6 := by decide +kernel
theorem R246 : Ref (sub X245 0) := ref_split (o := o6_9) K246 C246_6
theorem R259 : Ref (sub X245 1) := ref_go (o := o6_97) (by decide +kernel)
theorem R260 : Ref (sub X245 2) := ref_go (o := o6_97) (by decide +kernel)
theorem R261 : Ref (sub X245 3) := ref_go (o := o6_97) (by decide +kernel)
theorem C245_0 : ∀ l < 0, Ref (sub X245 l) := up0
theorem C245_1 : ∀ l < 1, Ref (sub X245 l) := upd C245_0 R246
theorem C245_2 : ∀ l < 2, Ref (sub X245 l) := upd C245_1 R259
theorem C245_3 : ∀ l < 3, Ref (sub X245 l) := upd C245_2 R260
theorem C245_4 : ∀ l < 4, Ref (sub X245 l) := upd C245_3 R261
theorem K245 : X245.L ≤ 4 := by decide +kernel
theorem R245 : Ref (sub X0 3) := ref_split (o := o3_6) K245 C245_4
theorem R265 : Ref (sub X264 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R266 : Ref (sub X264 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R267 : Ref (sub X264 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R268 : Ref (sub X264 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R269 : Ref (sub X264 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R270 : Ref (sub X264 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R271 : Ref (sub X264 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R272 : Ref (sub X264 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C264_0 : ∀ l < 0, Ref (sub X264 l) := up0
theorem C264_1 : ∀ l < 1, Ref (sub X264 l) := upd C264_0 R265
theorem C264_2 : ∀ l < 2, Ref (sub X264 l) := upd C264_1 R266
theorem C264_3 : ∀ l < 3, Ref (sub X264 l) := upd C264_2 R267
theorem C264_4 : ∀ l < 4, Ref (sub X264 l) := upd C264_3 R268
theorem C264_5 : ∀ l < 5, Ref (sub X264 l) := upd C264_4 R269
theorem C264_6 : ∀ l < 6, Ref (sub X264 l) := upd C264_5 R270
theorem C264_7 : ∀ l < 7, Ref (sub X264 l) := upd C264_6 R271
theorem C264_8 : ∀ l < 8, Ref (sub X264 l) := upd C264_7 R272
theorem K264 : X264.L ≤ 8 := by decide +kernel
theorem R264 : Ref (sub X263 0) := ref_split (o := o9_12) K264 C264_8
theorem R273 : Ref (sub X263 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R274 : Ref (sub X263 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R275 : Ref (sub X263 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R276 : Ref (sub X263 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R277 : Ref (sub X263 5) := ref_go (o := o9_97) (by decide +kernel)
theorem R278 : Ref (sub X263 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R279 : Ref (sub X263 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C263_0 : ∀ l < 0, Ref (sub X263 l) := up0
theorem C263_1 : ∀ l < 1, Ref (sub X263 l) := upd C263_0 R264
theorem C263_2 : ∀ l < 2, Ref (sub X263 l) := upd C263_1 R273
theorem C263_3 : ∀ l < 3, Ref (sub X263 l) := upd C263_2 R274
theorem C263_4 : ∀ l < 4, Ref (sub X263 l) := upd C263_3 R275
theorem C263_5 : ∀ l < 5, Ref (sub X263 l) := upd C263_4 R276
theorem C263_6 : ∀ l < 6, Ref (sub X263 l) := upd C263_5 R277
theorem C263_7 : ∀ l < 7, Ref (sub X263 l) := upd C263_6 R278
theorem C263_8 : ∀ l < 8, Ref (sub X263 l) := upd C263_7 R279
theorem K263 : X263.L ≤ 8 := by decide +kernel
theorem R263 : Ref (sub X262 0) := ref_split (o := o6_9) K263 C263_8
theorem R280 : Ref (sub X262 1) := ref_go (o := o6_97) (by decide +kernel)
theorem R283 : Ref (sub X282 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R284 : Ref (sub X282 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R285 : Ref (sub X282 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R286 : Ref (sub X282 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R287 : Ref (sub X282 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R288 : Ref (sub X282 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R289 : Ref (sub X282 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R290 : Ref (sub X282 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C282_0 : ∀ l < 0, Ref (sub X282 l) := up0
theorem C282_1 : ∀ l < 1, Ref (sub X282 l) := upd C282_0 R283
theorem C282_2 : ∀ l < 2, Ref (sub X282 l) := upd C282_1 R284
theorem C282_3 : ∀ l < 3, Ref (sub X282 l) := upd C282_2 R285
theorem C282_4 : ∀ l < 4, Ref (sub X282 l) := upd C282_3 R286
theorem C282_5 : ∀ l < 5, Ref (sub X282 l) := upd C282_4 R287
theorem C282_6 : ∀ l < 6, Ref (sub X282 l) := upd C282_5 R288
theorem C282_7 : ∀ l < 7, Ref (sub X282 l) := upd C282_6 R289
theorem C282_8 : ∀ l < 8, Ref (sub X282 l) := upd C282_7 R290
theorem K282 : X282.L ≤ 8 := by decide +kernel
theorem R282 : Ref (sub X281 0) := ref_split (o := o9_12) K282 C282_8
theorem R291 : Ref (sub X281 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R292 : Ref (sub X281 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R293 : Ref (sub X281 3) := ref_go (o := o9_97) (by decide +kernel)
theorem C281_0 : ∀ l < 0, Ref (sub X281 l) := up0
theorem C281_1 : ∀ l < 1, Ref (sub X281 l) := upd C281_0 R282
theorem C281_2 : ∀ l < 2, Ref (sub X281 l) := upd C281_1 R291
theorem C281_3 : ∀ l < 3, Ref (sub X281 l) := upd C281_2 R292
theorem C281_4 : ∀ l < 4, Ref (sub X281 l) := upd C281_3 R293
theorem K281 : X281.L ≤ 4 := by decide +kernel
theorem R281 : Ref (sub X262 2) := ref_split (o := o6_9) K281 C281_4
theorem R294 : Ref (sub X262 3) := ref_go (o := o6_97) (by decide +kernel)
theorem R296 : Ref (sub X295 0) := ref_go (o := o9_97) (by decide +kernel)
theorem R297 : Ref (sub X295 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R298 : Ref (sub X295 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R299 : Ref (sub X295 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R300 : Ref (sub X295 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R301 : Ref (sub X295 5) := ref_go (o := o9_97) (by decide +kernel)
theorem R302 : Ref (sub X295 6) := ref_go (o := o9_97) (by decide +kernel)
theorem R303 : Ref (sub X295 7) := ref_go (o := o9_97) (by decide +kernel)
theorem C295_0 : ∀ l < 0, Ref (sub X295 l) := up0
theorem C295_1 : ∀ l < 1, Ref (sub X295 l) := upd C295_0 R296
theorem C295_2 : ∀ l < 2, Ref (sub X295 l) := upd C295_1 R297
theorem C295_3 : ∀ l < 3, Ref (sub X295 l) := upd C295_2 R298
theorem C295_4 : ∀ l < 4, Ref (sub X295 l) := upd C295_3 R299
theorem C295_5 : ∀ l < 5, Ref (sub X295 l) := upd C295_4 R300
theorem C295_6 : ∀ l < 6, Ref (sub X295 l) := upd C295_5 R301
theorem C295_7 : ∀ l < 7, Ref (sub X295 l) := upd C295_6 R302
theorem C295_8 : ∀ l < 8, Ref (sub X295 l) := upd C295_7 R303
theorem K295 : X295.L ≤ 8 := by decide +kernel
theorem R295 : Ref (sub X262 4) := ref_split (o := o6_9) K295 C295_8
theorem R304 : Ref (sub X262 5) := ref_go (o := o6_97) (by decide +kernel)
theorem R305 : Ref (sub X262 6) := ref_go (o := o6_97) (by decide +kernel)
theorem R306 : Ref (sub X262 7) := ref_go (o := o6_97) (by decide +kernel)
theorem C262_0 : ∀ l < 0, Ref (sub X262 l) := up0
theorem C262_1 : ∀ l < 1, Ref (sub X262 l) := upd C262_0 R263
theorem C262_2 : ∀ l < 2, Ref (sub X262 l) := upd C262_1 R280
theorem C262_3 : ∀ l < 3, Ref (sub X262 l) := upd C262_2 R281
theorem C262_4 : ∀ l < 4, Ref (sub X262 l) := upd C262_3 R294
theorem C262_5 : ∀ l < 5, Ref (sub X262 l) := upd C262_4 R295
theorem C262_6 : ∀ l < 6, Ref (sub X262 l) := upd C262_5 R304
theorem C262_7 : ∀ l < 7, Ref (sub X262 l) := upd C262_6 R305
theorem C262_8 : ∀ l < 8, Ref (sub X262 l) := upd C262_7 R306
theorem K262 : X262.L ≤ 8 := by decide +kernel
theorem R262 : Ref (sub X0 4) := ref_split (o := o3_6) K262 C262_8
theorem R310 : Ref (sub X309 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R311 : Ref (sub X309 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R312 : Ref (sub X309 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R313 : Ref (sub X309 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R314 : Ref (sub X309 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R315 : Ref (sub X309 5) := ref_go (o := o12_97) (by decide +kernel)
theorem C309_0 : ∀ l < 0, Ref (sub X309 l) := up0
theorem C309_1 : ∀ l < 1, Ref (sub X309 l) := upd C309_0 R310
theorem C309_2 : ∀ l < 2, Ref (sub X309 l) := upd C309_1 R311
theorem C309_3 : ∀ l < 3, Ref (sub X309 l) := upd C309_2 R312
theorem C309_4 : ∀ l < 4, Ref (sub X309 l) := upd C309_3 R313
theorem C309_5 : ∀ l < 5, Ref (sub X309 l) := upd C309_4 R314
theorem C309_6 : ∀ l < 6, Ref (sub X309 l) := upd C309_5 R315
theorem K309 : X309.L ≤ 6 := by decide +kernel
theorem R309 : Ref (sub X308 0) := ref_split (o := o9_12) K309 C309_6
theorem R316 : Ref (sub X308 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R317 : Ref (sub X308 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R318 : Ref (sub X308 3) := ref_go (o := o9_97) (by decide +kernel)
theorem R319 : Ref (sub X308 4) := ref_go (o := o9_97) (by decide +kernel)
theorem R320 : Ref (sub X308 5) := ref_go (o := o9_97) (by decide +kernel)
theorem C308_0 : ∀ l < 0, Ref (sub X308 l) := up0
theorem C308_1 : ∀ l < 1, Ref (sub X308 l) := upd C308_0 R309
theorem C308_2 : ∀ l < 2, Ref (sub X308 l) := upd C308_1 R316
theorem C308_3 : ∀ l < 3, Ref (sub X308 l) := upd C308_2 R317
theorem C308_4 : ∀ l < 4, Ref (sub X308 l) := upd C308_3 R318
theorem C308_5 : ∀ l < 5, Ref (sub X308 l) := upd C308_4 R319
theorem C308_6 : ∀ l < 6, Ref (sub X308 l) := upd C308_5 R320
theorem K308 : X308.L ≤ 6 := by decide +kernel
theorem R308 : Ref (sub X307 0) := ref_split (o := o6_9) K308 C308_6
theorem R321 : Ref (sub X307 1) := ref_go (o := o6_97) (by decide +kernel)
theorem R322 : Ref (sub X307 2) := ref_go (o := o6_97) (by decide +kernel)
theorem R323 : Ref (sub X307 3) := ref_go (o := o6_97) (by decide +kernel)
theorem C307_0 : ∀ l < 0, Ref (sub X307 l) := up0
theorem C307_1 : ∀ l < 1, Ref (sub X307 l) := upd C307_0 R308
theorem C307_2 : ∀ l < 2, Ref (sub X307 l) := upd C307_1 R321
theorem C307_3 : ∀ l < 3, Ref (sub X307 l) := upd C307_2 R322
theorem C307_4 : ∀ l < 4, Ref (sub X307 l) := upd C307_3 R323
theorem K307 : X307.L ≤ 4 := by decide +kernel
theorem R307 : Ref (sub X0 5) := ref_split (o := o3_6) K307 C307_4
theorem R327 : Ref (sub X326 0) := ref_go (o := o12_97) (by decide +kernel)
theorem R328 : Ref (sub X326 1) := ref_go (o := o12_97) (by decide +kernel)
theorem R329 : Ref (sub X326 2) := ref_go (o := o12_97) (by decide +kernel)
theorem R330 : Ref (sub X326 3) := ref_go (o := o12_97) (by decide +kernel)
theorem R331 : Ref (sub X326 4) := ref_go (o := o12_97) (by decide +kernel)
theorem R332 : Ref (sub X326 5) := ref_go (o := o12_97) (by decide +kernel)
theorem R333 : Ref (sub X326 6) := ref_go (o := o12_97) (by decide +kernel)
theorem R334 : Ref (sub X326 7) := ref_go (o := o12_97) (by decide +kernel)
theorem C326_0 : ∀ l < 0, Ref (sub X326 l) := up0
theorem C326_1 : ∀ l < 1, Ref (sub X326 l) := upd C326_0 R327
theorem C326_2 : ∀ l < 2, Ref (sub X326 l) := upd C326_1 R328
theorem C326_3 : ∀ l < 3, Ref (sub X326 l) := upd C326_2 R329
theorem C326_4 : ∀ l < 4, Ref (sub X326 l) := upd C326_3 R330
theorem C326_5 : ∀ l < 5, Ref (sub X326 l) := upd C326_4 R331
theorem C326_6 : ∀ l < 6, Ref (sub X326 l) := upd C326_5 R332
theorem C326_7 : ∀ l < 7, Ref (sub X326 l) := upd C326_6 R333
theorem C326_8 : ∀ l < 8, Ref (sub X326 l) := upd C326_7 R334
theorem K326 : X326.L ≤ 8 := by decide +kernel
theorem R326 : Ref (sub X325 0) := ref_split (o := o9_12) K326 C326_8
theorem R335 : Ref (sub X325 1) := ref_go (o := o9_97) (by decide +kernel)
theorem R336 : Ref (sub X325 2) := ref_go (o := o9_97) (by decide +kernel)
theorem R337 : Ref (sub X325 3) := ref_go (o := o9_97) (by decide +kernel)
theorem C325_0 : ∀ l < 0, Ref (sub X325 l) := up0
theorem C325_1 : ∀ l < 1, Ref (sub X325 l) := upd C325_0 R326
theorem C325_2 : ∀ l < 2, Ref (sub X325 l) := upd C325_1 R335
theorem C325_3 : ∀ l < 3, Ref (sub X325 l) := upd C325_2 R336
theorem C325_4 : ∀ l < 4, Ref (sub X325 l) := upd C325_3 R337
theorem K325 : X325.L ≤ 4 := by decide +kernel
theorem R325 : Ref (sub X324 0) := ref_split (o := o6_9) K325 C325_4
theorem R338 : Ref (sub X324 1) := ref_go (o := o6_97) (by decide +kernel)
theorem R339 : Ref (sub X324 2) := ref_go (o := o6_97) (by decide +kernel)
theorem R340 : Ref (sub X324 3) := ref_go (o := o6_97) (by decide +kernel)
theorem C324_0 : ∀ l < 0, Ref (sub X324 l) := up0
theorem C324_1 : ∀ l < 1, Ref (sub X324 l) := upd C324_0 R325
theorem C324_2 : ∀ l < 2, Ref (sub X324 l) := upd C324_1 R338
theorem C324_3 : ∀ l < 3, Ref (sub X324 l) := upd C324_2 R339
theorem C324_4 : ∀ l < 4, Ref (sub X324 l) := upd C324_3 R340
theorem K324 : X324.L ≤ 4 := by decide +kernel
theorem R324 : Ref (sub X0 6) := ref_split (o := o3_6) K324 C324_4
theorem C0_0 : ∀ l < 0, Ref (sub X0 l) := up0
theorem C0_1 : ∀ l < 1, Ref (sub X0 l) := upd C0_0 R1
theorem C0_2 : ∀ l < 2, Ref (sub X0 l) := upd C0_1 R139
theorem C0_3 : ∀ l < 3, Ref (sub X0 l) := upd C0_2 R187
theorem C0_4 : ∀ l < 4, Ref (sub X0 l) := upd C0_3 R245
theorem C0_5 : ∀ l < 5, Ref (sub X0 l) := upd C0_4 R262
theorem C0_6 : ∀ l < 6, Ref (sub X0 l) := upd C0_5 R307
theorem C0_7 : ∀ l < 7, Ref (sub X0 l) := upd C0_6 R324
theorem K0 : X0.L ≤ 7 := by decide +kernel
theorem R0 : Ref (init) := ref_split (o := o0_3) K0 C0_7

theorem no_good (c : Nat → Bool) (hg : Good c) : False :=
  R0 c hg inv_init 0 (by show 0 < 1; omega) (cons_init c)

end OMA.VDWL

namespace OMA.VDW
open Set Green14

theorem forced : 97 ∈ Green14.mixedMonoAPGuaranteeSet 3 10 := by
  intro col
  by_contra h
  rw [not_or] at h
  let g : Nat → Bool := fun i => if hi : i < 97 then decide (col ⟨i+1, by constructor <;> omega⟩ = 1) else false
  have g0 : ∀ i (hi : i < 97), g i = false → col ⟨i+1, by constructor <;> omega⟩ = 0 := by
    intro i hi hg
    have : ¬ col ⟨i+1, by constructor <;> omega⟩ = 1 := by
      simpa [g, hi] using hg
    exact (show ∀ x : Fin 2, ¬ x = 1 → x = 0 by decide) _ this
  have g1 : ∀ i (hi : i < 97), g i = true → col ⟨i+1, by constructor <;> omega⟩ = 1 := by
    intro i hi hg
    simpa [g, hi] using hg
  apply OMA.VDWL.no_good g
  constructor
  · intro a d hd had
    by_contra hcon
    simp only [not_or, Bool.not_eq_true] at hcon
    apply h.1
    apply progression_at (k := 3) (d := d) (a := a) hd col 0
    · intro i
      have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
      omega
    · intro i hi
      apply g0 _ hi
      have hi3 := i.isLt
      rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with e | e | e <;> rw [e]
      · simpa using hcon.1
      · simpa using hcon.2.1
      · exact hcon.2.2
  · intro a d hd had
    by_contra hcon
    simp only [not_exists, not_and, Bool.not_eq_false] at hcon
    apply h.2
    apply progression_at (k := 10) (d := d) (a := a) hd col 1
    · intro i
      have := Nat.mul_le_mul_right d (show i.val ≤ 10 - 1 by omega)
      omega
    · intro i hi
      exact g1 _ hi (hcon i.val i.isLt)

end OMA.VDW

namespace OMA.GreenCertificate
def red : Nat := 0x4033030805008406609080
def blue : Nat := (2^96-1) ^^^ red
def coloring (i : Nat) : Bool := !(red.testBit i)
end OMA.GreenCertificate

open Green14.FunctionCertificateBridge OMA.GreenCertificate in
theorem OMA.solution : type_of% @Green14.W_3_10 := by
  apply le_antisymm (Nat.sInf_le OMA.VDW.forced)
  apply Green14.W_ge_succ_of_not_mem 3 10 96 ⟨_, OMA.VDW.forced⟩
  intro h
  rcases h (certificateColoring 96 coloring) with hr | hb
  · apply no_monoAP_of_hasAP_eq_false (k := 3) (color := false) (mask := red)
      (by decide) (by decide +kernel) ?_ hr
    intro i _ hi
    simpa [coloring] using hi
  · apply no_monoAP_of_hasAP_eq_false (k := 10) (color := true) (mask := blue)
      (by decide) (by decide +kernel) ?_ hb
    intro i hi hc
    change (((2^_ - 1 : Nat) ^^^ red).testBit i) = true
    rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true_eq.mpr hi]
    simpa [coloring] using hc
