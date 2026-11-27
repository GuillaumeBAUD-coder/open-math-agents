import FormalConjectures.GreensOpenProblems.«14»

-- Reduction Green14.W_3_12.R1 of Ben Green's Open Problem 14 — W 3 12
-- Credit: @iskan-ai
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Exact mixed van der Waerden number W(3,12) = 135

The lower bound is certified below by an explicit colouring of `{1, …, 134}`.

For the upper bound, a colouring of `{1, …, 135}` is read as `r : ℕ → Bool` with `r i = true`
meaning colour 1 at the number `i+1` (positions `0, …, 134`). We split on the colours of the central
positions `64, …, 70`, ordered outward from the centre `67`. The reflection `i ↦ 134 - i` maps
progressions to progressions and swaps `66 ↔ 68`, `65 ↔ 69`, `64 ↔ 70`, so whenever a pair of
mirror positions gets the colours (true, false) we may reflect to (false, true). The remaining
patterns are grouped into the four finite hypotheses, each saying that any `r` with that central
pattern has a colour-0 3-term or a colour-1 12-term progression inside `0, …, 134`.
Each hypothesis is a finite statement about colourings of 135 points (all positions used are below
135), checkable by an exhaustive search.

The order and arithmetic-progression lemmas and the lower-bound check are adapted from the
Apache-2.0 reduction Green14.W_3_11.R1 by @Halldon (open-math-agents PR 1046), which in turn adapts
Dominic Dabish's proof of W(3,9), open-math-agents PR 591.
-/

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_12_R1

def H1 : Prop :=
  ∀ r : ℕ → Bool, (r 66 = false ∧ r 68 = true) →
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
      ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b

def H2 : Prop :=
  ∀ r : ℕ → Bool, ((r 66 = false ∧ r 68 = false) ∨ (r 66 = true ∧ r 68 = true ∧ r 67 = false)) →
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
      ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b

def H3 : Prop :=
  ∀ r : ℕ → Bool, (r 66 = true ∧ r 67 = true ∧ r 68 = true ∧
      ((r 65 = false ∧ r 69 = true) ∨
        (r 65 = true ∧ r 69 = true ∧ r 64 = false ∧ r 70 = true) ∨
        (r 65 = true ∧ r 69 = true ∧ r 64 = false ∧ r 70 = false))) →
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
      ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b

def H4 : Prop :=
  ∀ r : ℕ → Bool, (r 66 = true ∧ r 67 = true ∧ r 68 = true ∧
      ((r 65 = false ∧ r 69 = false) ∨
        (r 65 = true ∧ r 69 = true ∧ r 64 = true ∧ r 70 = true))) →
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
      ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b

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
private theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

private lemma progression_at {N k a d : Nat} (hd : 0 < d)
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


private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val-1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k-1)*d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val*d.val) = col := by
  obtain ⟨s,⟨a,d,hcard,hset⟩,hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i*d := by
    change a + i*d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k-1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k-1)*d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k-1 by omega)
  refine ⟨⟨a-1,by omega⟩,⟨d,by omega⟩,hpos,by change a-1+(k-1)*d < N; omega,?_⟩
  intro i
  obtain ⟨x,hx,hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val*d) = col
  convert he using 2 <;> omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lower_witness : 134 ∉ mixedMonoAPGuaranteeSet 3 12 := by
  let q (i : ℕ) : Fin 2 := if (0x100802450128800c0045202890040200 : ℕ).testBit i then 0 else 1
  have red : ∀ a d : Fin 134, 0 < d.val → a.val + 2*d.val < 134 →
      ¬ ∀ i : Fin 3, q (a.val + i.val*d.val) = 0 := by decide +kernel
  have blue : ∀ a d : Fin 134, 0 < d.val → a.val + 11*d.val < 134 →
      ¬ ∀ i : Fin 12, q (a.val + i.val*d.val) = 1 := by decide +kernel
  intro h
  rcases h (fun x => q (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    exact red a d hd hbound hc
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 12) q 1 hb
    exact blue a d hd hbound hc

/-- A colouring with a monochromatic progression in the sense of the hypotheses. -/
private theorem mirror_ap (r : ℕ → Bool)
    (h : ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
      ∀ t ≤ (if b then 11 else 2), (fun i => r (134 - i)) (a + t * d) = b) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
      ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b := by
  obtain ⟨b, a, d, hd, he, hm⟩ := h
  generalize hL : (if b then 11 else 2) = L at he hm
  refine ⟨b, 134 - (a + L*d), d, hd, ?_, ?_⟩
  · rw [hL]; omega
  · rw [hL]
    intro t ht
    have hh := hm (L - t) (by omega)
    have hmul := Nat.mul_le_mul_right d ht
    simp only at hh
    rw [Nat.sub_mul] at hh
    simpa only [show 134 - (a + (L*d - t*d)) = 134 - (a + L*d) + t*d by omega] using hh

private theorem some_progression (h₁ : H1) (h₂ : H2) (h₃ : H3) (h₄ : H4) (r : ℕ → Bool) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
      ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b := by
  have m66 : (fun i => r (134 - i)) 66 = r 68 := rfl
  have m68 : (fun i => r (134 - i)) 68 = r 66 := rfl
  have m67 : (fun i => r (134 - i)) 67 = r 67 := rfl
  have m65 : (fun i => r (134 - i)) 65 = r 69 := rfl
  have m69 : (fun i => r (134 - i)) 69 = r 65 := rfl
  have m64 : (fun i => r (134 - i)) 64 = r 70 := rfl
  have m70 : (fun i => r (134 - i)) 70 = r 64 := rfl
  cases e66 : r 66 <;> cases e68 : r 68
  · exact h₂ r (Or.inl ⟨e66, e68⟩)
  · exact h₁ r ⟨e66, e68⟩
  · exact mirror_ap r (h₁ (fun i => r (134 - i)) ⟨e68, e66⟩)
  · cases e67 : r 67
    · exact h₂ r (Or.inr ⟨e66, e68, e67⟩)
    · cases e65 : r 65 <;> cases e69 : r 69
      · exact h₄ r ⟨e66, e67, e68, Or.inl ⟨e65, e69⟩⟩
      · exact h₃ r ⟨e66, e67, e68, Or.inl ⟨e65, e69⟩⟩
      · exact mirror_ap r (h₃ (fun i => r (134 - i)) ⟨e68, e67, e66,
          Or.inl ⟨e69, e65⟩⟩)
      · cases e64 : r 64 <;> cases e70 : r 70
        · exact h₃ r ⟨e66, e67, e68, Or.inr (Or.inr ⟨e65, e69, e64, e70⟩)⟩
        · exact h₃ r ⟨e66, e67, e68, Or.inr (Or.inl ⟨e65, e69, e64, e70⟩)⟩
        · exact mirror_ap r (h₃ (fun i => r (134 - i)) ⟨e68, e67, e66,
            Or.inr (Or.inl ⟨e69, e65, e70, e64⟩)⟩)
        · exact h₄ r ⟨e66, e67, e68, Or.inr ⟨e65, e69, e64, e70⟩⟩

theorem main : H1 → H2 → H3 → H4 → type_of% @Green14.W_3_12 := by
  intro h₁ h₂ h₃ h₄
  have upper : 135 ∈ mixedMonoAPGuaranteeSet 3 12 := by
    intro c
    let r (i : ℕ) : Bool := if hi : i < 135 then decide (c ⟨i+1, by constructor <;> omega⟩ = 1) else false
    obtain ⟨b,a,d,hd,he,hm⟩ := some_progression h₁ h₂ h₃ h₄ r
    cases b
    · left
      apply progression_at (a := a) hd c 0
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
        simp only [Bool.false_eq_true, if_false] at he
        omega
      · intro i hi
        have hh := hm i.val (by simp only [Bool.false_eq_true, if_false]; omega)
        have hv : ¬ c ⟨a+i.val*d+1, by constructor <;> omega⟩ = 1 := by
          simpa [r, hi] using hh
        exact (show ∀ x : Fin 2, ¬ x = 1 → x = 0 by decide) _ hv
    · right
      apply progression_at (a := a) hd c 1
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 11 by omega)
        simp only [if_true] at he
        omega
      · intro i hi
        have hh := hm i.val (by simp only [if_true]; omega)
        simpa [r, hi] using hh
  exact le_antisymm (Nat.sInf_le upper)
    (W_ge_succ_of_not_mem 3 12 134 ⟨135,upper⟩ lower_witness)

end OMA.R_Green14_W_3_12_R1
