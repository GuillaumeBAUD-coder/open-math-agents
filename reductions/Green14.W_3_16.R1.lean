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


/-!
# Extending a two-coloring by one position

Index positions from zero and let true denote red. A coloring of the first
237 positions which already contains a red triple or a blue 16-term
progression needs no further work. For every other prefix, an obstruction
to adding red at position 237 consists of two red positions equally spaced
backward from the endpoint. The obstruction to adding blue consists of
fifteen blue positions equally spaced backward from it.

The interval and progression lemmas are adapted from Halldon's W(3,11)
reduction and the earlier Apache-2.0 Green14 proofs of Dominic Dabish.
The lower-bound coloring is from Tanbir Ahmed, An Implementation of the DPLL
Algorithm, Table 4.3, p. 89 (A = B = C = 2). Both colors are checked below.
The endpoint reduction for W(3,16) is by @MrSeizy.
-/

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_16_R1

/-- Every admissible prefix has a progression which blocks a red extension. -/
def H1 : Prop :=
  ∀ r : Fin 237 → Bool,
    (∀ a d : Fin 237, 0 < d.val → a.val + 2 * d.val < 237 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 237 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 237, 0 < d.val → a.val + 15 * d.val < 237 →
      ¬ ∀ t : Fin 16, r (Fin.ofNat 237 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 119, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 237 (237 - (2 - t.val) * d.val)) = true

/-- Every admissible prefix has a progression which blocks a blue extension. -/
def H2 : Prop :=
  ∀ r : Fin 237 → Bool,
    (∀ a d : Fin 237, 0 < d.val → a.val + 2 * d.val < 237 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 237 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 237, 0 < d.val → a.val + 15 * d.val < 237 →
      ¬ ∀ t : Fin 16, r (Fin.ofNat 237 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 15,
      r (Fin.ofNat 237 (237 - (15 - t.val) * d.val)) = false

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
private theorem lower_witness : 237 ∉ mixedMonoAPGuaranteeSet 3 16 := by
  let q (i : ℕ) : Fin 2 := if (0x20041822001012000b04800202401100080029001608000c801400080 : ℕ).testBit i then 0 else 1
  have red : ∀ a d : Fin 237, 0 < d.val → a.val + 2*d.val < 237 →
      ¬ ∀ i : Fin 3, q (a.val + i.val*d.val) = 0 := by decide +kernel
  have blue : ∀ a d : Fin 237, 0 < d.val → a.val + 15*d.val < 237 →
      ¬ ∀ i : Fin 16, q (a.val + i.val*d.val) = 1 := by decide +kernel
  intro h
  rcases h (fun x => q (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    exact red a d hd hbound hc
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 16) q 1 hb
    exact blue a d hd hbound hc

theorem main : H1 → H2 → type_of% @Green14.W_3_16 := by
  intro blockRed blockBlue
  have upper : 238 ∈ mixedMonoAPGuaranteeSet 3 16 := by
    intro c
    by_contra bad
    let color (n : ℕ) := c ⟨n % 238 + 1, by have := Nat.mod_lt n (by decide : 0 < 238); constructor <;> omega⟩
    let red (n : ℕ) := decide (color n = 0)
    let initialColors (i : Fin 237) := red i.val
    have liftAP {k a d : ℕ} (v : Fin 2) (hd : 0 < d) (he : a + (k-1)*d < 238)
        (h : ∀ t : Fin k, color (a+t.val*d) = v) :
        ∃ s : Finset (Icc 1 238), ({(z : ℕ) | z ∈ s} : Set ℕ).IsAPOfLength k ∧
          ∀ z ∈ s, c z = v := by
      apply progression_at (a := a) hd c v
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ k - 1 by omega)
        omega
      · intro i hi
        simpa only [color, Nat.mod_eq_of_lt hi] using h i
    have noRed (a d : ℕ) (hd : 0 < d) (he : a + 2*d < 238) :
        ¬ ∀ t : Fin 3, red (a+t.val*d) = true := by
      intro h
      exact bad (Or.inl (liftAP (k := 3) 0 hd he (fun t => of_decide_eq_true (h t))))
    have noBlue (a d : ℕ) (hd : 0 < d) (he : a + 15*d < 238) :
        ¬ ∀ t : Fin 16, red (a+t.val*d) = false := by
      intro h
      apply bad
      right
      apply liftAP (k := 16) 1 hd he
      intro t
      have hn : color (a+t.val*d) ≠ 0 := of_decide_eq_false (h t)
      exact (show ∀ v : Fin 2, v ≠ 0 → v = 1 by decide) _ hn
    have restrict {k : ℕ} {b : Bool}
        (avoid : ∀ a d : ℕ, 0 < d → a + (k-1)*d < 238 →
          ¬ ∀ t : Fin k, red (a+t.val*d) = b) :
        ∀ a d : Fin 237, 0 < d.val → a.val + (k-1)*d.val < 237 →
          ¬ ∀ t : Fin k, initialColors (Fin.ofNat 237 (a.val+t.val*d.val)) = b := by
      intro a d hd he h
      apply avoid a d hd (by omega)
      intro t
      have := Nat.mul_le_mul_right d.val (show t.val ≤ k-1 by omega)
      have hi : a.val + t.val*d.val < 237 := by omega
      have ht := h t
      change red ((a.val + t.val*d.val) % 237) = b at ht
      rwa [Nat.mod_eq_of_lt hi] at ht
    have extend {m d : ℕ} {b : Bool} (hd : 0 < d) (hb : m*d ≤ 237)
        (prior : ∀ t : Fin m, initialColors (Fin.ofNat 237 (237 - (m-t.val)*d)) = b)
        (last : red 237 = b) :
        ∀ t : Fin (m+1), red (237 - m*d + t.val*d) = b := by
      intro t
      by_cases eq : t.val = m
      · rwa [eq, Nat.sub_add_cancel hb]
      · have lt : t.val < m := by omega
        have hmul := Nat.mul_lt_mul_of_pos_right lt hd
        have hi : 237 - (m-t.val)*d < 237 := by rw [Nat.sub_mul]; omega
        have hx := prior ⟨t.val,lt⟩
        change red ((237-(m-t.val)*d) % 237) = b at hx
        rwa [Nat.mod_eq_of_lt hi, Nat.sub_mul,
          show 237 - (m*d-t.val*d) = 237-m*d+t.val*d by omega] at hx
    cases last : red 237 with
    | true =>
      obtain ⟨d, hd, prev⟩ := blockRed initialColors (restrict (k := 3) noRed) (restrict (k := 16) noBlue)
      have hb : 2*d.val ≤ 237 := by omega
      exact noRed (237-2*d.val) d.val hd (by omega) (extend hd hb prev last)
    | false =>
      obtain ⟨d, hd, prev⟩ := blockBlue initialColors (restrict (k := 3) noRed) (restrict (k := 16) noBlue)
      have hb : 15*d.val ≤ 237 := by omega
      exact noBlue (237-15*d.val) d.val hd (by omega) (extend hd hb prev last)
  exact le_antisymm (Nat.sInf_le upper)
    (W_ge_succ_of_not_mem 3 16 237 ⟨238, upper⟩ lower_witness)

end OMA.R_Green14_W_3_16_R1
