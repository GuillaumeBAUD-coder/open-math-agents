import FormalConjectures.GreensOpenProblems.«14»

/-!
# Mixed van der Waerden number W(3, 20)

The good partition is from Ahmed, Kullmann and Snevily (2014), Appendix A.
The bit mask follows Dominic Dabish’s Apache-2.0 Green14FastKernel20 certificate
(commit 013a0f04de0057d2bd1034c7cc4caf10ac8dc2cf).
It is checked here by independent red and blue bit sweeps in the Lean kernel.

For the upper bound, inspect the central 21 positions of the 389-point coloring.
If all are blue, the first 20 form a progression. Otherwise use reflection to
place a red point nearest the center on the left and split by its distance.
The order and extraction arguments adapt the W(3, 19) reduction by @nijv,
which credits Dominic Dabish and @Halldon for its progression helpers.
-/

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_20_R1

def H1 : Prop :=
  ∀ r : Fin 389 → Bool, ∀ j : Fin 11, 0 ≤ j.val → j.val ≤ 2 →
    r (Fin.ofNat 389 (194 - j.val)) = true →
    (∀ i : Fin 389, 194 - j.val < i.val → i.val < 194 + j.val → r i = false) →
    ∃ (b : Bool) (a d : Fin 389), 0 < d.val ∧ a.val + (if b then 2 else 19) * d.val < 389 ∧
      ∀ t : Fin 20, t.val ≤ (if b then 2 else 19) → r (Fin.ofNat 389 (a.val + t.val * d.val)) = b

def H2 : Prop :=
  ∀ r : Fin 389 → Bool, ∀ j : Fin 11, 3 ≤ j.val → j.val ≤ 5 →
    r (Fin.ofNat 389 (194 - j.val)) = true →
    (∀ i : Fin 389, 194 - j.val < i.val → i.val < 194 + j.val → r i = false) →
    ∃ (b : Bool) (a d : Fin 389), 0 < d.val ∧ a.val + (if b then 2 else 19) * d.val < 389 ∧
      ∀ t : Fin 20, t.val ≤ (if b then 2 else 19) → r (Fin.ofNat 389 (a.val + t.val * d.val)) = b

def H3 : Prop :=
  ∀ r : Fin 389 → Bool, ∀ j : Fin 11, 6 ≤ j.val → j.val ≤ 10 →
    r (Fin.ofNat 389 (194 - j.val)) = true →
    (∀ i : Fin 389, 194 - j.val < i.val → i.val < 194 + j.val → r i = false) →
    ∃ (b : Bool) (a d : Fin 389), 0 < d.val ∧ a.val + (if b then 2 else 19) * d.val < 389 ∧
      ∀ t : Fin 20, t.val ≤ (if b then 2 else 19) → r (Fin.ofNat 389 (a.val + t.val * d.val)) = b

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
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨emb y, Finset.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]; exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨emb y, Finset.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]; exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

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
    (bound : ∀ i : Fin k, a + i.val * d < N)
    (mono : ∀ (i : Fin k) (hi : a + i.val * d < N),
      c ⟨a + i.val * d + 1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val * d + 1
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
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨point i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a + 1, d, ?_, ?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, by exact_mod_cast i.isLt, by simp [value]; omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, by exact_mod_cast hi⟩, by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)

private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val - 1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k - 1) * d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val * d.val) = col := by
  obtain ⟨s, ⟨a, d, hcard, hset⟩, hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i * d := by
    change a + i * d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k - 1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k - 1) * d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, _, rfl⟩; rfl
      · rintro rfl; exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k - 1) * d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k - 1 by omega)
  refine ⟨⟨a - 1, by omega⟩, ⟨d, by omega⟩, hpos, by change a - 1 + (k - 1) * d < N; omega, ?_⟩
  intro i
  obtain ⟨x, hx, hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val * d) = col
  convert he using 2 <;> omega

private theorem lower_witness : 388 ∉ mixedMonoAPGuaranteeSet 3 20 := by
  let red : ℕ :=
    0x1001080a10004010a00063401000020085044008000402000100220a10040000802c6000508020008501080080000
  let blue : ℕ := (2 ^ 388 - 1) ^^^ red
  let q (i : ℕ) : Fin 2 := if red.testBit i then 0 else 1
  have hred_clear :
      ((List.range 193).all fun d0 =>
        ((red &&& (red >>> (d0 + 1))) &&& (red >>> (2 * (d0 + 1)))) == 0) = true := by
    decide
  have hblue_clear :
      ((List.range 20).all fun d0 =>
        let d := d0 + 1
        (blue &&& (blue >>> d) &&& (blue >>> (2 * d)) &&& (blue >>> (3 * d)) &&&
          (blue >>> (4 * d)) &&& (blue >>> (5 * d)) &&& (blue >>> (6 * d)) &&&
          (blue >>> (7 * d)) &&& (blue >>> (8 * d)) &&& (blue >>> (9 * d)) &&&
          (blue >>> (10 * d)) &&& (blue >>> (11 * d)) &&& (blue >>> (12 * d)) &&&
          (blue >>> (13 * d)) &&& (blue >>> (14 * d)) &&& (blue >>> (15 * d)) &&&
          (blue >>> (16 * d)) &&& (blue >>> (17 * d)) &&& (blue >>> (18 * d)) &&& (blue >>> (19 * d))) == 0) = true := by
    decide
  intro h
  rcases h (fun x => q (x.val - 1)) with hr | hb
  · obtain ⟨a, d, hd, hbound, hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    have hd_lt : d.val - 1 < 193 := by omega
    have hz := List.all_eq_true.mp hred_clear (d.val - 1) (List.mem_range.mpr hd_lt)
    simp only [beq_iff_eq, Nat.sub_add_cancel (show 1 ≤ d.val by omega)] at hz
    have hbit (t : Fin 3) : red.testBit (t.val * d.val + a.val) = true := by
      have hct := hc t
      dsimp only [q] at hct
      rw [Nat.add_comm]
      by_cases htb : red.testBit (a.val + t.val * d.val)
      · exact htb
      · simp [htb] at hct
    have hall :
        (((red &&& (red >>> d.val)) &&& (red >>> (2 * d.val))).testBit a.val) = true := by
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true]
      exact ⟨⟨by simpa using hbit ⟨0, by decide⟩, by simpa using hbit ⟨1, by decide⟩⟩,
        by simpa using hbit ⟨2, by decide⟩⟩
    rw [hz, Nat.zero_testBit] at hall
    cases hall
  · obtain ⟨a, d, hd, hbound, hc⟩ := extract_progression (by decide : 2 ≤ 20) q 1 hb
    have hd_lt : d.val - 1 < 20 := by omega
    have hz := List.all_eq_true.mp hblue_clear (d.val - 1) (List.mem_range.mpr hd_lt)
    simp only [beq_iff_eq, Nat.sub_add_cancel (show 1 ≤ d.val by omega)] at hz
    have hbit (t : Fin 20) : blue.testBit (t.val * d.val + a.val) = true := by
      have hct := hc t
      have hlt : a.val + t.val * d.val < 388 := by
        have := Nat.mul_le_mul_right d.val (show t.val ≤ 19 by omega)
        omega
      dsimp only [q] at hct
      have hrfalse : red.testBit (a.val + t.val * d.val) = false := by
        by_cases htb : red.testBit (a.val + t.val * d.val)
        · simp [htb] at hct
        · exact Bool.eq_false_iff.mpr htb
      rw [Nat.add_comm]
      dsimp only [blue]
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true (by omega), hrfalse]
      rfl
    have hall :
        ((blue &&& (blue >>> d.val) &&& (blue >>> (2 * d.val)) &&& (blue >>> (3 * d.val)) &&&
          (blue >>> (4 * d.val)) &&& (blue >>> (5 * d.val)) &&& (blue >>> (6 * d.val)) &&&
          (blue >>> (7 * d.val)) &&& (blue >>> (8 * d.val)) &&& (blue >>> (9 * d.val)) &&&
          (blue >>> (10 * d.val)) &&& (blue >>> (11 * d.val)) &&& (blue >>> (12 * d.val)) &&&
          (blue >>> (13 * d.val)) &&& (blue >>> (14 * d.val)) &&& (blue >>> (15 * d.val)) &&&
          (blue >>> (16 * d.val)) &&& (blue >>> (17 * d.val)) &&&
          (blue >>> (18 * d.val)) &&& (blue >>> (19 * d.val))).testBit a.val) = true := by
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true]
      repeat' constructor
      · simpa using hbit ⟨0, by decide⟩
      · simpa using hbit ⟨1, by decide⟩
      · simpa using hbit ⟨2, by decide⟩
      · simpa using hbit ⟨3, by decide⟩
      · simpa using hbit ⟨4, by decide⟩
      · simpa using hbit ⟨5, by decide⟩
      · simpa using hbit ⟨6, by decide⟩
      · simpa using hbit ⟨7, by decide⟩
      · simpa using hbit ⟨8, by decide⟩
      · simpa using hbit ⟨9, by decide⟩
      · simpa using hbit ⟨10, by decide⟩
      · simpa using hbit ⟨11, by decide⟩
      · simpa using hbit ⟨12, by decide⟩
      · simpa using hbit ⟨13, by decide⟩
      · simpa using hbit ⟨14, by decide⟩
      · simpa using hbit ⟨15, by decide⟩
      · simpa using hbit ⟨16, by decide⟩
      · simpa using hbit ⟨17, by decide⟩
      · simpa using hbit ⟨18, by decide⟩
      · simpa using hbit ⟨19, by decide⟩
    rw [hz, Nat.zero_testBit] at hall
    cases hall

private lemma idx_val (i : ℕ) (hi : i < 389) : (Fin.ofNat 389 i).val = i :=
  Nat.mod_eq_of_lt hi

private lemma some_progression (h₁ : H1) (h₂ : H2) (h₃ : H3) (r : Fin 389 → Bool) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 19) * d < 389 ∧
      ∀ t ≤ (if b then 2 else 19), r (Fin.ofNat 389 (a + t * d)) = b := by
  let Good (s : Fin 389 → Bool) := ∃ (b : Bool) (a d : ℕ),
    0 < d ∧ a + (if b then 2 else 19) * d < 389 ∧
      ∀ t ≤ (if b then 2 else 19), s (Fin.ofNat 389 (a + t * d)) = b
  have normal (s : Fin 389 → Bool) (j : ℕ) (hj : j ≤ 10)
      (hr : s (Fin.ofNat 389 (194 - j)) = true)
      (hb : ∀ i : Fin 389, 194 - j < i.val → i.val < 194 + j → s i = false) : Good s := by
    let k : Fin 11 := ⟨j, by omega⟩
    have hc : ∃ (b : Bool) (a d : Fin 389), 0 < d.val ∧
        a.val + (if b then 2 else 19) * d.val < 389 ∧
        ∀ t : Fin 20, t.val ≤ (if b then 2 else 19) →
          s (Fin.ofNat 389 (a.val + t.val * d.val)) = b := by
      by_cases h : j ≤ 2
      · exact h₁ s k (Nat.zero_le j) h hr hb
      by_cases h' : j ≤ 5
      · exact h₂ s k (show 3 ≤ j by omega) h' hr hb
      exact h₃ s k (show 6 ≤ j by omega) hj hr hb
    obtain ⟨b, a, d, hd, he, hm⟩ := hc
    refine ⟨b, a.val, d.val, hd, he, ?_⟩
    intro t ht
    have hL : (if b then 2 else 19 : ℕ) ≤ 19 := by cases b <;> decide
    exact hm ⟨t, by omega⟩ ht
  let P (j : ℕ) := j ≤ 10 ∧
    (r (Fin.ofNat 389 (194 - j)) = true ∨ r (Fin.ofNat 389 (194 + j)) = true)
  by_cases h : ∃ j, P j
  · let j := Nat.find h
    obtain ⟨hj, hred⟩ := Nat.find_spec h
    change j ≤ 10 at hj
    have blue (i : ℕ) (hi : 194 - j < i) (hi' : i < 194 + j) :
        r (Fin.ofNat 389 i) = false := by
      by_contra! hh
      by_cases left : i ≤ 194
      · have heq : 194 - (194 - i) = i := by omega
        have hp : P (194 - i) := ⟨by omega, Or.inl (by simpa [heq] using hh)⟩
        have := Nat.find_min' h hp
        change j ≤ 194 - i at this
        omega
      · have heq : 194 + (i - 194) = i := by omega
        have hp : P (i - 194) := ⟨by omega, Or.inr (by simpa [heq] using hh)⟩
        have := Nat.find_min' h hp
        change j ≤ i - 194 at this
        omega
    rcases hred with left | right
    · apply normal r j hj left
      intro i hi hi'
      simpa using blue i.val hi hi'
    · let flip (i : Fin 389) := r (Fin.ofNat 389 (388 - i.val))
      have hf : flip (Fin.ofNat 389 (194 - j)) = true := by
        dsimp only [flip]
        rw [idx_val _ (by omega), show 388 - (194 - j) = 194 + j by omega]
        exact right
      have hb (i : Fin 389) (hl : 194 - j < i.val) (hr : i.val < 194 + j) : flip i = false :=
        blue _ (by omega) (by omega)
      obtain ⟨b, a, d, hd, he, hm⟩ := normal flip j hj hf hb
      let L : ℕ := if b then 2 else 19
      change a + L * d < 389 at he
      change ∀ t ≤ L, flip (Fin.ofNat 389 (a + t * d)) = b at hm
      refine ⟨b, 388 - (a + L * d), d, hd, by change 388 - (a + L * d) + L * d < 389; omega, ?_⟩
      intro t ht
      change t ≤ L at ht
      have hh := hm (L - t) (by omega)
      dsimp only [flip] at hh
      have hmul := Nat.mul_le_mul_right d ht
      rw [Nat.sub_mul, idx_val _ (by omega)] at hh
      simpa only [show 388 - (a + (L * d - t * d)) = 388 - (a + L * d) + t * d by omega] using hh
  · refine ⟨false, 184, 1, by decide, by decide, ?_⟩
    intro t ht
    change t ≤ 19 at ht
    by_contra! hh
    have hh : r (Fin.ofNat 389 (184 + t * 1)) = true := by simpa using hh
    by_cases left : t ≤ 10
    · have heq : 194 - (10 - t) = 184 + t * 1 := by omega
      exact h ⟨10 - t, by omega, Or.inl (by simpa only [heq] using hh)⟩
    · have heq : 194 + (t - 10) = 184 + t * 1 := by omega
      exact h ⟨t - 10, by omega, Or.inr (by simpa only [heq] using hh)⟩

theorem main : H1 → H2 → H3 → type_of% @Green14.W_3_20 := by
  intro h₁ h₂ h₃
  have upper : 389 ∈ mixedMonoAPGuaranteeSet 3 20 := by
    intro c
    let r (i : Fin 389) := decide (c ⟨i.val + 1, by constructor <;> omega⟩ = 0)
    obtain ⟨b, a, d, hd, he, hm⟩ := some_progression h₁ h₂ h₃ r
    cases b
    · right
      apply progression_at (a := a) hd c 1
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 19 by omega)
        simp only [Bool.false_eq_true, if_false] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 19; omega)
        have hx : Fin.ofNat 389 (a + i.val * d) = ⟨a + i.val * d, hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        have hv : c ⟨a + i.val * d + 1, by constructor <;> omega⟩ ≠ 0 := of_decide_eq_false hh
        exact (show ∀ x : Fin 2, x ≠ 0 → x = 1 by decide) _ hv
    · left
      apply progression_at (a := a) hd c 0
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
        simp only [if_true] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 2; omega)
        have hx : Fin.ofNat 389 (a + i.val * d) = ⟨a + i.val * d, hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        exact of_decide_eq_true hh
  exact le_antisymm (Nat.sInf_le upper)
    (W_ge_succ_of_not_mem 3 20 388 ⟨389, upper⟩ lower_witness)

end OMA.R_Green14_W_3_20_R1
