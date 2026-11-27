import FormalConjectures.ErdosProblems.«342»

/-!
# Finite phase conditions for distance-two Ulam pairs

Write the phase of a value as the fractional part of its product with a frequency.
If a translate by 2 is missing, a second representation exists alongside the one using
the seed 2. On the arcs below, the phase of its larger summand increases by at least
1/20. Eight iterations would exceed the width of the narrow arc.

The first hypothesis supplies a finite block in that arc. The second propagates
exceptions to a wider arc forward, so the clean block also certifies earlier terms.
-/

namespace OMA.R_Erdos342_erdos_342_parts_i_R1

open Erdos342

theorem strictlyIncreasing {a : ℕ → ℕ} (ha : IsUlamSequence a) : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp [ha.1, ha.2.1]
  | succ k => exact (ha.2.2 (k + 2) (by omega)).1

/-- Missing a translate by 2 forces a second pair, neither of whose terms is 2. -/
theorem alternativeSum {a : ℕ → ℕ} (ha : IsUlamSequence a) {n : ℕ} (hn : 1 < n)
    (hmiss : ¬ ∃ m, a m = a n + 2) :
    ∃ i j, i < j ∧ a i ≠ 2 ∧ a j ≠ 2 ∧ a i + a j = a n + 2 := by
  classical
  have inc := strictlyIncreasing ha
  have hex : ∃ k, a n + 2 ≤ a k := ⟨a n + 2, inc.id_le _⟩
  let k := Nat.find hex
  have hk : a n + 2 ≤ a k := Nat.find_spec hex
  have hnk : n < k := inc.lt_iff_lt.mp (by omega)
  have hprev : ¬ a n + 2 ≤ a (k - 1) := Nat.find_min hex (show k - 1 < k by omega)
  have hnot := (ha.2.2 k (by omega)).2.2 (a n + 2) (by omega)
    (lt_of_le_of_ne hk (fun h => hmiss ⟨k, h.symm⟩))
  have seed := ha.2.1
  have canonical : a n + 2 = a 1 + a n := by omega
  by_contra! bad
  apply hnot
  refine ⟨(1,n), ⟨hn, hnk, canonical⟩, ?_⟩
  rintro ⟨i,j⟩ ⟨hij, _, hsum⟩
  change a n + 2 = a i + a j at hsum
  change i < j at hij
  by_cases h : a i = 2
  · have hi : i = 1 := inc.injective (h.trans seed.symm)
    have hj : j = n := inc.injective (by omega)
    simp [hi,hj]
  · have hj : a j ≠ 2 := by
      intro hj
      have : a i < a j := inc hij
      have : a 1 < a n := inc hn
      omega
    exact (bad i j hij h hj hsum.symm).elim

/-- The congruence between four fractional parts lifts to an equality when its error lies
strictly between -1 and 1. -/
theorem phaseIncrease {t : ℝ} {x u v : ℕ} (hsum : u + v = x + 2)
    (hu : Int.fract (t * u) ∈ Set.Icc (21/100 : ℝ) (76/100))
    (hv : Int.fract (t * v) ∈ Set.Icc (31/100 : ℝ) (69/100))
    (hx : Int.fract (t * x) ∈ Set.Icc (31/100 : ℝ) (69/100))
    (h₂ : t * 2 ∈ Set.Icc (81/100 : ℝ) (82/100)) :
    Int.fract (t * x) + 1/20 ≤ Int.fract (t * v) := by
  have hr : (u : ℝ) + v = x + 2 := by exact_mod_cast hsum
  have heq : t * u + t * v = t * x + t * 2 := by rw [← mul_add, ← mul_add, hr]
  let z : ℤ := ⌊t * u⌋ + ⌊t * v⌋ - ⌊t * x⌋
  have hz : (z : ℝ) =
      Int.fract (t * x) + t * 2 - Int.fract (t * u) - Int.fract (t * v) := by
    simp only [z, Int.fract, Int.cast_add, Int.cast_sub]
    linarith
  obtain ⟨hu₁,hu₂⟩ := hu
  obtain ⟨hv₁,hv₂⟩ := hv
  obtain ⟨hx₁,hx₂⟩ := hx
  obtain ⟨ht₁,ht₂⟩ := h₂
  have hneg : (-1 : ℝ) < (z : ℝ) := by linarith
  have hpos : (z : ℝ) < 1 := by linarith
  have hneg' : (-1 : ℤ) < z := by exact_mod_cast hneg
  have hpos' : z < 1 := by exact_mod_cast hpos
  have : z = 0 := by omega
  rw [this, Int.cast_zero] at hz
  linarith


/-- Eight alternative representations force eight phase increments. The larger summand
can decrease by at most a factor of two or increase by at most one in value. -/
theorem pairInBlock {a : ℕ → ℕ} (ha : IsUlamSequence a) (s B : ℕ)
    (hB : 3 ≤ B) (hstart : 256 * B ≤ a s) (t : ℝ)
    (h₂ : t * 2 ∈ Set.Icc (81/100 : ℝ) (82/100))
    (hcoarse : ∀ k, a k ≤ a s + 8 → a k ≠ 2 →
      Int.fract (t * a k) ∈ Set.Icc (21/100 : ℝ) (76/100))
    (hnarrow : ∀ k, B ≤ a k → a k ≤ a s + 8 →
      Int.fract (t * a k) ∈ Set.Icc (31/100 : ℝ) (69/100)) :
    ∃ n, B ≤ a n ∧ a n ≤ a s + 8 ∧ ∃ m, a m = a n + 2 := by
  by_contra! habsent
  have inc := strictlyIncreasing ha
  have lower (k : ℕ) : 1 ≤ a k := by
    have := inc.monotone (Nat.zero_le k)
    simpa [ha.1] using this
  have step (k : ℕ) (hk : B ≤ a k) (hu : a k ≤ a s + 7) (hk' : 2*B ≤ a k) :
      ∃ j, a k ≤ 2*a j ∧ a j ≤ a k + 1 ∧
        Int.fract (t * a k) + 1/20 ≤ Int.fract (t * a j) := by
    have hindex : 1 < k := inc.lt_iff_lt.mp (by have := ha.2.1; omega)
    have hmiss : ¬ ∃ m, a m = a k + 2 := fun ⟨m, hm⟩ => habsent k hk (by omega) m hm
    obtain ⟨i,j,hij,hi₂,_,hsum⟩ := alternativeSum ha hindex hmiss
    have huv := inc hij
    have hi := lower i
    refine ⟨j, by omega, by omega, phaseIncrease hsum ?_ ?_ ?_ h₂⟩
    · exact hcoarse i (by omega) hi₂
    · exact hnarrow j (by omega) (by omega)
    · exact hnarrow k hk (by omega)
  have climb (d : ℕ) (hd : d ≤ 8) :
      ∃ k, 2^(8-d) * B ≤ a k ∧ a k ≤ a s + d ∧
        Int.fract (t * a s) + (d : ℝ)/20 ≤ Int.fract (t * a k) := by
    induction d with
    | zero => exact ⟨s, by simpa using hstart, by omega, by simp⟩
    | succ d ih =>
      obtain ⟨k, hk, hu, hr⟩ := ih (by omega)
      have he : 8-d = (8-(d+1))+1 := by omega
      rw [he, pow_succ] at hk
      have hpow : 1 ≤ (2:ℕ) ^ (8-(d+1)) := Nat.one_le_pow _ _ (by decide)
      have hB' : B ≤ 2^(8-(d+1))*B := by simpa using Nat.mul_le_mul_right B hpow
      obtain ⟨j,hj,huj,hrj⟩ := step k (by nlinarith) (by omega) (by nlinarith)
      refine ⟨j, by nlinarith, by omega, ?_⟩
      push_cast
      linarith
  obtain ⟨j,hj,hu,hd⟩ := climb 8 le_rfl
  norm_num at hj hd
  have hmax := (hnarrow j hj hu).2
  have hmin := (hnarrow s (by omega) (by omega)).1
  linarith



/-- A term crosses each large threshold by at most a factor of two. -/
theorem crossThreshold {a : ℕ → ℕ} (ha : IsUlamSequence a) {T : ℕ} (hT : 3 ≤ T) :
    ∃ s, T ≤ a s ∧ a s ≤ 2*T := by
  classical
  have inc := strictlyIncreasing ha
  have hex : ∃ k, T ≤ a k := ⟨T, inc.id_le T⟩
  let s := Nat.find hex
  have hs : T ≤ a s := Nat.find_spec hex
  have hs' : 1 < s := inc.lt_iff_lt.mp (by have := ha.2.1; omega)
  obtain ⟨⟨i,j⟩, ⟨hi,hj,hsum⟩, _⟩ := (ha.2.2 s (by omega)).2.1
  change i < j at hi
  change j < s at hj
  change a s = a i + a j at hsum
  have := Nat.find_min hex (show i < s from hi.trans hj)
  have := Nat.find_min hex hj
  exact ⟨s, hs, by omega⟩

/-- Arbitrarily far out a single finite block fits a narrow arc. Its frequency may
depend on the block. -/
def H1 : Prop :=
  ∀ a : ℕ → ℕ, IsUlamSequence a → ∀ N : ℕ, ∃ B : ℕ, N ≤ B ∧ ∃ t : ℝ,
    t ∈ Set.Icc (40925/100000 : ℝ) (40927/100000) ∧
    ∀ k, B ≤ a k → a k ≤ 512*B+8 →
      Int.fract (t * a k) ∈ Set.Icc (31/100 : ℝ) (69/100)

/-- At a calibrated frequency, a broad-arc exception other than the seed 2 has
another such exception within a factor of 512. Each instance uses a finite prefix. -/
def H2 : Prop :=
  ∀ a : ℕ → ℕ, IsUlamSequence a → ∀ t : ℝ,
    t ∈ Set.Icc (40925/100000 : ℝ) (40927/100000) →
    ∀ i, a i ≠ 2 → Int.fract (t * a i) ∉ Set.Icc (21/100 : ℝ) (76/100) →
      ∃ j, a i < a j ∧ a j ≤ 512 * a i ∧ a j ≠ 2 ∧
        Int.fract (t * a j) ∉ Set.Icc (21/100 : ℝ) (76/100)

theorem main : H1 → H2 → type_of% @Erdos342.erdos_342.parts.i := by
  intro hblocks hprop a ha
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨B, hB, t, ht, hnarrow⟩ := hblocks a ha (a N + 3)
  obtain ⟨s, hsl, hsu⟩ := crossThreshold ha (T := 256*B) (by omega)
  have clean (k : ℕ) (hk : a k ≤ 512*B+8) (h₂ : a k ≠ 2) :
      Int.fract (t * a k) ∈ Set.Icc (21/100 : ℝ) (76/100) := by
    generalize hd : B - a k = d
    induction d using Nat.strong_induction_on generalizing k with
    | h d ih =>
      by_cases hb : B ≤ a k
      · obtain ⟨hlo,hhi⟩ := hnarrow k hb hk
        constructor <;> linarith
      · by_contra hbad
        obtain ⟨j,hj,hu,hne,hout⟩ := hprop a ha t ht k h₂ hbad
        exact hout (ih (B - a j) (by omega) j (by omega) hne rfl)
  have ht₂ : t * 2 ∈ Set.Icc (81/100 : ℝ) (82/100) := by
    obtain ⟨hl,hu⟩ := ht
    constructor <;> linarith
  obtain ⟨n, hl, _, hm⟩ := pairInBlock ha s B (by omega) hsl t ht₂
    (fun k hk hne => clean k (by omega) hne) (fun k hk hu => hnarrow k hk (by omega))
  exact ⟨n, hm, (strictlyIncreasing ha).lt_iff_lt.mp (by omega)⟩

end OMA.R_Erdos342_erdos_342_parts_i_R1
