import OMAStatements.S_oeis_a283965
import Mathlib

/-!
Proof idea. Zeros are isolated, so the fixed point is a concatenation of the blocks
`A = 10` and `B = 1`; on blocks the morphism reads `A ↦ AAB`, `B ↦ AA`, and the `n`-th one
sits at `n + #A(first n - 1 blocks)`. Every prefix of `τ v` is `τ (prefix of v)` followed by
`r ≤ 2` further `A`s, so the discrepancy `s = #A - (√3 - 1) * length` satisfies
`s ↦ (1 - √3) * s + (2 - √3) * r`, which keeps `[2√3/3 - 2, 2√3/3]` invariant.
-/

namespace OMA.P283965

open OMA.S_oeis_a283965

/-- Block encoding: `true` is the block `A = 10`, `false` is the block `B = 1`. -/
def enc (b : Bool) : List Bool := if b then [true, false] else [true]

def E (v : List Bool) : List Bool := v.flatMap enc

/-- The morphism on blocks: `A ↦ AAB`, `B ↦ AA`. -/
def tau (b : Bool) : List Bool := if b then [true, true, false] else [true, true]

def T (v : List Bool) : List Bool := v.flatMap tau

def V : ℕ → List Bool
  | 0 => [false]
  | k + 1 => T (V k)

lemma subst_E (v : List Bool) : subst (E v) = E (T v) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp_all [subst, E, T, enc, tau, letter, List.flatMap_cons]

lemma iter_eq (k : ℕ) : iter k = E (V k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iter, V, ih, subst_E]

lemma nthOne_E (v : List Bool) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ v.length) :
    nthOne n (E v) = n + (v.take (n - 1)).count true := by
  induction v generalizing n with
  | nil => simp at h2; omega
  | cons b v ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rcases m with _ | m
    · cases b <;> simp [E, enc, nthOne]
    · have hm : m + 1 ≤ v.length := by simp at h2; omega
      have := ih (m + 1) (by omega) hm
      cases b
      · simp only [E, List.flatMap_cons, enc] at this ⊢
        simp [nthOne, this, List.take_succ_cons]
        omega
      · simp only [E, List.flatMap_cons, enc] at this ⊢
        simp [nthOne, this, List.take_succ_cons]
        omega

lemma length_T (v : List Bool) : (T v).length = 2 * v.length + v.count true := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp_all [T, tau, List.flatMap_cons] <;> ring

lemma decomp (v : List Bool) (m : ℕ) (hm : m ≤ (T v).length) :
    ∃ m' r : ℕ, m' ≤ v.length ∧ r ≤ 2 ∧
      ((T v).take m).count true = 2 * m' + r ∧
      m = 2 * m' + (v.take m').count true + r := by
  induction v generalizing m with
  | nil => exact ⟨0, 0, by simp, by simp, by simp_all [T], by simp_all [T]⟩
  | cons b v ih =>
    have hT : T (b :: v) = tau b ++ T v := by simp [T, List.flatMap_cons]
    by_cases hsmall : m < (tau b).length
    · refine ⟨0, m, by simp, ?_, ?_, by simp⟩
      · cases b <;> simp [tau] at hsmall <;> omega
      · rw [hT, List.take_append_of_le_length hsmall.le]
        cases b <;> simp [tau] at hsmall <;> interval_cases m <;> simp [tau]
    · push Not at hsmall
      obtain ⟨m₂, rfl⟩ : ∃ m₂, m = (tau b).length + m₂ := ⟨m - (tau b).length, by omega⟩
      have hm₂ : m₂ ≤ (T v).length := by
        rw [hT, List.length_append] at hm; omega
      obtain ⟨m', r, h1, h2, h3, h4⟩ := ih m₂ hm₂
      refine ⟨m' + 1, r, by simp; omega, h2, ?_, ?_⟩
      · rw [hT, List.take_append, List.take_of_length_le (l := tau b) (by omega)]
        simp only [Nat.add_sub_cancel_left, List.count_append, h3]
        cases b <;> simp [tau] <;> ring
      · simp only [List.take_succ_cons, List.count_cons]
        rw [h4]
        cases b <;> simp [tau] <;> ring

lemma length_V (k : ℕ) : k + 1 ≤ (V k).length := by
  induction k with
  | zero => simp [V]
  | succ k ih =>
    simp only [V, length_T]
    omega

/-- The invariant interval for the discrepancy of prefixes of `V k`. -/
lemma disc (k : ℕ) : ∀ m ≤ (V k).length,
    2 * Real.sqrt 3 / 3 - 2 ≤ (((V k).take m).count true : ℝ) - (Real.sqrt 3 - 1) * m ∧
    (((V k).take m).count true : ℝ) - (Real.sqrt 3 - 1) * m ≤ 2 * Real.sqrt 3 / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlt : Real.sqrt 3 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  induction k with
  | zero =>
    intro m hm
    simp [V] at hm
    interval_cases m
    · simp; constructor <;> nlinarith
    · simp [V]; constructor <;> nlinarith
  | succ k ih =>
    intro m hm
    obtain ⟨m', r, h1, h2, h3', h4⟩ := decomp (V k) m hm
    obtain ⟨hL, hU⟩ := ih m' h1
    simp only [V]
    rw [h3', h4]
    set x : ℝ := (((V k).take m').count true : ℝ) - (Real.sqrt 3 - 1) * m' with hx
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have hr2 : (r : ℝ) ≤ 2 := by exact_mod_cast h2
    have key : ((2 * m' + r : ℕ) : ℝ) - (Real.sqrt 3 - 1) * ((2 * m' + ((V k).take m').count true + r : ℕ) : ℝ)
        = (1 - Real.sqrt 3) * x + (2 - Real.sqrt 3) * r := by
      rw [hx]; push_cast; ring_nf; rw [h3]; ring
    rw [key]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr hpos.le)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hpos.le)]

end OMA.P283965

open OMA.P283965 in
theorem OMA.solution : type_of% @OMA.S_oeis_a283965.main := by
  intro n hn
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 3 < 3 := by nlinarith
  have hlen := length_V n
  have ha : OMA.S_oeis_a283965.a n = n + ((V n).take (n - 1)).count true := by
    rw [OMA.S_oeis_a283965.a, iter_eq]
    exact nthOne_E _ _ hn (by omega)
  obtain ⟨hL, hU⟩ := disc n (n - 1) (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hL hU
  rw [ha]
  push_cast
  constructor <;> nlinarith
