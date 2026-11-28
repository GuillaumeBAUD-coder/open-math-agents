import OMAReductions.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1

-- Reduction Erdos1135.erdos_1135.R2.H1.R1.H1.R1.H2.R1 of step Erdos1135.erdos_1135.R2.H1.R1.H1.R1.H2
-- Credit: @Ciphore

/-! The `7 (mod 8)` accelerated-Collatz core splits into thirty-two classes modulo `256`.
Sixteen classes descend in eight explicit affine steps once `2048 < n`. The sixteen remaining
classes are grouped by their modulo-32 residue so the four high-density cores are independent. -/

namespace OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1_H2_R1

private abbrev acc (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

lemma step_even (x : ℕ) (h : x % 2 = 0) : acc x = x / 2 := by
  simp [acc, h]

lemma step_odd (x : ℕ) (h : x % 2 = 1) : acc x = (3 * x + 1) / 2 := by
  simp [acc, h]

lemma descent7 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 7) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_even ((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega), step_odd (((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2) / 2)) (by omega)]
  omega

lemma descent15 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 15) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_even ((((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2)) (by omega)]
  omega

lemma descent23 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 23) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_even ((((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2)) (by omega), step_odd (((((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2) / 2)) (by omega)]
  omega

lemma descent39 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 39) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega)]
  omega

lemma descent79 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 79) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_even (((3 * ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2)) (by omega)]
  omega

lemma descent87 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 87) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_odd ((((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2)) (by omega), step_even (((3 * (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2) + 1) / 2)) (by omega)]
  omega

lemma descent95 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 95) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_odd (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega)]
  omega

lemma descent119 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 119) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_even (((3 * ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2) / 2)) (by omega)]
  omega

lemma descent135 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 135) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_even ((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2) / 2)) (by omega)]
  omega

lemma descent143 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 143) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_odd ((((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2)) (by omega)]
  omega

lemma descent151 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 151) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_even ((((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2)) (by omega), step_even (((((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2) / 2)) (by omega)]
  omega

lemma descent175 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 175) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((3 * (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_even ((((3 * (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega)]
  omega

lemma descent183 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 183) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_odd (((3 * ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega)]
  omega

lemma descent199 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 199) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_odd ((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega), step_even (((3 * (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega)]
  omega

lemma descent215 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 215) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_odd ((((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2)) (by omega), step_odd (((3 * (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) / 2) + 1) / 2)) (by omega)]
  omega

lemma descent247 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 247) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_odd (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega), step_even (((3 * ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2) + 1) / 2) / 2)) (by omega)]
  omega

/-- Residual core descending from `7 (mod 32)`, apart from eliminated modulo-256 classes. -/
def H1 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 32 = 7 → n % 256 ≠ 7 → n % 256 ≠ 39 → n % 256 ≠ 135 → n % 256 ≠ 199 → ∃ k : ℕ, T^[k] n < n

/-- Residual core descending from `15 (mod 32)`, apart from eliminated modulo-256 classes. -/
def H2 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 32 = 15 → n % 256 ≠ 15 → n % 256 ≠ 79 → n % 256 ≠ 143 → n % 256 ≠ 175 → ∃ k : ℕ, T^[k] n < n

/-- Residual core descending from `23 (mod 32)`, apart from eliminated modulo-256 classes. -/
def H3 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 32 = 23 → n % 256 ≠ 23 → n % 256 ≠ 87 → n % 256 ≠ 119 → n % 256 ≠ 151 → n % 256 ≠ 183 → n % 256 ≠ 215 → n % 256 ≠ 247 → ∃ k : ℕ, T^[k] n < n

/-- Residual core descending from `31 (mod 32)`, apart from eliminated modulo-256 classes. -/
def H4 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 32 = 31 → n % 256 ≠ 95 → ∃ k : ℕ, T^[k] n < n

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1.H2 := by
  intro h7core h15core h23core h31core n hn hmod
  have h32 : n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 23 ∨ n % 32 = 31 := by omega
  rcases h32 with h7 | h15 | h23 | h31
  · have h2567 : n % 256 = 7 ∨
        n % 256 = 39 ∨
        n % 256 = 71 ∨
        n % 256 = 103 ∨
        n % 256 = 135 ∨
        n % 256 = 167 ∨
        n % 256 = 199 ∨
        n % 256 = 231 := by omega
    rcases h2567 with h | h | h | h | h | h | h | h
    · exact descent7 hn h
    · exact descent39 hn h
    · exact h7core n hn h7 (by omega) (by omega) (by omega) (by omega)
    · exact h7core n hn h7 (by omega) (by omega) (by omega) (by omega)
    · exact descent135 hn h
    · exact h7core n hn h7 (by omega) (by omega) (by omega) (by omega)
    · exact descent199 hn h
    · exact h7core n hn h7 (by omega) (by omega) (by omega) (by omega)
  · have h25615 : n % 256 = 15 ∨
        n % 256 = 47 ∨
        n % 256 = 79 ∨
        n % 256 = 111 ∨
        n % 256 = 143 ∨
        n % 256 = 175 ∨
        n % 256 = 207 ∨
        n % 256 = 239 := by omega
    rcases h25615 with h | h | h | h | h | h | h | h
    · exact descent15 hn h
    · exact h15core n hn h15 (by omega) (by omega) (by omega) (by omega)
    · exact descent79 hn h
    · exact h15core n hn h15 (by omega) (by omega) (by omega) (by omega)
    · exact descent143 hn h
    · exact descent175 hn h
    · exact h15core n hn h15 (by omega) (by omega) (by omega) (by omega)
    · exact h15core n hn h15 (by omega) (by omega) (by omega) (by omega)
  · have h25623 : n % 256 = 23 ∨
        n % 256 = 55 ∨
        n % 256 = 87 ∨
        n % 256 = 119 ∨
        n % 256 = 151 ∨
        n % 256 = 183 ∨
        n % 256 = 215 ∨
        n % 256 = 247 := by omega
    rcases h25623 with h | h | h | h | h | h | h | h
    · exact descent23 hn h
    · exact h23core n hn h23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact descent87 hn h
    · exact descent119 hn h
    · exact descent151 hn h
    · exact descent183 hn h
    · exact descent215 hn h
    · exact descent247 hn h
  · have h25631 : n % 256 = 31 ∨
        n % 256 = 63 ∨
        n % 256 = 95 ∨
        n % 256 = 127 ∨
        n % 256 = 159 ∨
        n % 256 = 191 ∨
        n % 256 = 223 ∨
        n % 256 = 255 := by omega
    rcases h25631 with h | h | h | h | h | h | h | h
    · exact h31core n hn h31 (by omega)
    · exact h31core n hn h31 (by omega)
    · exact descent95 hn h
    · exact h31core n hn h31 (by omega)
    · exact h31core n hn h31 (by omega)
    · exact h31core n hn h31 (by omega)
    · exact h31core n hn h31 (by omega)
    · exact h31core n hn h31 (by omega)

end OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1_H2_R1
