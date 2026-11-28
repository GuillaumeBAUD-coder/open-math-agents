import OMAReductions.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1

-- Reduction Erdos1135.erdos_1135.R2.H1.R1.H1.R1.H1.R1 of step Erdos1135.erdos_1135.R2.H1.R1.H1.R1.H1
-- Credit: @Ciphore

/-! The `3 (mod 8)` accelerated-Collatz core splits into thirty-two classes modulo `256`.
Twenty-eight classes descend by short explicit affine iterates. The four remaining high-density
classes are independent stopping-time cores. -/

namespace OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1_H1_R1

private abbrev acc (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

lemma step_even (x : ℕ) (h : x % 2 = 0) : acc x = x / 2 := by
  simp [acc, h]

lemma step_odd (x : ℕ) (h : x % 2 = 1) : acc x = (3 * x + 1) / 2 := by
  simp [acc, h]

lemma descent3 {n : ℕ} (_hn : 2048 < n) (hr : n % 32 = 3) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨4, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega)]
  omega

lemma descent11 {n : ℕ} (_hn : 2048 < n) (hr : n % 32 = 11) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨5, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega)]
  omega

lemma descent19 {n : ℕ} (_hn : 2048 < n) (hr : n % 32 = 19) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨4, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega)]
  omega

lemma descent59 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 59) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨7, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega)]
  omega

lemma descent123 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 123) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega), step_even (((3 * (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega)]
  omega

lemma descent187 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 187) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨7, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega)]
  omega

lemma descent219 {n : ℕ} (_hn : 2048 < n) (hr : n % 256 = 219) :
    ∃ k : ℕ, acc^[k] n < n := by
  refine ⟨8, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [step_odd (n) (by omega), step_odd (((3 * n + 1) / 2)) (by omega), step_even (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega), step_odd ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega), step_odd (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega), step_odd (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even (((3 * ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega), step_even ((((3 * ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega)]
  omega

/-- Residual core congruent to `27 (mod 256)`. -/
def H1 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 256 = 27 → ∃ k : ℕ, T^[k] n < n

/-- Residual core congruent to `91 (mod 256)`. -/
def H2 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 256 = 91 → ∃ k : ℕ, T^[k] n < n

/-- Residual core congruent to `155 (mod 256)`. -/
def H3 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 256 = 155 → ∃ k : ℕ, T^[k] n < n

/-- Residual core congruent to `251 (mod 256)`. -/
def H4 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 256 = 251 → ∃ k : ℕ, T^[k] n < n

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1.H1 := by
  intro h27 h91 h155 h251 n hn hmod
  have h32 : n % 32 = 3 ∨ n % 32 = 11 ∨ n % 32 = 19 ∨ n % 32 = 27 := by omega
  rcases h32 with h | h | h | h
  · exact descent3 hn h
  · exact descent11 hn h
  · exact descent19 hn h
  · have h256 : n % 256 = 27 ∨ n % 256 = 59 ∨ n % 256 = 91 ∨ n % 256 = 123 ∨
        n % 256 = 155 ∨ n % 256 = 187 ∨ n % 256 = 219 ∨ n % 256 = 251 := by omega
    rcases h256 with h | h | h | h | h | h | h | h
    · exact h27 n hn h
    · exact descent59 hn h
    · exact h91 n hn h
    · exact descent123 hn h
    · exact h155 n hn h
    · exact descent187 hn h
    · exact descent219 hn h
    · exact h251 n hn h

end OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1_H1_R1
