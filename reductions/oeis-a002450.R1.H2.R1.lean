import OMAReductions.R_oeis_a002450_R1

-- Reduction oeis-a002450.R1.H2.R1 of step oeis-a002450.R1.H2
-- Credit: @Ciphore

/-! The odd-start descent step is refined by a modulo-`256` accelerated Collatz sieve.
A kernel-checked finite certificate discharges 109 of the 128 odd residue classes within eight
accelerated steps. The nineteen remaining classes are split into four independent groups. -/

namespace OMA.R_oeis_a002450_R1_H2_R1

open OMA.S_oeis_a002450 Function

/-- Residue classes modulo `256` that resist the eight-step accelerated sieve, group 1. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n % 2 = 1 → n % 256 ∈ ([27, 31, 47, 63, 71] : List ℕ) → ∃ t : ℕ, collatz^[t] n < n

/-- Residue classes modulo `256` that resist the eight-step accelerated sieve, group 2. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n % 2 = 1 → n % 256 ∈ ([91, 103, 111, 127, 155] : List ℕ) → ∃ t : ℕ, collatz^[t] n < n

/-- Residue classes modulo `256` that resist the eight-step accelerated sieve, group 3. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → n % 2 = 1 → n % 256 ∈ ([159, 167, 191, 207, 223] : List ℕ) → ∃ t : ℕ, collatz^[t] n < n

/-- Residue classes modulo `256` that resist the eight-step accelerated sieve, group 4. -/
def H4 : Prop :=
  ∀ n : ℕ, 1 < n → n % 2 = 1 → n % 256 ∈ ([231, 239, 251, 255] : List ℕ) → ∃ t : ℕ, collatz^[t] n < n

theorem accelerated_step (T : ℕ → ℕ)
    (hT : ∀ n, T n = if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) (n : ℕ) :
    ∃ k, collatz^[k] n = T n := by
  by_cases he : n % 2 = 0
  · exact ⟨1, by simp [hT, collatz, he]⟩
  · have h3 : (3 * n + 1) % 2 = 0 := by omega
    refine ⟨2, ?_⟩
    change collatz (collatz n) = T n
    simp [hT, collatz, he, h3]

theorem accelerated_iterate (T : ℕ → ℕ)
    (hT : ∀ n, T n = if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) (n j : ℕ) :
    ∃ k, collatz^[k] n = T^[j] n := by
  induction j generalizing n with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨a, ha⟩ := accelerated_step T hT n
    obtain ⟨b, hb⟩ := ih (T n)
    exact ⟨b + a, by rw [iterate_add_apply, ha, iterate_succ_apply, hb]⟩

/-- The quotient in an entire residue class enters each accelerated iterate affinely. -/
theorem residue_affine (T : ℕ → ℕ)
    (hT : ∀ n, T n = if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) (j r : ℕ) :
    ∃ a : ℕ, ∀ x : ℕ, T^[j] (2 ^ j * x + r) = a * x + T^[j] r := by
  have one_step (x b : ℕ) : T (2 * x + b) = (if b % 2 = 0 then 1 else 3) * x + T b := by
    simp only [hT]
    split_ifs <;> omega
  induction j generalizing r with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨a, ha⟩ := ih (T r)
    let b : ℕ := if r % 2 = 0 then 1 else 3
    refine ⟨a * b, fun x => ?_⟩
    rw [iterate_succ_apply, iterate_succ_apply T j r]
    rw [show 2 ^ (j + 1) * x + r = 2 * (2 ^ j * x) + r by ring, one_step]
    change T^[j] (b * (2 ^ j * x) + T r) = _
    rw [show b * (2 ^ j * x) = 2 ^ j * (b * x) by ring, ha, Nat.mul_assoc]

lemma not_mem_four_append {x : ℕ} {a b c d : List ℕ}
    (ha : x ∉ a) (hb : x ∉ b) (hc : x ∉ c) (hd : x ∉ d) :
    x ∉ a ++ b ++ c ++ d := by
  intro h
  simp only [List.mem_append] at h
  tauto

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem certificate256 (T : ℕ → ℕ)
    (hT : T = fun n => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) :
    ∀ r : Fin 256, (r.val + 2) % 256 ∉ ([27, 31, 47, 63, 71] : List ℕ) ++ ([91, 103, 111, 127, 155] : List ℕ) ++ ([159, 167, 191, 207, 223] : List ℕ) ++ ([231, 239, 251, 255] : List ℕ) →
      ∃ j : Fin 9, T^[j.val] (r.val + 2) < r.val + 2 ∧
        T^[j.val] (256 + (r.val + 2)) ≤ 256 + T^[j.val] (r.val + 2) := by
  subst T
  decide +kernel

theorem forward_descent256 {n : ℕ} (hn : 1 < n)
    (hres : n % 256 ∉ ([27, 31, 47, 63, 71] : List ℕ) ++ ([91, 103, 111, 127, 155] : List ℕ) ++ ([159, 167, 191, 207, 223] : List ℕ) ++ ([231, 239, 251, 255] : List ℕ)) : ∃ k, collatz^[k] n < n := by
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  let r : Fin 256 := ⟨(n - 2) % 256, Nat.mod_lt _ (by decide)⟩
  let b := r.val + 2
  let q := (n - 2) / 256
  have hnq : n = 256 * q + b := by dsimp [q, b, r]; omega
  have hb : b % 256 = n % 256 := by omega
  obtain ⟨j, hdrop, hslope⟩ := certificate256 T rfl r (by simpa only [← hb] using hres)
  change T^[j.val] b < b at hdrop
  change T^[j.val] (256 + b) ≤ 256 + T^[j.val] b at hslope
  let d := 2 ^ (8 - j.val)
  have hj : j.val ≤ 8 := by omega
  have hd : 2 ^ j.val * d = 256 := by
    dsimp [d]
    rw [← pow_add, show j.val + (8 - j.val) = 8 by omega]
    decide
  obtain ⟨a, ha⟩ := residue_affine T (fun _ => rfl) j.val b
  have ha' := ha d
  rw [hd] at ha'
  have had : a * d ≤ 256 := by omega
  have hcalc : T^[j.val] n = a * d * q + T^[j.val] b := by
    calc T^[j.val] n = T^[j.val] (2 ^ j.val * (d * q) + b) := by rw [← Nat.mul_assoc, hd, ← hnq]
         _ = _ := by rw [ha, Nat.mul_assoc]
  obtain ⟨k, hk⟩ := accelerated_iterate T (fun _ => rfl) n j.val
  exact ⟨k, by rw [hk, hcalc]; have := Nat.mul_le_mul_right q had; omega⟩

theorem main : H1 → H2 → H3 → H4 → OMA.R_oeis_a002450_R1.H2 := by
  intro hA hB hC hD n hn hodd
  by_cases hA' : n % 256 ∈ ([27, 31, 47, 63, 71] : List ℕ)
  · exact hA n hn hodd hA'
  by_cases hB' : n % 256 ∈ ([91, 103, 111, 127, 155] : List ℕ)
  · exact hB n hn hodd hB'
  by_cases hC' : n % 256 ∈ ([159, 167, 191, 207, 223] : List ℕ)
  · exact hC n hn hodd hC'
  by_cases hD' : n % 256 ∈ ([231, 239, 251, 255] : List ℕ)
  · exact hD n hn hodd hD'
  apply forward_descent256 hn
  exact not_mem_four_append hA' hB' hC' hD'

end OMA.R_oeis_a002450_R1_H2_R1
