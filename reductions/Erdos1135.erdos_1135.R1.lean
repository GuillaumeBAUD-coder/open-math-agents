import FormalConjectures.ErdosProblems.«1135»

/-! A forward and backward sieve for least counterexamples to the Collatz conjecture.
The short forward steps exclude all but 19 residues modulo 256. Smaller odd
predecessors exclude additional classes modulo 27 among integers coprime to 3.
The two outstanding descent assertions cover 190 of the 6912 residue classes.
-/

namespace OMA.R_Erdos1135_erdos_1135_R1

open CollatzConjecture Function

/-- Descent for the remaining residues congruent to one modulo three. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n % 27 ∈ ([1, 4, 7, 10, 16, 19, 25] : List ℕ) →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ) → ∃ k : ℕ, collatzStep^[k] n < n

/-- The remaining residues congruent to two modulo three have their immediate
smaller odd predecessor divisible by three. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n % 9 = 5 →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ) → ∃ k : ℕ, collatzStep^[k] n < n

theorem step_even (n : ℕ) : collatzStep (2 * n) = n := by
  simp [collatzStep]

theorem hits_step (n : ℕ) : (∃ k, collatzStep^[k] n = 1) ↔
    ∃ k, collatzStep^[k] (collatzStep n) = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change n = 1 at hk
      subst n
      exact ⟨2, by decide⟩
    | succ k => exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, hk⟩

theorem hits_iterate (n k : ℕ) : (∃ t, collatzStep^[t] n = 1) ↔
    ∃ t, collatzStep^[t] (collatzStep^[k] n) = 1 := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => exact (hits_step n).trans (ih (collatzStep n))

theorem accelerated_step (T : ℕ → ℕ)
    (hT : ∀ n, T n = if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) (n : ℕ) :
    ∃ k, collatzStep^[k] n = T n := by
  by_cases he : n % 2 = 0
  · exact ⟨1, by simp [hT, collatzStep, Nat.even_iff, he]⟩
  · have h3 : (3 * n + 1) % 2 = 0 := by omega
    refine ⟨2, ?_⟩
    change collatzStep (collatzStep n) = T n
    simp [hT, collatzStep, Nat.even_iff, he, h3]

theorem accelerated_iterate (T : ℕ → ℕ)
    (hT : ∀ n, T n = if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) (n j : ℕ) :
    ∃ k, collatzStep^[k] n = T^[j] n := by
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem short_certificate (T : ℕ → ℕ)
    (hT : T = fun n => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) :
    ∀ r : Fin 256, (r.val + 2) % 256 ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155,
      159, 167, 191, 207, 223, 231, 239, 251, 255] : List ℕ) →
      ∃ j : Fin 9, T^[j.val] (r.val + 2) < r.val + 2 ∧
        T^[j.val] (256 + (r.val + 2)) ≤ 256 + T^[j.val] (r.val + 2) := by
  subst T
  decide +kernel

theorem forward_descent {n : ℕ} (hn : 1 < n)
    (hres : n % 256 ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191,
      207, 223, 231, 239, 251, 255] : List ℕ)) : ∃ k, collatzStep^[k] n < n := by
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  let r : Fin 256 := ⟨(n - 2) % 256, Nat.mod_lt _ (by decide)⟩
  let b := r.val + 2
  let q := (n - 2) / 256
  have hnq : n = 256 * q + b := by dsimp [q, b, r]; omega
  have hb : b % 256 = n % 256 := by omega
  obtain ⟨j, hdrop, hslope⟩ := short_certificate T rfl r (by simpa only [← hb] using hres)
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

theorem iterate_pos_mod_three {n : ℕ} (hn : 0 < n) (h3 : n % 3 ≠ 0) (k : ℕ) :
    0 < collatzStep^[k] n ∧ (collatzStep^[k] n) % 3 ≠ 0 := by
  induction k generalizing n with
  | zero => exact ⟨hn, h3⟩
  | succ k ih =>
    rw [iterate_succ_apply]
    have hs : 0 < collatzStep n ∧ (collatzStep n) % 3 ≠ 0 := by
      simp only [collatzStep, Nat.even_iff]
      split <;> omega
    exact ih hs.1 hs.2

theorem odd_predecessor {a n : ℕ} (ha : a % 2 = 1) (h : 3 * a + 1 = 2 * n) :
    (∃ k, collatzStep^[k] a = 1) ↔ ∃ k, collatzStep^[k] n = 1 := by
  have hstep : collatzStep a = 2 * n := by simpa [collatzStep, Nat.even_iff, ha] using h
  calc (∃ k, collatzStep^[k] a = 1) ↔ ∃ k, collatzStep^[k] (collatzStep a) = 1 := hits_step a
       _ ↔ _ := by rw [hstep]; simpa only [step_even] using hits_step (2 * n)

/-- For these four classes a smaller positive integer coprime to three lies in the same orbit tree. -/
theorem smaller_predecessor {n : ℕ} (hn : 1 < n)
    (hres : n % 9 = 2 ∨ n % 9 = 8 ∨ n % 27 = 13 ∨ n % 27 = 22) :
    ∃ a, 0 < a ∧ a < n ∧ a % 3 ≠ 0 ∧
      ((∃ k, collatzStep^[k] a = 1) ↔ ∃ k, collatzStep^[k] n = 1) := by
  by_cases hshort : n % 9 = 2 ∨ n % 9 = 8
  · let a := (2 * n - 1) / 3
    obtain ⟨ha, hlt, hmod, hodd, heq⟩ : 0 < a ∧ a < n ∧ a % 3 ≠ 0 ∧ a % 2 = 1 ∧
        3 * a + 1 = 2 * n := by dsimp [a]; omega
    exact ⟨a, ha, hlt, hmod, odd_predecessor hodd heq⟩
  · let a := (8 * n - 5) / 9
    let b := (4 * n - 1) / 3
    have hr : n % 27 = 13 ∨ n % 27 = 22 := by tauto
    obtain ⟨ha, hlt, hmod, haodd, haeq, hbodd, hbeq⟩ :
        0 < a ∧ a < n ∧ a % 3 ≠ 0 ∧ a % 2 = 1 ∧ 3 * a + 1 = 2 * b ∧
          b % 2 = 1 ∧ 3 * b + 1 = 2 * (2 * n) := by dsimp [a, b]; omega
    have hlast := hits_step (2 * n)
    rw [step_even] at hlast
    exact ⟨a, ha, hlt, hmod, (odd_predecessor haodd haeq).trans ((odd_predecessor hbodd hbeq).trans hlast)⟩

theorem classified_mod_three (n : ℕ) (hn : n % 3 ≠ 0) :
    (n % 9 = 2 ∨ n % 9 = 8 ∨ n % 27 = 13 ∨ n % 27 = 22) ∨
    n % 27 ∈ ([1, 4, 7, 10, 16, 19, 25] : List ℕ) ∨ n % 9 = 5 := by
  have h3 : (n % 27) % 3 = n % 3 := Nat.mod_mod_of_dvd _ (by decide)
  have h9 : (n % 27) % 9 = n % 9 := Nat.mod_mod_of_dvd _ (by decide)
  generalize h : n % 27 = r at *
  have hr : r < 27 := h ▸ Nat.mod_lt _ (by decide)
  interval_cases r <;> norm_num at * <;> aesop

theorem main : H1 → H2 → type_of% @Erdos1135.erdos_1135 := by
  intro h1 h2
  have good : ∀ n : ℕ, 0 < n → n % 3 ≠ 0 → ∃ k, collatzStep^[k] n = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn h3
      by_cases hbase : n = 1
      · exact ⟨0, hbase⟩
      have hlarge : 1 < n := by omega
      rcases classified_mod_three n h3 with hpred | hremaining
      · obtain ⟨a, ha, hlt, hmod, hiff⟩ := smaller_predecessor hlarge hpred
        exact hiff.mp (ih a hlt ha hmod)
      · have descend : ∃ k, collatzStep^[k] n < n := by
          by_cases hres : n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167,
              191, 207, 223, 231, 239, 251, 255] : List ℕ)
          · exact hremaining.elim (fun h => h1 n hlarge h hres) (fun h => h2 n hlarge h hres)
          · exact forward_descent hlarge hres
        obtain ⟨k, hk⟩ := descend
        obtain ⟨hp, hmod⟩ := iterate_pos_mod_three hn h3 k
        exact (hits_iterate n k).mpr (ih _ hk hp hmod)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    apply (hits_step n).mpr
    by_cases he : Even n
    · rw [collatzStep, if_pos he]
      apply ih _ (by omega)
      rw [Nat.even_iff] at he
      omega
    · rw [collatzStep, if_neg he]
      exact good _ (by omega) (by omega)

end OMA.R_Erdos1135_erdos_1135_R1
