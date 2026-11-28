import OMAStatements.S_oeis_a026200
import Mathlib

open OMA.S_oeis_a026200

namespace OMA.A026200Proof

theorem state_succ (n : ℕ) (hn : 1 ≤ n) : state (n + 1) = step (n + 1) (state n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem step_apply (n : ℕ) (f : ℕ → ℕ) (p : ℕ) :
    step n f p = if f (n - (n - 1) / 2) = 0 then (if p = n - (n - 1) / 2 then n else f p)
      else (if p = n + (n - 1) / 2 then n else f p) := by
  unfold step
  split_ifs <;> simp [Function.update_apply, *]

theorem step_occ (n : ℕ) (f : ℕ → ℕ) (p : ℕ) (hf : f p ≠ 0) (hR : n + (n - 1) / 2 ≠ p) :
    step n f p = f p := by
  rw [step_apply]
  by_cases h1 : f (n - (n - 1) / 2) = 0
  · rw [if_pos h1]
    by_cases h2 : p = n - (n - 1) / 2
    · subst h2; exact absurd h1 hf
    · rw [if_neg h2]
  · rw [if_neg h1, if_neg (Ne.symm hR)]

theorem step_free (n : ℕ) (f : ℕ → ℕ) (p : ℕ) (hL : n - (n - 1) / 2 ≠ p)
    (hR : n + (n - 1) / 2 ≠ p) : step n f p = f p := by
  rw [step_apply]
  split_ifs <;> first | rfl | omega

theorem write_L (n : ℕ) (f : ℕ → ℕ) (p : ℕ) (hL : n - (n - 1) / 2 = p) (h0 : f p = 0) :
    step n f p = n := by
  rw [step_apply, hL, if_pos h0, if_pos rfl]

theorem write_R (n : ℕ) (f : ℕ → ℕ) (p : ℕ) (hR : n + (n - 1) / 2 = p)
    (hocc : f (n - (n - 1) / 2) ≠ 0) : step n f p = n := by
  rw [step_apply, if_neg hocc, if_pos hR.symm]

/-- Positions divisible by 3 are still free before step 6q - 2. -/
theorem free3 (q : ℕ) (hq : 1 ≤ q) (n : ℕ) (hn : n < 6 * q - 2) : state n (3 * q) = 0 := by
  induction n with
  | zero => show init (3 * q) = 0; simp only [init]; split_ifs <;> omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; show init (3 * q) = 0; simp only [init]; split_ifs <;> omega
    · rw [state_succ n h, step_free _ _ _ (by omega) (by omega)]
      exact ih (by omega)

/-- After step 2m, position m + 1 is occupied; hence step 2m + 1 always writes at R. -/
theorem occ_half (m : ℕ) (hm : 1 ≤ m) : state (2 * m) (m + 1) ≠ 0 := by
  have h := state_succ (2 * m - 1) (by omega)
  rw [show 2 * m - 1 + 1 = 2 * m by omega] at h
  rw [h, step_apply, show 2 * m - (2 * m - 1) / 2 = m + 1 by omega]
  split_ifs <;> omega

def Inv (f : ℕ → ℕ) : Prop :=
  ∀ p, f p ≠ 0 → (p = 1 ∧ f p = 1) ∨ (2 ≤ f p ∧ f p % 2 = 0 ∧ f p - (f p - 1) / 2 = p) ∨
    (2 ≤ f p ∧ f p + (f p - 1) / 2 = p ∧ (f p % 2 = 1 ∨ (f p - (f p - 1) / 2) % 3 ≠ 0))

theorem inv_init : Inv init := by
  intro p hp
  left
  simp only [init] at hp ⊢
  split_ifs at hp ⊢ with h
  · exact ⟨h, rfl⟩
  · exact absurd rfl hp

theorem inv_state (n : ℕ) : Inv (state n) := by
  induction n with
  | zero => exact inv_init
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact inv_init
    rw [state_succ n h]
    intro p hp
    by_cases h1 : state n (n + 1 - (n + 1 - 1) / 2) = 0
    · by_cases hp' : p = n + 1 - (n + 1 - 1) / 2
      · have hv : step (n + 1) (state n) p = n + 1 := by
          rw [step_apply, if_pos h1, if_pos hp']
        rw [hv]
        right; left
        refine ⟨by omega, ?_, by omega⟩
        by_contra hodd
        -- n + 1 = 2m + 1 with m ≥ 1: position m + 1 is occupied after step 2m
        have hm := occ_half (n / 2) (by omega)
        rw [show 2 * (n / 2) = n by omega, show n / 2 + 1 = n + 1 - (n + 1 - 1) / 2 by omega]
          at hm
        exact hm h1
      · have hv : step (n + 1) (state n) p = state n p := by
          rw [step_apply, if_pos h1, if_neg hp']
        rw [hv] at hp ⊢
        exact ih p hp
    · by_cases hp' : p = n + 1 + (n + 1 - 1) / 2
      · have hv : step (n + 1) (state n) p = n + 1 := by
          rw [step_apply, if_neg h1, if_pos hp']
        rw [hv]
        right; right
        refine ⟨by omega, by omega, ?_⟩
        by_contra hc
        push Not at hc
        -- n + 1 even with L = 3q: then L is still free at step n = 6q - 3
        have hfree := free3 ((n + 1 - (n + 1 - 1) / 2) / 3) (by omega) n (by omega)
        rw [show 3 * ((n + 1 - (n + 1 - 1) / 2) / 3) = n + 1 - (n + 1 - 1) / 2 by omega]
          at hfree
        exact h1 hfree
      · have hv : step (n + 1) (state n) p = state n p := by
          rw [step_apply, if_neg h1, if_neg hp']
        rw [hv] at hp ⊢
        exact ih p hp

theorem stable_occ (p M : ℕ) (hM : 1 ≤ M) (h0 : state M p ≠ 0) (N : ℕ) (hMN : M ≤ N)
    (hR : ∀ n, M < n → n ≤ N → n + (n - 1) / 2 ≠ p) : state N p = state M p := by
  induction N, hMN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih =>
    have ihv := ih (fun n h1 h2 => hR n h1 (by omega))
    rw [state_succ N (by omega), step_occ _ _ _ (by rw [ihv]; exact h0)
      (hR _ (by omega) le_rfl), ihv]

theorem val3 (q : ℕ) (hq : 1 ≤ q) : A026166 (3 * q) = 6 * q - 2 := by
  have h1 : state (6 * q - 3 + 1) (3 * q) = 6 * q - 3 + 1 := by
    rw [state_succ _ (by omega)]
    exact write_L _ _ _ (by omega) (free3 q hq _ (by omega))
  rw [show 6 * q - 3 + 1 = 6 * q - 2 by omega] at h1
  have h2 := stable_occ (3 * q) (6 * q - 2) (by omega) (by rw [h1]; omega) (6 * q) (by omega)
    (fun n hn1 hn2 => by omega)
  unfold A026166
  rw [show 2 * (3 * q) = 6 * q by ring, h2, h1]

theorem val9 (k : ℕ) : A026166 (9 * k + 1) = 6 * k + 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; rfl
  have h1 : state (6 * k + 1) (9 * k + 1) = 6 * k + 1 := by
    rw [state_succ _ (by omega)]
    refine write_R _ _ _ (by omega) ?_
    have := occ_half (3 * k) (by omega)
    rwa [show 2 * (3 * k) = 6 * k by ring, show 3 * k + 1 = 6 * k + 1 - (6 * k + 1 - 1) / 2 by
      omega] at this
  have h2 := stable_occ (9 * k + 1) (6 * k + 1) (by omega) (by rw [h1]; omega)
    (2 * (9 * k + 1)) (by omega) (fun n hn1 hn2 => by omega)
  unfold A026166
  rw [h2, h1]

theorem charP (p : ℕ) :
    (1 ≤ p ∧ A026166 p % 3 = 1) ↔ (1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) := by
  constructor
  · rintro ⟨hp, hv⟩
    refine ⟨hp, ?_⟩
    have hI := inv_state (2 * p) p (by unfold A026166 at hv; omega)
    unfold A026166 at hv
    generalize state (2 * p) p = v at hI hv
    obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 6 ∧ v = 6 * t + r := ⟨v / 6, v % 6, by omega, by omega⟩
    interval_cases r <;> omega
  · rintro ⟨hp, h | h⟩
    · obtain ⟨q, rfl⟩ : ∃ q, p = 3 * q := ⟨p / 3, by omega⟩
      rw [val3 q (by omega)]
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, p = 9 * k + 1 := ⟨p / 9, by omega⟩
      rw [val9 k]
      omega

theorem hpred : (fun p => 1 ≤ p ∧ A026166 p % 3 = 1) =
    (fun p => 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) :=
  funext fun p => propext (charP p)

theorem shiftQ (k : ℕ) : (fun i => 1 ≤ 9 * k + 1 + i ∧ ((9 * k + 1 + i) % 3 = 0 ∨
    (9 * k + 1 + i) % 9 = 1)) = (fun i => 1 ≤ 1 + i ∧ ((1 + i) % 3 = 0 ∨ (1 + i) % 9 = 1)) := by
  funext i
  apply propext
  omega

theorem countQ (k : ℕ) :
    Nat.count (fun p => 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) (9 * k + 1) = 4 * k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 9 * (k + 1) + 1 = 9 * k + 1 + 9 by ring, Nat.count_add, ih]
    simp only [shiftQ]
    have : Nat.count (fun i => 1 ≤ 1 + i ∧ ((1 + i) % 3 = 0 ∨ (1 + i) % 9 = 1)) 9 = 4 := by
      decide
    rw [this]
    ring

theorem countQ' (k b : ℕ) : Nat.count (fun p => 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) (9 * k + 1 + b)
    = 4 * k + Nat.count (fun i => 1 ≤ 1 + i ∧ ((1 + i) % 3 = 0 ∨ (1 + i) % 9 = 1)) b := by
  rw [Nat.count_add, countQ]
  simp only [shiftQ]

theorem nthQ (k : ℕ) :
    Nat.nth (fun p => 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) (4 * k) = 9 * k + 1 ∧
    Nat.nth (fun p => 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) (4 * k + 1) = 9 * k + 3 ∧
    Nat.nth (fun p => 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) (4 * k + 2) = 9 * k + 6 ∧
    Nat.nth (fun p => 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) (4 * k + 3) = 9 * k + 9 := by
  have c0 := countQ' k 0
  have c2 := countQ' k 2
  have c5 := countQ' k 5
  have c8 := countQ' k 8
  have e2 : Nat.count (fun i => 1 ≤ 1 + i ∧ ((1 + i) % 3 = 0 ∨ (1 + i) % 9 = 1)) 2 = 1 := by
    decide
  have e5 : Nat.count (fun i => 1 ≤ 1 + i ∧ ((1 + i) % 3 = 0 ∨ (1 + i) % 9 = 1)) 5 = 2 := by
    decide
  have e8 : Nat.count (fun i => 1 ≤ 1 + i ∧ ((1 + i) % 3 = 0 ∨ (1 + i) % 9 = 1)) 8 = 3 := by
    decide
  rw [Nat.count_zero, add_zero, add_zero] at c0
  rw [e2] at c2
  rw [e5] at c5
  rw [e8] at c8
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← c0]; exact Nat.nth_count (by omega)
  · rw [← c2]; rw [show 9 * k + 3 = 9 * k + 1 + 2 by ring]; exact Nat.nth_count (by omega)
  · rw [← c5]; rw [show 9 * k + 6 = 9 * k + 1 + 5 by ring]; exact Nat.nth_count (by omega)
  · rw [← c8]; rw [show 9 * k + 9 = 9 * k + 1 + 8 by ring]; exact Nat.nth_count (by omega)

theorem a_formula (k : ℕ) : a (4 * k + 1) = 2 * k + 1 ∧ a (4 * k + 2) = 6 * k + 2 ∧
    a (4 * k + 3) = 6 * k + 4 ∧ a (4 * k + 4) = 6 * k + 6 := by
  obtain ⟨n0, n1, n2, n3⟩ := nthQ k
  simp only [a, s, hpred]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 4 * k + 1 - 1 = 4 * k by omega, n0, val9]; omega
  · rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega, n1, show 9 * k + 3 = 3 * (3 * k + 1) by ring,
      val3 _ (by omega)]; omega
  · rw [show 4 * k + 3 - 1 = 4 * k + 2 by omega, n2, show 9 * k + 6 = 3 * (3 * k + 2) by ring,
      val3 _ (by omega)]; omega
  · rw [show 4 * k + 4 - 1 = 4 * k + 3 by omega, n3, show 9 * k + 9 = 3 * (3 * k + 3) by ring,
      val3 _ (by omega)]; omega

/-- Closed form of a(n) for n ≥ 1, by residue of n - 1 mod 4. -/
def cf (n : ℕ) : ℕ :=
  if n = 0 then 0 else if (n - 1) % 4 = 0 then 2 * ((n - 1) / 4) + 1
  else 6 * ((n - 1) / 4) + 2 * ((n - 1) % 4)

theorem a_cf (n : ℕ) (hn : 1 ≤ n) : a n = cf n := by
  obtain ⟨k, h | h | h | h⟩ : ∃ k, n = 4 * k + 1 ∨ n = 4 * k + 2 ∨ n = 4 * k + 3 ∨
      n = 4 * k + 4 := ⟨(n - 1) / 4, by omega⟩ <;> subst h
  · rw [(a_formula k).1]; unfold cf; split_ifs <;> omega
  · rw [(a_formula k).2.1]; unfold cf; split_ifs <;> omega
  · rw [(a_formula k).2.2.1]; unfold cf; split_ifs <;> omega
  · rw [(a_formula k).2.2.2]; unfold cf; split_ifs <;> omega

theorem b_cf (n : ℕ) : (if n = 0 then (0 : ℚ) else (a n : ℚ)) = (cf n : ℚ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [cf]
  · rw [if_neg (by omega), a_cf n h]

end OMA.A026200Proof

open OMA.A026200Proof PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a026200.main := by
  refine ⟨?_, ?_⟩
  · rw [show (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = fun n => (cf n : ℚ) from
      funext b_cf]
    ext d
    have e1 : ∀ A : PowerSeries ℚ,
        A * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2) =
          A - C (2 : ℚ) * (A * X ^ 4) + A * X ^ 8 := by
      intro A
      rw [show (C (2 : ℚ) : PowerSeries ℚ) = 2 from map_ofNat C 2]
      ring
    have e2 : (X * (1 + 2 * X + 4 * X ^ 2 + 6 * X ^ 3 + X ^ 4 + 4 * X ^ 5 + 2 * X ^ 6) :
        PowerSeries ℚ) = X ^ 1 + C (2 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (6 : ℚ) * X ^ 4 +
          X ^ 5 + C (4 : ℚ) * X ^ 6 + C (2 : ℚ) * X ^ 7 := by
      rw [show (C (2 : ℚ) : PowerSeries ℚ) = 2 from map_ofNat C 2,
        show (C (4 : ℚ) : PowerSeries ℚ) = 4 from map_ofNat C 4,
        show (C (6 : ℚ) : PowerSeries ℚ) = 6 from map_ofNat C 6]
      ring
    rw [e1, e2]
    simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_X_pow, coeff_C]
    rcases (show d ≤ 8 ∨ 9 ≤ d by omega) with hd | hd
    · interval_cases d <;> simp [cf] <;> norm_num
    · have key : cf d + cf (d - 8) = 2 * cf (d - 4) := by
        unfold cf
        split_ifs <;> omega
      have keyQ : (cf d : ℚ) + (cf (d - 8) : ℚ) = 2 * (cf (d - 4) : ℚ) := by
        exact_mod_cast key
      have g2 : 2 ≤ d := by omega
      have g3 : 3 ≤ d := by omega
      have g4 : 4 ≤ d := by omega
      have g5 : 5 ≤ d := by omega
      have g6 : 6 ≤ d := by omega
      have g7 : 7 ≤ d := by omega
      have g8 : 8 ≤ d := by omega
      have n1 : d - 1 ≠ 0 := by omega
      have n2 : d - 2 ≠ 0 := by omega
      have n3 : d - 3 ≠ 0 := by omega
      have n4 : d - 4 ≠ 0 := by omega
      have n5 : d - 5 ≠ 0 := by omega
      have n6 : d - 6 ≠ 0 := by omega
      have n7 : d - 7 ≠ 0 := by omega
      have m1 : d ≠ 1 := by omega
      have m5 : d ≠ 5 := by omega
      simp [g2, g3, g4, g5, g6, g7, g8, n1, n2, n3, n4, n5, n6, n7, m1, m5]
      linarith
  · intro n hn
    rw [a_cf n (by omega), a_cf (n - 4) (by omega), a_cf (n - 8) (by omega)]
    unfold cf
    split_ifs <;> omega
