import OMAStatements.S_oeis_a249916

open OMA.S_oeis_a249916 PowerSeries

private lemma a_rec : ∀ n : ℕ, 4 < n →
    a n = 2 * a (n - 1) - a (n - 2) - a (n - 3) + 2 * a (n - 4) - a (n - 5) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h1 : a (k + 5) = 4 * (((k + 2 : ℕ) : ℤ) + 2) - a (k + 2) := rfl
  have h2 : a (k + 4) = 4 * (((k + 1 : ℕ) : ℤ) + 2) - a (k + 1) := rfl
  have h3 : a (k + 3) = 4 * ((k : ℤ) + 2) - a k := rfl
  push_cast at h1 h2
  change a (k + 5) = 2 * a (k + 4) - a (k + 3) - a (k + 2) + 2 * a (k + 1) - a k
  linarith

private lemma a_gf :
    PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X ^ 3)) = 1 - X + 4 * X ^ 2 - X ^ 3 + X ^ 4 := by
  set f : PowerSeries ℤ := PowerSeries.mk a
  have hlhs : f * ((1 - X) ^ 2 * (1 + X ^ 3)) =
      f - f * X ^ 1 - f * X ^ 1 + f * X ^ 2 + f * X ^ 3 - f * X ^ 4 - f * X ^ 4 + f * X ^ 5 := by
    ring
  have hrhs : (1 : PowerSeries ℤ) - X + 4 * X ^ 2 - X ^ 3 + X ^ 4 =
      1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 + X ^ 4 := by
    ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow]
  have hmk : ∀ k, PowerSeries.coeff k f = a k := fun k => PowerSeries.coeff_mk k a
  simp only [hmk]
  match n with
  | 0 => simp [a]
  | 1 => simp [a]
  | 2 => simp [a]
  | 3 => simp [a]
  | 4 => simp [a]
  | m + 5 =>
    have hrec := a_rec (m + 5) (by omega)
    simp only [show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega,
      show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, ↓reduceIte,
      show m + 5 ≠ 0 by omega, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega,
      show m + 5 ≠ 3 by omega, show m + 5 ≠ 4 by omega]
    linarith

private lemma a_add_six (n : ℕ) : a (n + 6) = a n + 12 := by
  have h1 : a (n + 6) = 4 * (((n + 3 : ℕ) : ℤ) + 2) - a (n + 3) := rfl
  have h2 : a (n + 3) = 4 * ((n : ℤ) + 2) - a n := rfl
  push_cast at h1
  linarith

private lemma a_mul_six_add (k r : ℕ) : a (6 * k + r) = 12 * (k : ℤ) + a r := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : 6 * (k + 1) + r = (6 * k + r) + 6 := by omega
    rw [h, a_add_six, ih]
    push_cast
    ring

private lemma a_eq_div_mod (n : ℕ) : a n = 12 * ((n / 6 : ℕ) : ℤ) + a (n % 6) := by
  have h := a_mul_six_add (n / 6) (n % 6)
  rwa [Nat.div_add_mod] at h

private lemma a_mod_six_vals (n : ℕ) :
    (n % 6 = 0 ∧ a n = 12 * ((n / 6 : ℕ) : ℤ) + 1) ∨
    (n % 6 = 1 ∧ a n = 12 * ((n / 6 : ℕ) : ℤ) + 1) ∨
    (n % 6 = 2 ∧ a n = 12 * ((n / 6 : ℕ) : ℤ) + 5) ∨
    (n % 6 = 3 ∧ a n = 12 * ((n / 6 : ℕ) : ℤ) + 7) ∨
    (n % 6 = 4 ∧ a n = 12 * ((n / 6 : ℕ) : ℤ) + 11) ∨
    (n % 6 = 5 ∧ a n = 12 * ((n / 6 : ℕ) : ℤ) + 11) := by
  have h := a_eq_div_mod n
  have h0 : a 0 = 1 := rfl
  have h1 : a 1 = 1 := rfl
  have h2 : a 2 = 5 := rfl
  have h3 : a 3 = 7 := by decide
  have h4 : a 4 = 11 := by decide
  have h5 : a 5 = 11 := by decide
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr
  · left; exact ⟨hr, by rw [h, hr, h0]⟩
  · right; left; exact ⟨hr, by rw [h, hr, h1]⟩
  · right; right; left; exact ⟨hr, by rw [h, hr, h2]⟩
  · right; right; right; left; exact ⟨hr, by rw [h, hr, h3]⟩
  · right; right; right; right; left; exact ⟨hr, by rw [h, hr, h4]⟩
  · right; right; right; right; right; exact ⟨hr, by rw [h, hr, h5]⟩

private lemma a_ncard (m : ℕ) :
    {n : ℕ | a n = (m : ℤ)}.ncard =
      if m % 12 = 1 ∨ m % 12 = 11 then 2 else if m % 12 = 5 ∨ m % 12 = 7 then 1 else 0 := by
  by_cases h1 : m % 12 = 1
  · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12), 6 * (m / 12) + 1} := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases a_mod_six_vals n with ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ <;>
        omega
    rw [hs, Set.ncard_pair (by omega)]
    simp [h1]
  · by_cases h11 : m % 12 = 11
    · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12) + 4, 6 * (m / 12) + 5} := by
        ext n
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases a_mod_six_vals n with ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ <;>
          omega
      rw [hs, Set.ncard_pair (by omega)]
      simp [h11]
    · by_cases h5 : m % 12 = 5
      · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12) + 2} := by
          ext n
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
          rcases a_mod_six_vals n with ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ <;>
            omega
        rw [hs, Set.ncard_singleton]
        simp [h5]
      · by_cases h7 : m % 12 = 7
        · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12) + 3} := by
            ext n
            simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
            rcases a_mod_six_vals n with ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ <;>
              omega
          rw [hs, Set.ncard_singleton]
          simp [h7]
        · have hs : {n : ℕ | a n = (m : ℤ)} = ∅ := by
            ext n
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            rcases a_mod_six_vals n with ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ | ⟨hr, ha⟩ <;>
              omega
          rw [hs, Set.ncard_empty]
          simp [h1, h11, h5, h7]

theorem OMA.solution : type_of% @OMA.S_oeis_a249916.main :=
  ⟨a_rec, a_gf, a_ncard⟩
