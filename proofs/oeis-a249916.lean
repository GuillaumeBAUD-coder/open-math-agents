import OMAStatements.S_oeis_a249916

/-!
The identities were confirmed in OEIS A249916 by Jianing Song (January 28, 2019).
Taking two differences of the defining recurrence gives the five-term relation
and hence the generating function. A shift by six adds twelve, so the first six
values determine every fiber of the sequence.
-/

namespace OEISA249916

open OMA.S_oeis_a249916 PowerSeries

private theorem step (n : ℕ) : a (n + 3) = 4 * ((n : ℤ) + 2) - a n := rfl

private theorem recurrence (n : ℕ) (hn : 4 < n) :
    a n = 2 * a (n - 1) - a (n - 2) - a (n - 3) + 2 * a (n - 4) - a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 5 := ⟨n - 5, by omega⟩
  have e5 : a (k + 5) = 4 * ((k : ℤ) + 4) - a (k + 2) := by
    rw [show k + 5 = (k + 2) + 3 by omega, step]
    push_cast
    ring
  have e4 : a (k + 4) = 4 * ((k : ℤ) + 3) - a (k + 1) := by
    rw [show k + 4 = (k + 1) + 3 by omega, step]
    push_cast
    ring
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega, e5, e4, step]
  ring

private theorem generating :
    PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X ^ 3)) = 1 - X + 4 * X ^ 2 - X ^ 3 + X ^ 4 := by
  let G := PowerSeries.mk a
  have hl : G * ((1 - X) ^ 2 * (1 + X ^ 3)) =
      G - (G * X ^ 1 + G * X ^ 1) + G * X ^ 2 + G * X ^ 3 -
        (G * X ^ 4 + G * X ^ 4) + G * X ^ 5 := by ring
  have hr : (1 : ℤ⟦X⟧) - X + 4 * X ^ 2 - X ^ 3 + X ^ 4 =
      X ^ 0 - X ^ 1 + (X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2) - X ^ 3 + X ^ 4 := by ring
  change G * _ = _
  rw [hl, hr]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk]
  by_cases hn : 4 < n
  · have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h0' : n ≠ 0 := by omega
    have h1' : n ≠ 1 := by omega
    have h2' : n ≠ 2 := by omega
    have h3' : n ≠ 3 := by omega
    have h4' : n ≠ 4 := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5,
      if_neg h0', if_neg h1', if_neg h2', if_neg h3', if_neg h4']
    have h := recurrence n hn
    omega
  · interval_cases n <;> norm_num [a]

private theorem shift_six (n : ℕ) : a (n + 6) = a n + 12 := by
  rw [show n + 6 = (n + 3) + 3 by omega, step (n + 3), step n]
  push_cast
  ring

private theorem blocks (q r : ℕ) : a (6 * q + r) = 12 * (q : ℤ) + a r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 6 * (q + 1) + r = (6 * q + r) + 6 by omega, shift_six, ih]
    push_cast
    ring

private theorem base_value (r : ℕ) (hr : r < 6) :
    a r = if r ≤ 1 then 1 else if r = 2 then 5 else if r = 3 then 7 else 11 := by
  interval_cases r <;> norm_num [a]

private theorem value (n : ℕ) :
    a n = 12 * ((n / 6 : ℕ) : ℤ) +
      (if n % 6 ≤ 1 then 1 else if n % 6 = 2 then 5 else if n % 6 = 3 then 7 else 11) := by
  calc
    a n = a (6 * (n / 6) + n % 6) := congrArg a (Nat.div_add_mod n 6).symm
    _ = _ := by rw [blocks, base_value _ (Nat.mod_lt _ (by decide))]

private theorem multiplicity (m : ℕ) :
    {n : ℕ | a n = (m : ℤ)}.ncard =
      if m % 12 = 1 ∨ m % 12 = 11 then 2 else if m % 12 = 5 ∨ m % 12 = 7 then 1 else 0 := by
  let k := 6 * (m / 12)
  have hits (n : ℕ) :
      a n = (m : ℤ) ↔
        (m % 12 = 1 ∧ (n = k ∨ n = k + 1)) ∨
        (m % 12 = 5 ∧ n = k + 2) ∨ (m % 12 = 7 ∧ n = k + 3) ∨
        (m % 12 = 11 ∧ (n = k + 4 ∨ n = k + 5)) := by
    have hm : (12 : ℤ) * ((m / 12 : ℕ) : ℤ) + ((m % 12 : ℕ) : ℤ) = (m : ℤ) := by
      exact_mod_cast Nat.div_add_mod m 12
    have hnr := Nat.div_add_mod n 6
    have hnlt := Nat.mod_lt n (by decide : 0 < 6)
    have hmlt := Nat.mod_lt m (by decide : 0 < 12)
    rw [value, ← hm]
    dsimp [k]
    split_ifs <;> omega
  by_cases h1 : m % 12 = 1
  · have hs : {n : ℕ | a n = (m : ℤ)} = {k, k + 1} := by
      ext n
      simp [hits, h1]
    rw [hs, Set.ncard_pair (by omega : k ≠ k + 1)]
    simp [h1]
  by_cases h5 : m % 12 = 5
  · have hs : {n : ℕ | a n = (m : ℤ)} = {k + 2} := by
      ext n
      simp [hits, h5]
    simp [hs, h5]
  by_cases h7 : m % 12 = 7
  · have hs : {n : ℕ | a n = (m : ℤ)} = {k + 3} := by
      ext n
      simp [hits, h7]
    simp [hs, h7]
  by_cases h11 : m % 12 = 11
  · have hs : {n : ℕ | a n = (m : ℤ)} = {k + 4, k + 5} := by
      ext n
      simp [hits, h11]
    rw [hs, Set.ncard_pair (by omega : k + 4 ≠ k + 5)]
    simp [h11]
  have hs : {n : ℕ | a n = (m : ℤ)} = ∅ := by
    ext n
    simp [hits, h1, h5, h7, h11]
  simp [hs, h1, h5, h7, h11]

end OEISA249916

theorem OMA.solution : type_of% @OMA.S_oeis_a249916.main :=
  ⟨OEISA249916.recurrence, OEISA249916.generating, OEISA249916.multiplicity⟩
