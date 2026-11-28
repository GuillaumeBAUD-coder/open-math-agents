import OMAStatements.S_oeis_a089640

namespace OMA.S_oeis_a089640_Proof

open OMA.S_oeis_a089640 PowerSeries

private lemma a_rec : ∀ n : ℕ, 5 < n → a n = a (n - 3) + 2 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 6 := ⟨n - 6, by omega⟩
  have h1 : r + 6 - 1 = (r + 2) + 3 := by omega
  have h2 : r + 6 - 3 - 1 = r + 2 := by omega
  have h3 : r + 6 - 4 - 1 = r + 1 := by omega
  have h4 : r + 6 - 5 - 1 = r := by omega
  simp only [a, h1, h2, h3, h4]
  change ways ((r + 2) + 3) true = ways (r + 2) true + 2 * ways (r + 1) true + ways r true
  have hw1 : ways ((r + 2) + 3) true = ways ((r + 1) + 3) false + ways (r + 3) false := rfl
  have hw2 : ways ((r + 1) + 3) false = ways (r + 2) true + ways (r + 1) true := rfl
  have hw3 : ways (r + 3) false = ways (r + 1) true + ways r true := rfl
  rw [hw1, hw2, hw3]
  ring

private lemma coeff_X_pow_mul (A : PowerSeries ℤ) (d k : ℕ) :
    PowerSeries.coeff k (A * X ^ d) = if d ≤ k then PowerSeries.coeff (k - d) A else 0 := by
  rw [mul_comm, PowerSeries.coeff_X_pow_mul']

private lemma gf_eq :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) =
      X * (-X ^ 2 - X - 1) := by
  let A : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n)
  have hcoeff : ∀ k : ℕ, PowerSeries.coeff k A = if k = 0 then (0 : ℤ) else (a k : ℤ) := by
    intro k; simp [A]
  have hrhs : X * (-X ^ 2 - X - 1 : PowerSeries ℤ) = -(X ^ 3) - X ^ 2 - X := by ring
  have hlhs : A * (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) =
      A * X ^ 5 + A * X ^ 4 + A * X ^ 4 + A * X ^ 3 - A := by
    ring
  change A * (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) = X * (-X ^ 2 - X - 1)
  rw [hlhs, hrhs]
  ext k
  simp only [map_sub, map_add, map_neg, coeff_X_pow_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_X, hcoeff]
  rcases k with _ | _ | _ | _ | _ | _ | m
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have hrec := a_rec (m + 6) (by omega)
    have hrec_z : (a (m + 6) : ℤ) = (a (m + 3) : ℤ) + 2 * (a (m + 2) : ℤ) + (a (m + 1) : ℤ) := by
      have h1 : m + 6 - 3 = m + 3 := by omega
      have h2 : m + 6 - 4 = m + 2 := by omega
      have h3 : m + 6 - 5 = m + 1 := by omega
      rw [h1, h2, h3] at hrec
      exact_mod_cast hrec
    have hc1 : m + 6 - 5 = m + 1 := by omega
    have hc2 : m + 6 - 4 = m + 2 := by omega
    have hc3 : m + 6 - 3 = m + 3 := by omega
    simp only [show 5 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
      ↓reduceIte, hc1, hc2, hc3, show m + 1 ≠ 0 by omega, show m + 2 ≠ 0 by omega,
      show m + 3 ≠ 0 by omega, show m + 6 ≠ 0 by omega, show m + 6 ≠ 3 by omega,
      show m + 6 ≠ 2 by omega, show m + 6 ≠ 1 by omega]
    linarith

theorem main_proof :
    (∀ n : ℕ, 5 < n → a n = a (n - 3) + 2 * a (n - 4) + a (n - 5)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) =
        X * (-X ^ 2 - X - 1) :=
  ⟨a_rec, gf_eq⟩

end OMA.S_oeis_a089640_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a089640.main :=
  OMA.S_oeis_a089640_Proof.main_proof
