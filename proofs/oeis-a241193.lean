import OMAStatements.S_oeis_a241193
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of the conjectured recurrence for A241193.

1. With `j = n - k`, the summand at `n = m + 1` is
   `F m j = (2m+j+1)! / (m!^2 j! (m+j+1)) = C(2m+j+1, m) C(m+j, j)`, so `a(m+1) = Σ_{j ≤ m} F m j`.
2. Zeilberger's algorithm gives the certificate
   `F m j + F (m+1) j = G m (j+1) - G m j` with `G m j = j (10n^2 + 8jn + 3n + 2j^2 + j) / (2 n^2 (2n+1)) F m j`
   (`n = m + 1`), checked as a rational-function identity. Summing over `j ≤ m` gives
   `(2m+3) (a(m+1) + a(m+2) - F(m+1,m+1)) = (10m+12) F(m, m+1)`.
3. The recurrence, multiplied by `(m+1)^2 (m+2)^2` (with `n = m + 4`), is an explicit linear
   combination of three instances of this relation and five factorial-ratio identities for `F`.
-/

namespace OMA.A241193Proof

open OMA.S_oeis_a241193

/-- The summand at `n = m + 1` after the substitution `j = n - k`. -/
def F (m j : ℕ) : ℚ :=
  ((2 * m + j + 1).factorial : ℚ) / ((m.factorial : ℚ) * m.factorial * j.factorial * ((m : ℚ) + j + 1))

/-- Shift in the summation index. -/
theorem F_succ_j (m j : ℕ) :
    F m (j + 1) * (((j : ℚ) + 1) * ((m : ℚ) + j + 2)) =
      F m j * ((2 * (m : ℚ) + j + 2) * ((m : ℚ) + j + 1)) := by
  unfold F
  rw [show 2 * m + (j + 1) + 1 = 2 * m + j + 1 + 1 by ring, Nat.factorial_succ (2 * m + j + 1),
    Nat.factorial_succ j]
  push_cast
  have h1 : ((m : ℚ) + j + 1) ≠ 0 := by positivity
  have h2 : ((m : ℚ) + (j + 1) + 1) ≠ 0 := by positivity
  have h3 : ((m.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have h4 : ((j.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- Shift in `m`. -/
theorem F_succ_m (m j : ℕ) :
    F (m + 1) j * (((m : ℚ) + 1) ^ 2 * ((m : ℚ) + j + 2)) =
      F m j * ((2 * (m : ℚ) + j + 2) * (2 * (m : ℚ) + j + 3) * ((m : ℚ) + j + 1)) := by
  unfold F
  rw [show 2 * (m + 1) + j + 1 = 2 * m + j + 1 + 1 + 1 by ring, Nat.factorial_succ (2 * m + j + 1 + 1),
    Nat.factorial_succ (2 * m + j + 1), Nat.factorial_succ m]
  push_cast
  have h1 : ((m : ℚ) + j + 1) ≠ 0 := by positivity
  have h2 : ((m : ℚ) + 1 + j + 1) ≠ 0 := by positivity
  have h3 : ((m.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have h4 : ((j.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- Zeilberger's certificate: `F m j + F (m+1) j = G m (j+1) - G m j`. -/
def G (m j : ℕ) : ℚ :=
  (j : ℚ) * (10 * ((m : ℚ) + 1) ^ 2 + 8 * j * ((m : ℚ) + 1) + 3 * ((m : ℚ) + 1) + 2 * (j : ℚ) ^ 2 + j) /
    (((m : ℚ) + 1) ^ 2 * (2 * (2 * ((m : ℚ) + 1) + 1))) * F m j

theorem tele (m j : ℕ) : F m j + F (m + 1) j = G m (j + 1) - G m j := by
  have e1 : F m (j + 1) =
      F m j * ((2 * (m : ℚ) + j + 2) * ((m : ℚ) + j + 1)) / (((j : ℚ) + 1) * ((m : ℚ) + j + 2)) :=
    (eq_div_iff (by positivity)).mpr (F_succ_j m j)
  have e2 : F (m + 1) j =
      F m j * ((2 * (m : ℚ) + j + 2) * (2 * (m : ℚ) + j + 3) * ((m : ℚ) + j + 1)) /
        (((m : ℚ) + 1) ^ 2 * ((m : ℚ) + j + 2)) :=
    (eq_div_iff (by positivity)).mpr (F_succ_m m j)
  unfold G
  rw [e1, e2]
  push_cast
  have h1 : ((m : ℚ) + j + 2) ≠ 0 := by positivity
  have h2 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have h3 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h4 : (2 * (2 * ((m : ℚ) + 1) + 1)) ≠ 0 := by positivity
  field_simp
  ring

theorem sum_tele (m J : ℕ) : ∑ j ∈ Finset.range J, (F m j + F (m + 1) j) = G m J := by
  induction J with
  | zero => simp [G]
  | succ J ih => rw [Finset.sum_range_succ, ih, tele]; ring

/-- The definition, re-indexed by `j = n - k`. -/
theorem a_eq (m : ℕ) : a (m + 1) = ∑ j ∈ Finset.range (m + 1), F m j := by
  unfold a
  refine Finset.sum_nbij' (fun k => m + 1 - k) (fun j => m + 1 - j) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨j, hj, rfl⟩ : ∃ j, j ≤ m ∧ k = m + 1 - j := ⟨m + 1 - k, by omega, by omega⟩
    rw [show m + 1 - (m + 1 - j) = j by omega, show 3 * (m + 1) - (m + 1 - j) - 2 = 2 * m + j by omega,
      show m + 1 - 1 = m by omega]
    unfold F
    rw [Nat.cast_sub (by omega : j ≤ m + 1), Nat.factorial_succ (2 * m + j)]
    push_cast
    rw [show (2 * ((m : ℚ) + 1) - ((m : ℚ) + 1 - j)) = (m : ℚ) + j + 1 by ring]
    have h1 : ((m : ℚ) + j + 1) ≠ 0 := by positivity
    have h3 : ((m.factorial : ℕ) : ℚ) ≠ 0 := by positivity
    have h4 : ((j.factorial : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
    ring

theorem pair (m : ℕ) : a (m + 1) + a (m + 2) = G m (m + 1) + F (m + 1) (m + 1) := by
  rw [a_eq, show m + 2 = m + 1 + 1 by ring, a_eq (m + 1), Finset.sum_range_succ _ (m + 1),
    ← sum_tele m (m + 1), Finset.sum_add_distrib]
  ring

theorem G_diag (m : ℕ) : G m (m + 1) * (2 * (m : ℚ) + 3) = (10 * (m : ℚ) + 12) * F m (m + 1) := by
  unfold G
  push_cast
  have h3 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h4 : (2 * (2 * ((m : ℚ) + 1) + 1)) ≠ 0 := by positivity
  field_simp
  ring

/-- `a(n) + a(n+1)` is a hypergeometric term (here in the form used below). -/
theorem pairZ (m : ℕ) :
    (2 * (m : ℚ) + 3) * (a (m + 1) + a (m + 2) - F (m + 1) (m + 1)) - (10 * (m : ℚ) + 12) * F m (m + 1) = 0 := by
  linear_combination (2 * (m : ℚ) + 3) * pair m + G_diag m

end OMA.A241193Proof

open OMA.S_oeis_a241193 OMA.A241193Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a241193.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
  have r0 := pairZ m
  have r1 := pairZ (m + 1)
  have r2 := pairZ (m + 2)
  have s1 := F_succ_m m (m + 1)
  have t1 := F_succ_j (m + 1) (m + 1)
  have s2 := F_succ_m (m + 1) (m + 2)
  have t2 := F_succ_j (m + 2) (m + 2)
  have s3 := F_succ_m (m + 2) (m + 3)
  rw [show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring] at r1
  rw [show m + 2 + 1 = m + 3 by ring, show m + 2 + 2 = m + 4 by ring] at r2
  rw [show m + 1 + 1 = m + 2 by ring] at t1 s2
  rw [show m + 2 + 1 = m + 3 by ring] at t2 s3
  push_cast at r0 r1 r2 s1 t1 s2 t2 s3 ⊢
  have hD : ((m : ℚ) + 1) ^ 2 * ((m : ℚ) + 2) ^ 2 ≠ 0 := by positivity
  refine (mul_eq_zero.mp ?_).resolve_left hD
  linear_combination (-162*(m:ℚ)^6 - 1458*(m:ℚ)^5 - 5382*(m:ℚ)^4 - 10422*(m:ℚ)^3 - 11160*(m:ℚ)^2 - 6264*(m:ℚ) - 1440) * r0 + (33*(m:ℚ)^6 + 378*(m:ℚ)^5 + 1764*(m:ℚ)^4 + 4266*(m:ℚ)^3 + 5607*(m:ℚ)^2 + 3780*(m:ℚ) + 1020) * r1 + (-(m:ℚ)^6 - 12*(m:ℚ)^5 - 58*(m:ℚ)^4 - 144*(m:ℚ)^3 - 193*(m:ℚ)^2 - 132*(m:ℚ) - 36) * r2 + (90*(m:ℚ)^4 + 618*(m:ℚ)^3 + 1572*(m:ℚ)^2 + 1752*(m:ℚ) + 720) * s1 + (84*(m:ℚ)^5 + 612*(m:ℚ)^4 + 1740*(m:ℚ)^3 + 2412*(m:ℚ)^2 + 1632*(m:ℚ) + 432) * t1 + (-9*(m:ℚ)^4 - 88*(m:ℚ)^3 - 262*(m:ℚ)^2 - 296*(m:ℚ) - 113) * s2 + (-14*(m:ℚ)^5 - 130*(m:ℚ)^4 - 458*(m:ℚ)^3 - 766*(m:ℚ)^2 - 608*(m:ℚ) - 184) * t2 + (-(m:ℚ)^4 - 6*(m:ℚ)^3 - 13*(m:ℚ)^2 - 12*(m:ℚ) - 4) * s3
