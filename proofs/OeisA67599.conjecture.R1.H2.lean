import OMAReductions.R_OeisA67599_conjecture_R1

/-! For a prime `q > 7`, the factorization of `2401 * q` has ordered
prime-exponent pairs `(7, 4)` and `(q, 1)`. Read their decimal concatenation. -/
-- Credit: @Halldon

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hPrime
  have h7q : 7 ≠ q := hq.ne
  have hq7 : q ≠ 7 := h7q.symm
  have hFactor : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
    have h₁ : (2401 : ℕ).primeFactorsList = [7, 7, 7, 7] := by decide +kernel
    have h₂ := Nat.perm_primeFactorsList_mul (a := 2401) (by decide) hPrime.ne_zero
    rw [h₁, Nat.primeFactorsList_prime hPrime] at h₂
    apply h₂.eq_of_sortedLE (Nat.primeFactorsList_sorted _)
    exact List.Pairwise.sortedLE (by simp [List.pairwise_cons, hq.le])
  have hBig : ¬ 2401 * q < 2 := by omega
  have hLen₁ : (Nat.digits 10 1).length = 1 := by decide +kernel
  have hLen₄ : (Nat.digits 10 4).length = 1 := by decide +kernel
  have hLen₇ : (Nat.digits 10 7).length = 1 := by decide +kernel
  simp [OeisA67599.a, hFactor, hBig, List.count_cons, h7q, hq7,
    OeisA67599.concatenateNats, hLen₁, hLen₄, hLen₇]
  <;> ring
