import FormalConjectures.Wikipedia.Hadamard

-- Reduction Hadamard.HadamardConjecture.R1 of Hadamard's conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
# Hadamard's conjecture: Paley I, Paley II, and the odd residual core

Sylvester's doubling `M ↦ [[M, M], [M, -M]]` turns a Hadamard matrix of order `n`
into one of order `2n`, so it suffices to treat orders `4k` with `k` odd.
Paley's two constructions (R. E. A. C. Paley, *On orthogonal matrices*, 1933) give
Hadamard matrices of order `q + 1` for prime powers `q ≡ 3 (mod 4)` and of order
`2(q + 1)` for prime powers `q ≡ 1 (mod 4)`; for odd `k` they cover every `k` with
`4k - 1` or `2k - 1` a prime power.

* `H1` (Paley I, known): order `q + 1` for every prime power `q ≡ 3 (mod 4)`.
* `H2` (Paley II, known): order `2(q + 1)` for every prime power `q ≡ 1 (mod 4)`.
* `H3` (open core): order `4k` for every odd `k` such that neither `4k - 1` nor `2k - 1`
  is a prime power.

All three are stated with the orthogonality form `IsHadamard'` (`Mᵀ M = n`). `main`
proves Sylvester doubling, the 2-adic decomposition of `k`, the Paley case split, and
the passage from `Mᵀ M = n` to the determinant form `IsHadamard` used by the target.
-/

namespace OMA.R_Hadamard_HadamardConjecture_R1

open Matrix Hadamard

/-- Paley I: a Hadamard matrix of order `q + 1` for each prime power `q ≡ 3 (mod 4)`. -/
def H1 : Prop :=
  ∀ q : ℕ, IsPrimePow q → q % 4 = 3 → ∃ M, IsHadamard' (n := q + 1) M

/-- Paley II: a Hadamard matrix of order `2(q + 1)` for each prime power `q ≡ 1 (mod 4)`. -/
def H2 : Prop :=
  ∀ q : ℕ, IsPrimePow q → q % 4 = 1 → ∃ M, IsHadamard' (n := 2 * (q + 1)) M

/-- Open core: order `4k` for odd `k` not covered by either Paley construction. -/
def H3 : Prop :=
  ∀ k : ℕ, Odd k → ¬ IsPrimePow (4 * k - 1) → ¬ IsPrimePow (2 * k - 1) →
    ∃ M, IsHadamard' (n := 4 * k) M

lemma had_cast {n m : ℕ} (h : n = m) :
    (∃ M, IsHadamard' (n := n) M) → ∃ M, IsHadamard' (n := m) M := by
  subst h
  exact id

lemma pm_neg {x : ℝ} (hx : x ∈ ({1, -1} : Finset ℝ)) : -x ∈ ({1, -1} : Finset ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with h | h <;> rw [h] <;> norm_num

/-- Sylvester doubling. -/
lemma had_double {n : ℕ} :
    (∃ M, IsHadamard' (n := n) M) → ∃ M, IsHadamard' (n := 2 * n) M := by
  rintro ⟨M, hpm, horth⟩
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n := (finCongr (two_mul n)).trans finSumFinEquiv.symm
  let A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fromBlocks M M M (-M)
  refine ⟨A.submatrix e e, ?_, ?_⟩
  · intro i j
    simp only [submatrix_apply]
    rcases e i with a | a <;> rcases e j with b | b
    · exact hpm a b
    · exact hpm a b
    · exact hpm a b
    · simpa [A] using pm_neg (hpm a b)
  · have hAA : Aᵀ * A = diagonal (Sum.elim (fun _ => ((2 * n : ℕ) : ℝ)) fun _ => ((2 * n : ℕ) : ℝ)) := by
      simp only [A, fromBlocks_transpose, fromBlocks_multiply, transpose_neg, neg_mul, mul_neg,
        neg_neg, horth]
      rw [← fromBlocks_diagonal]
      congr 1
      · rw [← Nat.cast_add, ← two_mul]
        rfl
      · simp
      · simp
      · rw [← Nat.cast_add, ← two_mul]
        rfl
    rw [transpose_submatrix, submatrix_mul_equiv, hAA, submatrix_diagonal_equiv, ← diagonal_natCast]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rcases e i with a | a <;> rfl

lemma had_pow_two (j k : ℕ) :
    (∃ M, IsHadamard' (n := 4 * k) M) → ∃ M, IsHadamard' (n := 4 * (2 ^ j * k)) M := by
  induction j with
  | zero => intro h; exact had_cast (by ring) h
  | succ j ih =>
    intro h
    exact had_cast (by ring) (had_double (ih h))

/-- `Mᵀ M = n` implies the determinant form (this direction is proved upstream in
`isHadamard_equiv_isHadamard'`; it is repeated here because that lemma also contains an
unproved converse direction). -/
lemma isHadamard_of_isHadamard' {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (h : Hadamard.IsHadamard' M) : Hadamard.IsHadamard M := by
  refine ⟨h.1, ?_⟩
  have h_det : (M.transpose * M).det = n ^ ((n : ℝ)) := by
    have : Matrix.diagonal (fun _ : Fin n => (n : ℝ)) = (n : Matrix (Fin n) (Fin n) ℝ) := rfl
    rw [h.2, ← this]
    norm_num
  simp only [Matrix.det_mul, Matrix.det_transpose] at h_det
  rw [← Real.sqrt_mul_self_eq_abs M.det, h_det]
  have : √(↑n ^ (n : ℝ)) = (↑n ^ (n : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_div_two_eq_sqrt]
    · simp only [Real.rpow_natCast, Real.rpow_one]
    · simp only [Real.rpow_natCast, Nat.cast_nonneg, pow_nonneg]
  rw [this, ← Real.rpow_mul (Nat.cast_nonneg' n)]
  congr 1
  ring

lemma odd_case (h1 : H1) (h2 : H2) (h3 : H3) (k : ℕ) (hk : Odd k) :
    ∃ M, IsHadamard' (n := 4 * k) M := by
  obtain ⟨r, hr⟩ := hk
  by_cases hp : IsPrimePow (4 * k - 1)
  · exact had_cast (by omega) (h1 (4 * k - 1) hp (by omega))
  · by_cases hq : IsPrimePow (2 * k - 1)
    · exact had_cast (by omega) (h2 (2 * k - 1) hq (by omega))
    · exact h3 k ⟨r, hr⟩ hp hq

theorem main : H1 → H2 → H3 → type_of% @Hadamard.HadamardConjecture := by
  intro h1 h2 h3 k
  suffices hs : ∃ M, IsHadamard' (n := 4 * k) M by
    obtain ⟨M, hM⟩ := hs
    exact ⟨M, isHadamard_of_isHadamard' hM⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, fun i => i.elim0, ?_⟩
    ext i
    exact i.elim0
  · obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk.ne'
    exact had_pow_two j m (odd_case h1 h2 h3 m hm)

end OMA.R_Hadamard_HadamardConjecture_R1
