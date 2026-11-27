import Mathlib

/-!
# Is the exponent of matrix multiplication equal to two?

Source: https://en.wikipedia.org/wiki/Computational_complexity_of_matrix_multiplication
Credit: @shc261392

Question. Let `ω` be the infimum of the exponents `τ` such that two `n × n` matrices can be
multiplied with `O(n^τ)` arithmetic operations. Is `ω = 2`?

Reading used here (the affirmative answer):
* By Strassen's theorem, `ω` is also the infimum of the `τ` such that the tensor rank of the
  matrix multiplication tensor `⟨n, n, n⟩ = ∑_{i,j,k} e_{ij} ⊗ e_{jk} ⊗ e_{ki}` is `O(n^τ)`;
  the field is `ℂ`, the usual setting.
* `ω = 2` then says: for every `ε > 0` there is `C` such that, for every `n`, the tensor
  `⟨n, n, n⟩` is a sum of at most `C n^{2 + ε}` rank-one tensors `a_l ⊗ b_l ⊗ c_l`, i.e. there
  are `r ≤ C n^{2+ε}` and `a, b, c : Fin r → Fin n → Fin n → ℂ` with
  `∑_l a_l(i, j) b_l(j', k) c_l(k', i') = 1` if `j = j'`, `k = k'`, `i' = i`, and `0` otherwise.
-/

namespace OMA.S_wpc_omega_equals_two

theorem main :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, ∃ r : ℕ, (r : ℝ) ≤ C * (n : ℝ) ^ (2 + ε) ∧
      ∃ a b c : Fin r → Fin n → Fin n → ℂ,
        ∀ i j j' k k' i' : Fin n,
          ∑ l, a l i j * b l j' k * c l k' i' = if j = j' ∧ k = k' ∧ i' = i then 1 else 0 := by
  sorry

end OMA.S_wpc_omega_equals_two
