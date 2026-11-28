import OMAStatements.S_oeis_a386649

/-! OEIS A386649: `A214589(n) = a(n) + 2` for `n ≥ 1`.

Taking `k₂ = 0` in the condition, a triangle is counted iff every row `k` sums to `(k + 1) v`,
where `v = T(0, 0) ∈ {0, 1, 2}`. Split by `v`: each fiber is a product of row sets. A row of
length `m` with sum `0` (resp. `2 m`) is constant `0` (resp. `2`), so `v = 0` and `v = 2` give one
triangle each. Rows of length `m` with sum `m` are counted by `[x ^ m] (1 + x + x ^ 2) ^ m`, the
central trinomial coefficient, so `v = 1` gives `∏_{k < n} A002426(k + 1) = a(n)`. -/

namespace OpenMath.A386649

open Finset OMA.S_oeis_a386649 Polynomial

/-- Rows of length `m` with entry sum `m * v`. -/
private def R (m v : ℕ) : Finset (Fin m → Fin 3) :=
  Finset.univ.filter fun r => ∑ j, (r j).val = m * v

private theorem card_R0 (m : ℕ) : (R m 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => 0, ?_⟩
  ext r
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, mul_zero, Finset.mem_singleton]
  constructor
  · intro h
    funext j
    exact Fin.ext ((Finset.sum_eq_zero_iff.1 h) j (Finset.mem_univ j))
  · rintro rfl
    simp

private theorem card_R2 (m : ℕ) : (R m 2).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => 2, ?_⟩
  ext r
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), (r j).val ≤ 2 := fun j _ =>
    Nat.le_of_lt_succ (r j).isLt
  have hsum2 : ∑ _j : Fin m, 2 = m * 2 := by simp
  constructor
  · intro h
    rw [← hsum2] at h
    have h' := (Finset.sum_eq_sum_iff_of_le hle).1 h
    funext j
    exact Fin.ext (h' j (Finset.mem_univ j))
  · rintro rfl
    simp

private theorem card_R1 (m : ℕ) : (R m 1).card = centralTrinomial m := by
  have h3 : (1 + X + X ^ 2 : ℕ[X]) = ∑ t : Fin 3, X ^ t.val := by
    rw [Fin.sum_univ_three]
    simp
  have hexp : (∑ t : Fin 3, (X : ℕ[X]) ^ t.val) ^ m =
      ∑ r : Fin m → Fin 3, X ^ (∑ j, (r j).val) := by
    rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun r _ => Finset.prod_pow_eq_pow_sum _ _ _
  unfold centralTrinomial
  rw [h3, hexp, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  unfold R
  simp only [mul_one, Nat.cast_id]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

theorem main :
    ∀ n : ℕ, 1 ≤ n → A214589 n = a n + 2 := by
  intro n hn
  have hz : ∀ T : (k : Fin n) → Fin (k.1 + 1) → Fin 3,
      ∑ j : Fin ((⟨0, hn⟩ : Fin n).1 + 1), (T ⟨0, hn⟩ j).1 =
        (T ⟨0, hn⟩ ⟨0, Nat.zero_lt_succ 0⟩).1 :=
    fun T => Fin.sum_univ_one _
  have hfib : ∀ v : Fin 3,
      (Finset.univ.filter fun T : (k : Fin n) → Fin (k.1 + 1) → Fin 3 =>
        ∀ k1 k2 : Fin n, (k2.1 + 1) * (∑ j : Fin (k1.1 + 1), (T k1 j).1) =
          (k1.1 + 1) * (∑ j : Fin (k2.1 + 1), (T k2 j).1)).filter
          (fun T => T ⟨0, hn⟩ ⟨0, Nat.zero_lt_succ 0⟩ = v) =
        Fintype.piFinset fun k : Fin n => R (k.1 + 1) v.1 := by
    intro v
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, R]
    constructor
    · rintro ⟨hT, hv⟩ k
      have h1 := hT k ⟨0, hn⟩
      rw [hz T, hv] at h1
      simpa using h1
    · intro hT
      refine ⟨fun k1 k2 => by rw [hT k1, hT k2]; ring, ?_⟩
      have h1 := hT ⟨0, hn⟩
      rw [hz T] at h1
      exact Fin.ext (by simpa using h1)
  have hc0 : centralTrinomial 0 = 1 := by simp [centralTrinomial]
  have ha : a n = ∏ k : Fin n, centralTrinomial (k.1 + 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun k => centralTrinomial (k + 1)) n]
    unfold a
    rw [Finset.prod_range_succ', hc0, mul_one]
  unfold A214589
  rw [Finset.card_eq_sum_card_fiberwise (f := fun T => T ⟨0, hn⟩ ⟨0, Nat.zero_lt_succ 0⟩)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp only [hfib, Fintype.card_piFinset]
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, card_R0, card_R1, card_R2,
    Finset.prod_const_one]
  rw [ha]
  omega

end OpenMath.A386649

theorem OMA.solution : type_of% @OMA.S_oeis_a386649.main := OpenMath.A386649.main
