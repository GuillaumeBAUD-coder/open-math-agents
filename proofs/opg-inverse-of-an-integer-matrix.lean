import OMAStatements.S_opg_inverse_of_an_integer_matrix

/-!
Gregory’s rowwise guess fails even for two identical all-one rows in X.
The theorem GregoryProof.finiteTest gives a finite necessary and sufficient test.
Source: https://www.openproblemgarden.org/op/inverse_of_an_integer_matrix
Credit: @rleshner
-/

namespace GregoryProof

open OMA.S_opg_inverse_of_an_integer_matrix

/-- Each standard basis vector must be reached modulo the diagonal by an explicitly
bounded combination of the columns of X. Every quantifier here is finite. -/
def residueTest {m n : ℕ} (d : Fin m → ℕ) (X : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ j : Fin m, ∃ c : Fin n → Fin (∏ i, d i), ∀ i : Fin m,
    (∑ k, X i k * (c k : ℤ)) ≡ (if i = j then 1 else 0) [ZMOD (d i : ℤ)]

theorem finiteTest {m n : ℕ} (d : Fin m → ℕ) (X : Matrix (Fin m) (Fin n) ℤ)
    (hd : ∀ i, 2 ≤ d i) : admitsRightInverse d X ↔ residueTest d X := by
  classical
  let L := ∏ i, d i
  have hL : 0 < L := Finset.prod_pos fun i _ => by have := hd i; omega
  have hLz : 0 < (L : ℤ) := by exact_mod_cast hL
  constructor
  · rintro ⟨R, hR⟩ j
    let B := R.toRows₂
    let rem (k : Fin n) := B k j % (L : ℤ)
    have hpos (k) : 0 ≤ rem k := Int.emod_nonneg _ (ne_of_gt hLz)
    have hlt (k) : rem k < (L : ℤ) := Int.emod_lt_of_pos _ hLz
    let c (k : Fin n) : Fin L := ⟨(rem k).toNat, by have := hpos k; have := hlt k; omega⟩
    refine ⟨c, fun i => ?_⟩
    have hsub : (d i : ℤ) ∣ (L : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
    have hsum : (∑ k, X i k * (c k : ℤ)) ≡ (∑ k, X i k * B k j) [ZMOD (d i : ℤ)] := by
      apply Int.ModEq.sum
      intro k _
      apply Int.ModEq.mul_left
      apply Int.ModEq.of_dvd hsub
      change ((rem k).toNat : ℤ) % (L : ℤ) = B k j % (L : ℤ)
      rw [Int.toNat_of_nonneg (hpos k)]
      exact Int.emod_emod _ _
    apply hsum.trans
    unfold block at hR
    rw [← Matrix.fromRows_toRows R, Matrix.fromCols_mul_fromRows] at hR
    have hij := congrArg (fun A : Matrix (Fin m) (Fin m) ℤ => A i j) hR
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.one_apply] at hij
    simp only [Matrix.mul_apply] at hij
    apply Int.modEq_iff_dvd.mpr
    refine ⟨R.toRows₁ i j, ?_⟩
    change (if i = j then 1 else 0) - (∑ k, X i k * R.toRows₂ k j) = _
    linarith only [hij]
  · intro h
    choose c hc using h
    let B : Matrix (Fin n) (Fin m) ℤ := fun k j => (c j k : ℤ)
    let A : Matrix (Fin m) (Fin m) ℤ := fun i j =>
      ((if i = j then 1 else 0) - (X * B) i j) / (d i : ℤ)
    refine ⟨Matrix.fromRows A B, ?_⟩
    unfold block
    rw [Matrix.fromCols_mul_fromRows]
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.one_apply]
    change (d i : ℤ) * (((if i = j then 1 else 0) - (X * B) i j) / (d i : ℤ)) + _ = _
    have hdvd : (d i : ℤ) ∣ (if i = j then 1 else 0) - (X * B) i j := (hc j i).dvd
    rw [Int.mul_ediv_cancel' hdvd]
    ring

/-- The proposed row condition is necessary. -/
theorem primitive_of_inverse {m n : ℕ} {d : Fin m → ℕ} {X : Matrix (Fin m) (Fin n) ℤ}
    (h : admitsRightInverse d X) : primitiveRows d X := by
  obtain ⟨R, hR⟩ := h
  intro i q hq
  have hdiag := congrArg (fun A : Matrix (Fin m) (Fin m) ℤ => A i i) hR
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at hdiag
  rw [← hdiag]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (hq k) _

end GregoryProof

open OMA.S_opg_inverse_of_an_integer_matrix

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_inverse_of_an_integer_matrix.main) := by
  intro proposed
  let d : Fin 2 → ℕ := fun _ => 2
  let X : Matrix (Fin 2) (Fin 2) ℤ := fun _ _ => 1
  have hrows : primitiveRows d X := fun _ _ hq => hq (Sum.inr (0 : Fin 2))
  have hinv := (proposed 2 2 le_rfl d X (fun _ => le_rfl)).mpr hrows
  obtain ⟨c, hc⟩ := (GregoryProof.finiteTest d X (fun _ => le_rfl)).mp hinv 0
  have h₀ := hc 0
  have h₁ := hc 1
  simp [X, d, Int.ModEq] at h₀ h₁
  omega
