import OMAStatements.S_oeis_a144621
import Mathlib

namespace ParityBlocks

open Matrix OMA.S_oeis_a144621

private def halfIndex (n : ℕ) (i : Fin (2 ^ (n + 1))) : Fin (2 ^ n) :=
  ⟨i.val / 2, by
    have h : i.val < 2 ^ n * 2 := by simpa only [pow_succ] using i.isLt
    omega⟩

private def parityIndex (n : ℕ) : (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ≃ Fin (2 ^ (n + 1)) where
  toFun
    | .inl i => ⟨2 * i.val, by rw [pow_succ]; have h := i.isLt; omega⟩
    | .inr i => ⟨2 * i.val + 1, by rw [pow_succ]; have h := i.isLt; omega⟩
  invFun i := if i.val % 2 = 0 then .inl (halfIndex n i) else .inr (halfIndex n i)
  left_inv := by
    rintro (i | i)
    · change (if (2 * i.val) % 2 = 0 then Sum.inl _ else Sum.inr _) = Sum.inl i
      rw [if_pos (by omega)]
      congr 1
      apply Fin.ext
      change 2 * i.val / 2 = i.val
      omega
    · change (if (2 * i.val + 1) % 2 = 0 then Sum.inl _ else Sum.inr _) = Sum.inr i
      rw [if_neg (by omega)]
      congr 1
      apply Fin.ext
      change (2 * i.val + 1) / 2 = i.val
      omega
  right_inv := by
    intro i
    by_cases hi : i.val % 2 = 0
    · simp only [if_pos hi]
      apply Fin.ext
      change 2 * (i.val / 2) = i.val
      omega
    · simp only [if_neg hi]
      apply Fin.ext
      change 2 * (i.val / 2) + 1 = i.val
      omega

private theorem double_valuation (n : ℕ) (hn : 0 < n) :
    padicValNat 2 (2 * n) = 1 + padicValNat 2 n := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by decide) (by omega), padicValNat_self]

private def constant (n : ℕ) (c : ℤ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ :=
  Matrix.of fun _ _ => c

private def shifted (n : ℕ) (c : ℤ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ :=
  Matrix.of fun i j => M n i j + c

private theorem blocks (n : ℕ) (c : ℤ) :
    (shifted (n + 1) c).submatrix (parityIndex n) (parityIndex n) =
      fromBlocks (constant n (c + 1)) (shifted n (c + 1))
        (shifted n (c + 1)) (constant n (c + 1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change 1 + (padicValNat 2 (2 * i.val + 2 * j.val + 1) : ℤ) + c = c + 1
    rw [padicValNat.eq_zero_of_not_dvd (by omega), Nat.cast_zero]
    ring
  · change 1 + (padicValNat 2 (2 * i.val + (2 * j.val + 1) + 1) : ℤ) + c =
      1 + (padicValNat 2 (i.val + j.val + 1) : ℤ) + (c + 1)
    rw [show 2 * i.val + (2 * j.val + 1) + 1 = 2 * (i.val + j.val + 1) by omega,
      double_valuation _ (by omega), Nat.cast_add, Nat.cast_one]
    ring
  · change 1 + (padicValNat 2 (2 * i.val + 1 + 2 * j.val + 1) : ℤ) + c =
      1 + (padicValNat 2 (i.val + j.val + 1) : ℤ) + (c + 1)
    rw [show 2 * i.val + 1 + 2 * j.val + 1 = 2 * (i.val + j.val + 1) by omega,
      double_valuation _ (by omega), Nat.cast_add, Nat.cast_one]
    ring
  · change 1 + (padicValNat 2 (2 * i.val + 1 + (2 * j.val + 1) + 1) : ℤ) + c = c + 1
    rw [padicValNat.eq_zero_of_not_dvd (by omega), Nat.cast_zero]
    ring

private theorem det_symmetric_blocks {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℤ) :
    (fromBlocks A B B A).det = (A + B).det * (A - B).det := by
  let L : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ := fromBlocks 1 0 (-1) 1
  let R : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ := fromBlocks 1 0 1 1
  have hL : L.det = 1 := by simp [L]
  have hR : R.det = 1 := by simp [R]
  have hmul : L * fromBlocks A B B A * R = fromBlocks (A + B) B 0 (A - B) := by
    simp only [L, R, fromBlocks_multiply, neg_mul, one_mul, zero_mul, mul_zero,
      mul_one, add_zero, zero_add]
    congr 1 <;> abel
  calc
    (fromBlocks A B B A).det = (L * fromBlocks A B B A * R).det := by
      simp only [det_mul, hL, hR, one_mul, mul_one]
    _ = _ := by rw [hmul, det_fromBlocks_zero₂₁]

private def D (n : ℕ) (c : ℤ) : ℤ := (shifted n c).det

private theorem D_step (n : ℕ) (c : ℤ) :
    D (n + 1) c = (-1) ^ (2 ^ n) * D n 0 * D n (2 * c + 2) := by
  have hadd : constant n (c + 1) + shifted n (c + 1) = shifted n (2 * c + 2) := by
    ext i j
    change (c + 1) + (M n i j + (c + 1)) = M n i j + (2 * c + 2)
    ring
  have hsub : constant n (c + 1) - shifted n (c + 1) = -shifted n 0 := by
    ext i j
    change (c + 1) - (M n i j + (c + 1)) = -(M n i j + 0)
    ring
  unfold D
  rw [← det_submatrix_equiv_self (parityIndex n), blocks, det_symmetric_blocks,
    hadd, hsub, det_neg, Fintype.card_fin]
  ring

private theorem D_zero (c : ℤ) : D 0 c = 1 + c := by
  unfold D
  rw [det_fin_one]
  change 1 + (padicValNat 2 1 : ℤ) + c = 1 + c
  norm_num

private theorem D_one (c : ℤ) : D 1 c = -(2 * c + 3) := by
  rw [D_step, D_zero, D_zero]
  norm_num
  ring

private theorem D_step_pos (n : ℕ) (hn : 0 < n) (c : ℤ) :
    D (n + 1) c = D n 0 * D n (2 * c + 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [D_step, pow_succ (2 : ℕ), Nat.mul_comm (2 ^ m) 2, pow_mul]
  norm_num

private theorem affine (n : ℕ) (c d : ℤ) :
    D n (3 * c - 2 * d) = 3 * D n c - 2 * D n d := by
  induction n generalizing c d with
  | zero => simp only [D_zero]; ring
  | succ n ih =>
    simp only [D_step]
    rw [show 2 * (3 * c - 2 * d) + 2 = 3 * (2 * c + 2) - 2 * (2 * d + 2) by ring,
      ih]
    ring

private theorem determinant_recurrence (n : ℕ) :
    D (n + 3) 0 = D (n + 2) 0 * (3 * D (n + 2) 0 - 2 * D (n + 1) 0 ^ 2) := by
  have h₀ : D (n + 2) 0 = D (n + 1) 0 * D (n + 1) 2 := D_step_pos (n + 1) (by omega) 0
  have h₂ : D (n + 2) 2 = D (n + 1) 0 * D (n + 1) 6 := D_step_pos (n + 1) (by omega) 2
  have h₆ : D (n + 1) 6 = 3 * D (n + 1) 2 - 2 * D (n + 1) 0 := affine (n + 1) 2 0
  have h : D (n + 2) 2 = 3 * D (n + 2) 0 - 2 * D (n + 1) 0 ^ 2 := by
    rw [h₂, h₆, h₀]
    ring
  calc
    D (n + 3) 0 = D (n + 2) 0 * D (n + 2) 2 := D_step_pos (n + 2) (by omega) 0
    _ = _ := by rw [h]

private theorem D_two : D 2 0 = a 3 := by
  have h : D 2 0 = D 1 0 * D 1 2 := D_step_pos 1 (by decide) 0
  rw [h, D_one, D_one]
  decide

private theorem values (n : ℕ) :
    D (n + 2) 0 = a (n + 3) ∧ D (n + 3) 0 = a (n + 4) := by
  induction n with
  | zero =>
    refine ⟨D_two, ?_⟩
    rw [determinant_recurrence 0, D_two, D_one]
    decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change D (n + 4) 0 = a (n + 5)
    rw [determinant_recurrence (n + 1), ih.2, ih.1]
    rfl

theorem result (n : ℕ) (hn : 2 < n) : a (n + 1) = (M n).det := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have hm : shifted (k + 2) 0 = M (k + 2) := by
    ext i j
    change M (k + 2) i j + 0 = M (k + 2) i j
    exact add_zero _
  have h := (values k).1
  unfold D at h
  rw [hm] at h
  exact h.symm

end ParityBlocks

theorem OMA.solution : type_of% @OMA.S_oeis_a144621.main := ParityBlocks.result