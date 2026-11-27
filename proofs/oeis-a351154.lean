import OMAStatements.S_oeis_a351154
import Mathlib

/-! Following Sela Fried’s first differences for the matrix of A351154, one further
row swap exposes the factorial as the product of a triangular diagonal.
https://oeis.org/A351154/a351154_1.pdf -/
open Matrix
open scoped BigOperators
namespace FriedDeterminant
open OMA.S_oeis_a351154
def delta (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  fun i j => Fin.cases (if j = 0 then 1 else 0)
    (fun a => (if j = a.succ then 1 else 0) - (if j = a.castSucc then 1 else 0)) i

lemma delta_det (n : ℕ) : (delta n).det = 1 := by
  have h : (delta n).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    induction i using Fin.cases with
    | zero => simp [delta, ne_of_gt hij]
    | succ i =>
      have h₁ : j ≠ i.succ := ne_of_gt hij
      have h₂ : j ≠ i.castSucc := ne_of_gt (lt_trans (@Fin.castSucc_lt_succ _ i) hij)
      simp [delta,h₁,h₂]
  rw [Matrix.det_of_isLowerTriangular _ h]
  suffices diag : ∀ i : Fin (n+1), delta n i i = 1 by simp [diag]
  intro i
  induction i using Fin.cases with
  | zero => simp [delta]
  | succ i => simp [delta, ne_of_gt (@Fin.castSucc_lt_succ _ i)]

lemma delta_zero {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (j) :
    (delta n * A) 0 j = A 0 j := by
  simp [Matrix.mul_apply, delta, ite_mul]
lemma delta_succ {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (i : Fin n) (j) :
    (delta n * A) i.succ j = A i.succ j - A i.castSucc j := by
  simp [Matrix.mul_apply, delta, sub_mul, Finset.sum_sub_distrib, ite_mul]

def border (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  fun i j => if i=0 ∨ j=0 then 1 else if i=j then (n:ℚ) - i.val else 0

lemma entry (n : ℕ) (i j : Fin n) :
    M n i j = (n:ℚ) * (min i.val j.val : ℕ) -
      (min i.val j.val : ℕ) * ((min i.val j.val : ℕ) - (1:ℚ)) / 2 + 1 +
      |(i.val:ℚ)-j.val| := by
  unfold M triangle
  push_cast
  ring

lemma border_eq (n : ℕ) : delta n * (delta n * M (n+1))ᵀ = border n := by
  ext i j
  induction i using Fin.cases with
  | zero =>
    rw [delta_zero, Matrix.transpose_apply]
    induction j using Fin.cases with
    | zero => simp [delta_zero,entry,border]
    | succ j => rw [delta_succ]; simp [entry,border]; rw [abs_of_nonneg (by positivity)]; ring
  | succ i =>
    rw [delta_succ,Matrix.transpose_apply, Matrix.transpose_apply]
    induction j using Fin.cases with
    | zero =>
      simp [delta_zero,entry,border]
      have hi : (0:ℚ) ≤ i.val := by positivity
      rw [abs_of_nonpos (show (-1:ℚ) + - (i.val:ℚ) ≤ 0 by linarith)]
      ring
    | succ j =>
      simp only [delta_succ,entry,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      rcases lt_trichotomy i.val j.val with h | h | h
      · have h₁ : i.val+1 ≤ j.val := h
        have h₂ : i.val ≤ j.val := h.le
        have h₃ : i.val ≤ j.val+1 := by omega
        have h₄ : i.val+1 ≤ j.val+1 := by omega
        simp only [min_eq_right h₁,min_eq_right h₂,min_eq_right h₃,min_eq_right h₄]
        have ne : i ≠ j := Fin.ne_of_lt h
        have hh : (i.val:ℚ)+1 ≤ j.val := by exact_mod_cast h₁
        simp [border,ne]
        simp only [abs_eq_max_neg,max_def]
        split_ifs <;> linarith
      · have hh : i=j := Fin.ext h
        subst j
        simp [border,Fin.succ_ne_zero,abs_of_nonneg,abs_of_nonpos]; ring
      · have h₁ : j.val+1 ≤ i.val := h
        have h₂ : j.val ≤ i.val := h.le
        have h₃ : j.val ≤ i.val+1 := by omega
        have h₄ : j.val+1 ≤ i.val+1 := by omega
        simp only [min_eq_left h₁,min_eq_left h₂,min_eq_left h₃,min_eq_left h₄]
        have ne : i ≠ j := Fin.ne_of_gt h
        have hh : (j.val:ℚ)+1 ≤ i.val := by exact_mod_cast h₁
        simp [border,ne]
        simp only [abs_eq_max_neg,max_def]
        split_ifs <;> linarith
end FriedDeterminant
open Matrix
open scoped BigOperators
namespace FriedDeterminant
open OMA.S_oeis_a351154

lemma falling (n : ℕ) : (∏ i : Fin n, ((n:ℚ) - i.val)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Nat.factorial_succ, Nat.cast_mul, ← ih]
    simp only [Fin.val_zero,Nat.cast_zero, sub_zero,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring

lemma border_det (m : ℕ) : (border (m+1)).det = - (m.factorial:ℚ) := by
  let z : Fin (m+2) := 0
  let l : Fin (m+2) := Fin.last (m+1)
  have hzl : z ≠ l := by
    intro h
    have := congrArg Fin.val h
    simp [z,l] at this
  let S := (border (m+1)).submatrix (Equiv.swap z l) id
  have tri : S.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    have hj : j ≠ z := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hij)
    have hil : i ≠ l := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last _))
    by_cases hi : i=z
    · subst i
      change border (m+1) ((Equiv.swap z l) z) j = 0
      rw [Equiv.swap_apply_left]
      by_cases hh : j=l
      · subst j; simp [border,l, show Fin.last (m+1) ≠ 0 from hzl.symm]
      · simp [border, l, show j ≠ 0 from hj, show Fin.last (m+1) ≠ j from Ne.symm hh]
    · change border (m+1) ((Equiv.swap z l) i) j = 0
      rw [Equiv.swap_apply_of_ne_of_ne hi hil]
      simp [border, show i ≠ 0 from hi, show j ≠ 0 from hj, ne_of_lt hij]
  have d0 : S 0 0 = 1 := by simp [S,z,border]
  have dl : S l l = 1 := by simp [S,z,l,border]
  have di (i : Fin m) : S i.castSucc.succ i.castSucc.succ = (m:ℚ) - i.val := by
    have hn : i.castSucc.succ ≠ l := by
      intro h
      have e := congrArg Fin.val h
      simp [l] at e
      omega
    simp [S,Equiv.swap_apply_of_ne_of_ne (show i.castSucc.succ ≠ z from Fin.succ_ne_zero _) hn,
      border, Fin.succ_ne_zero]
  have p : S.det = m.factorial := by
    rw [Matrix.det_of_isLowerTriangular _ tri, Fin.prod_univ_succ]
    rw [Fin.prod_univ_castSucc, d0, one_mul]
    have dl' : S (Fin.last m).succ (Fin.last m).succ = 1 := dl
    simpa only [di,dl',mul_one] using (falling m)
  have perm := Matrix.det_permute (Equiv.swap z l) (border (m+1))
  change S.det = _ at perm
  rw [p, Equiv.Perm.sign_swap hzl] at perm
  simpa using (congrArg Neg.neg perm).symm

lemma determinant (m : ℕ) : (M (m+2)).det = - (m.factorial:ℚ) := by
  have h := congrArg Matrix.det (border_eq (m+1))
  simpa [Matrix.det_mul,Matrix.det_transpose,delta_det,border_det] using h

lemma result :
    (M 0).det = 1 ∧ (M 1).det = 1 ∧
    (∀ n : ℕ, 1 < n → (M n).det = -((n-2).factorial : ℚ)) ∧
    (∀ n : ℕ, |(M n).det| = |romanFactorial ((n:ℤ)-2)|) := by
  have h₀ : (M 0).det = 1 := Matrix.det_fin_zero
  have h₁ : (M 1).det = 1 := by norm_num [Matrix.det_fin_one, M, triangle]
  refine ⟨h₀,h₁,?_,?_⟩
  · intro n hn
    obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2,by omega⟩
    simpa using determinant m
  · intro n
    match n with
    | 0 => norm_num [h₀,romanFactorial]
    | 1 => rw [h₁]; norm_num [romanFactorial]
    | m+2 =>
      rw [determinant]
      simp [romanFactorial, abs_neg]
end FriedDeterminant

theorem OMA.solution : type_of% @OMA.S_oeis_a351154.main := FriedDeterminant.result
