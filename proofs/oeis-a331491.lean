import OMAStatements.S_oeis_a331491

/-!
Separate the even and odd indices. After subtracting the differences of the
pair indices, the matrix has off-diagonal blocks U and -Uᵀ, where U is the
upper triangular matrix of ones. This skew form B has determinant one.
The endpoint difference w satisfies Bw = 1. The original matrix is the
congruence of B by I + wvᵀ, with v the pair index. The rank-one determinant
formula gives 1 + vᵀw = n.
-/

namespace ToeplitzPairs
open Matrix
open scoped Matrix

private abbrev Ix (n : ℕ) := Fin n ⊕ Fin n
private def parityIndex (n : ℕ) : Ix n ≃ Fin (2*n) where
  toFun := Sum.elim (fun i => ⟨2*i.val, by omega⟩) (fun i => ⟨2*i.val+1, by omega⟩)
  invFun j := if j.val % 2 = 0 then Sum.inl ⟨j.val/2, by omega⟩
              else Sum.inr ⟨j.val/2, by omega⟩
  left_inv i := by
    rcases i with i | i
    · simp
    · simp
      apply Fin.ext
      dsimp
      omega
  right_inv j := by
    dsimp only
    split <;> apply Fin.ext <;> dsimp <;> omega

private def height {n : ℕ} : Ix n → ℤ := Sum.elim (fun i => i.val) (fun i => i.val)
private def upper (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => if i ≤ j then 1 else 0
private def form (n : ℕ) : Matrix (Ix n) (Ix n) ℤ := fromBlocks 0 (upper n) (-(upper n)ᵀ) 0

private lemma det_form (n : ℕ) : (form n).det = 1 := by
  let I : Matrix (Fin n) (Fin n) ℤ := 1
  have hU : (upper n).det = 1 := by
    rw [det_of_isUpperTriangular (by intro i j h; exact if_neg (not_le_of_gt h) : (upper n).IsUpperTriangular)]
    simp [upper]
  let E := fromBlocks I I 0 I
  let F := fromBlocks I 0 (-I) I
  let D := fromBlocks (upper n) 0 0 I
  have he : E.det = 1 := by simp [E,I]
  have hf : F.det = 1 := by simp [F,I]
  have hd : D.det = 1 := by simp [D,I,hU]
  have factor : form n = D * (E * F * E) * Dᵀ := by
    simp [form,D,E,F,I,fromBlocks_transpose,fromBlocks_multiply]
  rw [factor, det_mul, det_mul, det_mul, det_mul, det_transpose, he, hf, hd]
  norm_num

private lemma entries (n : ℕ) (i j : Ix n) :
    OMA.S_oeis_a331491.toeplitz _ (parityIndex n i) (parityIndex n j) =
      form n i j + height j - height i := by
  let t (x y : ℕ) : ℤ := if x < y then (((y-x+1)/2 : ℕ) : ℤ) else -(((x-y+1)/2 : ℕ) : ℤ)
  rcases i with i | i <;> rcases j with j | j
  · change t (2*i.val) (2*j.val) = 0 + (j.val:ℤ) - i.val
    unfold t
    split_ifs <;> omega
  · change t (2*i.val) (2*j.val+1) = (if i.val ≤ j.val then 1 else 0) + (j.val:ℤ) - i.val
    unfold t
    split_ifs <;> omega
  · change t (2*i.val+1) (2*j.val) = -(if j.val ≤ i.val then 1 else 0) + (j.val:ℤ) - i.val
    unfold t
    split_ifs <;> omega
  · change t (2*i.val+1) (2*j.val+1) = 0 + (j.val:ℤ) - i.val
    unfold t
    split_ifs <;> omega

private lemma determinant (m : ℕ) : (OMA.S_oeis_a331491.toeplitz (2*(m+1))).det = ((m+1:ℕ):ℤ)^2 := by
  let B := form (m+1)
  let v := @height (m+1)
  let w : Ix (m+1) → ℤ := Pi.single (.inr (Fin.last m)) 1 - Pi.single (.inl 0) 1
  let u : Ix (m+1) → ℤ := fun _ => 1
  let P := (1 : Matrix (Ix (m+1)) (Ix (m+1)) ℤ) + vecMulVec w v
  have bw : B *ᵥ w = u := by
    rw [show w = _ from rfl, mulVec_sub, mulVec_single_one, mulVec_single_one]
    funext i
    cases i <;> simp [B,form,Matrix.col,upper,u,Fin.le_last]
  have skew : Bᵀ = -B := by
    ext i j
    cases i <;> cases j <;> simp [B,form,transpose_apply]
  have wb : w ᵥ* B = -u := by rw [← mulVec_transpose, skew, neg_mulVec, bw]
  have wu : w ⬝ᵥ u = 0 := by simp [w,sub_dotProduct,single_dotProduct,u]
  have detP : P.det = ((m+1:ℕ):ℤ) := by
    rw [show P = 1 + _ from rfl, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
    simp [v,height,w,dotProduct_sub,dotProduct_single,add_comm]
  have congruence : (OMA.S_oeis_a331491.toeplitz _).submatrix
      (parityIndex (m+1)) (parityIndex (m+1)) = Pᵀ * (B * P) := by
    dsimp only [P]
    conv_rhs =>
      rw [transpose_add,transpose_one,transpose_vecMulVec,mul_add,mul_one,mul_vecMulVec,bw,
        add_mul,one_mul,mul_add,vecMulVec_mul,wb,vecMulVec_mul_vecMulVec,wu]
    ext i j
    rw [submatrix_apply,entries]
    simp [B,u,v,vecMulVec_apply]
    ring
  rw [← det_submatrix_equiv_self (parityIndex (m+1)), congruence,
    det_mul,det_mul,det_transpose,detP,show B.det = 1 from det_form _]
  ring

end ToeplitzPairs

theorem OMA.solution : type_of% @OMA.S_oeis_a331491.main := by
  refine ⟨Matrix.det_isEmpty, ?_⟩
  rintro (_ | n) hn
  · omega
  · exact ToeplitzPairs.determinant n
