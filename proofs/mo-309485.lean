import OMAStatements.S_mo_309485

open Polynomial Finset

namespace OMA.Aux309485

lemma S1 {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    ∑ i ∈ range (n+1), (-1:R)^i * (n.choose i : R) * (a+1)^i = (-a)^n := by
  have h := add_pow (-(a+1)) (1:R) n
  rw [show -(a+1) + 1 = -a by ring] at h
  rw [h]
  refine sum_congr rfl fun i _ => ?_
  rw [one_pow, neg_pow (a+1)]; ring

lemma S2 {R : Type*} [CommRing R] (a : R) (n m : ℕ) :
    ∑ i ∈ range (n+1), (-1:R)^i * (n.choose i : R) * (a^i * (a+1)^(m+n-i)) = (a+1)^m := by
  have h := add_pow (-a) (a+1) n
  rw [show -a + (a+1) = 1 by ring, one_pow] at h
  have : ∑ i ∈ range (n+1), (-1:R)^i * (n.choose i : R) * (a^i * (a+1)^(m+n-i))
      = (a+1)^m * ∑ i ∈ range (n+1), (-a)^i * (a+1)^(n-i) * (n.choose i : R) := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [show m + n - i = m + (n - i) by omega, pow_add, neg_pow]; ring
  rw [this, ← h, mul_one]

lemma S3 {R : Type*} [CommRing R] (a : R) (n m : ℕ) :
    ∑ i ∈ range (n+1), (-1:R)^i * (n.choose i : R) * (a+1)^(m+n-i) = (a+1)^m * a^n := by
  have h := add_pow (-1) (a+1) n
  rw [show -1 + (a+1) = a by ring] at h
  rw [h, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show m + n - i = m + (n - i) by omega, pow_add]; ring

/-- generic row polynomial -/
def row {R : Type*} [CommRing R] (a : R) (n i : ℕ) : R :=
  (a+1)^i + a^i * (a+1)^(2*n+1-i) + (a+1)^(2*n+1-i)

lemma Ln {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    ∑ i ∈ range (n+1), (-1:R)^i * (n.choose i : R) * row a n i
      = (-a)^n + (a+1)^(n+1) + (a+1)^(n+1) * a^n := by
  have e : 2*n+1 = (n+1)+n := by ring
  simp only [row, mul_add, sum_add_distrib]
  rw [e, S1, S2, S3]

lemma Ln1 {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    ∑ i ∈ range (n+1), (-1:R)^i * ((n+1).choose i : R) * row a n i
      = (-a)^(n+1) + (a+1)^n + (a+1)^n * a^(n+1)
        - (-1:R)^(n+1) * ((a+1)^(n+1) + a^(n+1) * (a+1)^n + (a+1)^n) := by
  have e : 2*n+1 = n+(n+1) := by ring
  have h := sum_range_succ (fun i => (-1:R)^i * ((n+1).choose i : R) * row a n i) (n+1)
  have hfull : ∑ i ∈ range (n+1+1), (-1:R)^i * ((n+1).choose i : R) * row a n i
      = (-a)^(n+1) + (a+1)^n + (a+1)^n * a^(n+1) := by
    simp only [row, mul_add, sum_add_distrib]
    rw [e, S1, S2, S3]
  have hlast : row a n (n+1) = (a+1)^(n+1) + a^(n+1) * (a+1)^n + (a+1)^n := by
    simp only [row]
    rw [show 2*n+1-(n+1) = n by omega]
  rw [hfull, hlast, Nat.choose_self, Nat.cast_one, mul_one] at h
  rw [h]; ring

lemma mainSum {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    ∑ i ∈ range (n+1), ((-1:R)^i * ((n.choose i : R) + ((n+1).choose i : R))
        - (if i = n then 1 + (-1:R)^n else 0)) * row a n i
      = a^(n+1) * (-(-1:R)^n * (1 + ∑ k ∈ range (n+1), (a+1)^k)
          + (1 + (-1:R)^n) * (a+1)^n) := by
  have hsplit : ∀ i ∈ range (n+1), ((-1:R)^i * ((n.choose i : R) + ((n+1).choose i : R))
        - (if i = n then 1 + (-1:R)^n else 0)) * row a n i
      = (-1:R)^i * (n.choose i : R) * row a n i + (-1:R)^i * ((n+1).choose i : R) * row a n i
        - (if i = n then (1 + (-1:R)^n) * row a n i else 0) := by
    intro i _
    split_ifs <;> ring
  rw [sum_congr rfl hsplit, sum_sub_distrib, sum_add_distrib, Ln, Ln1, sum_ite_eq']
  rw [if_pos (mem_range.mpr (Nat.lt_succ_self n))]
  have hrow : row a n n = (a+1)^n + a^n * (a+1)^(n+1) + (a+1)^(n+1) := by
    simp only [row]; rw [show 2*n+1-n = n+1 by omega]
  have hg := geom_sum_mul_add a (n+1)
  rw [hrow, neg_pow a n, neg_pow a (n+1)]
  linear_combination ((-1:R)^n * a^n) * hg

noncomputable def rowP (n i : ℕ) : ℂ[X] := row (X : ℂ[X]) n i

lemma entry (n : ℕ) (i j : Fin (n+1)) :
    OMA.S_mo_309485.matrix n i j = (rowP n i.val).coeff j.val := by
  simp only [OMA.S_mo_309485.matrix, rowP, row, coeff_add, coeff_X_add_one_pow,
    coeff_X_pow_mul']

def yv (n i : ℕ) : ℂ :=
  (-1:ℂ)^i * ((n.choose i : ℂ) + ((n+1).choose i : ℂ)) - (if i = n then 1 + (-1:ℂ)^n else 0)

lemma yv_C (n i : ℕ) : C (yv n i) = ((-1:ℂ[X])^i * ((n.choose i : ℂ[X]) + ((n+1).choose i : ℂ[X]))
        - (if i = n then 1 + (-1:ℂ[X])^n else 0)) := by
  unfold yv
  split_ifs <;> simp

lemma vec_zero (n : ℕ) :
    Matrix.vecMul (fun i : Fin (n+1) => yv n i.val) (OMA.S_mo_309485.matrix n) = 0 := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, entry]
  have : ∑ i : Fin (n+1), yv n i.val * (rowP n i.val).coeff j.val
      = (∑ i ∈ range (n+1), C (yv n i) * rowP n i).coeff j.val := by
    rw [finsetSum_coeff, ← Fin.sum_univ_eq_sum_range (fun i => (C (yv n i) * rowP n i).coeff j.val)]
    simp only [coeff_C_mul]
  rw [this]
  simp only [yv_C, rowP]
  rw [mainSum, coeff_X_pow_mul', if_neg (by have := j.isLt; omega)]

end OMA.Aux309485

theorem OMA.solution : type_of% @OMA.S_mo_309485.main := by
  intro n
  constructor
  · intro h
    by_contra hn
    have h0 : n = 0 := by omega
    subst h0
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply,
      zero_smul] at hv
    apply hv.2
    funext k
    have hk : k = 0 := Fin.ext (by have := k.isLt; simp)
    subst hk
    have := congrFun hv.1 0
    simp [Matrix.mulVec, dotProduct, OMA.S_mo_309485.matrix] at this
    rcases this with h1 | h1
    · norm_num at h1
    · simpa using h1
  · intro hn
    have hdet : (OMA.S_mo_309485.matrix n).det = 0 := by
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨fun i : Fin (n+1) => OMA.Aux309485.yv n i.val, ?_, OMA.Aux309485.vec_zero n⟩
      intro h0
      have := congrFun h0 ⟨0, Nat.succ_pos n⟩
      simp only [OMA.Aux309485.yv, Pi.zero_apply] at this
      rw [if_neg (by omega)] at this
      norm_num at this
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply,
      zero_smul]
    exact ⟨hv, hv0⟩
