import OMAStatements.S_oeis_a005329
import Mathlib

/-! Apply the linear functional taking X^k to the kth 2-factorial. Translation
of its argument implements the binomial transform, while the product recurrence
identifies the transform at twice the argument. -/
namespace Deldor14.TwoFactorials
open Polynomial Finset OMA.S_oeis_a005329
private noncomputable def L : ℤ[X] →ₗ[ℤ] ℤ :=
  Polynomial.lsum (fun n => a n • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
private lemma mono (n : ℕ) (z : ℤ) : L (monomial n z) = z*a n := by
  simp [L,Polynomial.lsum_apply,Polynomial.sum_monomial_index,mul_comm]
private lemma atom (n : ℕ) : L (X^n) = a n := by
  simpa [← C_mul_X_pow_eq_monomial] using mono n 1
private lemma scalar (z : ℤ) (p : ℤ[X]) : L (C z * p) = z*L p := by
  rw [← smul_eq_C_mul, map_smul]; rfl
private lemma recA (n : ℕ) : a (n+1)=a n*(2^(n+1)-1) := by
  unfold a; rw [Finset.prod_Icc_succ_top (by omega)]
private lemma double (p : ℤ[X]) : L ((1+X)*p)=2*L (p.comp (2*X)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add,map_add,add_comp,map_add,hp,hq];ring
  | monomial n z =>
    rw [← C_mul_X_pow_eq_monomial,mul_comp,C_comp,pow_comp,X_comp,mul_pow]
    have e : (1+X)*(C z*X^n)=C z*X^n+C z*X^(n+1) := by rw [pow_succ];ring
    rw [e,map_add,scalar,scalar,atom,atom,recA]
    rw [show (C z * ((2:ℤ[X])^n * X^n))=C (z*2^n)*X^n by
      simp only [map_mul,map_pow];norm_num;ring,scalar,atom,pow_succ]
    ring
private lemma expand (p : ℤ[X]) (z : ℤ) (n : ℕ) :
    L ((p+C z)^n)= ∑ k ∈ range (n+1), z^(n-k)*(n.choose k : ℤ)*L (p^k) := by
  rw [add_pow,map_sum]
  apply sum_congr rfl
  intro k _
  rw [show p^k*C z^(n-k)*(n.choose k : ℤ[X])=C (z^(n-k)*(n.choose k : ℤ))*p^k by
    rw [map_mul,map_pow,C_eq_natCast];ring,scalar]
private lemma separate (n : ℕ) :
    L ((1+X)^(n+1))=2*L ((1+2*X)^n) := by
  rw [pow_succ',double,pow_comp,add_comp,one_comp,X_comp]
private lemma total (n : ℕ) :
    ∑ k ∈ range (n+1), (n.choose k : ℤ)*L ((1+2*X)^k) =
      2^n*L ((1+X)^n) := by
  have e := expand (1+2*X) 1 n
  simp only [map_one,one_pow,one_mul] at e
  rw [← e,show (1+2*X+1 : ℤ[X])=C 2*(1+X) by norm_num;ring,mul_pow,
    ← map_pow,scalar]
private lemma seqB (n : ℕ) : b n=L ((1+2*X)^n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [b,a] using (atom 0).symm
    | succ n =>
      rw [b,ih n (by omega)]
      have h := total (n+1)
      rw [sum_range_succ,Nat.choose_self,Nat.cast_one,one_mul,separate] at h
      rw [Fin.sum_univ_eq_sum_range (fun k => ((n+1).choose k : ℤ)*b k)]
      have eq : ∑ k ∈ range (n+1), ((n+1).choose k : ℤ)*b k =
          ∑ k ∈ range (n+1), ((n+1).choose k : ℤ)*L ((1+2*X)^k) := by
        apply sum_congr rfl
        intro k hk
        rw [ih k (mem_range.mp hk)]
      rw [eq,show n+2=(n+1)+1 by omega,pow_succ]
      linarith
private lemma seqC (n : ℕ) : c n=L ((1+X)^n) := by
  cases n with
  | zero => simpa [c,a] using (atom 0).symm
  | succ n => rw [c,seqB,separate]
theorem full : type_of% @OMA.S_oeis_a005329.main := by
  intro n
  have h := expand (1+X) (-1) n
  rw [show (1+X+C (-1) : ℤ[X])=X by simp,atom] at h
  simpa only [seqC] using h
end Deldor14.TwoFactorials
theorem OMA.solution : type_of% @OMA.S_oeis_a005329.main := Deldor14.TwoFactorials.full
