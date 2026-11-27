import FormalConjectures.Wikipedia.WeighingMatrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Composition
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Construction of weighing matrices using symmetric odd-order square-weight factors. -/

open Matrix Filter
open scoped Kronecker
namespace WeightConstruction

private def ternary (x : ℤ) := x = -1 ∨ x = 0 ∨ x = 1
private def signed {I : Type*} (A : Matrix I I ℤ) := ∀ i j, ternary (A i j)
private def weighs {I : Type*} [Fintype I] [DecidableEq I] (w : ℕ) (A : Matrix I I ℤ) :=
  signed A ∧ A*A.transpose=(w : Matrix I I ℤ)

private lemma good_iff {n w : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} :
    weighs w A ↔ WeighingMatrix.IsWeighingMatrix w A := by
  unfold weighs signed ternary WeighingMatrix.IsWeighingMatrix
  simp

private lemma neg_ternary {x : ℤ} (h : ternary x) : ternary (-x) := by
  rcases h with h | h | h <;> simp [ternary,h]

private lemma signed_id (I : Type*) [DecidableEq I] : signed (1 : Matrix I I ℤ) := by
  intro i j
  by_cases h : i=j <;> simp [one_apply,h,ternary]

private lemma weight_id (I : Type*) [Fintype I] [DecidableEq I] : weighs 1 (1 : Matrix I I ℤ) :=
  ⟨signed_id I, by simp⟩

private lemma weight_zero (I : Type*) [Fintype I] [DecidableEq I] : weighs 0 (0 : Matrix I I ℤ) :=
  ⟨fun _ _ ↦ Or.inr (Or.inl rfl), by simp⟩

private lemma weight_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {w : ℕ} {A : Matrix I I ℤ} (h : weighs w A) (e : I ≃ J) : weighs w (reindex e e A) := by
  refine ⟨fun i j ↦ h.1 _ _,?_⟩
  change (reindexRingEquiv ℤ e) A * (reindexRingEquiv ℤ e) A.transpose = _
  rw [←map_mul,h.2,map_natCast]

private lemma sym_reindex {I J : Type*} (e : I ≃ J) (A : Matrix I I ℤ) (h : A.transpose=A) :
    (reindex e e A).transpose=reindex e e A := congrArg (reindex e e) h

private lemma weight_tensor {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {a b : ℕ} {A : Matrix I I ℤ} {B : Matrix J J ℤ}
    (hA : weighs a A) (hB : weighs b B) : weighs (a*b) (A ⊗ₖ B) := by
  constructor
  · rintro ⟨i,j⟩ ⟨k,l⟩
    change ternary (A i k*B j l)
    obtain ha|ha|ha := hA.1 i k <;> obtain hb|hb|hb := hB.1 j l <;> simp [ha,hb,ternary]
  · change (A ⊗ₖ B)*(A.transpose ⊗ₖ B.transpose) = _
    rw [←mul_kronecker_mul,hA.2,hB.2,natCast_kronecker_natCast]

private lemma sym_tensor {I J : Type*} {A : Matrix I I ℤ} {B : Matrix J J ℤ}
    (hA : A.transpose=A) (hB : B.transpose=B) : (A ⊗ₖ B).transpose=A ⊗ₖ B := by
  change A.transpose ⊗ₖ B.transpose=A ⊗ₖ B
  rw [hA,hB]

private lemma block_natCast {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (w : ℕ) : fromBlocks (w : Matrix I I ℤ) 0 0 (w : Matrix J J ℤ) = (w : Matrix (I⊕J) (I⊕J) ℤ) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Nat.cast_succ, Nat.cast_succ, Nat.cast_succ, ←ih, ←fromBlocks_one]
    simp only [fromBlocks_add,add_zero]

private lemma weight_direct {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {w : ℕ} {A : Matrix I I ℤ} {B : Matrix J J ℤ} (hA : weighs w A) (hB : weighs w B) :
    weighs w (fromBlocks A 0 0 B) := by
  constructor
  · rintro (i|i) (j|j)
    · exact hA.1 i j
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact hB.1 i j
  · rw [fromBlocks_transpose,fromBlocks_multiply]
    simp only [transpose_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, hA.2,hB.2]
    exact block_natCast (I:=I) (J:=J) w

private lemma doubled {I : Type*} [Fintype I] [DecidableEq I]
    {w : ℕ} (A : Matrix I I ℤ) (h : weighs w A) (hs : A.transpose=A) :
    let B := fromBlocks A (1:Matrix I I ℤ) 1 (-A)
    B.transpose=B ∧ weighs (w+1) B := by
  dsimp only
  have ht : (fromBlocks A (1:Matrix I I ℤ) 1 (-A)).transpose = fromBlocks A 1 1 (-A) := by
    rw [fromBlocks_transpose,transpose_neg,transpose_one,hs]
  refine ⟨ht,?_,?_⟩
  · rintro (i|i) (j|j)
    · exact h.1 _ _
    · exact signed_id I _ _
    · exact signed_id I _ _
    · exact neg_ternary (h.1 _ _)
  · have haa : A*A=(w:Matrix I I ℤ) := by simpa only [hs] using h.2
    rw [ht,fromBlocks_multiply]
    simp only [haa,neg_mul,mul_neg,neg_neg,mul_one,one_mul,add_neg_cancel]
    rw [add_comm (1:Matrix I I ℤ) w,←Nat.cast_succ,block_natCast]

private lemma two_power_order (w : ℕ) : ∃ A : Matrix (Fin (2^w)) (Fin (2^w)) ℤ,
    A.transpose=A ∧ weighs w A := by
  induction w with
  | zero => exact ⟨0,transpose_zero,weight_zero _⟩
  | succ w ih =>
    obtain ⟨A,hs,ha⟩ := ih
    obtain ⟨hs',ha'⟩ := doubled A ha hs
    let e := finSumFinEquiv.trans (finCongr (show 2^w+2^w=2^(w+1) by rw [pow_succ]; omega))
    exact ⟨_,sym_reindex e _ hs',weight_reindex ha' e⟩

private def sevenMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  fun i j ↦ ![1,0,0,-1,0,-1,-1] (i+j)

private lemma two_block : ∃ n : ℕ, Odd n ∧ ∃ H : Matrix (Fin n) (Fin n) ℤ,
    H.transpose=H ∧ weighs (2^2) H := by
  refine ⟨7,by decide,sevenMatrix,?_,?_⟩
  · ext i j
    simp [sevenMatrix,add_comm]
  · constructor
    · change ∀ (i j : Fin 7), sevenMatrix i j = -1 ∨ sevenMatrix i j = 0 ∨ sevenMatrix i j = 1
      intro i j
      fin_cases i <;> fin_cases j <;> decide +kernel
    · ext i j
      fin_cases i <;> fin_cases j <;> decide +kernel


private def quad {I : Type*} (A B C D : Matrix I I ℤ) :
    Matrix (Fin 4) (Fin 4) (Matrix I I ℤ) :=
  !![A,B,C,D; -B,A,-D,C; -C,D,A,-B; -D,-C,B,A]

private lemma quaternion {I : Type*} [Fintype I] [DecidableEq I] {a b c d : ℕ}
    (A B C D : Matrix I I ℤ) (hA : weighs a A) (hB : weighs b B)
    (hC : weighs c C) (hD : weighs d D)
    (sA : A.transpose=A) (sB : B.transpose=B) (sC : C.transpose=C) (sD : D.transpose=D)
    (ab : B*A=A*B) (ac : C*A=A*C) (ad : D*A=A*D)
    (bc : C*B=B*C) (bd : D*B=B*D) (cd : D*C=C*D) :
    ∃ H : Matrix (Fin 4 × I) (Fin 4 × I) ℤ, weighs (a+b+c+d) H := by
  let Q := quad A B C D
  let e := compRingEquiv (Fin 4) I ℤ
  have symEntries (i j : Fin 4) : (Q i j).transpose=Q i j := by
    fin_cases i <;> fin_cases j <;> simp [Q,quad,sA,sB,sC,sD]
  have trans : (e Q).transpose=e Q.transpose := by
    ext ⟨i,k⟩ ⟨j,l⟩
    exact congrFun (congrFun (symEntries j i) k) l
  have entries : signed (e Q) := by
    rintro ⟨i,k⟩ ⟨j,l⟩
    change ternary (Q i j k l)
    fin_cases i <;> fin_cases j <;>
      first | exact hA.1 _ _ | exact hB.1 _ _ | exact hC.1 _ _ | exact hD.1 _ _
            | exact neg_ternary (hA.1 _ _) | exact neg_ternary (hB.1 _ _)
            | exact neg_ternary (hC.1 _ _) | exact neg_ternary (hD.1 _ _)
  have aa : A*A=(a:Matrix I I ℤ) := by simpa only [sA] using hA.2
  have bb : B*B=(b:Matrix I I ℤ) := by simpa only [sB] using hB.2
  have cc : C*C=(c:Matrix I I ℤ) := by simpa only [sC] using hC.2
  have dd : D*D=(d:Matrix I I ℤ) := by simpa only [sD] using hD.2
  have mm : Q*Q.transpose = ((a+b+c+d : ℕ) : Matrix (Fin 4) (Fin 4) (Matrix I I ℤ)) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Q,quad,mul_apply,Fin.sum_univ_four,Matrix.natCast_apply,
        aa,bb,cc,dd,ab,ac,ad,bc,bd,cd] <;> abel
  exact ⟨e Q,entries,by rw [trans,←map_mul,mm,map_natCast]⟩

private lemma put_together {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    {a b c d : ℕ} (A : Matrix I I ℤ) (B : Matrix J J ℤ) (C : Matrix K K ℤ) (D : Matrix L L ℤ)
    (hA : weighs a A) (hB : weighs b B) (hC : weighs c C) (hD : weighs d D)
    (sA : A.transpose=A) (sB : B.transpose=B) (sC : C.transpose=C) (sD : D.transpose=D) :
    ∃ H : Matrix (Fin 4 × ((I×J)×(K×L))) (Fin 4 × ((I×J)×(K×L))) ℤ, weighs (a+b+c+d) H := by
  let U := fun (P : Matrix I I ℤ) (Q : Matrix J J ℤ) (R : Matrix K K ℤ) (S : Matrix L L ℤ) ↦
    (P ⊗ₖ Q) ⊗ₖ (R ⊗ₖ S)
  have hw {x y z t : ℕ} {P : Matrix I I ℤ} {Q : Matrix J J ℤ} {R : Matrix K K ℤ} {S : Matrix L L ℤ}
      (p : weighs x P) (q : weighs y Q) (r : weighs z R) (s : weighs t S) :
      weighs (x*y*(z*t)) (U P Q R S) := weight_tensor (weight_tensor p q) (weight_tensor r s)
  apply quaternion (U A 1 1 1) (U 1 B 1 1) (U 1 1 C 1) (U 1 1 1 D)
  · simpa only [mul_one,one_mul] using hw hA (weight_id J) (weight_id K) (weight_id L)
  · simpa only [mul_one,one_mul] using hw (weight_id I) hB (weight_id K) (weight_id L)
  · simpa only [mul_one,one_mul] using hw (weight_id I) (weight_id J) hC (weight_id L)
  · simpa only [mul_one,one_mul] using hw (weight_id I) (weight_id J) (weight_id K) hD
  · exact sym_tensor (sym_tensor sA transpose_one) (sym_tensor transpose_one transpose_one)
  · exact sym_tensor (sym_tensor transpose_one sB) (sym_tensor transpose_one transpose_one)
  · exact sym_tensor (sym_tensor transpose_one transpose_one) (sym_tensor sC transpose_one)
  · exact sym_tensor (sym_tensor transpose_one transpose_one) (sym_tensor transpose_one sD)
  all_goals simp only [U,←mul_kronecker_mul,mul_one,one_mul]

private def squareOrder (s : ℕ) : Prop :=
  ∃ n : ℕ, Odd n ∧ ∃ A : Matrix (Fin n) (Fin n) ℤ, A.transpose=A ∧ weighs (s^2) A

private lemma square_orders
    (oddPrime : ∀ p : ℕ, p.Prime → Odd p → squareOrder p) (s : ℕ) : squareOrder s := by
  induction s using Nat.recOnMul with
  | zero => exact ⟨1,by decide,0,transpose_zero,by simpa using weight_zero (Fin 1)⟩
  | one => exact ⟨1,by decide,1,transpose_one,by simpa using weight_id (Fin 1)⟩
  | prime p hp =>
    rcases hp.eq_two_or_odd with he|ho
    · subst p; exact two_block
    · exact oddPrime _ hp (Nat.odd_iff.mpr ho)
  | mul p q hp hq =>
    obtain ⟨i,hi,A,hA,wa⟩ := hp
    obtain ⟨j,hj,B,hB,wb⟩ := hq
    refine ⟨i*j,hi.mul hj,reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B),
      sym_reindex _ _ (sym_tensor hA hB),?_⟩
    rw [mul_pow]
    exact weight_reindex (weight_tensor wa wb) _

private def possible (w n : ℕ) := ∃ A : Matrix (Fin n) (Fin n) ℤ, weighs w A

private lemma possible_add {w n m : ℕ} (h : possible w n) (h' : possible w m) :
    possible w (n+m) := by
  obtain ⟨A,ha⟩ := h
  obtain ⟨B,hb⟩ := h'
  exact ⟨_,weight_reindex (weight_direct ha hb) finSumFinEquiv⟩

private lemma possible_mul {w n : ℕ} (h : possible w n) (k : ℕ) : possible w (k*n) := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    refine ⟨0,?_,?_⟩
    · intro i
      exact Fin.elim0 i
    · ext i
      exact Fin.elim0 i
  | succ k ih =>
    rw [Nat.succ_mul]
    exact possible_add ih h

private lemma odd_multiplier (w : ℕ)
    (oddPrime : ∀ p : ℕ, p.Prime → Odd p → squareOrder p) :
    ∃ t : ℕ, Odd t ∧ possible w (4*t) := by
  obtain ⟨a,b,c,d,rfl⟩ := Nat.sum_four_squares w
  obtain ⟨i,hi,A,sA,hA⟩ := square_orders oddPrime a
  obtain ⟨j,hj,B,sB,hB⟩ := square_orders oddPrime b
  obtain ⟨k,hk,C,sC,hC⟩ := square_orders oddPrime c
  obtain ⟨l,hl,D,sD,hD⟩ := square_orders oddPrime d
  obtain ⟨H,hH⟩ := put_together A B C D hA hB hC hD sA sB sC sD
  let t := (i*j)*(k*l)
  let e := Fintype.equivFinOfCardEq (α:=Fin 4 × ((Fin i × Fin j) × (Fin k × Fin l)))
    (show Fintype.card _ = 4*t by simp [t])
  exact ⟨t,(hi.mul hj).mul (hk.mul hl),_,weight_reindex hH e⟩

private lemma eventual_orders (w : ℕ)
    (oddPrime : ∀ p : ℕ, p.Prime → Odd p → squareOrder p) :
    ∀ᶠ m in atTop, possible w (4*m) := by
  obtain ⟨t,ht,H⟩ := odd_multiplier w oddPrime
  obtain ⟨A,_,ha⟩ := two_power_order w
  have hb : possible w (4*(2^w)) := possible_mul (show possible w (2^w) from ⟨A,ha⟩) 4
  have cop : (2^w).Coprime t := (Nat.coprime_two_left.mpr ht).pow_left _
  filter_upwards [eventually_ge_atTop ((2^w-1)*(t-1))] with m hm
  obtain ⟨x,y,he⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (2^w) t m
    (by simp [cop.gcd_eq_one]) (by omega)
  have he' : x*(4*2^w)+y*(4*t)=4*m := by nlinarith only [congrArg (fun z : ℕ ↦ 4*z) he]
  rw [←he']
  exact possible_add (possible_mul hb x) (possible_mul H y)

end WeightConstruction

/- Symmetric odd-order blocks from the dot product on the projective plane. -/

open Finset
open scoped LinearAlgebra.Projectivization

namespace WeightConstruction

section

variable {F : Type} [Field F]

/-- The linear form associated with a row. -/
private def dotForm (u : Fin 3 → F) : (Fin 3 → F) →ₗ[F] F :=
  ∑ i, u i • LinearMap.proj i

private theorem dotForm_apply (u x : Fin 3 → F) :
    dotForm u x = ∑ i, u i * x i := by
  simp [dotForm, LinearMap.sum_apply]

private theorem dotForm_comm (u x : Fin 3 → F) : dotForm u x = dotForm x u := by
  simp only [dotForm_apply, mul_comm]

private theorem dotForm_single (u : Fin 3 → F) (i : Fin 3) :
    dotForm u (Pi.single i 1) = u i := by
  rw [dotForm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

private theorem dotForm_surj {u : Fin 3 → F} (hu : u ≠ 0) :
    Function.Surjective (dotForm u) := by
  have ⟨i,hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  intro y
  refine ⟨(y / u i) • Pi.single i 1, ?_⟩
  rw [map_smul,dotForm_single,smul_eq_mul,div_mul_cancel₀ _ hi]

private theorem two_forms_surj (u v : ℙ F (Fin 3 → F)) (huv : u ≠ v) :
    Function.Surjective ((dotForm u.rep).prod (dotForm v.rep)) := by
  let f := dotForm u.rep
  let g := dotForm v.rep
  obtain ⟨t,ht⟩ : ∃ t, g t = 1 := dotForm_surj v.rep_nonzero 1
  have hs : ∃ s, g s = 0 ∧ f s = 1 := by
    by_contra! h
    have hz (s : Fin 3 → F) (hg : g s = 0) : f s = 0 := by
      by_contra! hfs
      refine (h ((f s)⁻¹ • s) (by simp [hg])) ?_
      rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hfs]
    have hl (x : Fin 3 → F) : f x = g x * f t := by
      have hh := hz (x - (g x) • t) (by simp [ht])
      simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hh
    apply huv
    rw [← Projectivization.mk_rep u, ← Projectivization.mk_rep v,
      Projectivization.mk_eq_mk_iff']
    refine ⟨f t, funext fun i => ?_⟩
    have hh := hl (Pi.single i 1)
    change dotForm u.rep (Pi.single i 1) = dotForm v.rep (Pi.single i 1) * f t at hh
    simp only [dotForm_single] at hh
    change f t * v.rep i = u.rep i
    rw [hh,mul_comm]
  obtain ⟨s,hgs,hfs⟩ := hs
  rintro ⟨a,b⟩
  refine ⟨b • t + (a - b * f t) • s, ?_⟩
  change (f _, g _) = _
  simp [map_add,map_smul,smul_eq_mul,hgs,hfs,ht]

variable {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W]

/-- Split a surjective linear map by translating each fiber to the kernel. -/
private noncomputable def splitFiber (L : V →ₗ[F] W) (hL : Function.Surjective L) :
    V ≃ W × L.ker := by
  let s (w : W) := Classical.choose (hL w)
  have hs (w : W) : L (s w) = w := Classical.choose_spec (hL w)
  refine ⟨fun x => (L x,⟨x - s (L x), by simp [hs]⟩),
    fun y => s y.1 + y.2.1, ?_, ?_⟩
  · intro x
    simp
  · rintro ⟨w,k⟩
    have hk : L k.1 = 0 := k.2
    have he : L (s w + k.1) = w := by simp [hs,hk]
    apply Prod.ext he
    apply Subtype.ext
    change s w + k.1 - s (L (s w + k.1)) = k.1
    rw [he,add_comm,add_sub_cancel_right]

private theorem sum_fiber_split [Fintype V] [Fintype W] (L : V →ₗ[F] W)
    (hL : Function.Surjective L) [Fintype L.ker] (f : W → ℤ) :
    (∑ x : V, f (L x)) = (∑ w : W, f w) * (Fintype.card L.ker : ℤ) := by
  classical
  rw [Fintype.sum_equiv (splitFiber L hL) _ (fun y => f y.1) (by intro; rfl)]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  simp [mul_comm]

/-- Scale a chosen representative by a nonzero field element. -/
private noncomputable def unitRepEquiv :
    (ℙ F V) × Fˣ ≃ {x : V // x ≠ 0} := by
  let a (x : (ℙ F V) × Fˣ) : V := (x.2 : F) • x.1.rep
  have hn (x : (ℙ F V) × Fˣ) : a x ≠ 0 :=
    smul_ne_zero x.2.ne_zero x.1.rep_nonzero
  have hm (x : (ℙ F V) × Fˣ) : Projectivization.mk F (a x) (hn x) = x.1 := by
    rw [← Projectivization.mk_rep x.1, Projectivization.mk_eq_mk_iff']
    exact ⟨x.2,rfl⟩
  refine Equiv.ofBijective (fun x => ⟨a x,hn x⟩) ⟨?_,?_⟩
  · rintro ⟨x,c⟩ ⟨y,d⟩ h
    have hxy := congrArg (fun z : {v : V // v ≠ 0} => Projectivization.mk F z.1 z.2) h
    change Projectivization.mk F (a (x,c)) (hn (x,c)) =
      Projectivization.mk F (a (y,d)) (hn (y,d)) at hxy
    rw [hm,hm] at hxy
    change x = y at hxy
    subst y
    have he : (c : F) • x.rep = (d : F) • x.rep := congrArg Subtype.val h
    have hsub : ((c : F) - (d : F)) • x.rep = 0 := by rw [sub_smul,he,sub_self]
    have hcd : (c : F) = (d : F) :=
      sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right x.rep_nonzero)
    exact congrArg (fun s : Fˣ => (x,s)) (Units.ext hcd)
  · rintro ⟨x,hx⟩
    let X := Projectivization.mk F x hx
    have he : Projectivization.mk F x hx = Projectivization.mk F X.rep X.rep_nonzero :=
      (Projectivization.mk_rep X).symm
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff F _ _ hx X.rep_nonzero).mp he
    exact ⟨(X,c),Subtype.ext hc⟩

private theorem unitRepEquiv_apply (x : (ℙ F V) × Fˣ) :
    (unitRepEquiv x).1 = (x.2 : F) • x.1.rep := rfl

end

private theorem sum_projective {F V : Type} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V]
    [Module F V] [Fintype V] [Fintype (ℙ F V)] (f : V → ℤ) (hzero : f 0 = 0)
    (hscale : ∀ (c : Fˣ) (x : V), f ((c : F) • x) = f x) :
    (∑ x : V, f x) = (∑ u : ℙ F V, f u.rep) * (Fintype.card Fˣ : ℤ) := by
  classical
  have hz : (∑ x : {x : V // ¬ x ≠ 0}, f x.1) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [not_not.mp x.2,hzero]
  have h := Fintype.sum_subtype_add_sum_subtype (fun x : V => x ≠ 0) f
  rw [hz,add_zero] at h
  calc
    (∑ x : V, f x) = ∑ x : {x : V // x ≠ 0}, f x.1 := h.symm
    _ = ∑ y : (ℙ F V) × Fˣ, f y.1.rep :=
      (Fintype.sum_equiv unitRepEquiv _ _ (fun y => by
        rw [unitRepEquiv_apply,hscale])).symm
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      simp [mul_comm]

private theorem quadraticSquares {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    (∑ x : F, quadraticChar F x ^ 2) = (Fintype.card Fˣ : ℤ) := by
  rw [← MulChar.sum_one_eq_card_units]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0
  · subst x
    rw [quadraticChar_zero, zero_pow (by decide : 2 ≠ 0), MulChar.map_zero]
  · rw [quadraticChar_sq_one hx, MulChar.one_apply (Ne.isUnit hx)]

private theorem rowGram {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [Fintype (ℙ (ZMod p) (Fin 3 → ZMod p))]
    [DecidableEq (ℙ (ZMod p) (Fin 3 → ZMod p))]
    (u v : ℙ (ZMod p) (Fin 3 → ZMod p)) :
    (∑ z : ℙ (ZMod p) (Fin 3 → ZMod p),
      quadraticChar (ZMod p) (dotForm u.rep z.rep) *
        quadraticChar (ZMod p) (dotForm v.rep z.rep)) =
      if u = v then (p : ℤ)^2 else 0 := by
  classical
  let χ := quadraticChar (ZMod p)
  let f (x : Fin 3 → ZMod p) : ℤ := χ (dotForm u.rep x) * χ (dotForm v.rep x)
  have hsym (c : (ZMod p)ˣ) (x : Fin 3 → ZMod p) : f ((c : ZMod p) • x) = f x := by
    simp only [f, map_smul, smul_eq_mul, map_mul]
    have hs : χ (c : ZMod p) ^ 2 = 1 := quadraticChar_sq_one c.ne_zero
    calc
      _ = χ (c : ZMod p)^2 * (χ (dotForm u.rep x) * χ (dotForm v.rep x)) := by ring
      _ = _ := by rw [hs,one_mul]
  have hproj := sum_projective f (by simp [f, χ]) hsym
  have hχ : (∑ x : ZMod p, χ x) = 0 :=
    quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hc : (0 : ℤ) < (Fintype.card (ZMod p)ˣ : ℤ) := by
    exact_mod_cast Fintype.card_pos
  change (∑ z : ℙ (ZMod p) (Fin 3 → ZMod p), f z.rep) = _
  apply mul_right_cancel₀ hc.ne'
  rw [← hproj]
  by_cases huv : u = v
  · subst v
    rw [if_pos rfl]
    let L := dotForm u.rep
    have hs : Function.Surjective L := dotForm_surj u.rep_nonzero
    let _ : Fintype L.ker := Fintype.ofFinite _
    have hker : Fintype.card L.ker = p ^ 2 := by
      have h : p ^ 3 = p * Fintype.card L.ker := by
        simpa [Fintype.card_pi, ZMod.card] using Fintype.card_congr (splitFiber L hs)
      apply Nat.eq_of_mul_eq_mul_left (Fact.out (p := Nat.Prime p)).pos
      rw [← h]
      ring
    have hh := sum_fiber_split L hs (fun a => χ a ^ 2)
    rw [show (∑ a : ZMod p, χ a ^ 2) = _ from quadraticSquares,hker,Nat.cast_pow,mul_comm] at hh
    simpa only [L,f,pow_two] using hh
  · rw [if_neg huv, zero_mul]
    let L := (dotForm u.rep).prod (dotForm v.rep)
    have hs : Function.Surjective L := two_forms_surj u v huv
    let _ : Fintype L.ker := Fintype.ofFinite _
    rw [show (∑ x : Fin 3 → ZMod p, f x) =
      ∑ x : Fin 3 → ZMod p, χ (L x).1 * χ (L x).2 from rfl]
    rw [sum_fiber_split L hs (fun z => χ z.1 * χ z.2)]
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum,hχ]

/-- An odd-order symmetric weighing matrix of weight `p²` for each odd prime `p`. -/
theorem primeBlock {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ∃ n : ℕ, Odd n ∧ ∃ H : Matrix (Fin n) (Fin n) ℤ,
      H.transpose = H ∧ WeighingMatrix.IsWeighingMatrix (p^2) H := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let P := ℙ (ZMod p) (Fin 3 → ZMod p)
  let _ : Fintype P := Fintype.ofFinite P
  let n := Fintype.card P
  let e : Fin n ≃ P := (Fintype.equivFin P).symm
  have hn : n = p ^ 2 + p + 1 := by
    calc
      n = ∑ i ∈ Finset.range 3, p ^ i := by
        rw [show n = Nat.card P from Fintype.card_eq_nat_card]
        simpa only [P,Nat.card_zmod] using
          Projectivization.card_of_finrank (ZMod p) (Fin 3 → ZMod p) (n := 3) (by simp)
      _ = _ := by norm_num [Finset.sum_range_succ]; ring
  have hnOdd : Odd n := by
    obtain ⟨k,hk⟩ := ho
    refine ⟨2*k^2 + 3*k + 1,?_⟩
    rw [hn,hk]
    ring
  have hp2 : p ≠ 2 := by
    intro h
    exact (by decide : ¬ Odd (2 : ℕ)) (h ▸ ho)
  let H : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    quadraticChar (ZMod p) (dotForm (e i).rep (e j).rep)
  refine ⟨n,hnOdd,H,?_,?_,?_⟩
  · ext i j
    change quadraticChar (ZMod p) (dotForm (e j).rep (e i).rep) = _
    rw [dotForm_comm]
  · intro i j
    rcases quadraticChar_isQuadratic (ZMod p) (dotForm (e i).rep (e j).rep) with h | h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact .inl h
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    calc
      (∑ k : Fin n, H i k * H j k) =
          ∑ z : P, quadraticChar (ZMod p) (dotForm (e i).rep z.rep) *
            quadraticChar (ZMod p) (dotForm (e j).rep z.rep) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        rw [rowGram hp2]
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij,e.injective.ne hij]

end WeightConstruction

theorem OMA.solution : type_of% @WeighingMatrix.weighing_matrix_conjecture.variants.asymptotic := by
  intro w
  have hp : ∀ p : ℕ, p.Prime → Odd p → WeightConstruction.squareOrder p := by
    intro p h ho
    obtain ⟨n, hn, A, sA, hA⟩ := WeightConstruction.primeBlock h ho
    exact ⟨n, hn, A, sA, WeightConstruction.good_iff.mpr hA⟩
  filter_upwards [WeightConstruction.eventual_orders w hp] with m hm
  obtain ⟨A, hA⟩ := hm
  exact ⟨A, WeightConstruction.good_iff.mp hA⟩