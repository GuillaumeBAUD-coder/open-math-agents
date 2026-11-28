import OMAStatements.S_oeis_a263908

-- Problem: A263908: Barker's generating function and closed form for (2n+1) X 5 binary arrays with rows and columns ≡ 1 (mod 3).
-- Upstream: statements/oeis-a263908.lean (declaration OMA.S_oeis_a263908.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)

namespace OMA.ProofA263908

open Finset PowerSeries OMA.S_oeis_a263908

/-- Eisenstein integers `re + im * ω` where `ω^2 = -1 - ω`. -/
private structure Eis where
  re : ℤ
  im : ℤ
deriving DecidableEq

private lemma eis_ext {a b : Eis} (h1 : a.re = b.re) (h2 : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

private def eisAdd (x y : Eis) : Eis := ⟨x.re + y.re, x.im + y.im⟩
private def eisNeg (x : Eis) : Eis := ⟨-x.re, -x.im⟩
private def eisSub (x y : Eis) : Eis := ⟨x.re - y.re, x.im - y.im⟩
private def eisMul (x y : Eis) : Eis :=
  ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re - x.im * y.im⟩

private instance : Zero Eis := ⟨⟨0, 0⟩⟩
private instance : One Eis := ⟨⟨1, 0⟩⟩
private instance : Add Eis := ⟨eisAdd⟩
private instance : Neg Eis := ⟨eisNeg⟩
private instance : Sub Eis := ⟨eisSub⟩
private instance : Mul Eis := ⟨eisMul⟩

private lemma eis_add_re (x y : Eis) : (x + y).re = x.re + y.re := rfl
private lemma eis_add_im (x y : Eis) : (x + y).im = x.im + y.im := rfl
private lemma eis_mul_re (x y : Eis) : (x * y).re = x.re * y.re - x.im * y.im := rfl
private lemma eis_mul_im (x y : Eis) : (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl
private lemma eis_neg_re (x : Eis) : (-x).re = -x.re := rfl
private lemma eis_neg_im (x : Eis) : (-x).im = -x.im := rfl
private lemma eis_sub_re (x y : Eis) : (x - y).re = x.re - y.re := rfl
private lemma eis_sub_im (x y : Eis) : (x - y).im = x.im - y.im := rfl
private lemma eis_zero_re : (0 : Eis).re = 0 := rfl
private lemma eis_zero_im : (0 : Eis).im = 0 := rfl
private lemma eis_one_re : (1 : Eis).re = 1 := rfl
private lemma eis_one_im : (1 : Eis).im = 0 := rfl

private instance : CommRing Eis where
  add := eisAdd
  add_assoc a b c := by apply eis_ext <;> simp only [eis_add_re, eis_add_im] <;> ring
  zero := ⟨0, 0⟩
  zero_add a := by apply eis_ext <;> simp only [eis_add_re, eis_add_im, eis_zero_re, eis_zero_im] <;> ring
  add_zero a := by apply eis_ext <;> simp only [eis_add_re, eis_add_im, eis_zero_re, eis_zero_im] <;> ring
  nsmul := nsmulRec
  neg := eisNeg
  sub := eisSub
  sub_eq_add_neg a b := by apply eis_ext <;> simp only [eis_sub_re, eis_sub_im, eis_add_re, eis_add_im, eisNeg] <;> ring
  zsmul := zsmulRec
  neg_add_cancel a := by apply eis_ext <;> simp only [eis_add_re, eis_add_im, eisNeg, eis_zero_re, eis_zero_im] <;> ring
  add_comm a b := by apply eis_ext <;> simp only [eis_add_re, eis_add_im] <;> ring
  mul := eisMul
  left_distrib a b c := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im, eis_add_re, eis_add_im] <;> ring
  right_distrib a b c := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im, eis_add_re, eis_add_im] <;> ring
  zero_mul a := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im, eis_zero_re, eis_zero_im] <;> ring
  mul_zero a := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im, eis_zero_re, eis_zero_im] <;> ring
  mul_assoc a b c := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im] <;> ring
  one := ⟨1, 0⟩
  one_mul a := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im, eis_one_re, eis_one_im] <;> ring
  mul_one a := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im, eis_one_re, eis_one_im] <;> ring
  mul_comm a b := by apply eis_ext <;> simp only [eis_mul_re, eis_mul_im] <;> ring
  natCast n := ⟨n, 0⟩
  natCast_zero := rfl
  natCast_succ n := by apply eis_ext <;> simp only [eis_add_re, eis_add_im, eis_one_re, eis_one_im] <;> omega
  intCast n := ⟨n, 0⟩
  intCast_ofNat n := rfl
  intCast_negSucc n := by
    apply eis_ext
    · dsimp [eisNeg]; change Int.negSucc n = -((n + 1 : ℕ) : ℤ); omega
    · dsimp [eisNeg]; rfl

private lemma eis_intCast_re (k : ℤ) : (k : Eis).re = k := rfl
private lemma eis_natCast_re (k : ℕ) : (k : Eis).re = k := rfl

private def wPow (k : ℕ) : Eis :=
  match k % 3 with
  | 0 => ⟨1, 0⟩
  | 1 => ⟨0, 1⟩
  | _ => ⟨-1, -1⟩

private def wPowZ (x : ZMod 3) : Eis := wPow x.val

private lemma wPow_mod (k : ℕ) : wPow (k % 3) = wPow k := by
  simp [wPow]

private lemma wPowZ_add (x y : ZMod 3) : wPowZ (x + y) = wPowZ x * wPowZ y := by
  fin_cases x <;> fin_cases y <;> decide

private lemma wPowZ_zero : wPowZ 0 = 1 := rfl

private lemma wPowZ_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    wPowZ (∑ i ∈ s, f i) = ∏ i ∈ s, wPowZ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wPowZ_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, wPowZ_add, ih]

private lemma sum_wPowZ_mul (x : ZMod 3) :
    (∑ c : ZMod 3, wPowZ (c * x)) = if x = 0 then (3 : Eis) else 0 := by
  fin_cases x <;> decide

private def dot (v u : Fin 5 → ZMod 3) : ZMod 3 := ∑ j : Fin 5, v j * u j

private lemma sum_wPowZ_dot (u : Fin 5 → ZMod 3) :
    (∑ v : Fin 5 → ZMod 3, wPowZ (dot v u)) = if u = 0 then (243 : Eis) else 0 := by
  have h1 : (∑ v : Fin 5 → ZMod 3, wPowZ (dot v u)) =
      ∑ v : Fin 5 → ZMod 3, ∏ j : Fin 5, wPowZ (v j * u j) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    exact wPowZ_sum Finset.univ (fun j => v j * u j)
  rw [h1, ← Fintype.prod_sum (fun j c => wPowZ (c * u j))]
  have h2 : (∏ j : Fin 5, ∑ c : ZMod 3, wPowZ (c * u j)) =
      ∏ j : Fin 5, (if u j = 0 then (3 : Eis) else 0) := by
    refine Finset.prod_congr rfl fun j _ => sum_wPowZ_mul (u j)
  rw [h2]
  by_cases hu : u = 0
  · subst hu
    simp only [Pi.zero_apply, ↓reduceIte, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    decide
  · rw [if_neg hu]
    have hex : ∃ j : Fin 5, u j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu (funext hall)
    obtain ⟨j, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private lemma two_pow_zmod3 (k : ℕ) : (((2 ^ k : ℕ) : ZMod 3)) = (-1 : ZMod 3) ^ k := by
  rw [Nat.cast_pow]
  have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
  rw [h2]

private lemma neg_one_pow_sub_even (n : ℕ) {i : ℕ} (hi : i ≤ 2 * n) :
    (-1 : ZMod 3) ^ (2 * n - i) = (-1 : ZMod 3) ^ i := by
  have h : (-1 : ZMod 3) ^ (2 * n - i) * (-1 : ZMod 3) ^ i = (-1 : ZMod 3) ^ (2 * n) := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have h2n : (-1 : ZMod 3) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [h2n] at h
  have hsq : (-1 : ZMod 3) ^ i * (-1 : ZMod 3) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  calc (-1 : ZMod 3) ^ (2 * n - i)
      = (-1 : ZMod 3) ^ (2 * n - i) * 1 := (mul_one _).symm
    _ = (-1 : ZMod 3) ^ (2 * n - i) * ((-1 : ZMod 3) ^ i * (-1 : ZMod 3) ^ i) := by rw [hsq]
    _ = ((-1 : ZMod 3) ^ (2 * n - i) * (-1 : ZMod 3) ^ i) * (-1 : ZMod 3) ^ i := by ring
    _ = 1 * (-1 : ZMod 3) ^ i := by rw [h]
    _ = (-1 : ZMod 3) ^ i := one_mul _

private def rowZ (r : Fin 5 → Fin 2) : Fin 5 → ZMod 3 := fun j => ((r j : ℕ) : ZMod 3)

private def colVec {n : ℕ} (A : Fin (2 * n + 1) → Fin 5 → Fin 2) : Fin 5 → ZMod 3 :=
  fun j => (∑ i : Fin (2 * n + 1), (-1 : ZMod 3) ^ i.val * ((A i j : ℕ) : ZMod 3)) - 1

private lemma colVal_mod_three_iff {n : ℕ} (A : Fin (2 * n + 1) → Fin 5 → Fin 2) :
    (∀ j : Fin 5, colVal A j % 3 = 1) ↔ colVec A = 0 := by
  constructor
  · intro h
    ext j
    simp only [colVec, Pi.zero_apply, sub_eq_zero]
    have hj := h j
    have hcast : ((colVal A j : ℕ) : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, hj]
      rfl
    have hsum_eq : (∑ i : Fin (2 * n + 1), (-1 : ZMod 3) ^ i.val * ((A i j : ℕ) : ZMod 3)) =
        ((colVal A j : ℕ) : ZMod 3) := by
      rw [colVal, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.cast_mul, show 2 * n + 1 - 1 - i.val = 2 * n - i.val by omega,
        two_pow_zmod3, neg_one_pow_sub_even n (by omega : i.val ≤ 2 * n), mul_comm]
    rw [hsum_eq, hcast]
  · intro h j
    have hj := congrFun h j
    simp only [colVec, Pi.zero_apply, sub_eq_zero] at hj
    have hcast : ((colVal A j : ℕ) : ZMod 3) = 1 := by
      rw [colVal, Nat.cast_sum]
      calc ∑ i : Fin (2 * n + 1), (((A i j : ℕ) * 2 ^ (2 * n + 1 - 1 - i.val) : ℕ) : ZMod 3)
          = ∑ i : Fin (2 * n + 1), (-1 : ZMod 3) ^ i.val * ((A i j : ℕ) : ZMod 3) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Nat.cast_mul, show 2 * n + 1 - 1 - i.val = 2 * n - i.val by omega,
                two_pow_zmod3, neg_one_pow_sub_even n (by omega : i.val ≤ 2 * n), mul_comm]
        _ = 1 := hj
    have hval := congrArg ZMod.val hcast
    rw [ZMod.val_natCast] at hval
    exact hval

private def GoodRow : Finset (Fin 5 → Fin 2) :=
  Finset.univ.filter (fun r => rowVal r % 3 = 1)

private def Fv (v : Fin 5 → ZMod 3) : Eis :=
  ∑ r ∈ GoodRow, wPowZ (dot v (rowZ r))

private def Fconj (v : Fin 5 → ZMod 3) : Eis :=
  ∑ r ∈ GoodRow, wPowZ (- dot v (rowZ r))

private lemma prod_alt_odd (n : ℕ) (x y : Eis) :
    (∏ i : Fin (2 * n + 1), if i.val % 2 = 0 then x else y) = x * (x * y) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have h1 : (Fin.last (2 * n + 1 + 1)).val % 2 = 0 := by dsimp; omega
    have h2 : (Fin.last (2 * n + 1)).val % 2 = 1 := by dsimp; omega
    simp only [Fin.val_castSucc, h1, h2, ↓reduceIte, one_ne_zero]
    rw [ih, pow_succ]
    ring

private lemma fourier_formula (n : ℕ) :
    (243 : Eis) * (a n : Eis) =
      ∑ v : Fin 5 → ZMod 3, wPowZ (- ∑ j : Fin 5, v j) * Fv v * (Fv v * Fconj v) ^ n := by
  let AllGood : Finset (Fin (2 * n + 1) → Fin 5 → Fin 2) :=
    Fintype.piFinset (fun _ : Fin (2 * n + 1) => GoodRow)
  have ha_eq : a n = (AllGood.filter (fun A => colVec A = 0)).card := by
    unfold a
    congr 1
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, AllGood, Fintype.mem_piFinset,
      GoodRow, Valid, colVal_mod_three_iff]
  have hcard : (243 : Eis) * (a n : Eis) =
      ∑ A ∈ AllGood, if colVec A = 0 then (243 : Eis) else 0 := by
    rw [ha_eq, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      mul_comm]
  rw [hcard]
  have hsum_A : (∑ A ∈ AllGood, if colVec A = 0 then (243 : Eis) else 0) =
      ∑ A ∈ AllGood, ∑ v : Fin 5 → ZMod 3, wPowZ (dot v (colVec A)) := by
    refine Finset.sum_congr rfl fun A _ => (sum_wPowZ_dot (colVec A)).symm
  rw [hsum_A, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hdot : ∀ A : Fin (2 * n + 1) → Fin 5 → Fin 2,
      dot v (colVec A) =
        (- ∑ j : Fin 5, v j) + ∑ i : Fin (2 * n + 1), (-1 : ZMod 3) ^ i.val * dot v (rowZ (A i)) := by
    intro A
    calc dot v (colVec A)
        = (∑ j : Fin 5, v j * ∑ i : Fin (2 * n + 1), (-1 : ZMod 3) ^ i.val * ((A i j : ℕ) : ZMod 3)) -
            ∑ j : Fin 5, v j := by
            simp only [dot, colVec, mul_sub, mul_one, Finset.sum_sub_distrib]
      _ = (∑ i : Fin (2 * n + 1), (-1 : ZMod 3) ^ i.val * dot v (rowZ (A i))) - ∑ j : Fin 5, v j := by
            congr 1
            simp_rw [Finset.mul_sum, dot, rowZ, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = (- ∑ j : Fin 5, v j) + ∑ i : Fin (2 * n + 1), (-1 : ZMod 3) ^ i.val * dot v (rowZ (A i)) := by ring
  have hstep1 : (∑ A ∈ AllGood, wPowZ (dot v (colVec A))) =
      wPowZ (- ∑ j : Fin 5, v j) *
        ∑ A ∈ AllGood, ∏ i : Fin (2 * n + 1), wPowZ ((-1 : ZMod 3) ^ i.val * dot v (rowZ (A i))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [hdot A, wPowZ_add, wPowZ_sum]
  rw [hstep1]
  have hpi : (∑ A ∈ AllGood, ∏ i : Fin (2 * n + 1), wPowZ ((-1 : ZMod 3) ^ i.val * dot v (rowZ (A i)))) =
      ∏ i : Fin (2 * n + 1), ∑ r ∈ GoodRow, wPowZ ((-1 : ZMod 3) ^ i.val * dot v (rowZ r)) := by
    exact (Finset.prod_univ_sum (fun _ : Fin (2 * n + 1) => GoodRow)
      (fun i r => wPowZ ((-1 : ZMod 3) ^ i.val * dot v (rowZ r)))).symm
  rw [hpi]
  have hfac : ∀ i : Fin (2 * n + 1),
      (∑ r ∈ GoodRow, wPowZ ((-1 : ZMod 3) ^ i.val * dot v (rowZ r))) =
        if i.val % 2 = 0 then Fv v else Fconj v := by
    intro i
    split_ifs with heven
    · have h1 : (-1 : ZMod 3) ^ i.val = 1 := Even.neg_one_pow (Nat.even_iff.mpr heven)
      simp only [h1, one_mul, Fv]
    · have h1 : (-1 : ZMod 3) ^ i.val = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
      simp only [h1, neg_one_mul, Fconj]
  rw [Finset.prod_congr rfl fun i _ => hfac i, prod_alt_odd n (Fv v) (Fconj v), mul_assoc]

private def dec3 (k : ℕ) : Fin 5 → ZMod 3 :=
  fun j => (((k / 3 ^ j.val) % 3 : ℕ) : ZMod 3)

private def enc3 (v : Fin 5 → ZMod 3) : ℕ :=
  (v 0).val + 3 * (v 1).val + 9 * (v 2).val + 27 * (v 3).val + 81 * (v 4).val

private def e3 : Fin 243 ≃ (Fin 5 → ZMod 3) where
  toFun k := dec3 k.val
  invFun v := ⟨enc3 v, by
    have h0 := (v 0).val_lt
    have h1 := (v 1).val_lt
    have h2 := (v 2).val_lt
    have h3 := (v 3).val_lt
    have h4 := (v 4).val_lt
    dsimp [enc3]
    omega⟩
  left_inv k := by
    ext
    dsimp [enc3, dec3]
    simp only [ZMod.val_natCast]
    have hk := k.isLt
    omega
  right_inv v := by
    ext j
    dsimp [enc3, dec3]
    have h0 := (v 0).val_lt
    have h1 := (v 1).val_lt
    have h2 := (v 2).val_lt
    have h3 := (v 3).val_lt
    have h4 := (v 4).val_lt
    fin_cases j
    · change (((enc3 v / 1) % 3 : ℕ) : ZMod 3) = v 0
      rw [show (enc3 v / 1) % 3 = (v 0).val by dsimp [enc3]; omega, ZMod.natCast_zmod_val]
    · change (((enc3 v / 3) % 3 : ℕ) : ZMod 3) = v 1
      rw [show (enc3 v / 3) % 3 = (v 1).val by dsimp [enc3]; omega, ZMod.natCast_zmod_val]
    · change (((enc3 v / 9) % 3 : ℕ) : ZMod 3) = v 2
      rw [show (enc3 v / 9) % 3 = (v 2).val by dsimp [enc3]; omega, ZMod.natCast_zmod_val]
    · change (((enc3 v / 27) % 3 : ℕ) : ZMod 3) = v 3
      rw [show (enc3 v / 27) % 3 = (v 3).val by dsimp [enc3]; omega, ZMod.natCast_zmod_val]
    · change (((enc3 v / 81) % 3 : ℕ) : ZMod 3) = v 4
      rw [show (enc3 v / 81) % 3 = (v 4).val by dsimp [enc3]; omega, ZMod.natCast_zmod_val]

private def dec2 (k : ℕ) : Fin 5 → Fin 2 :=
  fun j => ⟨(k / 2 ^ j.val) % 2, Nat.mod_lt _ (by decide)⟩

private def enc2 (r : Fin 5 → Fin 2) : ℕ :=
  (r 0).val + 2 * (r 1).val + 4 * (r 2).val + 8 * (r 3).val + 16 * (r 4).val

private def e2 : Fin 32 ≃ (Fin 5 → Fin 2) where
  toFun k := dec2 k.val
  invFun r := ⟨enc2 r, by
    have h0 := (r 0).isLt
    have h1 := (r 1).isLt
    have h2 := (r 2).isLt
    have h3 := (r 3).isLt
    have h4 := (r 4).isLt
    dsimp [enc2]
    omega⟩
  left_inv k := by
    ext
    dsimp [enc2, dec2]
    have hk := k.isLt
    omega
  right_inv r := by
    ext j
    dsimp [enc2, dec2]
    have h0 := (r 0).isLt
    have h1 := (r 1).isLt
    have h2 := (r 2).isLt
    have h3 := (r 3).isLt
    have h4 := (r 4).isLt
    fin_cases j <;> simp <;> omega

private def natRowVal (r : ℕ) : ℕ :=
  (r % 2) * 16 + ((r / 2) % 2) * 8 + ((r / 4) % 2) * 4 + ((r / 8) % 2) * 2 + ((r / 16) % 2) * 1

private lemma rowVal_dec2 (r : ℕ) : rowVal (dec2 r) = natRowVal r := by
  simp [rowVal, dec2, natRowVal, Fin.sum_univ_five]

private def natDot (v r : ℕ) : ℕ :=
  (v % 3) * (r % 2) + ((v / 3) % 3) * ((r / 2) % 2) +
  ((v / 9) % 3) * ((r / 4) % 2) + ((v / 27) % 3) * ((r / 8) % 2) +
  ((v / 81) % 3) * ((r / 16) % 2)

private lemma dot_dec3_dec2 (v r : ℕ) :
    dot (dec3 v) (rowZ (dec2 r)) = (natDot v r : ZMod 3) := by
  simp [dot, dec3, rowZ, dec2, natDot, Fin.sum_univ_five]

private def natSumV (v : ℕ) : ℕ :=
  (v % 3) + ((v / 3) % 3) + ((v / 9) % 3) + ((v / 27) % 3) + ((v / 81) % 3)

private lemma sum_dec3 (v : ℕ) : (∑ j : Fin 5, dec3 v j) = (natSumV v : ZMod 3) := by
  simp [dec3, natSumV, Fin.sum_univ_five]

private lemma wPowZ_natCast (k : ℕ) : wPowZ (k : ZMod 3) = wPow k := by
  simp [wPowZ, wPow]

private lemma wPowZ_neg_natCast (k : ℕ) : wPowZ (-(k : ZMod 3)) = wPow (2 * k) := by
  have hneg : (-(k : ZMod 3)) = ((2 * k : ℕ) : ZMod 3) := by
    push_cast
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2]
    ring
  rw [hneg, wPowZ_natCast]

private def eisListSum : List Eis → Eis
  | [] => 0
  | a :: t => a + eisListSum t

private lemma eisListSum_eq_sum : ∀ l : List Eis, eisListSum l = l.sum
  | [] => rfl
  | a :: t => by simp [eisListSum, eisListSum_eq_sum t]

private lemma finset_sum_range_eq_eisListSum (n : ℕ) (f : ℕ → Eis) :
    (∑ i ∈ Finset.range n, f i) = eisListSum ((List.range n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, eisListSum_eq_sum,
      List.sum_append, ← eisListSum_eq_sum, ih]
    simp

private lemma eisListSum_filter_eq (L : List ℕ) (p : ℕ → Bool) (f : ℕ → Eis) :
    eisListSum ((L.filter p).map f) =
      eisListSum (L.map (fun x => if p x then f x else 0)) := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    cases hp : p a <;> simp [eisListSum, hp, ih]

private def goodRowIdxs : List ℕ :=
  (List.range 32).filter (fun r => decide (natRowVal r % 3 = 1))

private def natF (v : ℕ) : Eis :=
  eisListSum (goodRowIdxs.map (fun r => wPow (natDot v r)))

private def natFconj (v : ℕ) : Eis :=
  eisListSum (goodRowIdxs.map (fun r => wPow (2 * natDot v r)))

private def natWt (v : ℕ) : Eis :=
  wPow (2 * natSumV v) * natF v

private def natNorm (v : ℕ) : ℤ :=
  (natF v * natFconj v).re

private lemma Fv_dec3 (v : ℕ) : Fv (dec3 v) = natF v := by
  unfold Fv GoodRow
  rw [Finset.sum_filter]
  rw [← Fintype.sum_equiv e2 (fun k => if rowVal (dec2 k.val) % 3 = 1 then wPowZ (dot (dec3 v) (rowZ (dec2 k.val))) else 0)
    (fun r => if rowVal r % 3 = 1 then wPowZ (dot (dec3 v) (rowZ r)) else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range (fun k => if rowVal (dec2 k) % 3 = 1 then wPowZ (dot (dec3 v) (rowZ (dec2 k))) else 0) 32]
  rw [finset_sum_range_eq_eisListSum, natF, goodRowIdxs, eisListSum_filter_eq]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [rowVal_dec2, dot_dec3_dec2, wPowZ_natCast]
  by_cases h : natRowVal r % 3 = 1 <;> simp [h]

private lemma Fconj_dec3 (v : ℕ) : Fconj (dec3 v) = natFconj v := by
  unfold Fconj GoodRow
  rw [Finset.sum_filter]
  rw [← Fintype.sum_equiv e2 (fun k => if rowVal (dec2 k.val) % 3 = 1 then wPowZ (- dot (dec3 v) (rowZ (dec2 k.val))) else 0)
    (fun r => if rowVal r % 3 = 1 then wPowZ (- dot (dec3 v) (rowZ r)) else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range (fun k => if rowVal (dec2 k) % 3 = 1 then wPowZ (- dot (dec3 v) (rowZ (dec2 k))) else 0) 32]
  rw [finset_sum_range_eq_eisListSum, natFconj, goodRowIdxs, eisListSum_filter_eq]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [rowVal_dec2, dot_dec3_dec2, wPowZ_neg_natCast]
  by_cases h : natRowVal r % 3 = 1 <;> simp [h]

private def checkBases : Bool :=
  (List.range 243).all (fun v =>
    decide (natF v * natFconj v = ((natNorm v : ℤ) : Eis)) &&
    (decide (natNorm v = 4) || decide (natNorm v = 13) || decide (natNorm v = 31) || decide (natNorm v = 121)))

private theorem checkBases_ok : checkBases = true := by decide +kernel

private theorem sum_wt_4 :
    eisListSum (((List.range 243).filter (fun v => decide (natNorm v = 4))).map natWt) = (30 : Eis) := by
  decide +kernel

private theorem sum_wt_13 :
    eisListSum (((List.range 243).filter (fun v => decide (natNorm v = 13))).map natWt) = (93 : Eis) := by
  decide +kernel

private theorem sum_wt_31 :
    eisListSum (((List.range 243).filter (fun v => decide (natNorm v = 31))).map natWt) = (87 : Eis) := by
  decide +kernel

private theorem sum_wt_121 :
    eisListSum (((List.range 243).filter (fun v => decide (natNorm v = 121))).map natWt) = (33 : Eis) := by
  decide +kernel

private lemma eisListSum_split4 (L : List ℕ) (n : ℕ)
    (hL : ∀ v ∈ L,
      natF v * natFconj v = ((natNorm v : ℤ) : Eis) ∧
      (natNorm v = 4 ∨ natNorm v = 13 ∨ natNorm v = 31 ∨ natNorm v = 121)) :
    eisListSum (L.map (fun v => natWt v * (natF v * natFconj v) ^ n)) =
      eisListSum ((L.filter (fun v => decide (natNorm v = 4))).map natWt) * (4 : Eis) ^ n +
      eisListSum ((L.filter (fun v => decide (natNorm v = 13))).map natWt) * (13 : Eis) ^ n +
      eisListSum ((L.filter (fun v => decide (natNorm v = 31))).map natWt) * (31 : Eis) ^ n +
      eisListSum ((L.filter (fun v => decide (natNorm v = 121))).map natWt) * (121 : Eis) ^ n := by
  induction L with
  | nil => simp [eisListSum]
  | cons v t ih =>
    have hv := hL v (by simp)
    have ht := ih (fun x hx => hL x (by simp [hx]))
    simp only [List.map_cons, eisListSum, List.filter_cons]
    rw [hv.1, ht]
    rcases hv.2 with h | h | h | h <;> simp [h, eisListSum] <;> ring

private lemma closed_form_all (n : ℕ) :
    81 * (a n : ℤ) = 10 * 4 ^ n + 31 * 13 ^ n + 29 * 31 ^ n + 11 * 121 ^ n := by
  have hfourier := fourier_formula n
  rw [← Fintype.sum_equiv e3
    (fun k => wPowZ (- ∑ j : Fin 5, e3 k j) * Fv (e3 k) * (Fv (e3 k) * Fconj (e3 k)) ^ n)
    (fun v => wPowZ (- ∑ j : Fin 5, v j) * Fv v * (Fv v * Fconj v) ^ n) (fun _ => rfl)] at hfourier
  dsimp [e3] at hfourier
  rw [Fin.sum_univ_eq_sum_range (fun k => wPowZ (- ∑ j : Fin 5, dec3 k j) * Fv (dec3 k) * (Fv (dec3 k) * Fconj (dec3 k)) ^ n) 243,
    finset_sum_range_eq_eisListSum] at hfourier
  have hmap : ((List.range 243).map (fun k => wPowZ (- ∑ j : Fin 5, dec3 k j) * Fv (dec3 k) * (Fv (dec3 k) * Fconj (dec3 k)) ^ n)) =
      (List.range 243).map (fun k => natWt k * (natF k * natFconj k) ^ n) := by
    apply List.map_congr_left
    intro k _
    rw [sum_dec3, wPowZ_neg_natCast, Fv_dec3, Fconj_dec3, natWt]
  rw [hmap] at hfourier
  have hbases : ∀ v ∈ List.range 243,
      natF v * natFconj v = ((natNorm v : ℤ) : Eis) ∧
      (natNorm v = 4 ∨ natNorm v = 13 ∨ natNorm v = 31 ∨ natNorm v = 121) := by
    have hc := checkBases_ok
    unfold checkBases at hc
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    intro v hv
    rcases hc v hv with ⟨h1, ((h4 | h13) | h31) | h121⟩
    · exact ⟨h1, Or.inl h4⟩
    · exact ⟨h1, Or.inr (Or.inl h13)⟩
    · exact ⟨h1, Or.inr (Or.inr (Or.inl h31))⟩
    · exact ⟨h1, Or.inr (Or.inr (Or.inr h121))⟩
  rw [eisListSum_split4 (List.range 243) n hbases, sum_wt_4, sum_wt_13, sum_wt_31, sum_wt_121] at hfourier
  have hre := congrArg Eis.re hfourier
  have hpow_re : ∀ (c : ℤ) (k : ℕ), ((c : Eis) ^ k) = ((c ^ k : ℤ) : Eis) := by
    intro c k
    exact (Int.cast_pow c k).symm
  have hcast : ∀ (u c : ℤ) (k : ℕ), ((u : Eis) * (c : Eis) ^ k).re = u * c ^ k := by
    intro u c k
    rw [hpow_re, ← Int.cast_mul, eis_intCast_re]
  have hlhs : ((243 : Eis) * (a n : Eis)).re = 243 * (a n : ℤ) := by
    have : (243 : Eis) * (a n : Eis) = (((243 * (a n : ℤ)) : ℤ) : Eis) := by push_cast; rfl
    rw [this, eis_intCast_re]
  rw [hlhs, eis_add_re, eis_add_re, eis_add_re] at hre
  have ht1 : ((30 : Eis) * (4 : Eis) ^ n).re = 30 * 4 ^ n := by simpa using hcast 30 4 n
  have ht2 : ((93 : Eis) * (13 : Eis) ^ n).re = 93 * 13 ^ n := by simpa using hcast 93 13 n
  have ht3 : ((87 : Eis) * (31 : Eis) ^ n).re = 87 * 31 ^ n := by simpa using hcast 87 31 n
  have ht4 : ((33 : Eis) * (121 : Eis) ^ n).re = 33 * 121 ^ n := by simpa using hcast 33 121 n
  rw [ht1, ht2, ht3, ht4] at hre
  omega

private lemma closed_form (n : ℕ) (_ : 1 ≤ n) :
    81 * (a n : ℤ) = 5 * 2 ^ (1 + 2 * n) + 11 ^ (1 + 2 * n) + 31 * 13 ^ n + 29 * 31 ^ n := by
  have h := closed_form_all n
  have h2 : (5 : ℤ) * 2 ^ (1 + 2 * n) = 10 * 4 ^ n := by
    rw [pow_add, pow_one, pow_mul]
    ring
  have h11 : (11 : ℤ) ^ (1 + 2 * n) = 11 * 121 ^ n := by
    rw [pow_add, pow_one, pow_mul]
    norm_num
  linarith

private lemma a_recurrence (k : ℕ) :
    (a (k + 5) : ℤ) - 169 * a (k + 4) + 6387 * a (k + 3) - 71671 * a (k + 2) + 195052 * a (k + 1) = 0 := by
  have h5 := closed_form_all (k + 5)
  have h4 := closed_form_all (k + 4)
  have h3 := closed_form_all (k + 3)
  have h2 := closed_form_all (k + 2)
  have h1 := closed_form_all (k + 1)
  have h81 : 81 * ((a (k + 5) : ℤ) - 169 * a (k + 4) + 6387 * a (k + 3) -
      71671 * a (k + 2) + 195052 * a (k + 1)) = 0 := by
    have hpow : ∀ b : ℤ,
        b ^ (k + 5) = b ^ 4 * b ^ (k + 1) ∧
        b ^ (k + 4) = b ^ 3 * b ^ (k + 1) ∧
        b ^ (k + 3) = b ^ 2 * b ^ (k + 1) ∧
        b ^ (k + 2) = b * b ^ (k + 1) := by
      intro b
      refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
    have p4 := hpow 4
    have p13 := hpow 13
    have p31 := hpow 31
    have p121 := hpow 121
    linarith
  omega

private lemma gf_eq :
    (1 - 4 * X) * (1 - 13 * X) * (1 - 31 * X) * (1 - 121 * X) *
        PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (33 - 3178 * X + 57437 * X ^ 2 - 195052 * X ^ 3) : PowerSeries ℤ) := by
  let A : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ))
  have hL : (1 - 4 * X) * (1 - 13 * X) * (1 - 31 * X) * (1 - 121 * X) * A =
      A - C 169 * (X ^ 1 * A) + C 6387 * (X ^ 2 * A) - C 71671 * (X ^ 3 * A) + C 195052 * (X ^ 4 * A) := by
    simp only [map_ofNat]
    ring
  have hR : (X * (33 - 3178 * X + 57437 * X ^ 2 - 195052 * X ^ 3) : PowerSeries ℤ) =
      C 33 * X ^ 1 - C 3178 * X ^ 2 + C 57437 * X ^ 3 - C 195052 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  change (1 - 4 * X) * (1 - 13 * X) * (1 - 31 * X) * (1 - 121 * X) * A = _
  rw [hL, hR]
  have ha1 : (a 1 : ℤ) = 33 := by have := closed_form_all 1; omega
  have ha2 : (a 2 : ℤ) = 2399 := by have := closed_form_all 2; omega
  have ha3 : (a 3 : ℤ) = 252097 := by have := closed_form_all 3; omega
  have ha4 : (a 4 : ℤ) = 29452071 := by have := closed_form_all 4; omega
  have hA0 : PowerSeries.coeff 0 A = 0 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_pos rfl]
  have hA1 : PowerSeries.coeff 1 A = 33 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha1
  have hA2 : PowerSeries.coeff 2 A = 2399 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha2
  have hA3 : PowerSeries.coeff 3 A = 252097 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha3
  have hA4 : PowerSeries.coeff 4 A = 29452071 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha4
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow]
  rcases k with _ | _ | _ | _ | _ | k
  · simp only [show ¬ (1 ≤ 0) by decide, show ¬ (2 ≤ 0) by decide, show ¬ (3 ≤ 0) by decide,
      show ¬ (4 ≤ 0) by decide, show ¬ (0 = 1) by decide, show ¬ (0 = 2) by decide,
      show ¬ (0 = 3) by decide, show ¬ (0 = 4) by decide, ↓reduceIte, hA0]; norm_num
  · simp only [show (1 ≤ 1) by decide, show ¬ (2 ≤ 1) by decide, show ¬ (3 ≤ 1) by decide,
      show ¬ (4 ≤ 1) by decide, show (1 = 1) by decide, show ¬ (1 = 2) by decide,
      show ¬ (1 = 3) by decide, show ¬ (1 = 4) by decide, show 1 - 1 = 0 by decide,
      ↓reduceIte, hA0, hA1]; norm_num
  · simp only [show (1 ≤ 2) by decide, show (2 ≤ 2) by decide, show ¬ (3 ≤ 2) by decide,
      show ¬ (4 ≤ 2) by decide, show ¬ (2 = 1) by decide, show (2 = 2) by decide,
      show ¬ (2 = 3) by decide, show ¬ (2 = 4) by decide, show 2 - 1 = 1 by decide,
      show 2 - 2 = 0 by decide, ↓reduceIte, hA0, hA1, hA2]; norm_num
  · simp only [show (1 ≤ 3) by decide, show (2 ≤ 3) by decide, show (3 ≤ 3) by decide,
      show ¬ (4 ≤ 3) by decide, show ¬ (3 = 1) by decide, show ¬ (3 = 2) by decide,
      show (3 = 3) by decide, show ¬ (3 = 4) by decide, show 3 - 1 = 2 by decide,
      show 3 - 2 = 1 by decide, show 3 - 3 = 0 by decide, ↓reduceIte, hA0, hA1, hA2, hA3]; norm_num
  · simp only [show (1 ≤ 4) by decide, show (2 ≤ 4) by decide, show (3 ≤ 4) by decide,
      show (4 ≤ 4) by decide, show ¬ (4 = 1) by decide, show ¬ (4 = 2) by decide,
      show ¬ (4 = 3) by decide, show (4 = 4) by decide, show 4 - 1 = 3 by decide,
      show 4 - 2 = 2 by decide, show 4 - 3 = 1 by decide, show 4 - 4 = 0 by decide,
      ↓reduceIte, hA0, hA1, hA2, hA3, hA4]; norm_num
  · have hk5 : k + 1 + 1 + 1 + 1 + 1 = k + 5 := by omega
    rw [hk5]
    simp only [A, PowerSeries.coeff_mk,
      show ¬ (k + 5 = 0) by omega, show ¬ (k + 5 = 1) by omega, show ¬ (k + 5 = 2) by omega,
      show ¬ (k + 5 = 3) by omega, show ¬ (k + 5 = 4) by omega,
      show 1 ≤ k + 5 by omega, show 2 ≤ k + 5 by omega, show 3 ≤ k + 5 by omega, show 4 ≤ k + 5 by omega,
      show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
      show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega,
      show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega,
      ↓reduceIte, mul_zero, sub_zero, add_zero]
    exact a_recurrence k

end OMA.ProofA263908

theorem OMA.solution : type_of% @OMA.S_oeis_a263908.main :=
  ⟨OMA.ProofA263908.gf_eq, OMA.ProofA263908.closed_form⟩

