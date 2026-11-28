import OMAStatements.S_oeis_a126504
import Mathlib

namespace OMA.Band126504
open OMA.S_oeis_a126504 Finset PowerSeries

private abbrev Digit := Fin 9
private abbrev Word (n : ℕ) := Fin n → Digit

private def walk (n : ℕ) (p : Digit) (x : Word n) :=
  ∀ i : Fin n, adjOk ((Fin.cons p x : Word (n+1)) i.castSucc) (x i)
private instance (n : ℕ) (p : Digit) (x : Word n) : Decidable (walk n p x) := by
  unfold walk; infer_instance
private abbrev W (n : ℕ) (p : Digit) := {x : Word n // walk n p x}
private abbrev Near (p : Digit) := {d : Digit // adjOk p d}

private theorem consWalk (n : ℕ) (p d : Digit) (x : Word n) :
    walk (n+1) p (Fin.cons d x) ↔ adjOk p d ∧ walk n d x := by
  simp only [walk,Fin.forall_fin_succ]
  rfl

private def split (n : ℕ) (p : Digit) : W (n+1) p ≃ (Σ d : Near p, W n d.val) where
  toFun z :=
    let x := z.val
    let t := fun i : Fin n => x i.succ
    have h : adjOk p (x 0) ∧ walk n (x 0) t :=
      (consWalk n p (x 0) t).mp (by rw [show Fin.cons (x 0) t = x from Fin.cons_self_tail x]; exact z.property)
    ⟨⟨x 0,h.1⟩,⟨t,h.2⟩⟩
  invFun z := ⟨Fin.cons z.1.val z.2.val,(consWalk n p _ _).mpr ⟨z.1.property,z.2.property⟩⟩
  left_inv z := Subtype.ext (Fin.cons_self_tail _)
  right_inv z := by rcases z with ⟨⟨d,hd⟩,⟨x,hx⟩⟩; rfl

private def op (f : Digit → ℤ) (p : Digit) := ∑ d : Near p, f d.val
private def c : ℕ → Digit → ℤ
  | 0, _ => 1
  | n+1, p => op (c n) p

private theorem paths (n : ℕ) (p : Digit) : (Fintype.card (W n p) : ℤ) = c n p := by
  induction n generalizing p with
  | zero =>
    have : Unique (W 0 p) :=
      { default := ⟨Fin.elim0,fun i => i.elim0⟩
        uniq := fun z => Subtype.ext (funext fun i => i.elim0) }
    simp [c]
  | succ n ih =>
    rw [Fintype.card_congr (split n p),Fintype.card_sigma,Nat.cast_sum]
    apply Fintype.sum_congr
    intro d
    exact ih d.val

private abbrev allGood {n : ℕ} (x : Word n) := isValid n x

private theorem start (n : ℕ) (x : Word (n+1)) :
    allGood x ↔ walk n (x 0) (fun i => x i.succ) := by
  unfold walk
  rw [show (Fin.cons (x 0) (fun i => x i.succ) : Word (n+1))=x from Fin.cons_self_tail x]
  rfl

private def splitFirst (n : ℕ) : {x : Word (n+1) // allGood x} ≃ (Σ d : Digit, W n d) where
  toFun z := ⟨z.val 0,⟨fun i => z.val i.succ,(start n z.val).mp z.property⟩⟩
  invFun z := ⟨Fin.cons z.1 z.2.val,(start n _).mpr z.2.property⟩
  left_inv z := Subtype.ext (Fin.cons_self_tail _)
  right_inv z := by rcases z with ⟨d,⟨x,hx⟩⟩; rfl

private theorem count (n : ℕ) : (a (n+1) : ℤ) = ∑ d, c n d := by
  have h := Fintype.card_congr (splitFirst n)
  rw [Fintype.card_subtype,Fintype.card_sigma] at h
  change (#{x : Word (n+1) | allGood x} : ℤ) = _
  rw [h,Nat.cast_sum]
  apply Fintype.sum_congr
  exact paths n

private theorem emptyCount : a 0 = 1 := by decide +kernel

private def table : Fin 6 → Digit → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![5, 6, 7, 8, 9, 8, 7, 6, 5],
    ![35, 43, 50, 56, 61, 56, 50, 43, 35],
    ![245, 301, 351, 394, 429, 394, 351, 301, 245],
    ![1720, 2114, 2465, 2766, 3011, 2766, 2465, 2114, 1720],
    ![12076, 14842, 17307, 19421, 21141, 19421, 17307, 14842, 12076]]

private theorem checkStep : ∀ k : Fin 5, ∀ p : Digit, table k.succ p = op (table k.castSucc) p := by decide +kernel

private theorem table_eq (k : Fin 6) : c k.val = table k := by
  induction k using Fin.induction with
  | zero => funext p; fin_cases p <;> rfl
  | succ k ih =>
    funext p
    change op (c k.val) p = _
    change c k.val = table k.castSucc at ih
    rw [ih,checkStep]

private theorem vectorRec (n : ℕ) (p : Digit) : c (n+5) p = 7 * c (n+4) p + c (n+3) p - 6 * c (n+2) p + c n p := by
  induction n generalizing p with
  | zero =>
    simp only [Nat.zero_add,show c 5 = table 5 from table_eq 5, show c 4 = table 4 from table_eq 4, show c 3 = table 3 from table_eq 3, show c 2 = table 2 from table_eq 2, show c 0 = table 0 from table_eq 0]
    revert p
    decide +kernel
  | succ n ih =>
    change op (c (n+5)) p = 7 * op (c (n+4)) p + op (c (n+3)) p - 6 * op (c (n+2)) p + op (c n) p
    unfold op
    simp_rw [ih]
    simp only [sum_add_distrib,sum_sub_distrib,← mul_sum]

private theorem initial : ∀ k : Fin 6, ∑ p, table k p = ![9, 61, 429, 3011, 21141, 148433] k := by decide +kernel

private theorem term1 : (a 1 : ℤ) = 9 :=
  (count 0).trans (by rw [show c 0 = table 0 from table_eq 0]; exact initial 0)

private theorem term2 : (a 2 : ℤ) = 61 :=
  (count 1).trans (by rw [show c 1 = table 1 from table_eq 1]; exact initial 1)

private theorem term3 : (a 3 : ℤ) = 429 :=
  (count 2).trans (by rw [show c 2 = table 2 from table_eq 2]; exact initial 2)

private theorem term4 : (a 4 : ℤ) = 3011 :=
  (count 3).trans (by rw [show c 3 = table 3 from table_eq 3]; exact initial 3)

private theorem term5 : (a 5 : ℤ) = 21141 :=
  (count 4).trans (by rw [show c 4 = table 4 from table_eq 4]; exact initial 4)

private theorem recurrence : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 7 * a (n - 1) + a (n - 2) - 6 * a (n - 3) + a (n - 5) := by
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m, n=m+6 := ⟨n-6,by omega⟩
  have h := Finset.sum_congr (s₁:=(univ : Finset Digit)) rfl (fun p _ => vectorRec m p)
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum] at h
  simp only [show m+6-1 = (m+4)+1 by omega, show m+6-2 = (m+3)+1 by omega, show m+6-3 = (m+2)+1 by omega, show m+6-5 = (m+0)+1 by omega,show m+6 = (m+5)+1 by omega,count,Nat.add_zero]
  simpa only [Nat.add_zero] using h

private theorem generating :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X - X ^ 2 + 6 * X ^ 3 - X ^ 5) =
      (1 - X) * (1 + 3 * X - X ^ 3) := by
  let S := mk (fun n => (a n : ℚ))
  change S * _ = _
  have lhs : S*(1 - 7 * X - X ^ 2 + 6 * X ^ 3 - X ^ 5) = S - (7:ℕ) • (S*X^1) - (S*X^2) + (6:ℕ) • (S*X^3) - (S*X^5) := by simp only [nsmul_eq_mul]; ring
  have rhs : ((1 - X) * (1 + 3 * X - X ^ 3) : PowerSeries ℚ) = X^0 + (2:ℕ) • X^1 - (3:ℕ) • X^2 - X^3 + X^4 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 5<n
  · have recn : (a n : ℚ) = 7 * a (n-1) + a (n-2) - 6 * a (n-3) + a (n-5) := by exact_mod_cast recurrence n (by omega)
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega)]
    norm_num <;> linarith only [recn]
  · interval_cases n <;> norm_num [emptyCount,show a 1 = 9 by exact_mod_cast term1, show a 2 = 61 by exact_mod_cast term2, show a 3 = 429 by exact_mod_cast term3, show a 4 = 3011 by exact_mod_cast term4, show a 5 = 21141 by exact_mod_cast term5]

theorem result : type_of% @OMA.S_oeis_a126504.main := ⟨generating,recurrence⟩

end OMA.Band126504

theorem OMA.solution : type_of% @OMA.S_oeis_a126504.main := OMA.Band126504.result
