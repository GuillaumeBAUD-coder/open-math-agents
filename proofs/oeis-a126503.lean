import OMAStatements.S_oeis_a126503
import Mathlib

namespace OMA.Band126503
open OMA.S_oeis_a126503 Finset PowerSeries

private abbrev Digit := Fin 8
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

private def table : Fin 5 → Digit → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1],
    ![5, 6, 7, 8, 8, 7, 6, 5],
    ![34, 41, 47, 52, 52, 47, 41, 34],
    ![226, 273, 314, 348, 348, 314, 273, 226],
    ![1509, 1823, 2096, 2322, 2322, 2096, 1823, 1509]]

private theorem checkStep : ∀ k : Fin 4, ∀ p : Digit, table k.succ p = op (table k.castSucc) p := by decide +kernel

private theorem table_eq (k : Fin 5) : c k.val = table k := by
  induction k using Fin.induction with
  | zero => funext p; fin_cases p <;> rfl
  | succ k ih =>
    funext p
    change op (c k.val) p = _
    change c k.val = table k.castSucc at ih
    rw [ih,checkStep]

private theorem vectorRec (n : ℕ) (p : Digit) : c (n+4) p = 6 * c (n+3) p + 5 * c (n+2) p - 3 * c (n+1) p - 2 * c n p := by
  induction n generalizing p with
  | zero =>
    simp only [Nat.zero_add,show c 4 = table 4 from table_eq 4, show c 3 = table 3 from table_eq 3, show c 2 = table 2 from table_eq 2, show c 1 = table 1 from table_eq 1, show c 0 = table 0 from table_eq 0]
    revert p
    decide +kernel
  | succ n ih =>
    change op (c (n+4)) p = 6 * op (c (n+3)) p + 5 * op (c (n+2)) p - 3 * op (c (n+1)) p - 2 * op (c n) p
    unfold op
    simp_rw [ih]
    simp only [sum_add_distrib,sum_sub_distrib,← mul_sum]

private theorem initial : ∀ k : Fin 5, ∑ p, table k p = ![8, 52, 348, 2322, 15500] k := by decide +kernel

private theorem term1 : (a 1 : ℤ) = 8 :=
  (count 0).trans (by rw [show c 0 = table 0 from table_eq 0]; exact initial 0)

private theorem term2 : (a 2 : ℤ) = 52 :=
  (count 1).trans (by rw [show c 1 = table 1 from table_eq 1]; exact initial 1)

private theorem term3 : (a 3 : ℤ) = 348 :=
  (count 2).trans (by rw [show c 2 = table 2 from table_eq 2]; exact initial 2)

private theorem term4 : (a 4 : ℤ) = 2322 :=
  (count 3).trans (by rw [show c 3 = table 3 from table_eq 3]; exact initial 3)

private theorem recurrence : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) + 5 * a (n - 2) - 3 * a (n - 3) - 2 * a (n - 4) := by
  intro n hn
  by_cases h : n = 4
  · subst n
    norm_num [emptyCount,show a 1 = 8 by exact_mod_cast term1, show a 2 = 52 by exact_mod_cast term2, show a 3 = 348 by exact_mod_cast term3, show a 4 = 2322 by exact_mod_cast term4]
  obtain ⟨m,rfl⟩ : ∃ m, n=m+5 := ⟨n-5,by omega⟩
  have h := Finset.sum_congr (s₁:=(univ : Finset Digit)) rfl (fun p _ => vectorRec m p)
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum] at h
  simp only [show m+5-1 = (m+3)+1 by omega, show m+5-2 = (m+2)+1 by omega, show m+5-3 = (m+1)+1 by omega, show m+5-4 = (m+0)+1 by omega,show m+5 = (m+4)+1 by omega,count,Nat.add_zero]
  simpa only [Nat.add_zero] using h

private theorem generating :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X - 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4) =
      1 + 2 * X - X ^ 2 - X ^ 3 := by
  let S := mk (fun n => (a n : ℚ))
  change S * _ = _
  have lhs : S*(1 - 6 * X - 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4) = S - (6:ℕ) • (S*X^1) - (5:ℕ) • (S*X^2) + (3:ℕ) • (S*X^3) + (2:ℕ) • (S*X^4) := by simp only [nsmul_eq_mul]; ring
  have rhs : (1 + 2 * X - X ^ 2 - X ^ 3 : PowerSeries ℚ) = X^0 + (2:ℕ) • X^1 - X^2 - X^3 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 4<n
  · have recn : (a n : ℚ) = 6 * a (n-1) + 5 * a (n-2) - 3 * a (n-3) - 2 * a (n-4) := by exact_mod_cast recurrence n (by omega)
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega)]
    norm_num <;> linarith only [recn]
  · interval_cases n <;> norm_num [emptyCount,show a 1 = 8 by exact_mod_cast term1, show a 2 = 52 by exact_mod_cast term2, show a 3 = 348 by exact_mod_cast term3, show a 4 = 2322 by exact_mod_cast term4]

theorem result : type_of% @OMA.S_oeis_a126503.main := ⟨generating,recurrence⟩

end OMA.Band126503

theorem OMA.solution : type_of% @OMA.S_oeis_a126503.main := OMA.Band126503.result
