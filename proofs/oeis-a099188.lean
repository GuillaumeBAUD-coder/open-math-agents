import OMAStatements.S_oeis_a099188
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Convert

/- Wilson's conjecture in OEIS A099188. Earlier full-cone proof by Liungang:
https://github.com/lefttosolve2/open-math-agents/pull/31095
This proof uses a positive Pell transform and two diagonal seeds. -/

open OMA.S_oeis_a099188

namespace Wilson

private lemma parity_square (a : ℤ) : a ^ 2 % 2 = a % 2 := by
  have h : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases h with h | h <;> rw [pow_two, Int.mul_emod, h] <;> decide

private lemma lower_data {x y t : ℤ} (p : Path x y t) :
    (x : ℝ) + (y : ℝ) ≤ Real.sqrt 2 * (t : ℝ) ∧ (t - x - y) % 2 = 0 := by
  induction p with
  | zero => simp
  | edge x y t ht he =>
      constructor
      · have ht' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
        have he' : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = (t : ℝ) ^ 2 := by
          exact_mod_cast he
        have hr : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
        have hright : 0 ≤ Real.sqrt 2 * (t : ℝ) :=
          mul_nonneg (Real.sqrt_nonneg _) ht'
        by_contra! h
        have hsum : 0 < (x : ℝ) + (y : ℝ) + Real.sqrt 2 * (t : ℝ) := by
          linarith
        have hprod := mul_pos (sub_pos.mpr h) hsum
        have hr' : (Real.sqrt 2 * (t : ℝ)) ^ 2 = 2 * (t : ℝ) ^ 2 := by
          rw [mul_pow, hr]
        nlinarith [sq_nonneg ((x : ℝ) - (y : ℝ))]
      · have h := congrArg (fun a : ℤ => a % 2) he
        change (x ^ 2 + y ^ 2) % 2 = t ^ 2 % 2 at h
        rw [Int.add_emod, parity_square, parity_square, parity_square] at h
        omega
  | join p q hp hq =>
      constructor
      · push_cast
        nlinarith [hp.1, hq.1]
      · omega

private inductive PositivePath : ℤ → ℤ → ℤ → Prop
  | empty : PositivePath 0 0 0
  | edge (x y t : ℤ) : 0 ≤ x → 0 ≤ y → 0 ≤ t →
      x ^ 2 + y ^ 2 = t ^ 2 → PositivePath x y t
  | join {x y t u v s : ℤ} : PositivePath x y t → PositivePath u v s →
      PositivePath (x + u) (y + v) (t + s)

private lemma forget {x y t : ℤ} (p : PositivePath x y t) : Path x y t := by
  induction p with
  | empty => exact Path.zero
  | edge x y t _ _ h e => exact Path.edge x y t h e
  | join _ _ p q => exact Path.join p q

private lemma step {x y t : ℤ} (p : PositivePath x y t) :
    PositivePath (2*x+y+2*t) (x+2*y+2*t) (2*x+2*y+3*t) := by
  induction p with
  | empty => norm_num; exact PositivePath.empty
  | edge x y t hx hy ht e =>
      refine PositivePath.edge _ _ _ (by omega) (by omega) (by omega) ?_
      calc
        (2*x+y+2*t)^2 + (x+2*y+2*t)^2 =
            x^2+y^2-t^2+(2*x+2*y+3*t)^2 := by ring
        _ = _ := by rw [e]; ring
  | join _ _ p q =>
      convert PositivePath.join p q using 1 <;> ring

private lemma diag_step {n m : ℤ} (p : PositivePath n n (2*m)) :
    PositivePath (3*n+4*m) (3*n+4*m) (2*(2*n+3*m)) := by
  convert step p using 1 <;> ring

private lemma scale {x y t : ℤ} (p : PositivePath x y t) (k : ℕ) :
    PositivePath ((k:ℤ)*x) ((k:ℤ)*y) ((k:ℤ)*t) := by
  induction k with
  | zero => norm_num; exact PositivePath.empty
  | succ k ih =>
      convert PositivePath.join ih p using 1 <;> push_cast <;> ring

private lemma combine {n m u v a b : ℤ}
    (pn : PositivePath n n (2*m)) (pu : PositivePath u u (2*v))
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    PositivePath (a*n+b*u) (a*n+b*u) (2*(a*m+b*v)) := by
  have pa := scale pn a.toNat
  have pb := scale pu b.toNat
  rw [Int.toNat_of_nonneg ha] at pa
  rw [Int.toNat_of_nonneg hb] at pb
  convert PositivePath.join pa pb using 1 <;> ring

private lemma seed_one : PositivePath 1 1 2 := by
  have px : PositivePath 1 0 1 := PositivePath.edge 1 0 1 (by decide) (by decide) (by decide) (by decide)
  have py : PositivePath 0 1 1 := PositivePath.edge 0 1 1 (by decide) (by decide) (by decide) (by decide)
  exact PositivePath.join px py

private lemma seed_four : PositivePath 4 4 6 := by
  have px : PositivePath 3 4 5 := PositivePath.edge 3 4 5 (by decide) (by decide) (by decide) (by decide)
  have py : PositivePath 1 0 1 := PositivePath.edge 1 0 1 (by decide) (by decide) (by decide) (by decide)
  exact PositivePath.join px py

private lemma seed_seven : PositivePath 7 7 10 := by
  exact diag_step (m := 1) seed_one

private lemma diagonal : ∀ (m : ℕ) (n : ℤ), (m : ℤ) ≤ n →
    n ^ 2 ≤ 2*(m:ℤ)^2 → PositivePath n n (2*(m:ℤ)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro n hmn hs
      have hm : (0 : ℤ) ≤ (m : ℤ) := by omega
      by_cases h1 : 3*n ≤ 4*(m:ℤ)
      · have hp := combine (m := 1) (v := 3) seed_one seed_four
          (a := 4*(m:ℤ)-3*n) (b := n-(m:ℤ)) (by omega) (by omega)
        convert hp using 1 <;> ring
      by_cases h2 : 5*n ≤ 7*(m:ℤ)
      · have hp := combine (m := 3) (v := 5) seed_four seed_seven
          (a := 7*(m:ℤ)-5*n) (b := 3*n-4*(m:ℤ)) (by omega) (by omega)
        convert hp using 1 <;> ring
      let n' : ℤ := 3*n-4*(m:ℤ)
      let m' : ℤ := 3*(m:ℤ)-2*n
      have hmpos : 0 < (m : ℤ) := by
        by_contra! hh
        have hz : (m:ℤ) = 0 := by omega
        rw [hz] at hs
        nlinarith
      have hmp : 0 ≤ m' := by
        dsimp [m']
        by_contra! hh
        have p := mul_nonneg (show 0 ≤ 2*n-3*(m:ℤ) by omega)
          (show 0 ≤ 2*n+3*(m:ℤ) by omega)
        nlinarith [mul_pos hmpos hmpos]
      have hi : m'.toNat < m := by omega
      have hcast := Int.toNat_of_nonneg hmp
      have hm'n' : (m'.toNat : ℤ) ≤ n' := by
        rw [hcast]
        dsimp [m', n']
        omega
      have hs' : n'^2 ≤ 2*(m'.toNat:ℤ)^2 := by
        rw [hcast]
        dsimp [m', n']
        nlinarith
      have hp := diag_step (ih m'.toNat hi n' hm'n' hs')
      rw [hcast] at hp
      dsimp [m', n'] at hp
      convert hp using 1 <;> ring

theorem exact_diagonal (n : ℕ) :
    IsLeast {t : ℤ | Path (n : ℤ) n t} (2 * ⌈(n : ℝ) / Real.sqrt 2⌉) := by
  have hr : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hroot1 : 1 ≤ Real.sqrt (2 : ℝ) := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  let m : ℤ := ⌈(n : ℝ) / Real.sqrt 2⌉
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hm : 0 ≤ m := by exact Int.ceil_nonneg (div_nonneg hn hroot.le)
  have hmn : m ≤ (n : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast
    apply (div_le_iff₀ hroot).2
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hroot1)]
  have hb : (n : ℝ) ≤ Real.sqrt 2 * (m : ℝ) := by
    have hc : (n:ℝ) / Real.sqrt 2 ≤ (m:ℝ) := Int.le_ceil _
    simpa [mul_comm] using (div_le_iff₀ hroot).1 hc
  have hb' : (n:ℤ)^2 ≤ 2*m^2 := by
    have hmr : (0:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hp := mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg (mul_nonneg hroot.le hmr) hn)
    have hr' : (Real.sqrt 2 * (m : ℝ)) ^ 2 = 2 * (m : ℝ) ^ 2 := by
      rw [mul_pow, hr]
    have out : (n : ℝ)^2 ≤ 2*(m:ℝ)^2 := by nlinarith
    exact_mod_cast out
  constructor
  · have hp := diagonal m.toNat n (by simpa [Int.toNat_of_nonneg hm] using hmn)
      (by simpa [Int.toNat_of_nonneg hm] using hb')
    simpa [m, Int.toNat_of_nonneg hm] using forget hp
  · intro t ht
    change Path (n : ℤ) (n : ℤ) t at ht
    obtain ⟨hbound, hpar⟩ := lower_data ht
    let q : ℤ := t / 2
    have hq : 2*q = t := by dsimp [q]; omega
    have hreal : (2:ℝ)*(q:ℝ) = (t:ℝ) := by exact_mod_cast hq
    have hbound' : (n:ℝ) / Real.sqrt 2 ≤ (q:ℝ) := by
      apply (div_le_iff₀ hroot).2
      push_cast at hbound
      rw [← hreal] at hbound
      nlinarith
    have hmq : m ≤ q := Int.ceil_le.mpr hbound'
    change 2*m ≤ t
    omega

end Wilson

theorem OMA.solution : type_of% @OMA.S_oeis_a099188.main := by
  exact Wilson.exact_diagonal
