import OMAStatements.S_mo_47888
import Mathlib

/-!
# Multinomial averaging can destroy monotonicity for any number of trials

For category scores u = (0,1,2), take the monotone cubic field
F(x) = u (u · x)³. With one trial the dot product for p = (1,6,1)/8 and
q = (4,2,2)/8 equals −1/8. The same field admits interior counterexamples
for each positive trial count n. The proof computes the third moment of the
sum of n independent scores and compares two probability vectors.
-/

namespace MO47888Moment
open OMA.S_mo_47888

def T (x : Fin 3 → ℤ) : ℝ := (x 1 : ℝ) + 2 * (x 2 : ℝ)
def m1 (p : Fin 3 → ℝ) : ℝ := p 1 + 2*p 2
def m2 (p : Fin 3 → ℝ) : ℝ := p 1 + 4*p 2
def m3 (p : Fin 3 → ℝ) : ℝ := p 1 + 8*p 2

private theorem bump_zero (x : Fin 3 → ℤ) : T (bump x 0) = T x := by
  norm_num [T, bump, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide]
private theorem bump_one (x : Fin 3 → ℤ) : T (bump x 1) = T x + 1 := by
  norm_num [T, bump, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide]; ring
private theorem bump_two (x : Fin 3 → ℤ) : T (bump x 2) = T x + 2 := by
  norm_num [T, bump, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide]; ring

theorem cubic_from (p : Fin 3 → ℝ) (hp : onSimplex p) (n : ℕ) (x : Fin 3 → ℤ) :
    average p (fun y => (T y)^3) n x =
      (T x)^3 + 3*(T x)^2*n*m1 p +
      3*T x*((n:ℝ)*m2 p+n*((n:ℝ)-1)*(m1 p)^2) +
      n*m3 p + 3*n*((n:ℝ)-1)*m2 p*m1 p +
      n*((n:ℝ)-1)*((n:ℝ)-2)*(m1 p)^3 := by
  have hp0 : p 0 = 1-p 1-p 2 := by
    have h := hp.2
    rw [Fin.sum_univ_three] at h
    linarith
  induction n generalizing x with
  | zero => simp [average]
  | succ n ih =>
    rw [average, Fin.sum_univ_three, ih, ih, ih, bump_zero, bump_one, bump_two, Nat.cast_succ, hp0]
    unfold m1 m2 m3
    ring

theorem cubic (p : Fin 3 → ℝ) (hp : onSimplex p) (n : ℕ) :
    average p (fun x => (T x)^3) n 0 =
      n*m3 p + 3*n*((n:ℝ)-1)*m2 p*m1 p +
      n*((n:ℝ)-1)*((n:ℝ)-2)*(m1 p)^3 := by
  simpa [T] using cubic_from p hp n 0

end MO47888Moment

namespace MO47888

theorem moment_gap {n : ℝ} (hn : 1 ≤ n) :
    let δ := 1/(32*n)
    n*(7/4) + 3*n*(n-1)*(5/4) + n*(n-1)*(n-2) <
      n*(5/2-δ) + 3*n*(n-1)*(3/2-δ)*(1-δ) + n*(n-1)*(n-2)*(1-δ)^3 := by
  dsimp
  apply sub_pos.mp
  have hn' : 0 < n := by linarith
  have hshift : 0 ≤ n-1 := by linarith
  have hid :
      n*(5/2-1/(32*n)) + 3*n*(n-1)*(3/2-1/(32*n))*(1-1/(32*n))
        + n*(n-1)*(n-2)*(1-1/(32*n))^3
        - (n*(7/4) + 3*n*(n-1)*(5/4) + n*(n-1)*(n-2)) =
      (21504*(n-1)^4 + 87648*(n-1)^3 + 134239*(n-1)^2 + 91649*(n-1) + 23552) /
        (32768*n^2) := by
    field_simp [hn'.ne']
    ring
  rw [hid]
  positivity

end MO47888

namespace MultinomialCounterexample
open OMA.S_mo_47888

open MO47888Moment (T)

def direction : Fin 3 → ℝ := ![0,1,2]

noncomputable def field (x : Fin 3 → ℤ) (j : Fin 3) : ℝ :=
  direction j * T x ^ 3

theorem monotone_field : fieldMonotone field := by
  intro x y
  calc
    0 ≤ (T x - T y) * (T x ^ 3 - T y ^ 3) := by
      rcases le_total (T x) (T y) with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
          (sub_nonpos.mpr ((Odd.strictMono_pow (by decide : Odd 3)).monotone h))
      · exact mul_nonneg (sub_nonneg.mpr h)
          (sub_nonneg.mpr ((Odd.strictMono_pow (by decide : Odd 3)).monotone h))
    _ = _ := by simp [Fin.sum_univ_succ, field, direction, T]; ring

noncomputable def p : Fin 3 → ℝ := ![1/8, 6/8, 1/8]
noncomputable def q : Fin 3 → ℝ := ![4/8, 2/8, 2/8]

theorem p_simplex : onSimplex p := by
  constructor
  · intro j; fin_cases j <;> norm_num [p]
  · norm_num [p, Fin.sum_univ_succ]

theorem q_simplex : onSimplex q := by
  constructor
  · intro j; fin_cases j <;> norm_num [q]
  · norm_num [q, Fin.sum_univ_succ]

theorem averaged_pair :
    ∑ j, (p j-q j) * (smooth 1 field p j-smooth 1 field q j) = -(1/8 : ℝ) := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [direction, h20, h21, h12, p, q, smooth, average, bump, T, field, Fin.sum_univ_succ]

end MultinomialCounterexample

namespace MultinomialCounterexample
open OMA.S_mo_47888 MO47888Moment

private theorem average_mul (a : Fin 3 → ℝ) (h : (Fin 3 → ℤ) → ℝ) (c : ℝ) (n : ℕ)
    (x : Fin 3 → ℤ) : average a (fun y => c * h y) n x = c * average a h n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [average, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem smooth_eq (a : Fin 3 → ℝ) (n : ℕ) (j : Fin 3) :
    smooth n field a j = direction j * average a (fun x => (T x)^3) n 0 :=
  average_mul a _ _ _ _

/-- The same monotone field fails for every positive number of trials, even at
two interior points of the simplex. -/
theorem fails_every_trial_count (n : ℕ) (hn : 0 < n) :
    ∃ a b : Fin 3 → ℝ, onSimplex a ∧ onSimplex b ∧ (∀ j, 0 < a j ∧ 0 < b j) ∧
      ∑ j, (a j - b j) * (smooth n field a j - smooth n field b j) < 0 := by
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  let δ : ℝ := 1/(32*n)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ < 1/2 := by
    dsimp [δ]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  let b : Fin 3 → ℝ := ![1/4+δ, 1/2-δ, 1/4]
  have hpos (j : Fin 3) : 0 < p j ∧ 0 < b j := by
    fin_cases j <;> norm_num [p,b] <;> linarith
  have hb : onSimplex b := ⟨fun j => (hpos j).2.le, by simp [b, Fin.sum_univ_three]; ring⟩
  refine ⟨p, b, p_simplex, hb, hpos, ?_⟩
  let M (v : Fin 3 → ℝ) := average v (fun x => (T x)^3) n 0
  have hpM : M p = n*(7/4) + 3*n*((n:ℝ)-1)*(5/4) + n*((n:ℝ)-1)*((n:ℝ)-2) := by
    unfold M
    rw [cubic p p_simplex n]
    dsimp [p,m1,m2,m3]
    ring
  have hbM : M b = n*(5/2-δ) + 3*n*((n:ℝ)-1)*(3/2-δ)*(1-δ)
      + n*((n:ℝ)-1)*((n:ℝ)-2)*(1-δ)^3 := by
    unfold M
    rw [cubic b hb n]
    dsimp [b,m1,m2,m3]
    ring
  have hlt : M p < M b := by rw [hpM,hbM]; exact MO47888.moment_gap hn1
  simp_rw [smooth_eq]
  change (∑ j, (p j - b j) * (direction j * M p - direction j * M b)) < 0
  have he : (∑ j, (p j - b j) * (direction j * M p - direction j * M b)) =
      δ * (M p - M b) := by
    rw [Fin.sum_univ_three]
    dsimp [p, b, direction]
    ring
  rw [he]
  exact mul_neg_of_pos_of_neg hδ (sub_neg.mpr hlt)

end MultinomialCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_47888.main) := by
  intro h
  obtain ⟨a,b,ha,hb,_,hlt⟩ := MultinomialCounterexample.fails_every_trial_count 1 (by decide)
  exact hlt.not_ge (h 1 3 (by decide) (by decide) MultinomialCounterexample.field
    MultinomialCounterexample.monotone_field a b ha hb)
