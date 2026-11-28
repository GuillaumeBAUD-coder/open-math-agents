import OMAStatements.S_oeis_a036837
import Mathlib

namespace OMA.S_oeis_a036837

noncomputable def fz (t : ℕ) : ℤ := L (t + 6) (t + 1) t

theorem fz_zero : fz 0 = 1 := by simp [fz, L]

theorem fz_succ (t : ℕ) : fz (t + 1) = ⌈((t : ℚ) + 7) / ((t : ℚ) + 2) * (fz t : ℚ)⌉ := by
  unfold fz
  rw [show t + 1 + 6 = (t + 6) + 1 from rfl, show t + 1 + 1 = (t + 1) + 1 from rfl, L]
  have e1 : t + 6 + 1 - 1 = t + 6 := by omega
  have e2 : t + 1 + 1 - 1 = t + 1 := by omega
  rw [e1, e2]
  push_cast
  ring_nf

theorem stepGen (t : ℕ) (F N Qf Qn Dd : ℤ) (hF : 24 * F = Qf) (hN : 24 * N = Qn)
    (hD : ((t : ℤ) + 2) * Qn - ((t : ℤ) + 7) * Qf = 24 * Dd) (h0 : 0 ≤ Dd) (h1 : Dd < (t : ℤ) + 2) :
    ⌈((t : ℚ) + 7) / ((t : ℚ) + 2) * (F : ℚ)⌉ = N := by
  have key : ((t : ℤ) + 2) * N - ((t : ℤ) + 7) * F = Dd := by
    have : 24 * (((t : ℤ) + 2) * N - ((t : ℤ) + 7) * F) = 24 * Dd := by
      rw [← hD, ← hF, ← hN]; ring
    linarith
  rw [Int.ceil_eq_iff]
  have hp : (0 : ℚ) < (t : ℚ) + 2 := by positivity
  have k' : ((t : ℚ) + 2) * N - ((t : ℚ) + 7) * F = (Dd : ℚ) := by exact_mod_cast key
  have h0' : (0 : ℚ) ≤ Dd := by exact_mod_cast h0
  have h1' : (Dd : ℚ) < (t : ℚ) + 2 := by exact_mod_cast h1
  rw [div_mul_eq_mul_div, lt_div_iff₀ hp, div_le_iff₀ hp]
  constructor <;> nlinarith

def Q0 (q : ℤ) : ℤ := (q+1)*(125*q^4+375*q^3+400*q^2+180*q+24)
def Q1 (q : ℤ) : ℤ := (q+1)*(125*q^4+500*q^3+725*q^2+450*q+96)
def Q2 (q : ℤ) : ℤ := (q+1)*(125*q^4+625*q^3+1150*q^2+920*q+264)
def Q3 (q : ℤ) : ℤ := 25*(q+1)^2*(q+2)*(5*q^2+15*q+12)
def Q4 (q : ℤ) : ℤ := 25*(q+1)*(q+2)^2*(5*q^2+15*q+12)

theorem dvdQ0 (q : ℤ) : (24 : ℤ) ∣ Q0 q := by
  have h : ((Q0 q : ℤ) : ZMod 24) = 0 := by
    unfold Q0
    push_cast
    generalize (q : ZMod 24) = x
    revert x
    decide
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (Q0 q) 24).1 h
  exact_mod_cast this

theorem dvdQ1 (q : ℤ) : (24 : ℤ) ∣ Q1 q := by
  have h : ((Q1 q : ℤ) : ZMod 24) = 0 := by
    unfold Q1
    push_cast
    generalize (q : ZMod 24) = x
    revert x
    decide
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (Q1 q) 24).1 h
  exact_mod_cast this

theorem dvdQ2 (q : ℤ) : (24 : ℤ) ∣ Q2 q := by
  have h : ((Q2 q : ℤ) : ZMod 24) = 0 := by
    unfold Q2
    push_cast
    generalize (q : ZMod 24) = x
    revert x
    decide
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (Q2 q) 24).1 h
  exact_mod_cast this

theorem dvdQ3 (q : ℤ) : (24 : ℤ) ∣ Q3 q := by
  have h : ((Q3 q : ℤ) : ZMod 24) = 0 := by
    unfold Q3
    push_cast
    generalize (q : ZMod 24) = x
    revert x
    decide
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (Q3 q) 24).1 h
  exact_mod_cast this

theorem dvdQ4 (q : ℤ) : (24 : ℤ) ∣ Q4 q := by
  have h : ((Q4 q : ℤ) : ZMod 24) = 0 := by
    unfold Q4
    push_cast
    generalize (q : ZMod 24) = x
    revert x
    decide
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (Q4 q) 24).1 h
  exact_mod_cast this

theorem chain (q : ℕ) (h : 24 * fz (5 * q) = Q0 q) :
    24 * fz (5 * q + 1) = Q1 q ∧ 24 * fz (5 * q + 2) = Q2 q ∧ 24 * fz (5 * q + 3) = Q3 q ∧
    24 * fz (5 * q + 4) = Q4 q ∧ 24 * fz (5 * (q + 1)) = Q0 ((q + 1 : ℕ) : ℤ) := by
  obtain ⟨N0, hN0⟩ := dvdQ1 ((q : ℤ))
  replace hN0 := hN0.symm
  have h1 : 24 * fz (5 * q + 1) = Q1 q := by
    have hc := stepGen (5 * q) (fz (5 * q)) N0 (Q0 q) (Q1 q) (q+1) h hN0
      (by simp only [Q0, Q1, Q2, Q3, Q4]; push_cast; ring) (by positivity) (by push_cast; omega)
    have e := fz_succ (5 * q)
    rw [show 5 * q + 1 = 5 * q + 1 by ring] at e
    push_cast at hc e
    rw [e, hc]
    exact hN0
  obtain ⟨N1, hN1⟩ := dvdQ2 ((q : ℤ))
  replace hN1 := hN1.symm
  have h2 : 24 * fz (5 * q + 2) = Q2 q := by
    have hc := stepGen (5 * q + 1) (fz (5 * q + 1)) N1 (Q1 q) (Q2 q) (q+1) h1 hN1
      (by simp only [Q0, Q1, Q2, Q3, Q4]; push_cast; ring) (by positivity) (by push_cast; omega)
    have e := fz_succ (5 * q + 1)
    rw [show 5 * q + 1 + 1 = 5 * q + 2 by ring] at e
    push_cast at hc e
    rw [e, hc]
    exact hN1
  obtain ⟨N2, hN2⟩ := dvdQ3 ((q : ℤ))
  replace hN2 := hN2.symm
  have h3 : 24 * fz (5 * q + 3) = Q3 q := by
    have hc := stepGen (5 * q + 2) (fz (5 * q + 2)) N2 (Q2 q) (Q3 q) (q+1) h2 hN2
      (by simp only [Q0, Q1, Q2, Q3, Q4]; push_cast; ring) (by positivity) (by push_cast; omega)
    have e := fz_succ (5 * q + 2)
    rw [show 5 * q + 2 + 1 = 5 * q + 3 by ring] at e
    push_cast at hc e
    rw [e, hc]
    exact hN2
  obtain ⟨N3, hN3⟩ := dvdQ4 ((q : ℤ))
  replace hN3 := hN3.symm
  have h4 : 24 * fz (5 * q + 4) = Q4 q := by
    have hc := stepGen (5 * q + 3) (fz (5 * q + 3)) N3 (Q3 q) (Q4 q) (0) h3 hN3
      (by simp only [Q0, Q1, Q2, Q3, Q4]; push_cast; ring) (by positivity) (by push_cast; omega)
    have e := fz_succ (5 * q + 3)
    rw [show 5 * q + 3 + 1 = 5 * q + 4 by ring] at e
    push_cast at hc e
    rw [e, hc]
    exact hN3
  obtain ⟨N4, hN4⟩ := dvdQ0 (((q + 1 : ℕ) : ℤ))
  replace hN4 := hN4.symm
  have h5 : 24 * fz (5 * (q + 1)) = Q0 ((q + 1 : ℕ) : ℤ) := by
    have hc := stepGen (5 * q + 4) (fz (5 * q + 4)) N4 (Q4 q) (Q0 ((q + 1 : ℕ) : ℤ)) (q+2) h4 hN4
      (by simp only [Q0, Q1, Q2, Q3, Q4]; push_cast; ring) (by positivity) (by push_cast; omega)
    have e := fz_succ (5 * q + 4)
    rw [show 5 * q + 4 + 1 = 5 * (q + 1) by ring] at e
    push_cast at hc e
    rw [e, hc]
    exact hN4
  exact ⟨h1, h2, h3, h4, h5⟩

theorem cl0 (q : ℕ) : 24 * fz (5 * q) = Q0 q := by
  induction q with
  | zero => simp [fz_zero, Q0]
  | succ q ih => exact (chain q ih).2.2.2.2

theorem cl1 (q : ℕ) : 24 * fz (5 * q + 1) = Q1 q := (chain q (cl0 q)).1
theorem cl2 (q : ℕ) : 24 * fz (5 * q + 2) = Q2 q := (chain q (cl0 q)).2.1
theorem cl3 (q : ℕ) : 24 * fz (5 * q + 3) = Q3 q := (chain q (cl0 q)).2.2.1
theorem cl4 (q : ℕ) : 24 * fz (5 * q + 4) = Q4 q := (chain q (cl0 q)).2.2.2.1

theorem rec10 (q r : ℕ) (hr : r < 5) :
    fz (5 * (q + 2) + r) - 5 * fz (5 * (q + 2) + r - 1) + 10 * fz (5 * (q + 2) + r - 2) - 10 * fz (5 * (q + 2) + r - 3) + 5 * fz (5 * (q + 2) + r - 4) - 2 * fz (5 * (q + 2) + r - 5) + 5 * fz (5 * (q + 2) + r - 6) - 10 * fz (5 * (q + 2) + r - 7) + 10 * fz (5 * (q + 2) + r - 8) - 5 * fz (5 * (q + 2) + r - 9) + fz (5 * (q + 2) + r - 10) = 0 := by
  interval_cases r
  · -- r = 0
    have c0 : 24 * fz (5 * (q + 2) + 0) = Q0 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 0 = 5 * (q + 2) by omega, cl0 (q + 2)]
      push_cast <;> rfl
    have c1 : 24 * fz (5 * (q + 2) + 0 - 1) = Q4 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 0 - 1 = 5 * (q + 1) + 4 by omega, cl4 (q + 1)]
      push_cast <;> rfl
    have c2 : 24 * fz (5 * (q + 2) + 0 - 2) = Q3 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 0 - 2 = 5 * (q + 1) + 3 by omega, cl3 (q + 1)]
      push_cast <;> rfl
    have c3 : 24 * fz (5 * (q + 2) + 0 - 3) = Q2 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 0 - 3 = 5 * (q + 1) + 2 by omega, cl2 (q + 1)]
      push_cast <;> rfl
    have c4 : 24 * fz (5 * (q + 2) + 0 - 4) = Q1 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 0 - 4 = 5 * (q + 1) + 1 by omega, cl1 (q + 1)]
      push_cast <;> rfl
    have c5 : 24 * fz (5 * (q + 2) + 0 - 5) = Q0 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 0 - 5 = 5 * (q + 1) by omega, cl0 (q + 1)]
      push_cast <;> rfl
    have c6 : 24 * fz (5 * (q + 2) + 0 - 6) = Q4 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 0 - 6 = 5 * (q + 0) + 4 by omega, cl4 (q + 0)]
      push_cast <;> rfl
    have c7 : 24 * fz (5 * (q + 2) + 0 - 7) = Q3 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 0 - 7 = 5 * (q + 0) + 3 by omega, cl3 (q + 0)]
      push_cast <;> rfl
    have c8 : 24 * fz (5 * (q + 2) + 0 - 8) = Q2 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 0 - 8 = 5 * (q + 0) + 2 by omega, cl2 (q + 0)]
      push_cast <;> rfl
    have c9 : 24 * fz (5 * (q + 2) + 0 - 9) = Q1 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 0 - 9 = 5 * (q + 0) + 1 by omega, cl1 (q + 0)]
      push_cast <;> rfl
    have c10 : 24 * fz (5 * (q + 2) + 0 - 10) = Q0 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 0 - 10 = 5 * (q + 0) by omega, cl0 (q + 0)]
      push_cast <;> rfl
    simp only [Q0, Q1, Q2, Q3, Q4] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have h24 : 24 * (fz (5 * (q + 2) + 0) - 5 * fz (5 * (q + 2) + 0 - 1) + 10 * fz (5 * (q + 2) + 0 - 2) - 10 * fz (5 * (q + 2) + 0 - 3) + 5 * fz (5 * (q + 2) + 0 - 4) - 2 * fz (5 * (q + 2) + 0 - 5) + 5 * fz (5 * (q + 2) + 0 - 6) - 10 * fz (5 * (q + 2) + 0 - 7) + 10 * fz (5 * (q + 2) + 0 - 8) - 5 * fz (5 * (q + 2) + 0 - 9) + fz (5 * (q + 2) + 0 - 10)) = 0 := by
      linear_combination (1) * c0 + (-5) * c1 + (10) * c2 + (-10) * c3 + (5) * c4 + (-2) * c5 + (5) * c6 + (-10) * c7 + (10) * c8 + (-5) * c9 + (1) * c10
    omega
  · -- r = 1
    have c0 : 24 * fz (5 * (q + 2) + 1) = Q1 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 1 = 5 * (q + 2) + 1 by omega, cl1 (q + 2)]
      push_cast <;> rfl
    have c1 : 24 * fz (5 * (q + 2) + 1 - 1) = Q0 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 1 - 1 = 5 * (q + 2) by omega, cl0 (q + 2)]
      push_cast <;> rfl
    have c2 : 24 * fz (5 * (q + 2) + 1 - 2) = Q4 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 1 - 2 = 5 * (q + 1) + 4 by omega, cl4 (q + 1)]
      push_cast <;> rfl
    have c3 : 24 * fz (5 * (q + 2) + 1 - 3) = Q3 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 1 - 3 = 5 * (q + 1) + 3 by omega, cl3 (q + 1)]
      push_cast <;> rfl
    have c4 : 24 * fz (5 * (q + 2) + 1 - 4) = Q2 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 1 - 4 = 5 * (q + 1) + 2 by omega, cl2 (q + 1)]
      push_cast <;> rfl
    have c5 : 24 * fz (5 * (q + 2) + 1 - 5) = Q1 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 1 - 5 = 5 * (q + 1) + 1 by omega, cl1 (q + 1)]
      push_cast <;> rfl
    have c6 : 24 * fz (5 * (q + 2) + 1 - 6) = Q0 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 1 - 6 = 5 * (q + 1) by omega, cl0 (q + 1)]
      push_cast <;> rfl
    have c7 : 24 * fz (5 * (q + 2) + 1 - 7) = Q4 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 1 - 7 = 5 * (q + 0) + 4 by omega, cl4 (q + 0)]
      push_cast <;> rfl
    have c8 : 24 * fz (5 * (q + 2) + 1 - 8) = Q3 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 1 - 8 = 5 * (q + 0) + 3 by omega, cl3 (q + 0)]
      push_cast <;> rfl
    have c9 : 24 * fz (5 * (q + 2) + 1 - 9) = Q2 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 1 - 9 = 5 * (q + 0) + 2 by omega, cl2 (q + 0)]
      push_cast <;> rfl
    have c10 : 24 * fz (5 * (q + 2) + 1 - 10) = Q1 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 1 - 10 = 5 * (q + 0) + 1 by omega, cl1 (q + 0)]
      push_cast <;> rfl
    simp only [Q0, Q1, Q2, Q3, Q4] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have h24 : 24 * (fz (5 * (q + 2) + 1) - 5 * fz (5 * (q + 2) + 1 - 1) + 10 * fz (5 * (q + 2) + 1 - 2) - 10 * fz (5 * (q + 2) + 1 - 3) + 5 * fz (5 * (q + 2) + 1 - 4) - 2 * fz (5 * (q + 2) + 1 - 5) + 5 * fz (5 * (q + 2) + 1 - 6) - 10 * fz (5 * (q + 2) + 1 - 7) + 10 * fz (5 * (q + 2) + 1 - 8) - 5 * fz (5 * (q + 2) + 1 - 9) + fz (5 * (q + 2) + 1 - 10)) = 0 := by
      linear_combination (1) * c0 + (-5) * c1 + (10) * c2 + (-10) * c3 + (5) * c4 + (-2) * c5 + (5) * c6 + (-10) * c7 + (10) * c8 + (-5) * c9 + (1) * c10
    omega
  · -- r = 2
    have c0 : 24 * fz (5 * (q + 2) + 2) = Q2 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 2 = 5 * (q + 2) + 2 by omega, cl2 (q + 2)]
      push_cast <;> rfl
    have c1 : 24 * fz (5 * (q + 2) + 2 - 1) = Q1 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 2 - 1 = 5 * (q + 2) + 1 by omega, cl1 (q + 2)]
      push_cast <;> rfl
    have c2 : 24 * fz (5 * (q + 2) + 2 - 2) = Q0 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 2 - 2 = 5 * (q + 2) by omega, cl0 (q + 2)]
      push_cast <;> rfl
    have c3 : 24 * fz (5 * (q + 2) + 2 - 3) = Q4 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 2 - 3 = 5 * (q + 1) + 4 by omega, cl4 (q + 1)]
      push_cast <;> rfl
    have c4 : 24 * fz (5 * (q + 2) + 2 - 4) = Q3 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 2 - 4 = 5 * (q + 1) + 3 by omega, cl3 (q + 1)]
      push_cast <;> rfl
    have c5 : 24 * fz (5 * (q + 2) + 2 - 5) = Q2 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 2 - 5 = 5 * (q + 1) + 2 by omega, cl2 (q + 1)]
      push_cast <;> rfl
    have c6 : 24 * fz (5 * (q + 2) + 2 - 6) = Q1 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 2 - 6 = 5 * (q + 1) + 1 by omega, cl1 (q + 1)]
      push_cast <;> rfl
    have c7 : 24 * fz (5 * (q + 2) + 2 - 7) = Q0 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 2 - 7 = 5 * (q + 1) by omega, cl0 (q + 1)]
      push_cast <;> rfl
    have c8 : 24 * fz (5 * (q + 2) + 2 - 8) = Q4 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 2 - 8 = 5 * (q + 0) + 4 by omega, cl4 (q + 0)]
      push_cast <;> rfl
    have c9 : 24 * fz (5 * (q + 2) + 2 - 9) = Q3 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 2 - 9 = 5 * (q + 0) + 3 by omega, cl3 (q + 0)]
      push_cast <;> rfl
    have c10 : 24 * fz (5 * (q + 2) + 2 - 10) = Q2 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 2 - 10 = 5 * (q + 0) + 2 by omega, cl2 (q + 0)]
      push_cast <;> rfl
    simp only [Q0, Q1, Q2, Q3, Q4] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have h24 : 24 * (fz (5 * (q + 2) + 2) - 5 * fz (5 * (q + 2) + 2 - 1) + 10 * fz (5 * (q + 2) + 2 - 2) - 10 * fz (5 * (q + 2) + 2 - 3) + 5 * fz (5 * (q + 2) + 2 - 4) - 2 * fz (5 * (q + 2) + 2 - 5) + 5 * fz (5 * (q + 2) + 2 - 6) - 10 * fz (5 * (q + 2) + 2 - 7) + 10 * fz (5 * (q + 2) + 2 - 8) - 5 * fz (5 * (q + 2) + 2 - 9) + fz (5 * (q + 2) + 2 - 10)) = 0 := by
      linear_combination (1) * c0 + (-5) * c1 + (10) * c2 + (-10) * c3 + (5) * c4 + (-2) * c5 + (5) * c6 + (-10) * c7 + (10) * c8 + (-5) * c9 + (1) * c10
    omega
  · -- r = 3
    have c0 : 24 * fz (5 * (q + 2) + 3) = Q3 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 3 = 5 * (q + 2) + 3 by omega, cl3 (q + 2)]
      push_cast <;> rfl
    have c1 : 24 * fz (5 * (q + 2) + 3 - 1) = Q2 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 3 - 1 = 5 * (q + 2) + 2 by omega, cl2 (q + 2)]
      push_cast <;> rfl
    have c2 : 24 * fz (5 * (q + 2) + 3 - 2) = Q1 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 3 - 2 = 5 * (q + 2) + 1 by omega, cl1 (q + 2)]
      push_cast <;> rfl
    have c3 : 24 * fz (5 * (q + 2) + 3 - 3) = Q0 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 3 - 3 = 5 * (q + 2) by omega, cl0 (q + 2)]
      push_cast <;> rfl
    have c4 : 24 * fz (5 * (q + 2) + 3 - 4) = Q4 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 3 - 4 = 5 * (q + 1) + 4 by omega, cl4 (q + 1)]
      push_cast <;> rfl
    have c5 : 24 * fz (5 * (q + 2) + 3 - 5) = Q3 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 3 - 5 = 5 * (q + 1) + 3 by omega, cl3 (q + 1)]
      push_cast <;> rfl
    have c6 : 24 * fz (5 * (q + 2) + 3 - 6) = Q2 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 3 - 6 = 5 * (q + 1) + 2 by omega, cl2 (q + 1)]
      push_cast <;> rfl
    have c7 : 24 * fz (5 * (q + 2) + 3 - 7) = Q1 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 3 - 7 = 5 * (q + 1) + 1 by omega, cl1 (q + 1)]
      push_cast <;> rfl
    have c8 : 24 * fz (5 * (q + 2) + 3 - 8) = Q0 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 3 - 8 = 5 * (q + 1) by omega, cl0 (q + 1)]
      push_cast <;> rfl
    have c9 : 24 * fz (5 * (q + 2) + 3 - 9) = Q4 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 3 - 9 = 5 * (q + 0) + 4 by omega, cl4 (q + 0)]
      push_cast <;> rfl
    have c10 : 24 * fz (5 * (q + 2) + 3 - 10) = Q3 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 3 - 10 = 5 * (q + 0) + 3 by omega, cl3 (q + 0)]
      push_cast <;> rfl
    simp only [Q0, Q1, Q2, Q3, Q4] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have h24 : 24 * (fz (5 * (q + 2) + 3) - 5 * fz (5 * (q + 2) + 3 - 1) + 10 * fz (5 * (q + 2) + 3 - 2) - 10 * fz (5 * (q + 2) + 3 - 3) + 5 * fz (5 * (q + 2) + 3 - 4) - 2 * fz (5 * (q + 2) + 3 - 5) + 5 * fz (5 * (q + 2) + 3 - 6) - 10 * fz (5 * (q + 2) + 3 - 7) + 10 * fz (5 * (q + 2) + 3 - 8) - 5 * fz (5 * (q + 2) + 3 - 9) + fz (5 * (q + 2) + 3 - 10)) = 0 := by
      linear_combination (1) * c0 + (-5) * c1 + (10) * c2 + (-10) * c3 + (5) * c4 + (-2) * c5 + (5) * c6 + (-10) * c7 + (10) * c8 + (-5) * c9 + (1) * c10
    omega
  · -- r = 4
    have c0 : 24 * fz (5 * (q + 2) + 4) = Q4 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 4 = 5 * (q + 2) + 4 by omega, cl4 (q + 2)]
      push_cast <;> rfl
    have c1 : 24 * fz (5 * (q + 2) + 4 - 1) = Q3 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 4 - 1 = 5 * (q + 2) + 3 by omega, cl3 (q + 2)]
      push_cast <;> rfl
    have c2 : 24 * fz (5 * (q + 2) + 4 - 2) = Q2 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 4 - 2 = 5 * (q + 2) + 2 by omega, cl2 (q + 2)]
      push_cast <;> rfl
    have c3 : 24 * fz (5 * (q + 2) + 4 - 3) = Q1 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 4 - 3 = 5 * (q + 2) + 1 by omega, cl1 (q + 2)]
      push_cast <;> rfl
    have c4 : 24 * fz (5 * (q + 2) + 4 - 4) = Q0 ((q : ℤ) + 2) := by
      rw [show 5 * (q + 2) + 4 - 4 = 5 * (q + 2) by omega, cl0 (q + 2)]
      push_cast <;> rfl
    have c5 : 24 * fz (5 * (q + 2) + 4 - 5) = Q4 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 4 - 5 = 5 * (q + 1) + 4 by omega, cl4 (q + 1)]
      push_cast <;> rfl
    have c6 : 24 * fz (5 * (q + 2) + 4 - 6) = Q3 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 4 - 6 = 5 * (q + 1) + 3 by omega, cl3 (q + 1)]
      push_cast <;> rfl
    have c7 : 24 * fz (5 * (q + 2) + 4 - 7) = Q2 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 4 - 7 = 5 * (q + 1) + 2 by omega, cl2 (q + 1)]
      push_cast <;> rfl
    have c8 : 24 * fz (5 * (q + 2) + 4 - 8) = Q1 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 4 - 8 = 5 * (q + 1) + 1 by omega, cl1 (q + 1)]
      push_cast <;> rfl
    have c9 : 24 * fz (5 * (q + 2) + 4 - 9) = Q0 ((q : ℤ) + 1) := by
      rw [show 5 * (q + 2) + 4 - 9 = 5 * (q + 1) by omega, cl0 (q + 1)]
      push_cast <;> rfl
    have c10 : 24 * fz (5 * (q + 2) + 4 - 10) = Q4 ((q : ℤ) + 0) := by
      rw [show 5 * (q + 2) + 4 - 10 = 5 * (q + 0) + 4 by omega, cl4 (q + 0)]
      push_cast <;> rfl
    simp only [Q0, Q1, Q2, Q3, Q4] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have h24 : 24 * (fz (5 * (q + 2) + 4) - 5 * fz (5 * (q + 2) + 4 - 1) + 10 * fz (5 * (q + 2) + 4 - 2) - 10 * fz (5 * (q + 2) + 4 - 3) + 5 * fz (5 * (q + 2) + 4 - 4) - 2 * fz (5 * (q + 2) + 4 - 5) + 5 * fz (5 * (q + 2) + 4 - 6) - 10 * fz (5 * (q + 2) + 4 - 7) + 10 * fz (5 * (q + 2) + 4 - 8) - 5 * fz (5 * (q + 2) + 4 - 9) + fz (5 * (q + 2) + 4 - 10)) = 0 := by
      linear_combination (1) * c0 + (-5) * c1 + (10) * c2 + (-10) * c3 + (5) * c4 + (-2) * c5 + (5) * c6 + (-10) * c7 + (10) * c8 + (-5) * c9 + (1) * c10
    omega

theorem a_fz (m : ℕ) (h : 7 ≤ m) : a m = fz (m - 6) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 7 := ⟨m - 7, by omega⟩
  unfold a fz
  have e1 : t + 7 - 5 = t + 1 + 1 := by omega
  have e2 : t + 7 - 6 = t + 1 := by omega
  have e3 : t + 1 + 6 = t + 7 := by omega
  rw [e1, e2, e3]

theorem fv1 : fz 1 = 4 := by
  have := cl1 0
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv2 : fz 2 = 11 := by
  have := cl2 0
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv3 : fz 3 = 25 := by
  have := cl3 0
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv4 : fz 4 = 50 := by
  have := cl4 0
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv5 : fz 5 = 92 := by
  have := cl0 1
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv6 : fz 6 = 158 := by
  have := cl1 1
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv7 : fz 7 = 257 := by
  have := cl2 1
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv8 : fz 8 = 400 := by
  have := cl3 1
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv9 : fz 9 = 600 := by
  have := cl4 1
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega
theorem fv10 : fz 10 = 873 := by
  have := cl0 2
  simp only [Q0, Q1, Q2, Q3, Q4] at this
  norm_num at this
  omega

open PowerSeries in
theorem gf_mul (b : ℕ → ℚ) (m q : ℕ) (d p : ℕ → ℚ) (D N : PowerSeries ℚ)
    (hD : D = ∑ j ∈ Finset.range (m + 1), C (d j) * X ^ j)
    (hN : N = ∑ j ∈ Finset.range (q + 1), C (p j) * X ^ j) (hp : ∀ n, q < n → p n = 0)
    (hb : ∀ n, ∑ j ∈ Finset.range (m + 1), d j * (if j ≤ n then b (n - j) else 0) =
      if n ≤ q then p n else 0) :
    mk b * D = N := by
  rw [hD, hN]
  ext n
  simp only [Finset.mul_sum, map_sum]
  have : ∀ j ∈ Finset.range (m + 1), coeff n (mk b * (C (d j) * X ^ j)) =
      d j * (if j ≤ n then b (n - j) else 0) := by
    intro j _
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp
  rw [Finset.sum_congr rfl this, hb n]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · by_cases h : n ≤ q
    · simp [h]
    · simp [h, hp n (by omega)]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; simp at h; simp [hp n (by omega)]

theorem rec10' (t : ℕ) (ht : 10 ≤ t) :
    fz t - 5 * fz (t - 1) + 10 * fz (t - 2) - 10 * fz (t - 3) + 5 * fz (t - 4) - 2 * fz (t - 5)
      + 5 * fz (t - 6) - 10 * fz (t - 7) + 10 * fz (t - 8) - 5 * fz (t - 9) + fz (t - 10) = 0 := by
  have := rec10 ((t - 10) / 5) ((t - 10) % 5) (by omega)
  rwa [show 5 * ((t - 10) / 5 + 2) + (t - 10) % 5 = t by omega] at this

noncomputable def sc (n : ℕ) : ℚ := if 7 ≤ n then (a n : ℚ) else 0

theorem sc_lt (m : ℕ) (h : m < 7) : sc m = 0 := by simp [sc, show ¬ 7 ≤ m by omega]

theorem scv (m : ℕ) (h : 7 ≤ m) : sc m = (fz (m - 6) : ℚ) := by
  simp [sc, h, a_fz m h]

def dl : ℕ → ℚ := fun j => [(1 : ℚ), -5, 10, -10, 5, -2, 5, -10, 10, -5, 1].getD j 0
def pl : ℕ → ℚ := fun j => [(0 : ℚ), 0, 0, 0, 0, 0, 0, 4, -9, 10, -5, 2, -5, 10, -10, 5, -1].getD j 0

theorem coefs (n : ℕ) : ∑ j ∈ Finset.range 11, dl j * (if j ≤ n then sc (n - j) else 0) =
    if n ≤ 16 then pl n else 0 := by
  by_cases hn : 17 ≤ n
  · rw [if_neg (by omega)]
    have r := rec10' (n - 6) (by omega)
    have rq : (fz (n - 6) : ℚ) - 5 * fz (n - 6 - 1) + 10 * fz (n - 6 - 2) - 10 * fz (n - 6 - 3)
        + 5 * fz (n - 6 - 4) - 2 * fz (n - 6 - 5) + 5 * fz (n - 6 - 6) - 10 * fz (n - 6 - 7)
        + 10 * fz (n - 6 - 8) - 5 * fz (n - 6 - 9) + fz (n - 6 - 10) = 0 := by exact_mod_cast r
    have e : ∀ j, j ≤ 10 → (if j ≤ n then sc (n - j) else 0) = (fz (n - 6 - j) : ℚ) := by
      intro j hj
      rw [if_pos (by omega), scv _ (by omega), show n - j - 6 = n - 6 - j by omega]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
      e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega),
      e 10 (by omega)]
    simp only [dl, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
    simp only [Nat.sub_zero] at *
    linarith
  · have hn' : n ≤ 16 := by omega
    rw [if_pos hn']
    have s7 : sc 7 = 4 := by rw [scv _ (by norm_num)]; norm_num [fv1]
    have s8 : sc 8 = 11 := by rw [scv _ (by norm_num)]; norm_num [fv2]
    have s9 : sc 9 = 25 := by rw [scv _ (by norm_num)]; norm_num [fv3]
    have s10 : sc 10 = 50 := by rw [scv _ (by norm_num)]; norm_num [fv4]
    have s11 : sc 11 = 92 := by rw [scv _ (by norm_num)]; norm_num [fv5]
    have s12 : sc 12 = 158 := by rw [scv _ (by norm_num)]; norm_num [fv6]
    have s13 : sc 13 = 257 := by rw [scv _ (by norm_num)]; norm_num [fv7]
    have s14 : sc 14 = 400 := by rw [scv _ (by norm_num)]; norm_num [fv8]
    have s15 : sc 15 = 600 := by rw [scv _ (by norm_num)]; norm_num [fv9]
    have s16 : sc 16 = 873 := by rw [scv _ (by norm_num)]; norm_num [fv10]
    interval_cases n <;>
      simp [Finset.sum_range_succ, dl, pl, sc_lt, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16] <;> norm_num

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if 7 ≤ n then (a n : ℚ) else 0) *
    ((PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + PowerSeries.X + 1) *
      (PowerSeries.X - 1) ^ 6) =
    PowerSeries.X ^ 7 * (4 - PowerSeries.X ^ 9 + 5 * PowerSeries.X ^ 8 - 10 * PowerSeries.X ^ 7 +
      10 * PowerSeries.X ^ 6 - 5 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 4 -
      5 * PowerSeries.X ^ 3 + 10 * PowerSeries.X ^ 2 - 9 * PowerSeries.X) := by
  apply gf_mul sc 10 16 dl pl
  · simp [Finset.sum_range_succ, dl, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, pl, map_ofNat PowerSeries.C]
    ring
  · intro n hn
    simp only [pl, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl
  · exact coefs

end OMA.S_oeis_a036837

theorem OMA.solution : type_of% @OMA.S_oeis_a036837.main := OMA.S_oeis_a036837.gf
