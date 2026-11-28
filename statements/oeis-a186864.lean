import Mathlib

/-!
# A186864: five-position self-avoiding king tours

Source: https://oeis.org/A186864, row 5 of https://oeis.org/A186861.

As in the OEIS examples, the five positions include the starting square.
The tour can use any of the eight king moves at each of its four moves.
The series has coefficient zero at degree zero by the empty-board convention.
-/

namespace OMA.S_oeis_a186864

abbrev Word := Fin 4 → Fin 8

def dx : Fin 8 → ℤ := ![-1,-1,-1,0,0,1,1,1]
def dy : Fin 8 → ℤ := ![-1,0,1,-1,1,-1,0,1]

def coordinate (step : Fin 8 → ℤ) (w : Word) (t : Fin 5) : ℤ :=
  ![0, step (w 0), step (w 0) + step (w 1),
    step (w 0) + step (w 1) + step (w 2),
    step (w 0) + step (w 1) + step (w 2) + step (w 3)] t

def SelfAvoiding (w : Word) : Prop :=
  (List.ofFn (fun t => (coordinate dx w t, coordinate dy w t))).Nodup

instance (w : Word) : Decidable (SelfAvoiding w) := by
  unfold SelfAvoiding
  infer_instance

def shapes : Finset Word := Finset.univ.filter SelfAvoiding

noncomputable def offsets (u : Fin 5 → ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.Ico 0 (n:ℤ)).filter fun z => ∀ t, 0 ≤ z + u t ∧ z + u t < (n:ℤ)

noncomputable def a (n : ℕ) : ℕ :=
  ∑ w ∈ shapes, (offsets (coordinate dx w) n).card * (offsets (coordinate dy w) n).card

noncomputable def gf : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)

theorem main :
    (∀ n ≥ 4, (a n : ℤ) = 2336*(n:ℤ)^2 - 10456*n + 11160) ∧
    (∀ n > 6, (a n : ℤ) = 3*a (n-1) - 3*a (n-2) + a (n-3)) ∧
    gf * (1-PowerSeries.X)^3 =
      8*PowerSeries.X^3*(151+386*PowerSeries.X+96*PowerSeries.X^2-49*PowerSeries.X^3) := by
  sorry

end OMA.S_oeis_a186864
