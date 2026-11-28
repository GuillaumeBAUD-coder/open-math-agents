import OMAStatements.S_oeis_a264200
import Mathlib

namespace KimberlingDyadic
open OMA.S_oeis_a264200

structure Weight where
  lo : ℤ
  loOffset : ℤ
  mid : ℤ
  midOffset : ℤ
  hi : ℤ
  hiOffset : ℤ

def weight (w : Weight) (d x : ℤ) : ℤ :=
  if x < d then w.lo * x + w.loOffset * d
  else if x < 2*d then w.mid * x + w.midOffset * d
  else w.hi * x + w.hiOffset * d

def step (w : Weight) : Weight :=
  ⟨w.lo + 2*w.mid, 2*(w.loOffset + w.mid + w.midOffset),
   w.lo + 2*w.hi, 2*(w.loOffset + w.hi + w.hiOffset),
   2*w.hi, 2*(w.hi + w.hiOffset)⟩

private theorem children (w : Weight) (d x : ℤ) (hd : 0 < d) (hx : 0 ≤ x) :
    weight w (2*d) (2*(x+d)) + (if x < 2*d then weight w (2*d) x else 0) =
      weight (step w) d x := by
  unfold weight
  split_ifs <;> first | omega | (simp only [step]; ring)

private theorem nonneg_values (n : ℕ) : ∀ x ∈ values 2 n, 0 ≤ x := by
  induction n with
  | zero => simp [values]
  | succ n ih =>
    intro x hx
    simp only [values, List.mem_append, List.mem_map, List.mem_filter] at hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨hx, _⟩
    · have := ih y hy
      have hpow : (0 : ℤ) < scale 2 n := by unfold scale; positivity
      omega
    · exact ih x hx

private theorem list_step (w : Weight) (d : ℤ) (hd : 0 < d) (xs : List ℤ)
    (hp : ∀ x ∈ xs, 0 ≤ x) :
    ((xs.map (fun x => 2*(x+d))).map (weight w (2*d))).sum +
      ((xs.filter (fun x => decide (x < 2*d))).map (weight w (2*d))).sum =
      (xs.map (weight (step w) d)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hp x (by simp)
    have hi := ih (fun y hy => hp y (by simp [hy]))
    have hc := children w d x hd hx
    by_cases h : x < 2*d <;>
      simp [h] at hc ⊢ <;> simp only [List.map_map] at hi <;> omega

def total (n : ℕ) (w : Weight) : ℤ :=
  ((values 2 n).map (weight w (scale 2 n))).sum

private theorem total_succ (n : ℕ) (w : Weight) :
    total (n+1) w = total n (step w) := by
  have hd : (0 : ℤ) < scale 2 n := by unfold scale; positivity
  have hscale : scale (2:ℤ) (n+1) = 2*scale 2 n := by simp [scale, pow_succ, mul_comm]
  unfold total
  rw [values, hscale, List.map_append, List.sum_append]
  exact list_step w (scale 2 n) hd _ (nonneg_values n)

private theorem total_zero (w : Weight) : total 0 w = w.mid + w.midOffset := by
  simp [total, values, scale, weight]

private theorem recurrence (n : ℕ) (w : Weight) :
    total (n+4) w = 3*total (n+3) w + 4*total (n+2) w -
      8*total (n+1) w - 8*total n w := by
  induction n generalizing w with
  | zero =>
    change total (((0+1)+1)+1+1) w = 3*total ((0+1)+1+1) w + 4*total (0+1+1) w -
      8*total (0+1) w - 8*total 0 w
    simp only [total_succ, total_zero, step]
    ring
  | succ n ih =>
    change total ((n+4)+1) w = 3*total ((n+3)+1) w + 4*total ((n+2)+1) w -
      8*total ((n+1)+1) w - 8*total (n+1) w
    simpa only [total_succ] using (ih (step w))

def identityWeight : Weight := ⟨1,0,1,0,1,0⟩

private theorem total_id (n : ℕ) : total n identityWeight = a 2 (n+1) := by
  have hw : weight identityWeight (scale 2 n) = id := by
    funext x
    simp [weight, identityWeight]
  simp [total, hw, a, sumVal]

theorem solve (n : ℕ) (hn : 4 ≤ n) :
    a 2 n = 3*a 2 (n-1) + 4*a 2 (n-2) - 8*a 2 (n-3) - 8*a 2 (n-4) := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    decide +kernel
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n-5, by omega⟩
    have H := recurrence k identityWeight
    simp only [total_id] at H
    rw [show k+5-1=k+4 by omega, show k+5-2=k+3 by omega,
      show k+5-3=k+2 by omega, show k+5-4=k+1 by omega]
    exact H

end KimberlingDyadic

theorem OMA.solution : type_of% @OMA.S_oeis_a264200.main := KimberlingDyadic.solve
