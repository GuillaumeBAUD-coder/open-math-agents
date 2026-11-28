import FormalConjectures.OEIS.«179537»
import Mathlib

/-!
Exact column identities adapted from TaifengYi, open-math-agents PR 3597.
The original submission treats prime moduli. Its finite identities hold over commutative rings.
The central binomial identity is due to Kasper Andersen (Lemma 4.1 in
Zhi-Wei Sun, Super congruences and Euler numbers).

The new argument clears both column recurrences over the integers, including
when their coefficients share prime factors with the modulus. Abel summation
then recombines the unweighted columns. The weighted columns use the integrality
of the Catalan numbers.
-/

namespace SunAlternating

theorem reorder (R : Type*) [CommRing R] (p : ℕ) (hp : 0 < p) (w : ℕ → R) :
    ∑ n ∈ Finset.range p, w n * (OeisA179537.a n : R) =
      ∑ j ∈ Finset.range ((p-1)/2+1), ((-16:R)^j * ((2*j).choose j : R)^2) *
        ∑ n ∈ Finset.range p, w n * (n.choose (2*j) : R)^2 := by
  let f (j : ℕ) : R := (-16:R)^j * ((2*j).choose j : R)^2
  have row (n : ℕ) (hn : n < p) : (OeisA179537.a n : R) =
      ∑ j ∈ Finset.range p, f j * (n.choose (2*j) : R)^2 := by
    unfold OeisA179537.a
    push_cast
    calc
      _ = ∑ j ∈ Finset.range (n+1), f j * (n.choose (2*j) : R)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        have h := Nat.choose_mul (n:=n) (k:=2*j) (s:=j) (by omega)
        rw [show 2*j-j=j by omega] at h
        have e := congrArg (fun t : ℕ => (t:R)) h
        push_cast at e
        dsimp only [f]
        linear_combination -(-16:R)^j * congrArg (fun t : R => t^2) e
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hj
        simp only [Finset.mem_range] at hj
        simp [Nat.choose_eq_zero_of_lt (show n < 2*j by omega)]
  calc
    _ = ∑ n ∈ Finset.range p, ∑ j ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [row n (Finset.mem_range.mp hn), Finset.mul_sum]
    _ = ∑ j ∈ Finset.range p, ∑ n ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range ((p-1)/2+1), ∑ n ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      simp only [Finset.mem_range] at hj
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [Nat.choose_eq_zero_of_lt (show n < 2*j by omega)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [f]
      ring

end SunAlternating

namespace SunAlternating

variable {R : Type*} [CommRing R]

theorem chooseAcross (n m : ℕ) :
    ((m:R)+1) * (n.choose (m+1) : R) = ((n:R)-m)*(n.choose m : R) := by
  by_cases h : m ≤ n
  · have e := congrArg (fun t : ℕ => (t:R)) (Nat.choose_succ_right_eq n m)
    push_cast [h] at e
    linear_combination e
  · have a : n < m := by omega
    simp [Nat.choose_eq_zero_of_lt a, Nat.choose_eq_zero_of_lt (show n < m+1 by omega)]

theorem chooseUp (n m : ℕ) :
    ((n:R)+1-m)*( (n+1).choose m : R) = ((n:R)+1)*(n.choose m : R) := by
  by_cases h : m ≤ n+1
  · have e := congrArg (fun t : ℕ => (t:R)) (Nat.choose_mul_succ_eq n m)
    push_cast [h] at e
    linear_combination -e
  · simp [Nat.choose_eq_zero_of_lt (show n < m by omega),
      Nat.choose_eq_zero_of_lt (show n+1 < m by omega)]

def cert (n m : R) := 2*n^2-(6*m+8)*n+(5*m+8)*(m+1)

def boundary (R : Type*) [CommRing R] (n m : ℕ) : R :=
  -(-1:R)^n * (((n:R)-m)*(n.choose m : R))^2 * cert (n:R) (m:R)

/-- The alternating sum of squared binomial coefficients in a fixed column. -/
def altColumn (R : Type*) [CommRing R] (N m : ℕ) : R :=
  ∑ n ∈ Finset.range N, (-1:R)^n * (n.choose m : R)^2

theorem step (n m : ℕ) :
    ((m:R)+1)^2*((m:R)+2) *
        (4*((m:R)+2)*((-1:R)^n*(n.choose (m+2) : R)^2)
        + ((m:R)+1)*((-1:R)^n*(n.choose m : R)^2)) =
      boundary R (n+1) m - boundary R n m := by
  have c₁ := chooseAcross (R:=R) n m
  have c₂ := chooseAcross (R:=R) n (m+1)
  push_cast at c₂
  have c : ((m:R)+1)*((m:R)+2)*(n.choose (m+2):R) =
      ((n:R)-m-1)*((n:R)-m)*(n.choose m:R) := by
    linear_combination ((m:R)+1)*c₂ + ((n:R)-m-1)*c₁
  unfold boundary
  push_cast
  rw [chooseUp, pow_succ]
  unfold cert
  linear_combination 4*(-1:R)^n * congrArg (fun t : R => t^2) c

theorem telescope (N m : ℕ) :
    ((m:R)+1)^2*((m:R)+2) *
      (4*((m:R)+2)*altColumn R N (m+2) + ((m:R)+1)*altColumn R N m) =
      boundary R N m := by
  induction N with
  | zero => cases m <;> simp [altColumn,boundary,Nat.choose]
  | succ N IH =>
    simp only [altColumn,Finset.sum_range_succ] at *
    linear_combination IH + step (R:=R) N m

end SunAlternating

namespace SunWeightedColumn

open SunAlternating

def column (R : Type*) [CommRing R] (N m : ℕ) : R :=
  ∑ n ∈ Finset.range N, (-1:R)^n * (2*(n:R)-m+1) * (n.choose m : R)^2

def cert {R : Type*} [CommRing R] (n m : R) : R :=
  4*n^3 - (14*m+20)*n^2 + (16*m^2+44*m+28)*n - (5*m^3+18*m^2+18*m+4)

def boundary (R : Type*) [CommRing R] (n m : ℕ) : R :=
  -(-1:R)^n * (((n:R)-m)*(n.choose m : R))^2 * cert (n:R) (m:R)

variable {R : Type*} [CommRing R]

theorem step (n m : ℕ) :
    ((m:R)+1)*((m:R)+2)^2 *
      (4*((m:R)+1)*((-1:R)^n*(2*(n:R)-((m:R)+2)+1)*(n.choose (m+2):R)^2)
        + ((m:R)+2)*((-1:R)^n*(2*(n:R)-m+1)*(n.choose m:R)^2)) =
      boundary R (n+1) m - boundary R n m := by
  have c₁ := chooseAcross (R:=R) n m
  have c₂ := chooseAcross (R:=R) n (m+1)
  push_cast at c₂
  have c : ((m:R)+1)*((m:R)+2)*(n.choose (m+2):R) =
      ((n:R)-m-1)*((n:R)-m)*(n.choose m:R) := by
    linear_combination ((m:R)+1)*c₂ + ((n:R)-m-1)*c₁
  unfold boundary
  push_cast
  rw [chooseUp, pow_succ (a := (-1:R))]
  unfold cert
  linear_combination 4*(-1:R)^n*(2*(n:R)-m-1)*congrArg (fun t : R => t^2) c

theorem telescope (N m : ℕ) :
    ((m:R)+1)*((m:R)+2)^2 *
      (4*((m:R)+1)*column R N (m+2) + ((m:R)+2)*column R N m) =
      boundary R N m := by
  induction N with
  | zero => cases m <;> simp [column,boundary,Nat.choose]
  | succ N ih =>
    simp only [column,Finset.sum_range_succ] at *
    have h := step (R:=R) N m
    push_cast at ih ⊢
    linear_combination ih + h

theorem column_zero (N : ℕ) :
    column R N 0 = -(-1:R)^N * N := by
  induction N with
  | zero => simp [column]
  | succ k ih =>
    unfold column at *
    rw [Finset.sum_range_succ,ih]
    simp only [Nat.cast_succ, pow_succ, Nat.cast_zero, sub_zero, Nat.choose_zero_right,
      Nat.cast_one, one_pow, mul_one]
    ring

end SunWeightedColumn

open Finset

namespace SunWeighted

def c (n k : ℕ) : ℤ := (n+k).choose n

theorem c_sym (n k : ℕ) : c n k = c k n := by
  unfold c
  rw [Nat.choose_symm_add, Nat.add_comm n k]

theorem c_pascal (n k : ℕ) :
    c (n+1) (k+1) = c n (k+1) + c (n+1) k := by
  unfold c
  rw [show n+1+(k+1) = (n+k+1)+1 by omega, Nat.choose_succ_succ]
  simp only [Nat.cast_add, show n+(k+1) = n+k+1 by omega, show n+1+k = n+k+1 by omega]

theorem c_ratio (n k : ℕ) :
    (n+k+1 : ℤ) * c n k = (n+1 : ℤ) * c (n+1) k := by
  unfold c
  rw [show n+1+k = n+k+1 by omega]
  exact_mod_cast (Nat.add_one_mul_choose_eq (n+k) n).trans (Nat.mul_comm _ _)

theorem c_twice (n : ℕ) : c (n+1) (n+1) = 2 * c n (n+1) := by
  rw [c_pascal, c_sym (n+1) n]
  ring

theorem telescope (n k : ℕ) :
    8*(2*((n:ℤ)+1)+1)*(∑ i ∈ range k, c (n+1) i ^ 2) -
      4*((n:ℤ)+1)*(∑ i ∈ range k, c n i ^ 2) =
    4*(2*(k:ℤ)+3*((n:ℤ)+1))*(c (n+1) k - c n k)^2 := by
  induction k with
  | zero => simp [c]
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ, c_pascal]
    push_cast
    linear_combination ih + (8*c n k-16*c (n+1) k) * c_ratio n k

theorem c_sum_step (n : ℕ) :
    8*(2*((n:ℤ)+1)+1)*(∑ i ∈ range (n+1+1), c (n+1) i ^ 2) -
      4*((n:ℤ)+1)*(∑ i ∈ range (n+1), c n i ^ 2) =
    (21*((n:ℤ)+1)+8)*c (n+1) (n+1)^2 := by
  rw [sum_range_succ]
  have h := telescope n (n+1)
  push_cast at h
  rw [c_twice] at h ⊢
  linear_combination h

end SunWeighted

open Finset

namespace SunComposite

theorem column_expand (n j : ℕ) :
    SunWeightedColumn.column ℤ n (2*j) =
      ∑ k ∈ range n, (-1:ℤ)^k*(2*(k:ℤ)-2*j+1)*(k.choose (2*j):ℤ)^2 := by
  simp [SunWeightedColumn.column]

theorem split (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range n, (42*(k:ℤ)+37)*(-1:ℤ)^k*OeisA179537.a k) =
      (∑ j ∈ range n, (42*(j:ℤ)+16)*(-16:ℤ)^j*((2*j).choose j:ℤ)^2*
        SunAlternating.altColumn ℤ n (2*j)) +
      ∑ j ∈ range n, 21*(-16:ℤ)^j*((2*j).choose j:ℤ)^2*
        SunWeightedColumn.column ℤ n (2*j) := by
  let f (j : ℕ) : ℤ := (-16:ℤ)^j*((2*j).choose j:ℤ)^2 *
    ∑ k ∈ range n, ((42*(k:ℤ)+37)*(-1:ℤ)^k)*(k.choose (2*j):ℤ)^2
  have h := SunAlternating.reorder ℤ n hn (fun k => (42*(k:ℤ)+37)*(-1:ℤ)^k)
  change _ = ∑ j ∈ range ((n-1)/2+1), f j at h
  have ext : (∑ j ∈ range ((n-1)/2+1), f j) = ∑ j ∈ range n, f j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    simp only [Finset.mem_range] at hj
    have hz : (∑ k ∈ range n, ((42*(k:ℤ)+37)*(-1:ℤ)^k)*(k.choose (2*j):ℤ)^2)=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      simp [Nat.choose_eq_zero_of_lt (show k < 2*j by omega)]
    simp [f,hz]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ range ((n-1)/2+1), f j := by simpa only [Int.cast_id] using h
    _ = ∑ j ∈ range n, f j := ext
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [f, SunAlternating.altColumn, column_expand, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring

end SunComposite

open Finset

namespace SunComposite

-- Clear the two consecutive binomial denominators before cancelling n+1 modulo n.
private theorem clearBoundary (n r s c t l h g : ℤ)
    (hc : n * c = r * t) (ht : (n + 1) * t = s * l) :
    (n + 1) * n * c ^ 2 * (r * h + n * g) =
      r ^ 2 * s * (c*l*h + t*l*g) := by
  calc
    _ = (n + 1) * (n*c) * (r*c*h + (n*c)*g) := by ring
    _ = (n + 1) * (r*t) * (r*c*h + (r*t)*g) := by rw [hc]
    _ = ((n+1)*t) * (r^2*(c*h + t*g)) := by ring
    _ = _ := by rw [ht]; ring

private theorem integerBoundary (n r s c t l x h g e : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hc : n * c = r * t) (ht : (n+1)*t = s*l)
    (hx : r^2*s*x = e*(n*c)^2*(r*h+n*g)) : n ∣ x := by
  have eq : (n+1)*x = n*(e*(c*l*h+t*l*g)) := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hr) hs)
    calc
      r^2*s*((n+1)*x) = (n+1)*(r^2*s*x) := by ring
      _ = n*e*((n+1)*n*c^2*(r*h+n*g)) := by rw [hx]; ring
      _ = _ := by rw [clearBoundary n r s c t l h g hc ht]; ring
  exact ⟨e*(c*l*h+t*l*g)-x, by linear_combination eq⟩

private theorem bracket (n : ℕ) (hn : 0 < n) (j : ℕ) :
    (n : ℤ) ∣ (2*(j:ℤ)+1)*SunAlternating.altColumn ℤ n (2*j) +
      8*((j:ℤ)+1)*SunAlternating.altColumn ℤ n (2*(j+1)) := by
  let c : ℤ := (n-1).choose (2*j)
  let t : ℤ := n.choose (2*j+1)
  let l : ℤ := (n+1).choose (2*j+2)
  have hp : n-1+1=n := by omega
  have hc : (n:ℤ)*c = (2*(j:ℤ)+1)*t := by
    have hn' := Nat.add_one_mul_choose_eq (n-1) (2*j)
    rw [hp] at hn'
    simpa [c,t, mul_comm (2 * (j:ℤ) + 1)] using
      (show (n:ℤ)*((n-1).choose (2*j):ℤ) =
        (n.choose (2*j+1):ℤ)*(2*(j:ℤ)+1) by exact_mod_cast hn')
  have ht : ((n:ℤ)+1)*t = (2*(j:ℤ)+2)*l := by
    have hn' := Nat.add_one_mul_choose_eq n (2*j+1)
    have h := (show ((n:ℤ)+1)*(n.choose (2*j+1):ℤ) =
        ((n+1).choose (2*j+2):ℤ)*(2*(j:ℤ)+2) by exact_mod_cast hn')
    simpa [t,l,mul_comm (2*(j:ℤ)+2)] using h
  have hb := SunAlternating.telescope (R:=ℤ) n (2*j)
  have bridge : ((n:ℤ)-2*(j:ℤ))*(n.choose (2*j):ℤ) = (n:ℤ)*c := by
    have h := SunAlternating.chooseUp (R:=ℤ) (n-1) (2*j)
    rw [hp] at h
    have nn : ((n-1 : ℕ):ℤ)+1=n := by exact_mod_cast hp
    push_cast at h
    rw [nn] at h
    exact h
  apply integerBoundary (n:ℤ) (2*(j:ℤ)+1) (2*(j:ℤ)+2) c t l _
    (10*(j:ℤ)+8) (2*(n:ℤ)-(12*(j:ℤ)+8)) (-(-1:ℤ)^n) (by positivity) (by positivity) hc ht
  unfold SunAlternating.boundary SunAlternating.cert at hb
  push_cast at hb
  rw [bridge] at hb
  rw [show 2*(j+1)=2*j+2 by omega]
  linear_combination hb

private def b (j : ℕ) : ℤ := ∑ k ∈ range (j+1), SunWeighted.c j k ^ 2

private theorem coeff_zero : b 0 = 1 := by norm_num [b, SunWeighted.c]
private theorem coeff_step (j : ℕ) :
    (42*((j:ℤ)+1)+16)*((2*(j+1)).choose (j+1):ℤ)^2 =
    16*(2*((j:ℤ)+1)+1)*b (j+1) - 8*((j:ℤ)+1)*b j := by
  have h := SunWeighted.c_sum_step j
  change 8*(2*((j:ℤ)+1)+1)*b (j+1) - 4*((j:ℤ)+1)*b j =
    (21*((j:ℤ)+1)+8)*SunWeighted.c (j+1) (j+1)^2 at h
  rw [show (2*(j+1)).choose (j+1) = ((j+1)+(j+1)).choose (j+1) by congr 1; omega]
  unfold SunWeighted.c at h
  linear_combination -2*h

private def term (n j : ℕ) : ℤ :=
  (42*(j:ℤ)+16)*(-16:ℤ)^j*((2*j).choose j:ℤ)^2*SunAlternating.altColumn ℤ n (2*j)

private def remainder (n m : ℕ) : ℤ :=
  8*(m:ℤ)*(-16:ℤ)^m*b (m-1)*SunAlternating.altColumn ℤ n (2*m)

-- Sum the adjacent-column identities, retaining the final boundary term.
private theorem abel (n : ℕ) (hn : 0 < n) (m : ℕ) :
    (n:ℤ) ∣ (∑ j ∈ range m, term n j) - remainder n m := by
  induction m with
  | zero => simp [remainder]
  | succ m ih =>
    have hd := dvd_mul_of_dvd_right (bracket n hn m) (16*(-16:ℤ)^m*b m)
    have he : term n m + remainder n m - remainder n (m+1) =
        16*(-16:ℤ)^m*b m*((2*(m:ℤ)+1)*SunAlternating.altColumn ℤ n (2*m) +
          8*((m:ℤ)+1)*SunAlternating.altColumn ℤ n (2*(m+1))) := by
      cases m with
      | zero => norm_num [term, remainder, coeff_zero]; ring
      | succ j =>
        have h := coeff_step j
        simp only [term,remainder,Nat.add_sub_cancel,
          Nat.cast_add,Nat.cast_one, pow_succ] at *
        linear_combination (-16:ℤ)^j*(-16)*SunAlternating.altColumn ℤ n (2*(j+1))*h
    rw [sum_range_succ]
    rw [← he] at hd
    rw [show (∑ j ∈ range m, term n j) + term n m - remainder n (m+1) =
        ((∑ j ∈ range m, term n j) - remainder n m) +
          (term n m + remainder n m - remainder n (m+1)) by ring]
    exact dvd_add ih hd

theorem unweighted (n : ℕ) (hn : 0 < n) :
    (n:ℤ) ∣ ∑ j ∈ range n, (42*(j:ℤ)+16)*(-16:ℤ)^j*
      ((2*j).choose j:ℤ)^2*SunAlternating.altColumn ℤ n (2*j) := by
  have h := abel n hn n
  have ht : (n:ℤ) ∣ remainder n n :=
    ⟨8*(-16:ℤ)^n*b (n-1)*SunAlternating.altColumn ℤ n (2*n), by simp [remainder]; ring⟩
  simpa only [sub_add_cancel, term] using dvd_add h ht

end SunComposite

namespace SunComposite

-- Multiplication by (n+1)^2 clears both factors in the weighted boundary.
private theorem weightedCancel (n d s z D L h g e : ℤ)
    (hds : d * s^2 ≠ 0) (hl : (n+1)*n*D = d*s*L)
    (ht : d*s^2*(2*z) = e*(n*D)^2*(s*(2*h)+n*(2*g))) :
    n ∣ z := by
  let t := (n+1)*D*L*h + d*L^2*g
  have hw : (2*d*s^2) * ((n+1)^2*z) = (2*d*s^2) * (n*e*t) := calc
    _ = (n+1)^2 * (d*s^2*(2*z)) := by ring
    _ = e*((n+1)*n*D)^2*(s*(2*h)+n*(2*g)) := by rw [ht]; ring
    _ = e*(d*s*L)^2*(s*(2*h)+n*(2*g)) := by rw [hl]
    _ = (2*d*s^2) * (n*e*t) := by
      dsimp [t]
      linear_combination -2*e*d*s^2*L*h*hl
  have hne : 2*d*s^2 ≠ 0 := by
    rw [mul_assoc]
    exact mul_ne_zero (by decide) hds
  have he := mul_left_cancel₀ hne hw
  refine ⟨e*t-(n+2)*z, ?_⟩
  linear_combination he

private theorem weightedPair (n j : ℕ) (hn : 0 < n) :
    (n:ℤ) ∣ (2*(2*(j:ℤ)+1)*SunWeightedColumn.column ℤ n (2*j+2) +
         ((j:ℤ)+1)*SunWeightedColumn.column ℤ n (2*j)) := by
  let D : ℤ := (n-1).choose (2*j)
  let T : ℤ := n.choose (2*j+1)
  let L : ℤ := (n+1).choose (2*j+2)
  let h : ℤ := -(10*(j:ℤ)^2+8*j+1)
  let g : ℤ := 2*(n:ℤ)^2 - (14*(j:ℤ)+10)*n + 32*(j:ℤ)^2 + 44*j + 14
  have hn' : n-1+1=n := by omega
  have hUp : (((n:ℤ)-2*j)*(n.choose (2*j):ℤ)) = (n:ℤ)*D := by
    have e := SunAlternating.chooseUp (R:=ℤ) (n-1) (2*j)
    rw [hn'] at e
    have hn'' : ((n-1:ℕ):ℤ)+1=(n:ℤ) := by omega
    rw [hn''] at e
    simpa [D] using e
  have hT : (n:ℤ)*D = (2*(j:ℤ)+1)*T := by
    have e := SunAlternating.chooseAcross (R:=ℤ) n (2*j)
    push_cast at e
    simpa [T] using hUp.symm.trans e.symm
  have hL : ((n:ℤ)+1)*T = (2*(j:ℤ)+2)*L := by
    have e := congrArg (fun x : ℕ => (x:ℤ)) (Nat.add_one_mul_choose_eq (n:=n) (k:=2*j+1))
    push_cast at e
    dsimp [T,L]
    linear_combination e
  apply weightedCancel n (2*(j:ℤ)+1) (2*(j:ℤ)+2) _ D L h g (-(-1:ℤ)^n)
  · positivity
  · linear_combination ((n:ℤ)+1)*hT + (2*(j:ℤ)+1)*hL
  · have e := SunWeightedColumn.telescope (R:=ℤ) n (2*j)
    unfold SunWeightedColumn.boundary at e
    push_cast at e
    rw [hUp] at e
    unfold SunWeightedColumn.cert at e
    dsimp [h,g]
    linear_combination e

theorem weighted (n j : ℕ) (hn : 0<n) :
    (n:ℤ) ∣ ((2*j).choose j:ℤ) * SunWeightedColumn.column ℤ n (2*j) := by
  induction j with
  | zero =>
    simp [SunWeightedColumn.column_zero]
  | succ j ih =>
    have e := weightedPair n j hn
    obtain ⟨v, hv⟩ := e
    obtain ⟨cat, hcat⟩ := Nat.succ_dvd_centralBinom j
    have h₁ := congrArg (fun x : ℕ => (x:ℤ)) hcat.symm
    have h₂ := congrArg (fun x : ℕ => (x:ℤ)) (Nat.succ_mul_centralBinom_succ j)
    simp only [Nat.centralBinom] at h₁ h₂
    push_cast at h₁ h₂
    have h₃ : ((2*(j+1)).choose (j+1):ℤ) = 2*(2*(j:ℤ)+1)*(cat:ℤ) := by
      apply mul_left_cancel₀ (show (j:ℤ)+1 ≠ 0 by positivity)
      linear_combination h₂ - 2*(2*(j:ℤ)+1)*h₁
    have hh : (n:ℤ) ∣ ((2*(j+1)).choose (j+1):ℤ) * SunWeightedColumn.column ℤ n (2*(j+1)) +
        ((2*j).choose j:ℤ) * SunWeightedColumn.column ℤ n (2*j) := by
      refine ⟨(cat:ℤ)*v, ?_⟩
      rw [h₃, ← h₁, show 2*(j+1)=2*j+2 by omega]
      linear_combination (cat:ℤ)*hv
    simpa using dvd_sub hh ih

end SunComposite

theorem OMA.solution : type_of% @OeisA179537.conjecture3 := by
  intro n hn
  rw [SunComposite.split n hn]
  apply dvd_add (SunComposite.unweighted n hn)
  apply Finset.dvd_sum
  intro j _
  obtain ⟨t, ht⟩ := SunComposite.weighted n j hn
  refine ⟨21 * (-16 : ℤ)^j * ((2*j).choose j : ℤ) * t, ?_⟩
  linear_combination 21 * (-16 : ℤ)^j * ((2*j).choose j : ℤ) * ht
