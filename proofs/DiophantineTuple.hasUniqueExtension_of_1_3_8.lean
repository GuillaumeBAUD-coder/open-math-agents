import FormalConjectures.Wikipedia.DiophantineTuple
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace TupleOddShift

/-- The coefficients of `(2 + √3)^n`, with the rational coordinate first. -/
def coeff : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => let (u, v) := coeff n; (2*u + 3*v, u + 2*v)

def U (n : Nat) : Int := (coeff n).1
def V (n : Nat) : Int := (coeff n).2

/-- Multiply the signed seed `A + B√3` by `(2 + √3)^n`. -/
def shift (n : Nat) (A B : Int) : Int × Int :=
  (U n*A + 3*V n*B, V n*A + U n*B)

@[simp] theorem U_zero : U 0 = 1 := rfl
@[simp] theorem V_zero : V 0 = 0 := rfl

theorem U_succ (n : Nat) : U (n+1) = 2*U n + 3*V n := by
  simp [U, V, coeff]

theorem V_succ (n : Nat) : V (n+1) = U n + 2*V n := by
  simp [U, V, coeff]

theorem coeff_nonneg (n : Nat) : 0 < U n ∧ 0 ≤ V n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [U_succ, V_succ]
      omega

theorem coeff_add (m n : Nat) :
    U (m+n) = U m*U n + 3*V m*V n ∧
    V (m+n) = U m*V n + V m*U n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, U_succ, V_succ, ih.1, ih.2, U_succ, V_succ]
      constructor <;> grind

theorem shift_succ (n : Nat) (A B : Int) :
    shift (n+1) A B =
      (2*(shift n A B).1 + 3*(shift n A B).2,
       (shift n A B).1 + 2*(shift n A B).2) := by
  unfold shift
  rw [U_succ, V_succ]
  congr 1 <;> grind

theorem shift_add (m n : Nat) (A B : Int) :
    shift (m+n) A B = shift m (shift n A B).1 (shift n A B).2 := by
  unfold shift
  rw [(coeff_add m n).1, (coeff_add m n).2]
  congr 1 <;> grind

theorem unit_norm (n : Nat) : U n*U n - 3*V n*V n = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [U_succ, V_succ]
      grind

/-- Odd multiples of the exponent have rational coefficient divisible by `U r`.
    Even multiples have their square-root coefficient divisible by `U r`. -/
theorem odd_even_dvd (r k : Nat) :
    U r ∣ U (r*(2*k+1)) ∧ U r ∣ V (r*(2*k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have he : r*(2*(k+1)) = r*(2*k+1)+r := by
        rw [← Nat.mul_succ]
        congr 1
      have ho : r*(2*(k+1)+1) = r*(2*(k+1))+r := Nat.mul_succ _ _
      have hEven : U r ∣ V (r*(2*(k+1))) := by
        rw [he, (coeff_add _ _).2]
        exact Int.dvd_add (Int.dvd_mul_of_dvd_left ih.1) (Int.dvd_mul_left _ _)
      refine ⟨?_, hEven⟩
      rw [ho, (coeff_add _ _).1]
      exact Int.dvd_add (Int.dvd_mul_left _ _)
        (Int.dvd_mul_of_dvd_left (Int.dvd_mul_of_dvd_right hEven))

/-- At an odd multiple of the shift exponent, the square of the first
    coordinate is congruent to `-3 B²` modulo `U r`. -/
theorem odd_shift_dvd (r k : Nat) (A B : Int) :
    U r ∣ (shift (r*(2*k+1)) A B).1 * (shift (r*(2*k+1)) A B).1 + 3*B*B := by
  let n := r*(2*k+1)
  let P := U n
  let Q := V n
  change U r ∣ (P*A + 3*Q*B) * (P*A + 3*Q*B) + 3*B*B
  have hn : P*P = 3*Q*Q + 1 := by
    have := unit_norm n
    change P*P - 3*Q*Q = 1 at this
    omega
  obtain ⟨t, ht⟩ := (odd_even_dvd r k).1
  change P = U r*t at ht
  refine ⟨t*(P*(A*A + 3*B*B) + 6*A*Q*B), ?_⟩
  calc
    _ = P*(P*A*A + 6*A*Q*B) + (3*Q*Q + 1)*(3*B*B) := by grind
    _ = P*(P*(A*A + 3*B*B) + 6*A*Q*B) := by rw [← hn]; grind
    _ = _ := by
      conv => lhs; arg 1; rw [ht]
      grind

theorem odd_shift_emod (r k : Nat) (A B : Int) :
    ((shift (r*(2*k+1)) A B).1 * (shift (r*(2*k+1)) A B).1) % U r =
      (-3*B*B) % U r := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.dvd_iff_emod_eq_zero.mp
  have hm : (shift (r*(2*k+1)) A B).1 * (shift (r*(2*k+1)) A B).1 - -3*B*B =
      (shift (r*(2*k+1)) A B).1 * (shift (r*(2*k+1)) A B).1 + 3*B*B := by grind
  rw [hm]
  exact odd_shift_dvd r k A B

theorem odd_shift_emod_of_odd (r h : Nat) (A B : Int) (hh : h % 2 = 1) :
    ((shift (r*h) A B).1 * (shift (r*h) A B).1) % U r =
      (-3*B*B) % U r := by
  have he : h = 2*(h/2)+1 := by omega
  conv => lhs; rw [he]
  exact odd_shift_emod r (h/2) A B

end TupleOddShift

namespace TuplePell

private theorem sq_le_sq {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) : a*a ≤ b*b := by
  exact Int.mul_le_mul hab hab ha (by omega)

private theorem descend_three (x y : Int) (hx : 1 < x) (hy : 0 < y)
    (he : y*y - 3*x*x = -2) :
    0 < 2*x-y ∧ 2*x-y < x ∧ 0 < 2*y-3*x ∧
    (2*y-3*x)*(2*y-3*x) - 3*(2*x-y)*(2*x-y) = -2 := by
  have hx2 : 4 ≤ x*x := by simpa using (sq_le_sq (a := 2) (by decide) (by omega : 2 ≤ x))
  have h₁ : y < 2*x := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ 2*x by omega) (show 2*x ≤ y by omega)
    grind
  have h₂ : x < y := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ y by omega) (show y ≤ x by omega)
    grind
  have h₃ : 3*x < 2*y := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ 2*y by omega) (show 2*y ≤ 3*x by omega)
    grind
  refine ⟨by omega, by omega, by omega, ?_⟩
  grind

/-- The orbit of `(1, 1)` under multiplication by `2 + √3`.
    The first coordinate multiplies `√3`. -/
def three : Nat → Int × Int
  | 0 => (1, 1)
  | n+1 => let (x,y) := three n; (2*x+y, 3*x+2*y)

theorem three_complete (x y : Int) (hx : 0 < x) (hy : 0 < y)
    (he : y*y - 3*x*x = -2) : ∃ n, three n = (x,y) := by
  if h : x = 1 then
    subst x
    have hyy : y = 1 := by
      have hh : (y-1)*(y+1) = 0 := by grind
      rcases Int.mul_eq_zero.mp hh with h | h <;> omega
    exact ⟨0, by simp [three, hyy]⟩
  else
    obtain ⟨hx', hlt, hy', he'⟩ := descend_three x y (by omega) hy he
    obtain ⟨n, hn⟩ := three_complete (2*x-y) (2*y-3*x) hx' hy' he'
    refine ⟨n+1, ?_⟩
    simp only [three, hn, Prod.mk.injEq]
    omega
termination_by x.toNat
decreasing_by omega

end TuplePell

namespace TupleSeedOrbit

open TupleOddShift

theorem coeff_pos (n : Nat) : 0 < U n ∧ 0 ≤ V n := by
  induction n with
  | zero => decide
  | succ n ih => rw [U_succ, V_succ]; omega

/-- The fourth power of 2 + √3 is 97 + 56√3, hence 1 modulo 4. -/
theorem U_mod_four (r : Nat) (hr : 4 ∣ r) : (U r).toNat % 4 = 1 := by
  obtain ⟨t, rfl⟩ := hr
  have h : U (4 * t) % 4 = 1 := by
    induction t with
    | zero => decide
    | succ t ih =>
      rw [Nat.mul_succ, (coeff_add _ 4).1]
      have hu : U 4 = 97 := by decide
      have hv : V 4 = 56 := by decide
      rw [hu, hv]
      omega
  have hp := (coeff_pos (4*t)).1
  omega

/-- The tuple recurrence stores the √3 coefficient first. -/
theorem standard_seed (n : Nat) :
    shift n 1 1 = ((TuplePell.three n).2, (TuplePell.three n).1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [shift_succ, ih]
    cases he : TuplePell.three n with
    | mk x y =>
      simp [TuplePell.three, he]
      omega

theorem minus_one_seed (n : Nat) :
    shift (n+1) (-1) 1 = ((TuplePell.three n).2, (TuplePell.three n).1) := by
  rw [shift_add]; exact standard_seed n

theorem minus_three_seed (n : Nat) :
    shift (n+3) (-19) 11 = ((TuplePell.three n).2, (TuplePell.three n).1) := by
  rw [shift_add]; exact standard_seed n

theorem plus_two_seed (n : Nat) (hn : 2 ≤ n) :
    shift (n-2) 19 11 = ((TuplePell.three n).2, (TuplePell.three n).1) := by
  have h := shift_add (n-2) 2 1 1
  have ht : n - 2 + 2 = n := by omega
  rw [ht, standard_seed] at h
  exact h.symm

end TupleSeedOrbit

namespace OMA.TupleIndexFactor

theorem twoPart (n : Nat) (hn : 0 < n) :
    ∃ e h : Nat, h % 2 = 1 ∧ n = 2^e * h := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases ho : n % 2 = 1
    · exact ⟨0, n, ho, by simp⟩
    · have hnEq : n = 2 * (n / 2) := by omega
      obtain ⟨e,h,hh,he⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨e+1,h,hh,?_⟩
      calc
        n = 2 * (n / 2) := hnEq
        _ = 2^(e+1) * h := by rw [he, Nat.pow_succ]; ac_rfl

theorem distanceFactor {d j : Nat} (hd : 0 < d) (hj : (4*j) ∣ d) :
    ∃ k h₀ : Nat, 2 ≤ k ∧ h₀ % 2 = 1 ∧ d = 2^k * j * h₀ := by
  obtain ⟨q,hq⟩ := hj
  have hqpos : 0 < q := by
    cases q with
    | zero => simp at hq; omega
    | succ q => omega
  obtain ⟨e,h₀,hh,h⟩ := twoPart q hqpos
  refine ⟨e+2,h₀,by omega,hh,?_⟩
  rw [hq,h,Nat.pow_add]
  change 4*j*(2^e*h₀) = 2^e*4*j*h₀
  ac_rfl

theorem divisorFactor {d j k h₀ g : Nat} (hj : j % 2 = 1)
    (h₀odd : h₀ % 2 = 1) (heq : d = 2^k*j*h₀) (hg : g ∣ j) :
    ∃ h : Nat, h % 2 = 1 ∧ d = (g*2^k)*h := by
  obtain ⟨q,hq⟩ := hg
  have ho : (g % 2 * (q % 2)) % 2 = 1 := by
    rw [← Nat.mul_mod, ← hq]
    exact hj
  have hqodd : q % 2 = 1 := by
    have hzero : q % 2 ≠ 0 := by
      intro hz
      rw [hz, Nat.mul_zero, Nat.zero_mod] at ho
      contradiction
    omega
  refine ⟨q*h₀, ?_, ?_⟩
  · rw [Nat.mul_mod, hqodd, h₀odd]
  · rw [heq,hq]
    ac_rfl

def GoodDistance (d j : Nat) : Prop :=
  ∃ k h₀ : Nat, 2 ≤ k ∧ h₀ % 2 = 1 ∧ d = 2^k*j*h₀ ∧
    ∀ g : Nat, g ∣ j → ∃ h : Nat, h % 2 = 1 ∧ d = (g*2^k)*h

theorem goodDistance {d j : Nat} (hd : 0 < d) (hj : j % 2 = 1) (hdiv : (4*j) ∣ d) :
    GoodDistance d j := by
  obtain ⟨k,h₀,hk,ho,heq⟩ := distanceFactor hd hdiv
  exact ⟨k,h₀,hk,ho,heq,fun _ hg => divisorFactor hj ho heq hg⟩

theorem seedZero {n : Nat} (hn : 3 ≤ n) (hm : n % 12 = 0) :
    GoodDistance n 3 := by
  apply goodDistance (by omega) (by decide)
  exact Nat.dvd_iff_mod_eq_zero.mpr hm

theorem seedNegOne {n : Nat} (hm : n % 12 = 11) :
    GoodDistance (n+1) 3 := by
  apply goodDistance (by omega) (by decide)
  apply Nat.dvd_iff_mod_eq_zero.mpr
  omega

theorem seedTwo {n : Nat} (hn : 3 ≤ n) (hm : n % 60 = 2) :
    GoodDistance (n-2) 15 := by
  apply goodDistance (by omega) (by decide)
  apply Nat.dvd_iff_mod_eq_zero.mpr
  omega

theorem seedNegThree {n : Nat} (hm : n % 60 = 57) :
    GoodDistance (n+3) 15 := by
  apply goodDistance (by omega) (by decide)
  apply Nat.dvd_iff_mod_eq_zero.mpr
  omega

/-- The seed is encoded by plus and minus, with integer value minus - plus.
Its distance satisfies n + plus = minus + d. -/
theorem selectSeed {n : Nat} (hn : 3 ≤ n)
    (h : n % 12 = 0 ∨ n % 12 = 11 ∨ n % 60 = 2 ∨ n % 60 = 57) :
    ∃ plus minus d j B : Nat,
      n + plus = minus + d ∧ GoodDistance d j ∧
      ((plus = 0 ∧ minus = 0 ∧ j = 3 ∧ B = 1) ∨
       (plus = 1 ∧ minus = 0 ∧ j = 3 ∧ B = 1) ∨
       (plus = 0 ∧ minus = 2 ∧ j = 15 ∧ B = 11) ∨
       (plus = 3 ∧ minus = 0 ∧ j = 15 ∧ B = 11)) := by
  rcases h with hm | hm | hm | hm
  · exact ⟨0,0,n,3,1,by omega,seedZero hn hm,Or.inl (by decide)⟩
  · exact ⟨1,0,n+1,3,1,by omega,seedNegOne hm,Or.inr (Or.inl (by decide))⟩
  · exact ⟨0,2,n-2,15,11,by omega,seedTwo hn hm,Or.inr (Or.inr (Or.inl (by decide)))⟩
  · exact ⟨3,0,n+3,15,11,by omega,seedNegThree hm,Or.inr (Or.inr (Or.inr (by decide)))⟩

end OMA.TupleIndexFactor

namespace TupleInitialSieve

private def residuePair (p : ℕ) : ℕ → ZMod p × ZMod p
  | 0 => (1, 1)
  | n + 1 =>
      let (x, y) := residuePair p n
      (2*x+y, 3*x+2*y)

private theorem residuePair_eq (p n : ℕ) :
    residuePair p n = (((TuplePell.three n).1 : ZMod p), ((TuplePell.three n).2 : ZMod p)) := by
  induction n with
  | zero => simp [residuePair, TuplePell.three]
  | succ n ih => simp [residuePair, TuplePell.three, ih]

private theorem periodic (p : ℕ) (h : residuePair p 120 = residuePair p 0) (n : ℕ) :
    residuePair p (n + 120) = residuePair p n := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [show n + 1 + 120 = (n + 120) + 1 by omega]
      change (let (x, y) := residuePair p (n + 120); (2*x+y, 3*x+2*y)) =
        (let (x, y) := residuePair p n; (2*x+y, 3*x+2*y))
      rw [ih]

private theorem reduceIndex (p : ℕ) (h : residuePair p 120 = residuePair p 0) (n : ℕ) :
    residuePair p n = residuePair p (n % 120) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn : n < 120
      · rw [Nat.mod_eq_of_lt hn]
      · have hp := periodic p h (n - 120)
        rw [show n - 120 + 120 = n by omega] at hp
        rw [hp, ih (n - 120) (by omega), show (n - 120) % 120 = n % 120 by omega]

/-- Binary powering with enough fuel to handle the four sieve exponents. -/
private def powBits {R : Type} [Monoid R] : ℕ → R → ℕ → R
  | 0, _, _ => 1
  | fuel + 1, a, n =>
      let b := powBits fuel (a*a) (n/2)
      if n % 2 = 0 then b else a*b

private theorem powBits_eq {R : Type} [Monoid R] (fuel : ℕ) (a : R) (n : ℕ)
    (hn : n < 2 ^ fuel) : powBits fuel a n = a ^ n := by
  induction fuel generalizing a n with
  | zero =>
      have : n = 0 := by simpa using hn
      subst n
      simp [powBits]
  | succ fuel ih =>
      rw [pow_succ] at hn
      have hhalf : n/2 < 2^fuel := by omega
      simp only [powBits, ih _ _ hhalf, ← pow_two a, ← pow_mul]
      split
      · congr 1
        omega
      · calc
          a * a ^ (2 * (n / 2)) = a ^ (1 + 2 * (n / 2)) := by rw [pow_add, pow_one]
          _ = a ^ n := by congr 1; omega

private def radicand (p n : ℕ) : ZMod p :=
  let x := (residuePair p n).1
  8*x*x-7

private def passes (p n : ℕ) : Prop :=
  radicand p n = 0 ∨ powBits 16 (radicand p n) ((p-1)/2) = 1

private instance (p n : ℕ) : Decidable (passes p n) := by
  unfold passes
  infer_instance

private theorem square_passes (p n : ℕ) (z : ℤ) (hp : p.Prime)
    (hodd : (p - 1) % 2 = 0) (hsize : (p - 1) / 2 < 2^16)
    (he : 8*(TuplePell.three n).1*(TuplePell.three n).1-7 = z*z) :
    passes p n := by
  let : Fact p.Prime := ⟨hp⟩
  have hr : radicand p n = (z : ZMod p) * (z : ZMod p) := by
    rw [radicand, residuePair_eq]
    have hc := congrArg (fun a : ℤ => (a : ZMod p)) he
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat] using hc
  unfold passes
  by_cases hz : (z : ZMod p) = 0
  · left
    simp [hr, hz]
  · right
    rw [powBits_eq _ _ _ hsize, hr, ← pow_two, ← pow_mul,
      show 2 * ((p - 1) / 2) = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hz

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem check120 : ∀ r : Fin 120,
    passes 61 r.val → passes 241 r.val → passes 1201 r.val → passes 37441 r.val →
    r.val % 12 = 0 ∨ r.val % 12 = 11 ∨ r.val % 60 = 2 ∨ r.val % 60 = 57 := by
  decide +kernel

private theorem pass_of_square (p n : ℕ) (z : ℤ) (hp : p.Prime)
    (hodd : (p - 1) % 2 = 0) (hsize : (p - 1) / 2 < 2^16)
    (hperiod : residuePair p 120 = residuePair p 0)
    (he : 8*(TuplePell.three n).1*(TuplePell.three n).1-7 = z*z) :
    passes p (n % 120) := by
  have h := square_passes p n z hp hodd hsize he
  unfold passes radicand at h ⊢
  rw [← reduceIndex p hperiod n]
  exact h

/-- The square condition for the orbit modulo 61, 241, 1201 and 37441. -/
theorem index_residues (n : ℕ) (z : ℤ)
    (he : 8*(TuplePell.three n).1*(TuplePell.three n).1-7 = z*z) :
    n % 12 = 0 ∨ n % 12 = 11 ∨ n % 60 = 2 ∨ n % 60 = 57 := by
  have h := check120 ⟨n % 120, by omega⟩
    (pass_of_square 61 n z (by norm_num) (by decide) (by decide) (by decide +kernel) he)
    (pass_of_square 241 n z (by norm_num) (by decide) (by decide) (by decide +kernel) he)
    (pass_of_square 1201 n z (by norm_num) (by decide) (by decide) (by decide +kernel) he)
    (pass_of_square 37441 n z (by norm_num) (by decide) (by decide) (by decide +kernel) he)
  simpa only [show n % 120 % 12 = n % 12 by omega,
    show n % 120 % 60 = n % 60 by omega] using h

end TupleInitialSieve

namespace TupleSquareObstruction

/-- If a Jacobi symbol is `-1`, changing the order and negating the numerator
preserves the obstruction when the new denominator is `1` modulo `4`. -/
theorem not_isSquare_of_jacobi {S : ℤ} {U β : ℕ}
    (hU : U % 4 = 1) (hβ : Odd β)
    (hS : S ≡ -(β : ℤ) [ZMOD (U : ℤ)])
    (hJ : jacobiSym (U : ℤ) β = -1) :
    ¬ IsSquare S := by
  have hUodd : Odd U := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hU)
  have hJ' : jacobiSym S U = -1 := by
    rw [jacobiSym.mod_left' hS, jacobiSym.neg _ hUodd, ZMod.χ₄_nat_one_mod_four hU, one_mul,
      ← jacobiSym.quadratic_reciprocity_one_mod_four hU hβ]
    exact hJ
  intro hsq
  obtain ⟨t, ht⟩ := hsq
  rw [ht, jacobiSym.mul_left] at hJ'
  exact (by decide : ¬ (0 : ℤ) ≤ -1)
    (hJ' ▸ mul_self_nonneg (jacobiSym t U))

/-- Congruence of the squared Pell coordinate induces the congruence used
in the Jacobi obstruction. -/
theorem constrained_modEq {A B : ℤ} {U : ℕ}
    (h : A ^ 2 ≡ -3 * B ^ 2 [ZMOD (U : ℤ)]) :
    24 * A ^ 2 - 15 ≡ -(72 * B ^ 2 + 15) [ZMOD (U : ℤ)] := by
  convert (h.mul_left 24).add_right (-15) using 1 <;> ring

end TupleSquareObstruction

namespace TupleJacobiTable

private def state (b : Nat) (a : Int) : Nat → Int
  | 0 => a % b
  | k+1 => (2 * state b a k ^ 2 - 1) % b

private theorem state_reduces (b : Nat) (a : Int) (t : Nat)
    (ht : 0 < t) (hclose : state b a (2+t) = state b a 2) (k : Nat) :
    state b a (k+2) = state b a (k%t+2) := by
  have hshift (j : Nat) : state b a (j+2+t) = state b a (j+2) := by
    induction j with
    | zero => simpa using hclose
    | succ j ih =>
      rw [show j+1+2+t = j+2+t+1 by omega, show j+1+2 = j+2+1 by omega, state, state, ih]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    if hk : k < t then
      rw [Nat.mod_eq_of_lt hk]
    else
      have hkt : k-t < k := by omega
      have he : k-t+2+t = k+2 := by omega
      have hm : (k-t)%t = k%t := by
        simpa only [Nat.add_mod_right] using congrArg (· % t) (Nat.sub_add_cancel (Nat.le_of_not_gt hk))
      calc
        _ = state b a (k-t+2+t) := by rw [he]
        _ = state b a (k-t+2) := hshift _
        _ = state b a ((k-t)%t+2) := ih (k-t) hkt
        _ = _ := by rw [hm]

private theorem state_of_coeff (U : Nat → Int) (hdouble : ∀ r, U (2*r) = 2*U r^2-1)
    (b g k : Nat) : U (g * 2^k) % b = state b (U g) k := by
  induction k with
  | zero => simp [state]
  | succ k ih =>
    have he : g * 2^(k+1) = 2 * (g * 2^k) := by rw [pow_succ]; ring
    rw [he, hdouble, state, ← ih]
    exact ((((Int.mod_modEq (U (g * 2^k)) b).symm.pow 2).mul_left 2).sub_right 1)

private theorem table87 (r : Fin 4) :
    jacobiSym (state 87 2 (r.val+2)) 87 = -1 ∨
    jacobiSym (state 87 26 (r.val+2)) 87 = -1 := by
  fin_cases r <;> norm_num [state]

set_option maxHeartbeats 2000000 in
private theorem table8727 (r : Fin 48) :
    jacobiSym (state 8727 2 (r.val+2)) 8727 = -1 ∨
    jacobiSym (state 8727 26 (r.val+2)) 8727 = -1 ∨
    jacobiSym (state 8727 362 (r.val+2)) 8727 = -1 ∨
    jacobiSym (state 8727 189750626 (r.val+2)) 8727 = -1 := by
  fin_cases r <;> norm_num [state]

private theorem lift_choice (U : Nat → Int) (hdouble : ∀ r, U (2*r) = 2*U r^2-1)
    (b g t j : Nat) (v : Int) (hv : U g = v) (ht : 0 < t)
    (hclose : state b v (2+t) = state b v 2)
    (h : jacobiSym (state b v (j%t+2)) b = -1) :
    jacobiSym (U (g*2^(j+2))) b = -1 := by
  rw [jacobiSym.mod_left, state_of_coeff U hdouble b g (j+2), hv,
    state_reduces b v t ht hclose]
  exact h

/-- For every doubling index at least two, one of the two odd multipliers
gives Jacobi symbol minus one modulo 87. -/
theorem jacobi87 (U : Nat → Int) (hdouble : ∀ r, U (2*r) = 2*U r^2-1)
    (h₁ : U 1 = 2) (h₃ : U 3 = 26) (k : Nat) (hk : 2 ≤ k) :
    jacobiSym (U (1*2^k)) 87 = -1 ∨ jacobiSym (U (3*2^k)) 87 = -1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
  rcases table87 ⟨j%4, Nat.mod_lt _ (by decide)⟩ with h | h
  · exact Or.inl (lift_choice U hdouble 87 1 4 j 2 h₁ (by decide) (by decide) h)
  · exact Or.inr (lift_choice U hdouble 87 3 4 j 26 h₃ (by decide) (by decide) h)

set_option maxRecDepth 10000 in
/-- For every doubling index at least two, one of the four odd multipliers
gives Jacobi symbol minus one modulo 8727. -/
theorem jacobi8727 (U : Nat → Int) (hdouble : ∀ r, U (2*r) = 2*U r^2-1)
    (h₁ : U 1 = 2) (h₃ : U 3 = 26) (h₅ : U 5 = 362) (h₁₅ : U 15 = 189750626)
    (k : Nat) (hk : 2 ≤ k) :
    jacobiSym (U (1*2^k)) 8727 = -1 ∨ jacobiSym (U (3*2^k)) 8727 = -1 ∨
    jacobiSym (U (5*2^k)) 8727 = -1 ∨ jacobiSym (U (15*2^k)) 8727 = -1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
  rcases table8727 ⟨j%48, Nat.mod_lt _ (by decide)⟩ with h | h | h | h
  · exact Or.inl (lift_choice U hdouble 8727 1 48 j 2 h₁ (by decide) (by decide) h)
  · exact Or.inr (Or.inl (lift_choice U hdouble 8727 3 48 j 26 h₃ (by decide) (by decide) h))
  · exact Or.inr (Or.inr (Or.inl (lift_choice U hdouble 8727 5 48 j 362 h₅
      (by decide) (by decide) h)))
  · exact Or.inr (Or.inr (Or.inr (lift_choice U hdouble 8727 15 48 j 189750626 h₁₅
      (by decide) (by decide) h)))

private theorem coeff_double (r : Nat) : TupleOddShift.U (2*r) = 2*TupleOddShift.U r^2-1 := by
  rw [show 2*r = r+r by omega, (TupleOddShift.coeff_add r r).1]
  have h := TupleOddShift.unit_norm r
  grind

theorem coeff87 (k : Nat) (hk : 2 ≤ k) :
    jacobiSym (TupleOddShift.U (1*2^k)) 87 = -1 ∨
    jacobiSym (TupleOddShift.U (3*2^k)) 87 = -1 :=
  jacobi87 TupleOddShift.U coeff_double (by decide) (by decide) k hk

theorem coeff8727 (k : Nat) (hk : 2 ≤ k) :
    jacobiSym (TupleOddShift.U (1*2^k)) 8727 = -1 ∨
    jacobiSym (TupleOddShift.U (3*2^k)) 8727 = -1 ∨
    jacobiSym (TupleOddShift.U (5*2^k)) 8727 = -1 ∨
    jacobiSym (TupleOddShift.U (15*2^k)) 8727 = -1 :=
  jacobi8727 TupleOddShift.U coeff_double (by decide) (by decide) (by decide) (by decide) k hk


end TupleJacobiTable

/-!
An elementary proof of the Baker–Davenport tuple theorem, using the constrained
Pell method of K. S. Kedlaya, Mathematics of Computation 67 (1998), 833–842,
sections 3, 4 and 6. The finite sieve and Jacobi certificates are for {1,3,8}.
-/

namespace TupleElementary

open TupleOddShift TupleSeedOrbit OMA.TupleIndexFactor

private theorem four_dvd_index (g k : ℕ) (hk : 2 ≤ k) : 4 ∣ g*2^k := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t+2 := ⟨k-2, by omega⟩
  refine ⟨g*2^t, ?_⟩
  rw [pow_add]
  change g*(2^t*4) = 4*(g*2^t)
  ac_rfl

private theorem exclude_seed (len j β : ℕ) (A B y : ℤ)
    (hseed : (shift len A B).1 = y)
    (hsquare : IsSquare (24*y^2-15))
    (hβ : Odd β) (hvalue : (β : ℤ) = 72*B^2+15)
    (hdist : GoodDistance len j)
    (htable : ∀ k : ℕ, 2 ≤ k → ∃ g : ℕ, g ∣ j ∧ jacobiSym (U (g*2^k)) β = -1) :
    False := by
  obtain ⟨k, _, hk, _, _, hfactors⟩ := hdist
  obtain ⟨g, hg, hJ⟩ := htable k hk
  obtain ⟨h, hodd, hlen⟩ := hfactors g hg
  let r := g*2^k
  have hfour := U_mod_four r (four_dvd_index g k hk)
  have hcast : ((U r).toNat : ℤ) = U r := Int.toNat_of_nonneg (coeff_nonneg r).1.le
  have horbit := odd_shift_emod_of_odd r h A B hodd
  rw [← hlen, hseed] at horbit
  have hA : y^2 ≡ -3*B^2 [ZMOD ((U r).toNat : ℤ)] := by
    rw [hcast]
    simpa [Int.ModEq, pow_two, mul_assoc] using horbit
  have hc := TupleSquareObstruction.constrained_modEq hA
  rw [← hvalue] at hc
  exact TupleSquareObstruction.not_isSquare_of_jacobi hfour hβ hc (hcast.symm ▸ hJ) hsquare

private theorem table_small (k : ℕ) (hk : 2 ≤ k) :
    ∃ g : ℕ, g ∣ 3 ∧ jacobiSym (U (g*2^k)) 87 = -1 := by
  rcases TupleJacobiTable.coeff87 k hk with h | h
  · exact ⟨1, by decide, h⟩
  · exact ⟨3, by decide, h⟩

private theorem table_large (k : ℕ) (hk : 2 ≤ k) :
    ∃ g : ℕ, g ∣ 15 ∧ jacobiSym (U (g*2^k)) 8727 = -1 := by
  rcases TupleJacobiTable.coeff8727 k hk with h | h | h | h
  · exact ⟨1, by decide, h⟩
  · exact ⟨3, by decide, h⟩
  · exact ⟨5, by decide, h⟩
  · exact ⟨15, by decide, h⟩

/-- Only the first and third terms of the first positive Pell orbit can meet the
second square equation. -/
theorem only_indices (n : ℕ) (x y z : ℤ) (hn : TuplePell.three n = (x,y))
    (hy : y*y - 3*x*x = -2) (hz : z*z = 8*x*x-7) :
    n = 0 ∨ n = 2 := by
  have he : 8*(TuplePell.three n).1*(TuplePell.three n).1-7 = z*z := by rw [hn]; exact hz.symm
  have hs := TupleInitialSieve.index_residues n z he
  by_contra! h
  have h3 : 3 ≤ n := by omega
  have hsq : IsSquare (24*y^2-15) := ⟨3*z, by nlinarith [hy, hz]⟩
  rcases hs with hs | hs | hs | hs
  · exact exclude_seed n 3 87 1 1 y (by rw [standard_seed, hn]) hsq (by decide)
      (by decide) (seedZero h3 hs) table_small
  · exact exclude_seed (n+1) 3 87 (-1) 1 y (by rw [minus_one_seed, hn]) hsq (by decide)
      (by decide) (seedNegOne hs) table_small
  · exact exclude_seed (n-2) 15 8727 19 11 y (by rw [plus_two_seed n (by omega), hn]) hsq
      (by decide) (by decide) (seedTwo h3 hs) table_large
  · exact exclude_seed (n+3) 15 8727 (-19) 11 y (by rw [minus_three_seed, hn]) hsq
      (by decide) (by decide) (seedNegThree hs) table_large

/-- The complete integer square-condition classification. -/
theorem unique_extension (d x y z : ℤ) (hx : 0 < x) (hy : 0 < y)
    (hdx : d+1=x*x) (hdy : 3*d+1=y*y) (hdz : 8*d+1=z*z) : d=0 ∨ d=120 := by
  have he : y*y-3*x*x = -2 := by linarith
  obtain ⟨n, horbit⟩ := TuplePell.three_complete x y hx hy he
  rcases only_indices n x y z horbit he (by linarith) with rfl | rfl
  · have hh := congrArg Prod.fst horbit
    change 1 = x at hh
    rw [← hh] at hdx
    omega
  · have hh := congrArg Prod.fst horbit
    change 11 = x at hh
    rw [← hh] at hdx
    omega

end TupleElementary

namespace TupleTargetAdapter

open DiophantineTuple

private theorem base_tuple : IsIntegralDiophantineTuple {1, 3, 8} := by
  norm_num [IsDiophantineTuple]

private theorem regular_value : regularExtension 1 3 8 = 120 := by
  unfold regularExtension
  decide +kernel

theorem of_integer_squares
    (integer_unique : ∀ (d x y z : ℤ), 0 < x → 0 < y →
      d + 1 = x*x → 3*d + 1 = y*y → 8*d + 1 = z*z → d = 0 ∨ d = 120) :
    HasUniqueExtension 1 3 8 := by
  refine ⟨base_tuple, ?_⟩
  intro d htuple hd
  have hlarge : 8 < d := by simpa using hd
  have hmem : d ∈ ({1, 3, 8, d} : Finset ℕ) := by simp
  have h₁ : IsSquare (d + 1) := by
    simpa only [one_mul] using htuple.2 1 (by simp) d hmem (by omega)
  have h₃ := htuple.2 3 (by simp) d hmem (by omega)
  have h₈ := htuple.2 8 (by simp) d hmem (by omega)
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₃
  obtain ⟨z, hz⟩ := h₈
  have hxp : 0 < (x : ℤ) := by
    have h : x ≠ 0 := fun h => by simp [h] at hx
    omega
  have hyp : 0 < (y : ℤ) := by
    have h : y ≠ 0 := fun h => by subst y; omega
    omega
  have hu := integer_unique d x y z hxp hyp (by exact_mod_cast hx)
    (by exact_mod_cast hy) (by exact_mod_cast hz)
  rw [regular_value]
  omega

end TupleTargetAdapter

theorem OMA.solution : type_of% @DiophantineTuple.hasUniqueExtension_of_1_3_8 :=
  TupleTargetAdapter.of_integer_squares TupleElementary.unique_extension
