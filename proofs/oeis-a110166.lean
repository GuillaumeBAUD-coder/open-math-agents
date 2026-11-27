import OMAStatements.S_oeis_a110166

-- Credit: @hehz2020
/-!
# The coefficient formula and recurrence for OEIS A110166

The coefficient of degree n in (1 + (k-2)X + X²)^n counts words with
equally many zeros and ones. Swapping those two letters pairs the words
on the two strict sides of the inequality. This reduces both assertions
to identities for the central coefficient of a quadratic polynomial.
-/

open Finset
open scoped BigOperators
namespace WordBalance

private noncomputable def walkPoly (a : ℤ) : Polynomial ℤ :=
  .X ^ 2 + .C a * .X + 1

private noncomputable def ties (a : ℤ) (n : ℕ) : ℤ := ((walkPoly a)^n).coeff n

-- At degree n+2, the coefficient of X Y' - (n+2)Y is zero.
private theorem ties_recurrence (a : ℤ) (n : ℕ) :
    ((n : ℤ)+2) * ties a (n+2) =
      a * (2*(n : ℤ)+3) * ties a (n+1) - (a^2-4)*((n : ℤ)+1)*ties a n := by
  let P := walkPoly a
  let X : Polynomial ℤ := .X
  let C := Polynomial.C (R := ℤ)
  let Y := (X^2-1)*P^(n+1)
  have dP : Polynomial.derivative P = 2*X + C a := by
    simp [P, walkPoly, X, C, Polynomial.derivative_pow_succ]
  have poly : X * Polynomial.derivative Y - C ((n : ℤ)+2)*Y =
      C ((n : ℤ)+2) * P^(n+2) -
        C (a*(2*(n : ℤ)+3)) * (X*P^(n+1)) +
        C ((a^2-4)*((n : ℤ)+1)) * (X^2*P^n) := by
    dsimp only [Y]
    rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
      show Polynomial.derivative (X^2) = 2*X by simp [X, Polynomial.derivative_pow_succ],
      Polynomial.derivative_pow_succ, dP]
    simp only [C, map_add, map_mul, map_sub, map_pow, map_ofNat, map_one, map_natCast,
      sub_zero, show n+2=n+1+1 by omega, pow_succ P]
    dsimp only [P, walkPoly, X]
    ring
  have zeroCoeff :
      (X * Polynomial.derivative Y - C ((n : ℤ)+2)*Y).coeff (n+2) = 0 := by
    simp only [X, C, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
      Polynomial.coeff_derivative, Polynomial.coeff_C_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [poly] at zeroCoeff
  simp only [X, C, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul] at zeroCoeff
  dsimp only [ties, P] at *
  linarith

private noncomputable def invPlus : PowerSeries ℤ :=
  PowerSeries.rescale (-1 : ℤ) (PowerSeries.invOneSubPow ℤ 1).val

private theorem invPlus_coeff (j : ℕ) :
    PowerSeries.coeff (j+1) (invPlus^(j+1)) =
      (-1 : ℤ)^(j+1) * ((j+(j+1)).choose j : ℤ) := by
  have h (m : ℕ) : ((PowerSeries.invOneSubPow ℤ 1).val)^m =
      (PowerSeries.invOneSubPow ℤ m).val := by
    induction m with
    | zero => simp [PowerSeries.invOneSubPow_zero]
    | succ m ih => rw [pow_succ, ih, PowerSeries.invOneSubPow_add]; rfl
  rw [invPlus, ← map_pow, h, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]

private theorem double_choose (s : ℕ) :
    (2*(s+1)).choose (s+1) = 2 * (s+(s+1)).choose s := by
  rw [show 2*(s+1)=(s+(s+1))+1 by omega, Nat.choose_succ_succ]
  have h := Nat.choose_symm (n := s+(s+1)) (k := s) (by omega)
  rw [show s+(s+1)-s=s+1 by omega] at h
  rw [h]
  omega

private theorem poly_term (B : Polynomial ℤ) (k : ℤ) (n j : ℕ) (h : j ≤ n) :
    (B^j * (Polynomial.C k * Polynomial.X)^(n-j) * (n.choose j : Polynomial ℤ)).coeff n =
      (n.choose j : ℤ)*k^(n-j)*(B^j).coeff j := by
  have he : B^j * (Polynomial.C k * Polynomial.X)^(n-j) * (n.choose j : Polynomial ℤ) =
      Polynomial.C ((n.choose j : ℤ)*k^(n-j)) * (B^j*Polynomial.X^(n-j)) := by
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [he, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow', if_pos (by omega),
    show n-(n-j)=j by omega]

private theorem series_term (B : PowerSeries ℤ) (k : ℤ) (n j : ℕ) (h : j ≤ n) :
    PowerSeries.coeff n (B^j * (PowerSeries.C k * PowerSeries.X)^(n-j) *
      (n.choose j : PowerSeries ℤ)) = (n.choose j : ℤ)*k^(n-j)*PowerSeries.coeff j (B^j) := by
  have he : B^j * (PowerSeries.C k * PowerSeries.X)^(n-j) * (n.choose j : PowerSeries ℤ) =
      PowerSeries.C ((n.choose j : ℤ)*k^(n-j)) * (B^j*PowerSeries.X^(n-j)) := by
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [he, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', if_pos (by omega),
    show n-(n-j)=j by omega]

-- Expand both powers around kX. Their middle binomial coefficients differ
-- by a factor of two at every positive index.
private theorem compare_coeff (k : ℤ) (n : ℕ) :
    2 * PowerSeries.coeff n ((PowerSeries.C k * PowerSeries.X + invPlus)^n) =
      k^n + ties (k-2) n := by
  let B := (Polynomial.X + Polynomial.C (-1 : ℤ))^2
  have hp : walkPoly (k-2) = B + Polynomial.C k * Polynomial.X := by
    simp only [walkPoly, B, map_sub, map_ofNat, map_neg, map_one]
    ring
  have ht (j : ℕ) : (B^j).coeff j = (-1 : ℤ)^j*((2*j).choose j : ℤ) := by
    rw [show B^j = (Polynomial.X+Polynomial.C (-1 : ℤ))^(2*j) by exact (pow_mul _ _ _).symm,
      Polynomial.coeff_X_add_C_pow, show 2*j-j=j by omega]
  rw [add_comm (PowerSeries.C k * PowerSeries.X), add_pow, map_sum, Finset.mul_sum]
  simp only [ties, hp, add_pow, Polynomial.finsetSum_coeff]
  have extra : k^n = ∑ j ∈ range (n+1), if j=0 then k^n else 0 := by simp
  rw [extra, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h : j ≤ n := by simpa using hj
  rw [series_term _ _ _ _ h, poly_term _ _ _ _ h, ht]
  cases j with
  | zero => simp [two_mul]
  | succ s =>
    rw [invPlus_coeff, double_choose]
    simp only [Nat.succ_ne_zero, if_false, zero_add, Nat.cast_mul, Nat.cast_ofNat]
    ring

open OMA.S_oeis_a110166

-- Shift each step by one to keep the word generating polynomial ordinary.
private def letter {k : ℕ} (d : Fin k) : ℕ :=
  if d.val = 0 then 2 else if d.val = 1 then 0 else 1

private def weight {n k : ℕ} (w : Fin n → Fin k) : ℕ := ∑ i, letter (w i)

private theorem weight_counts {n k : ℕ} (w : Fin n → Fin k) :
    weight w + occurrences w 1 = n + occurrences w 0 := by
  unfold weight occurrences
  simp only [Finset.card_filter]
  calc
    _ = ∑ i, (letter (w i) + if (w i).val = 1 then 1 else 0) := (Finset.sum_add_distrib).symm
    _ = ∑ i, (1 + if (w i).val = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [letter]
      split_ifs <;> omega
    _ = _ := by simp [Finset.sum_add_distrib]

private theorem generating_letter (q : ℕ) :
    (∑ i : Fin (q+2), (Polynomial.X : Polynomial ℤ)^letter i) = walkPoly q := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [letter, walkPoly, Fin.succ, nsmul_eq_mul, add_comm, add_left_comm, add_assoc]

private theorem tie_count (q n : ℕ) :
    ties q n = ∑ w : Fin n → Fin (q+2), if occurrences w 1 = occurrences w 0 then (1 : ℤ) else 0 := by
  have g := Fintype.prod_sum (fun (_ : Fin n) (d : Fin (q+2)) => (Polynomial.X : Polynomial ℤ)^letter d)
  simp only [generating_letter, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum] at g
  unfold ties
  rw [g, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro w _
  rw [Polynomial.coeff_X_pow]
  have h := weight_counts w
  change (if n = weight w then (1 : ℤ) else 0) = _
  split_ifs <;> omega

-- Pair a word with the word obtained by interchanging zero and one.
private theorem twice_wordCount (q n : ℕ) :
    2 * (wordCount (q+2) n : ℤ) = ((q+2 : ℕ) : ℤ)^n + ties q n := by
  classical
  let z : Fin (q+2) := ⟨0, by omega⟩
  let o : Fin (q+2) := ⟨1, by omega⟩
  let s := Equiv.swap z o
  let e := (Equiv.refl (Fin n)).arrowCongr s
  have swap0 (d : Fin (q+2)) : (s d).val = 0 ↔ d.val = 1 := by
    change (s d).val=z.val ↔ d.val=o.val
    rw [← Fin.ext_iff, ← Fin.ext_iff, ← s.eq_symm_apply]
    simp [s]
  have swap1 (d : Fin (q+2)) : (s d).val = 1 ↔ d.val = 0 := by
    change (s d).val=o.val ↔ d.val=z.val
    rw [← Fin.ext_iff, ← Fin.ext_iff, ← s.eq_symm_apply]
    simp [s]
  have h0 (w : Fin n → Fin (q+2)) : occurrences (e w) 0 = occurrences w 1 := by
    unfold occurrences
    congr 1
    exact Finset.filter_congr fun i _ => swap0 (w i)
  have h1 (w : Fin n → Fin (q+2)) : occurrences (e w) 1 = occurrences w 0 := by
    unfold occurrences
    congr 1
    exact Finset.filter_congr fun i _ => swap1 (w i)
  let A (w : Fin n → Fin (q+2)) : ℤ := if occurrences w 1 ≤ occurrences w 0 then 1 else 0
  have hA : (wordCount (q+2) n : ℤ) = ∑ w, A w := (Finset.sum_boole _ _).symm
  have hK : ((q+2 : ℕ) : ℤ)^n = ∑ _w : Fin n → Fin (q+2), (1 : ℤ) := by simp
  rw [two_mul, hA]
  nth_rw 1 [← e.sum_comp A]
  rw [hK, tie_count,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  simp only [A, h0, h1]
  split_ifs <;> omega

end WordBalance

open WordBalance OMA.S_oeis_a110166

theorem OMA.solution : type_of% @OMA.S_oeis_a110166.main := by
  intro k hk
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, k=q+2 := ⟨k-2, by omega⟩
  let K : ℤ := (q : ℤ)+2
  have h (j : ℕ) : 2*(wordCount (q+2) j : ℤ) = K^j + ties q j := by
    simpa [K] using twice_wordCount q j
  constructor
  · intro n
    have hp := compare_coeff K n
    have he : K-2 = (q : ℤ) := by dsimp [K]; ring
    rw [he] at hp
    have target : (wordCount (q+2) n : ℤ) =
        PowerSeries.coeff n ((PowerSeries.C K * PowerSeries.X + invPlus)^n) := by
      linarith only [hp, h n]
    simpa [series, invPlus, K] using target
  have hzero := h 0
  have hone := h 1
  have tzero : ties q 0 = 1 := by simp [ties]
  have tone : ties q 1 = q := by
    simp [ties, walkPoly, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  rw [tzero, pow_zero] at hzero
  rw [tone, pow_one] at hone
  refine ⟨by omega, ?_, ?_⟩
  · dsimp [K] at hone
    omega
  · intro n
    have ht (j : ℕ) : ties q j = 2*(wordCount (q+2) j : ℤ)-K^j := by
      linarith only [h j]
    have tr := ties_recurrence (q : ℤ) n
    rw [ht, ht, ht] at tr
    have hc : (q : ℤ)^2-4 = K*(K-4) := by dsimp [K]; ring
    rw [hc] at tr
    have hp : ((n : ℤ)+2)*K^(n+2) =
        (q : ℤ)*(2*(n : ℤ)+3)*K^(n+1) - K*(K-4)*((n : ℤ)+1)*K^n + 2*K^(n+1) := by
      simp only [show n+2=n+1+1 by omega, pow_succ]
      dsimp only [K]
      ring
    change ((n : ℤ)+2)*(wordCount (q+2) (n+2) : ℤ) =
      (((q+2 : ℕ) : ℤ)-2)*(2*(n : ℤ)+3)*(wordCount (q+2) (n+1) : ℤ) -
        ((q+2 : ℕ) : ℤ)*(((q+2 : ℕ) : ℤ)-4)*((n : ℤ)+1)*(wordCount (q+2) n : ℤ)
        + ((q+2 : ℕ) : ℤ)^(n+1)
    have castq : ((q+2 : ℕ) : ℤ) = K := by simp [K]
    rw [castq, show K-2=(q:ℤ) by dsimp [K]; ring]
    linarith only [tr, hp]
