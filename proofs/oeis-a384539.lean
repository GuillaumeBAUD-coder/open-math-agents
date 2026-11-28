import OMAStatements.S_oeis_a384539
import Mathlib

-- Credit: @grp06

/-!
OEIS A384539.
Problem and sequence data from The OEIS Foundation Inc. (CC BY-SA 4.0):
https://oeis.org/A384539/internal and https://oeis.org/A384539/b384539.txt
The official Lean statement is credited to Sai-yr.
Middle-split argument and parameter ranges adapted from the task dossier
`library-scout/digit-split-0215/route.md`.
-/

namespace A384539

open OMA.S_oeis_a384539 (term entries)

private theorem decimal_succ (j : ℕ) : (10 : ℕ)^(j+1) = 10*10^j := by
  rw [pow_succ, Nat.mul_comm (10^j) 10]

private theorem quotient_mod {n P L R : ℕ}
    (hp : 0 < P) (hr : R < P) (hn : n = P * L + R) :
    n / P = L ∧ n % P = R := by
  rw [hn, Nat.mul_add_div hp, Nat.mul_add_mod, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr,
    Nat.add_zero]
  exact ⟨rfl, rfl⟩

private theorem suffix_lower {n i : ℕ} (hd : n / 10^i % 10 ≠ 0) :
    10^i ≤ n % (10 * 10^i) := by
  let P := 10^i
  let T := 10 * P
  let L := n / T
  let R := n % T
  let b := R / P
  let D := R % P
  have hp : 0 < P := by dsimp [P]; positivity
  have ht : 0 < T := by dsimp [T]; omega
  have hR : R < T := Nat.mod_lt _ ht
  have hb : b < 10 := (Nat.div_lt_iff_lt_mul hp).2 hR
  have hD : D < P := Nat.mod_lt _ hp
  have hRD : P * b + D = R := Nat.div_add_mod _ _
  have hn : n = P * (10 * L + b) + D := calc
    n = T * L + R := (Nat.div_add_mod _ _).symm
    _ = T * L + (P * b + D) := by rw [hRD]
    _ = P * (10 * L + b) + D := by dsimp [T]; ring
  have hq := (quotient_mod hp hD hn).1
  change n / P % 10 ≠ 0 at hd
  rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hb] at hd
  change P ≤ R
  change b ≠ 0 at hd
  have h := (Nat.le_div_iff_mul_le hp).1 (Nat.pos_of_ne_zero hd)
  simpa only [Nat.one_mul] using h

private theorem prefix_bounds {n i j : ℕ} (hn : n ≠ 0)
    (hl : Nat.log 10 n = i + j) :
    10^j ≤ n / 10^i ∧ n / 10^i < 10 * 10^j := by
  have hp : 0 < (10 : ℕ)^i := by positivity
  constructor
  · apply (Nat.le_div_iff_mul_le hp).2
    rw [Nat.mul_comm, ← pow_add, ← hl]
    exact Nat.pow_log_le_self 10 hn
  · apply (Nat.div_lt_iff_lt_mul hp).2
    calc
      n < 10^(Nat.log 10 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
      _ = (10 * 10^j) * 10^i := by
        rw [hl, pow_succ, pow_add]
        ring

private theorem split_at {n i P L R : ℕ} (ht : term n)
    (hi : i < Nat.log 10 n) (hp : 10^(i+1) = P) (hr : R < P)
    (hn : n = P * L + R) : L ∣ R ∨ R ∣ L := by
  have hp' : 0 < P := by rw [← hp]; positivity
  have h := ht.2.2 i (List.mem_range.mpr hi)
  rw [hp, (quotient_mod hp' hr hn).1, (quotient_mod hp' hr hn).2] at h
  exact h

private theorem bounded_divisor {L S low bound : ℕ}
    (hL : 0 < L) (hlo : low ≤ S) (hhi : L < bound * low) (hd : S ∣ L) :
    ∃ q : ℕ, 0 < q ∧ q < bound ∧ L = q * S := by
  obtain ⟨q, hq⟩ := hd
  have he : L = q * S := by simpa only [Nat.mul_comm S q] using hq
  have hqp : 0 < q := by
    by_contra! h
    have hz : q = 0 := by omega
    simp [hz] at he
    omega
  refine ⟨q, hqp, ?_, he⟩
  by_contra! h
  have h' := Nat.mul_le_mul h hlo
  omega

private theorem shorter_divides {L S : ℕ} (hS : 0 < S) (hlt : S < L)
    (hd : L ∣ S ∨ S ∣ L) : S ∣ L := by
  rcases hd with h | h
  · exact (not_le_of_gt hlt (Nat.le_of_dvd hS h)).elim
  · exact h

private structure EvenData (n C : ℕ) where
  A : ℕ
  B : ℕ
  a : ℕ
  b : ℕ
  D : ℕ
  U : ℕ
  q : ℕ
  r : ℕ
  k : ℕ
  number : n = (10*C)*A + B
  front : A = 10*U + a
  back : B = C*b + D
  Apos : 0 < A
  Bpos : 0 < B
  digitA : 0 < a ∧ a < 10
  digitB : 0 < b ∧ b < 10
  shortBack : C ≤ 10*D
  left : 10*A + b = q*D
  right : (10*C)*a + B = r*U
  qBound : 0 < q ∧ q < 1000
  rBound : 0 < r ∧ r < 1000
  kBound : 0 < k ∧ k < 10
  center : A = k*B ∨ B = k*A
  Aband : C ≤ A ∧ A < 10*C
  Bband : C ≤ B ∧ B < 10*C

private structure OddData (n C : ℕ) where
  A : ℕ
  B : ℕ
  a : ℕ
  b : ℕ
  D : ℕ
  q : ℕ
  r : ℕ
  s : ℕ
  number : n = (10*C)*(10*A+a) + B
  back : B = C*b + D
  Apos : 0 < A
  Bpos : 0 < B
  digitA : 0 < a ∧ a < 10
  digitB : 0 < b ∧ b < 10
  left : 10*A+a = q*B
  right : a*(10*C)+B = r*A
  outer : 10*(10*A+a)+b = s*D
  qBound : 0 < q ∧ q < 100
  rBound : 0 < r ∧ r < 100
  sBound : 0 < s ∧ s < 10000
  Aband : C ≤ A ∧ A < 10*C
  Bband : C ≤ B ∧ B < 10*C

private theorem even_data {n j : ℕ} (hj : 0 < j) (ht : term n)
    (hl : Nat.log 10 n = 2*j+1) : Nonempty (EvenData n (10^j)) := by
  let C := (10 : ℕ)^j
  let W := (10 : ℕ)^(j-1)
  let T := 10*C
  let A := n/T
  let B := n%T
  let U := A/10
  let a := A%10
  let b := B/C
  let D := B%C
  have hc : 0 < C := by dsimp [C]; positivity
  have hw : 0 < W := by dsimp [W]; positivity
  have hJ : j-1+1 = j := by omega
  have hcw : C = 10*W := by
    simpa only [C, W, hJ] using decimal_succ (j-1)
  have htpos : 0 < T := by dsimp [T]; omega
  have hpT : (10 : ℕ)^(j+1) = T := decimal_succ j
  have hpTT : (10 : ℕ)^(j+1+1) = 10*T := by
    calc
      (10 : ℕ)^(j+1+1) = 10*10^(j+1) := decimal_succ (j+1)
      _ = 10*T := congrArg (fun x : ℕ => 10*x) hpT
  have hpC : (10 : ℕ)^(j-1+1) = C := by rw [hJ]
  have hn : n = T*A+B := (Nat.div_add_mod _ _).symm
  have hA : A = 10*U+a := (Nat.div_add_mod _ _).symm
  have hB : B = C*b+D := (Nat.div_add_mod _ _).symm
  have hAt : C ≤ A ∧ A < T := by
    have h := prefix_bounds (i := j+1) (j := j) (show n ≠ 0 from by have := ht.1; omega)
      (show Nat.log 10 n = j+1+j by omega)
    rw [hpT] at h
    exact h
  have hd (i : ℕ) (hi : i ≤ Nat.log 10 n) : n / 10^i % 10 ≠ 0 :=
    ht.2.1 i (List.mem_range.mpr (by omega))
  have hBt : C ≤ B ∧ B < T :=
    ⟨suffix_lower (hd j (by omega)), Nat.mod_lt _ htpos⟩
  have ha0 : a ≠ 0 := by simpa only [a, A, hpT] using hd (j+1) (by omega)
  have ha : 0 < a ∧ a < 10 := ⟨Nat.pos_of_ne_zero ha0, Nat.mod_lt _ (by decide)⟩
  have hb : 0 < b ∧ b < 10 := by
    have h1 : 1 ≤ b := (Nat.le_div_iff_mul_le hc).2 (by simpa only [Nat.one_mul] using hBt.1)
    exact ⟨by omega, (Nat.div_lt_iff_lt_mul hc).2 hBt.2⟩
  have hD : D < C := Nat.mod_lt _ hc
  have hNC : n = C*(10*A+b)+D := calc
    n = T*A+B := hn
    _ = T*A+(C*b+D) := by rw [← hB]
    _ = C*(10*A+b)+D := by dsimp [T]; ring
  have hNCC : n = (10*T)*U + (T*a+B) := calc
    n = T*A+B := hn
    _ = T*(10*U+a)+B := by rw [← hA]
    _ = (10*T)*U + (T*a+B) := by ring
  have hDlo : W ≤ D := by
    have hh := suffix_lower (hd (j-1) (by omega))
    change W ≤ n % (10*W) at hh
    rw [← hcw, (quotient_mod hc hD hNC).2] at hh
    exact hh
  have hUlo : W ≤ U := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < (10 : ℕ))).2
    rw [Nat.mul_comm, ← hcw]
    exact hAt.1
  have hUhi : U < C := by
    change A / 10 < C
    exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa only [T, Nat.mul_comm] using hAt.2)
  have hRlo : T ≤ T*a+B :=
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left T (show 1 ≤ a by omega) :
      T ≤ T*a).trans (Nat.le_add_right _ _)
  have hRhi : T*a+B < 10*T := by
    have h := Nat.mul_le_mul_left T (show a ≤ 9 by omega)
    omega
  have hPlo : C < 10*A+b := by omega
  have hPhi : 10*A+b < 100*C := by dsimp [T] at hAt; omega
  obtain ⟨q, hqp, hqb, hq⟩ := bounded_divisor
    (show 0 < 10*A+b by omega) hDlo
    (show 10*A+b < 1000*W by omega)
    (shorter_divides (show 0 < D by omega) (show D < 10*A+b by omega)
      (split_at ht (i := j-1) (by omega) hpC hD hNC))
  have hright : U ∣ T*a+B ∨ T*a+B ∣ U :=
    split_at ht (i := j+1) (by omega) hpTT hRhi hNCC
  have hUshort : U < T*a+B := hUhi.trans_le
    ((show C ≤ T by change C ≤ 10*C; omega).trans hRlo)
  have hRbound : T*a+B < 1000*W := calc
    T*a+B < 10*T := hRhi
    _ = 1000*W := by change 10*(10*C) = 1000*W; omega
  obtain ⟨r, hrp, hrb, hr⟩ := bounded_divisor
    (htpos.trans_le hRlo) hUlo hRbound
    (shorter_divides (show 0 < U by omega) hUshort hright.symm)
  have hcenter := split_at ht (i := j) (by omega) hpT hBt.2 hn
  have hAp : 0 < A := by have := hAt.1; omega
  have hBp : 0 < B := by have := hBt.1; omega
  obtain ⟨k, hkp, hkb, hk⟩ : ∃ k : ℕ, 0 < k ∧ k < 10 ∧ (A = k*B ∨ B = k*A) := by
    rcases hcenter with h | h
    · obtain ⟨k, hp, hbnd, he⟩ := bounded_divisor hBp hAt.1 hBt.2 h
      exact ⟨k, hp, hbnd, Or.inr he⟩
    · obtain ⟨k, hp, hbnd, he⟩ := bounded_divisor hAp hBt.1 hAt.2 h
      exact ⟨k, hp, hbnd, Or.inl he⟩
  exact ⟨⟨A, B, a, b, D, U, q, r, k, hn, hA, hB, hAp, hBp, ha, hb,
    by omega, hq, hr, ⟨hqp,hqb⟩, ⟨hrp,hrb⟩, ⟨hkp,hkb⟩, hk, hAt, hBt⟩⟩

private theorem odd_data {n j : ℕ} (hj : 0 < j) (ht : term n)
    (hl : Nat.log 10 n = 2*j+2) : Nonempty (OddData n (10^j)) := by
  let C := (10 : ℕ)^j
  let W := (10 : ℕ)^(j-1)
  let T := 10*C
  let E := n/T
  let A := E/10
  let B := n%T
  let a := E%10
  let b := B/C
  let D := B%C
  have hc : 0 < C := by dsimp [C]; positivity
  have hw : 0 < W := by dsimp [W]; positivity
  have hJ : j-1+1 = j := by omega
  have hcw : C = 10*W := by
    simpa only [C, W, hJ] using decimal_succ (j-1)
  have htpos : 0 < T := by dsimp [T]; omega
  have hpT : (10 : ℕ)^(j+1) = T := decimal_succ j
  have hpTT : (10 : ℕ)^(j+1+1) = 10*T := by
    calc
      (10 : ℕ)^(j+1+1) = 10*10^(j+1) := decimal_succ (j+1)
      _ = 10*T := congrArg (fun x : ℕ => 10*x) hpT
  have hpC : (10 : ℕ)^(j-1+1) = C := by rw [hJ]
  have hn : n = T*E+B := (Nat.div_add_mod _ _).symm
  have hE : E = 10*A+a := (Nat.div_add_mod _ _).symm
  have hB : B = C*b+D := (Nat.div_add_mod _ _).symm
  have hAt : C ≤ A ∧ A < T := by
    have h := prefix_bounds (i := j+1+1) (j := j) (show n ≠ 0 from by have := ht.1; omega)
      (show Nat.log 10 n = j+1+1+j by omega)
    rw [hpTT, Nat.mul_comm 10 T, ← Nat.div_div_eq_div_mul] at h
    exact h
  have hd (i : ℕ) (hi : i ≤ Nat.log 10 n) : n / 10^i % 10 ≠ 0 :=
    ht.2.1 i (List.mem_range.mpr (by omega))
  have hBt : C ≤ B ∧ B < T :=
    ⟨suffix_lower (hd j (by omega)), Nat.mod_lt _ htpos⟩
  have ha0 : a ≠ 0 := by simpa only [a, E, hpT] using hd (j+1) (by omega)
  have ha : 0 < a ∧ a < 10 := ⟨Nat.pos_of_ne_zero ha0, Nat.mod_lt _ (by decide)⟩
  have hb : 0 < b ∧ b < 10 := by
    have h1 : 1 ≤ b := (Nat.le_div_iff_mul_le hc).2 (by simpa only [Nat.one_mul] using hBt.1)
    exact ⟨by omega, (Nat.div_lt_iff_lt_mul hc).2 hBt.2⟩
  have hD : D < C := Nat.mod_lt _ hc
  have hNC : n = C*(10*E+b)+D := calc
    n = T*E+B := hn
    _ = T*E+(C*b+D) := by rw [← hB]
    _ = C*(10*E+b)+D := by dsimp [T]; ring
  have hNCC : n = (10*T)*A + (a*T+B) := calc
    n = T*E+B := hn
    _ = T*(10*A+a)+B := by rw [← hE]
    _ = (10*T)*A+(a*T+B) := by ring
  have hDlo : W ≤ D := by
    have hh := suffix_lower (hd (j-1) (by omega))
    change W ≤ n % (10*W) at hh
    rw [← hcw, (quotient_mod hc hD hNC).2] at hh
    exact hh
  have hRlo : T ≤ a*T+B := by
    have h := Nat.mul_le_mul_right T (show 1 ≤ a by omega)
    rw [Nat.one_mul] at h
    exact h.trans (Nat.le_add_right _ _)
  have hRhi : a*T+B < 10*T := by
    have h := Nat.mul_le_mul_right T (show a ≤ 9 by omega)
    omega
  have hElo : T ≤ E := by dsimp [T]; omega
  have hEhi : E < 10*T := by dsimp [T] at hAt ⊢; omega
  have hAp : 0 < A := by have := hAt.1; omega
  have hBp : 0 < B := by have := hBt.1; omega
  obtain ⟨q, hqp, hqb, hq⟩ := bounded_divisor
    (show 0 < E by omega) hBt.1
    (show E < 100*C by dsimp [T] at hEhi; omega)
    (shorter_divides hBp (show B < E by omega)
      (split_at ht (i := j) (by omega) hpT hBt.2 hn))
  have hright : A ∣ a*T+B ∨ a*T+B ∣ A :=
    split_at ht (i := j+1) (by omega) hpTT hRhi hNCC
  have hRbound : a*T+B < 100*C := calc
    a*T+B < 10*T := hRhi
    _ = 100*C := by change 10*(10*C) = 100*C; omega
  obtain ⟨r, hrp, hrb, hr⟩ := bounded_divisor
    (htpos.trans_le hRlo) hAt.1 hRbound
    (shorter_divides hAp (hAt.2.trans_le hRlo) hright.symm)
  have hPlo : C < 10*E+b := by dsimp [T] at hElo; omega
  have hPhi : 10*E+b < 1000*C := by dsimp [T] at hEhi; omega
  obtain ⟨s, hsp, hsb, hs⟩ := bounded_divisor
    (show 0 < 10*E+b by omega) hDlo
    (show 10*E+b < 10000*W by omega)
    (shorter_divides (show 0 < D by omega) (show D < 10*E+b by omega)
      (split_at ht (i := j-1) (by omega) hpC hD hNC))
  rw [hE] at hn hq hs
  exact ⟨⟨A, B, a, b, D, q, r, s, hn, hB, hAp, hBp, ha, hb,
    hq, hr, hs, ⟨hqp,hqb⟩, ⟨hrp,hrb⟩, ⟨hsp,hsb⟩, hAt, hBt⟩⟩

/-! For a sufficiently long block, compare the coefficients of the power of ten. -/

private theorem product_below {x y X Y : ℤ}
    (hx : 0 ≤ x) (hx' : x < X) (hy' : y < Y) (hY : 0 < Y) :
    x*y < X*Y :=
  (mul_le_mul_of_nonneg_left hy'.le hx).trans_lt (mul_lt_mul_of_pos_right hx' hY)

private theorem positive_left {x y z : ℤ}
    (hy : 0 < y) (hz : 0 < z) (h : x*y = z) : 0 < x := by
  by_contra! hx
  have := mul_nonpos_of_nonpos_of_nonneg hx hy.le
  omega

private theorem compare_coefficients {C X a b q r u v : ℤ}
    (hC : 10000000 ≤ C) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hv : 0 < v) (hr : 0 < r)
    (hsmall₁ : a*r*u < 10000000) (hsmall₂ : b*v < 10000000)
    (hU : u*X = b*(q*C+1)) (hV : v*X = a*(100*C+r)) :
    q*r = 100 := by
  have he : (b*q*v - 100*a*u)*C = a*r*u - b*v := by
    linear_combination u*hV - v*hU
  have hpos₁ := mul_pos (mul_pos ha hr) hu
  have hpos₂ := mul_pos hb hv
  have hcoeff : b*q*v - 100*a*u = 0 := by
    rcases lt_trichotomy (b*q*v - 100*a*u) 0 with h | h | h
    · have hle : b*q*v - 100*a*u ≤ -1 := by omega
      have hh := mul_le_mul_of_nonneg_right hle (show 0 ≤ C by omega)
      rw [neg_one_mul] at hh
      omega
    · exact h
    · have hle : 1 ≤ b*q*v - 100*a*u := by omega
      have hh := mul_le_mul_of_nonneg_right hle (show 0 ≤ C by omega)
      rw [one_mul] at hh
      omega
  have hconst : b*v - a*r*u = 0 := by rw [hcoeff, zero_mul] at he; omega
  have hzero : (q*r-100)*(a*u) = 0 := by linear_combination hcoeff - q*hconst
  rcases mul_eq_zero.mp hzero with h | h
  · omega
  · exact (ne_of_gt (mul_pos ha hu) h).elim

private theorem even_algebra {C A B a b D U q r k : ℤ}
    (hC : 10000000 ≤ C) (hA : A = 10*U+a) (hB : B = C*b+D)
    (hAp : 0 < A) (hBp : 0 < B) (ha : 0 < a ∧ a < 10) (hb : 0 < b ∧ b < 10)
    (hD : C ≤ 10*D) (hq : 10*A+b = q*D) (hr : (10*C)*a+B = r*U)
    (hqB : 0 < q ∧ q < 1000) (hrB : 0 < r ∧ r < 1000)
    (hkB : 0 < k ∧ k < 10) (hc : A = k*B ∨ B = k*A) : False := by
  have hCp : 0 < C := by omega
  have hRHS₁ : 0 < b*(q*C+1) := mul_pos hb.1 (by have := mul_pos hqB.1 hCp; omega)
  have hRHS₂ : 0 < a*(100*C+r) := mul_pos ha.1 (by omega)
  have har := product_below ha.1.le ha.2 hrB.2 (by decide)
  rcases hc with hk | hk
  · have hU : (q-10*k)*B = b*(q*C+1) := by linear_combination q*hB - hq + 10*hk
    have hV : (r*k-10)*B = a*(100*C+r) := by linear_combination r*hA - 10*hr - r*hk
    have hu := positive_left hBp hRHS₁ hU
    have hv := positive_left hBp hRHS₂ hV
    have huhi : q-10*k < 1000 := by omega
    have hvhi : r*k-10 < 10000 := by
      have hh := product_below hrB.1.le hrB.2 hkB.2 (by decide)
      omega
    have h₁ : a*r*(q-10*k) < 10000000 := by
      have hh := product_below (mul_pos ha.1 hrB.1).le har huhi (by decide)
      exact hh
    have h₂ : b*(r*k-10) < 10000000 := by
      have hh := product_below hb.1.le hb.2 hvhi (by decide)
      omega
    have he := compare_coefficients hC ha.1 hb.1 hu hv hrB.1 h₁ h₂ hU hV
    have hh := mul_pos hu hrB.1
    nlinarith only [he, hh, hv]
  · have hU : (q*k-10)*A = b*(q*C+1) := by linear_combination q*hB - hq - q*hk
    have hV : (r-10*k)*A = a*(100*C+r) := by linear_combination r*hA - 10*hr + 10*hk
    have hu := positive_left hAp hRHS₁ hU
    have hv := positive_left hAp hRHS₂ hV
    -- The leading digit bounds the left quotient after multiplication by k.
    have hshort : (q*k-10)*D = b*(10*C+k) := by
      linear_combination -k*hq + 10*hB - 10*hk
    have huhi : q*k-10 < 1000 := by
      by_contra! h
      have hDp : 0 < D := by omega
      have hlow := mul_le_mul_of_nonneg_right h hDp.le
      have hbC := mul_le_mul_of_nonneg_right (show b ≤ 9 by omega) hCp.le
      have hbk := mul_le_mul_of_nonneg_right (show b ≤ 9 by omega) hkB.1.le
      nlinarith only [hshort, hD, hC, hkB.2, hlow, hbC, hbk]
    have hvhi : r-10*k < 1000 := by omega
    have h₁ : a*r*(q*k-10) < 10000000 :=
      product_below (mul_pos ha.1 hrB.1).le har huhi (by decide)
    have h₂ : b*(r-10*k) < 10000000 := by
      have hh := product_below hb.1.le hb.2 hvhi (by decide)
      omega
    have he := compare_coefficients hC ha.1 hb.1 hu hv hrB.1 h₁ h₂ hU hV
    have hh := mul_pos hv hqB.1
    nlinarith only [he, hh, hu]

private theorem odd_algebra {C A B a b D q r s : ℤ}
    (hC : 10000000 ≤ C) (hBp : 0 < B)
    (ha : 0 < a ∧ a < 10) (hb : 0 < b ∧ b < 10) (hB : B = C*b+D)
    (hq : 10*A+a = q*B) (hr : a*(10*C)+B = r*A)
    (hs : 10*(10*A+a)+b = s*D)
    (hqB : 0 < q ∧ q < 100) (hrB : 0 < r ∧ r < 100)
    (hsB : 0 < s ∧ s < 10000) : False := by
  have hU : (s-10*q)*B = b*(s*C+1) := by linear_combination s*hB - hs + 10*hq
  have hV : (q*r-10)*B = a*(100*C+r) := by linear_combination -10*hr - r*hq
  have hRHS₁ : 0 < b*(s*C+1) :=
    mul_pos hb.1 (by have := mul_pos hsB.1 (show 0 < C by omega); omega)
  have hRHS₂ : 0 < a*(100*C+r) := mul_pos ha.1 (by omega)
  have hu := positive_left hBp hRHS₁ hU
  have hv := positive_left hBp hRHS₂ hV
  have huhi : s-10*q < 10000 := by omega
  have hvhi : q*r-10 < 10000 := by
    have hh := product_below hqB.1.le hqB.2 hrB.2 (by decide)
    omega
  have har := product_below ha.1.le ha.2 hrB.2 (by decide)
  have h₁ : a*r*(s-10*q) < 10000000 :=
    product_below (mul_pos ha.1 hrB.1).le har huhi (by decide)
  have h₂ : b*(q*r-10) < 10000000 := by
    have hh := product_below hb.1.le hb.2 hvhi (by decide)
    omega
  have he := compare_coefficients hC ha.1 hb.1 hu hv hrB.1 h₁ h₂ hU hV
  have hh := mul_pos hu hrB.1
  nlinarith only [he, hh, hv]

private theorem even_impossible {n C : ℕ} (hC : 10000000 ≤ C)
    (d : EvenData n C) : False := by
  rcases d with ⟨A, B, a, b, D, U, q, r, k, _, hA, hB, hAp, hBp, ha, hb,
    hD, hq, hr, hqb, hrb, hkb, hc, _, _⟩
  zify at hC hA hB hAp hBp ha hb hD hq hr hqb hrb hkb hc
  exact even_algebra hC hA hB hAp hBp ha hb hD hq hr hqb hrb hkb hc

private theorem odd_impossible {n C : ℕ} (hC : 10000000 ≤ C)
    (d : OddData n C) : False := by
  rcases d with ⟨A, B, a, b, D, q, r, s, _, hB, _, hBp, ha, hb,
    hq, hr, hs, hqb, hrb, hsb, _, _⟩
  zify at hC hB hBp ha hb hq hr hs hqb hrb hsb
  exact odd_algebra hC hBp ha hb hB hq hr hs hqb hrb hsb

private theorem parity_index {n : ℕ} (ht : term n) :
    ∃ j, Nat.log 10 n = 2*j+1 ∨ Nat.log 10 n = 2*j+2 := by
  have hpos : 0 < Nat.log 10 n := Nat.log_pos_iff.mpr ⟨ht.1, by decide⟩
  refine ⟨(Nat.log 10 n - 1) / 2, ?_⟩
  omega

private theorem width_bound {n : ℕ} (ht : term n) : Nat.log 10 n ≤ 14 := by
  obtain ⟨j, hj⟩ := parity_index ht
  by_contra! hlarge
  have hj7 : 7 ≤ j := by omega
  have hC : 10000000 ≤ (10 : ℕ)^j :=
    Nat.pow_le_pow_right (show 0 < (10 : ℕ) by decide) hj7
  rcases hj with heven | hodd
  · obtain ⟨d⟩ := even_data (by omega) ht heven
    exact even_impossible hC d
  · obtain ⟨d⟩ := odd_data (by omega) ht hodd
    exact odd_impossible hC d

/-! Reconstruct candidates from the middle-split quotients and check the remaining splits. -/

private theorem solve_product {x y D N : ℕ}
    (hN : 0 < N) (he : x*D = y*D+N) :
    0 < x-y ∧ N % (x-y) = 0 ∧ D = N / (x-y) := by
  have hxy : y < x := by
    by_contra! h
    have hh := Nat.mul_le_mul_right D h
    omega
  have hp : 0 < x-y := by omega
  have hprod : N = (x-y)*D := by rw [Nat.sub_mul]; omega
  refine ⟨hp, ?_, ?_⟩
  · calc
      N % (x-y) = ((x-y)*D) % (x-y) := congrArg (fun M => M % (x-y)) hprod
      _ = 0 := Nat.mul_mod_right _ _
  · calc
      D = ((x-y)*D) / (x-y) := (Nat.mul_div_cancel_left D hp).symm
      _ = N / (x-y) := congrArg (fun M => M / (x-y)) hprod.symm

private def accepted (n : ℕ) : Bool :=
  if term n then decide (n ∈ entries) else true

private theorem accepted_sound {n : ℕ} (h : accepted n = true) (ht : term n) :
    n ∈ entries := by
  unfold accepted at h
  rw [if_pos ht] at h
  exact of_decide_eq_true h

private def checkHalves (C A B n : ℕ) : Bool :=
  if (C ≤ A ∧ A < 10*C) ∧ (C ≤ B ∧ B < 10*C) then accepted n else true

private theorem checkHalves_sound {C A B n : ℕ}
    (hA : C ≤ A ∧ A < 10*C) (hB : C ≤ B ∧ B < 10*C)
    (h : checkHalves C A B n = true) (hn : term n) : n ∈ entries := by
  unfold checkHalves at h
  rw [if_pos ⟨hA, hB⟩] at h
  exact accepted_sound h hn

private def evenOne (C b k q : ℕ) : Bool :=
  let u := q-10*k
  let N := b*(10*C*k+1)
  if 0 < u ∧ N % u = 0 then
    let B := C*b + N/u
    let A := k*B
    checkHalves C A B ((10*C)*A+B)
  else true

private def evenTwo (C b k q : ℕ) : Bool :=
  let u := q*k-10
  let N := b*(10*C+k)
  if 0 < u ∧ N % u = 0 then
    let B := C*b + N/u
    let A := B/k
    checkHalves C A B ((10*C)*A+B)
  else true

private def oddCheck (C a q r : ℕ) : Bool :=
  let v := q*r-10
  let N := a*(q*(10*C)+1)
  let M := a*(100*C+r)
  if 0 < v ∧ N % v = 0 ∧ M % v = 0 then
    let A := N/v
    let B := M/v
    checkHalves C A B ((10*C)*(10*A+a)+B)
  else true

private def scan (blocks width : ℕ) (f : ℕ → Bool) : Bool :=
  (List.range blocks).all fun block =>
    (List.range width).all fun offset => f (width*block+offset)

private theorem scan_sound {blocks width i : ℕ} {f : ℕ → Bool} (hw : 0 < width)
    (hi : i < blocks*width) (hs : scan blocks width f = true) : f i = true := by
  have hb : i / width < blocks := (Nat.div_lt_iff_lt_mul hw).2 hi
  have ho : i % width < width := Nat.mod_lt _ hw
  unfold scan at hs
  have h := List.all_eq_true.mp hs (i/width) (List.mem_range.mpr hb)
  have h' : f (width*(i/width)+i%width) = true :=
    List.all_eq_true.mp h (i%width) (List.mem_range.mpr ho)
  simpa only [Nat.div_add_mod] using h'

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem even_one_small {j b k q : ℕ}
    (hj : 0 < j) (hj' : j < 7) (hb : 0 < b) (hb' : b < 10)
    (hk : k < 10) (hq : q < 1000) : evenOne (10^j) b k q = true := by
  have h : (List.range 10).all (fun k' => scan 20 50 (evenOne (10^j) b k')) = true := by
    interval_cases j <;> interval_cases b <;> decide +kernel
  exact scan_sound (blocks := 20) (width := 50) (by decide) hq
    (List.all_eq_true.mp h k (List.mem_range.mpr hk))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem even_two_small {j b k q : ℕ}
    (hj : 0 < j) (hj' : j < 7) (hb : 0 < b) (hb' : b < 10)
    (hk : k < 10) (hq : q < 1000) : evenTwo (10^j) b k q = true := by
  have h : (List.range 10).all (fun k' => scan 20 50 (evenTwo (10^j) b k')) = true := by
    interval_cases j <;> interval_cases b <;> decide +kernel
  exact scan_sound (blocks := 20) (width := 50) (by decide) hq
    (List.all_eq_true.mp h k (List.mem_range.mpr hk))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem odd_small {j a q r : ℕ}
    (hj : 0 < j) (hj' : j < 7) (ha : 0 < a) (ha' : a < 10)
    (hq : q < 100) (hr : r < 100) : oddCheck (10^j) a q r = true := by
  have h : (List.range 100).all (fun q' => scan 2 50 (oddCheck (10^j) a q')) = true := by
    interval_cases j <;> interval_cases a <;> decide +kernel
  exact scan_sound (blocks := 2) (width := 50) (by decide) hr
    (List.all_eq_true.mp h q (List.mem_range.mpr hq))

private theorem even_entries {n j : ℕ} (hj : 0 < j) (hj' : j < 7)
    (d : EvenData n (10^j)) (ht : term n) : n ∈ entries := by
  let C : ℕ := 10^j
  rcases d.center with hc | hc
  · have he : d.q*d.D = (10*d.k)*d.D + d.b*(10*C*d.k+1) := by
      have hq := d.left
      have hB := d.back
      have hc' := hc
      change d.B = C*d.b+d.D at hB
      zify at hq hB hc' ⊢
      linear_combination -hq + 10*hc' + 10*(d.k : ℤ)*hB
    have hN : 0 < d.b*(10*C*d.k+1) := Nat.mul_pos d.digitB.1 (by omega)
    obtain ⟨hu, hm, hD⟩ := solve_product hN he
    have h := even_one_small hj hj' d.digitB.1 d.digitB.2 d.kBound.2 d.qBound.2
    change evenOne C d.b d.k d.q = true at h
    dsimp only [evenOne] at h
    rw [if_pos ⟨hu, hm⟩, ← hD, ← d.back, ← hc] at h
    have hmemb := checkHalves_sound d.Aband d.Bband h
    rw [← d.number] at hmemb
    exact hmemb ht
  · have he : (d.q*d.k)*d.D = 10*d.D + d.b*(10*C+d.k) := by
      have hq := d.left
      have hB := d.back
      have hc' := hc
      change d.B = C*d.b+d.D at hB
      zify at hq hB hc' ⊢
      linear_combination -(d.k : ℤ)*hq + 10*hB - 10*hc'
    have hN : 0 < d.b*(10*C+d.k) := Nat.mul_pos d.digitB.1 (by have := d.kBound.1; omega)
    obtain ⟨hu, hm, hD⟩ := solve_product hN he
    have hdiv : d.B/d.k = d.A := by
      calc
        d.B/d.k = (d.k*d.A)/d.k := congrArg (fun B => B/d.k) hc
        _ = d.A := Nat.mul_div_cancel_left _ d.kBound.1
    have h := even_two_small hj hj' d.digitB.1 d.digitB.2 d.kBound.2 d.qBound.2
    change evenTwo C d.b d.k d.q = true at h
    dsimp only [evenTwo] at h
    rw [if_pos ⟨hu, hm⟩, ← hD, ← d.back, hdiv] at h
    have hmemb := checkHalves_sound d.Aband d.Bband h
    rw [← d.number] at hmemb
    exact hmemb ht

private theorem odd_entries {n j : ℕ} (hj : 0 < j) (hj' : j < 7)
    (d : OddData n (10^j)) (ht : term n) : n ∈ entries := by
  let C : ℕ := 10^j
  have hA : (d.q*d.r)*d.A = 10*d.A + d.a*(d.q*(10*C)+1) := by
    have hq := d.left
    have hr := d.right
    change d.a*(10*C)+d.B = d.r*d.A at hr
    zify at hq hr ⊢
    linear_combination -(d.q : ℤ)*hr - hq
  have hB : (d.q*d.r)*d.B = 10*d.B + d.a*(100*C+d.r) := by
    have hq := d.left
    have hr := d.right
    change d.a*(10*C)+d.B = d.r*d.A at hr
    zify at hq hr ⊢
    linear_combination -10*hr - (d.r : ℤ)*hq
  have hN : 0 < d.a*(d.q*(10*C)+1) := Nat.mul_pos d.digitA.1 (by omega)
  have hM : 0 < d.a*(100*C+d.r) := Nat.mul_pos d.digitA.1 (by have := d.rBound.1; omega)
  obtain ⟨hv, hmA, heA⟩ := solve_product hN hA
  obtain ⟨_, hmB, heB⟩ := solve_product hM hB
  have h := odd_small hj hj' d.digitA.1 d.digitA.2 d.qBound.2 d.rBound.2
  change oddCheck C d.a d.q d.r = true at h
  dsimp only [oddCheck] at h
  rw [if_pos ⟨hv, hmA, hmB⟩, ← heA, ← heB] at h
  have hmemb := checkHalves_sound d.Aband d.Bband h
  rw [← d.number] at hmemb
  exact hmemb ht

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem base_entries {n : ℕ} (hn : n < 1000) (ht : term n) :
    n ∈ entries := by
  have hs : scan 20 50 accepted = true := by decide +kernel
  exact accepted_sound (scan_sound (blocks := 20) (width := 50) (by decide) hn hs) ht

private theorem entries_complete {n : ℕ} (ht : term n) : n ∈ entries := by
  have hbound := width_bound ht
  obtain ⟨j, hj⟩ := parity_index ht
  have hj' : j < 7 := by omega
  by_cases hj0 : j = 0
  · have hn : n ≠ 0 := by have := ht.1; omega
    have hlog : Nat.log 10 n < 3 := by omega
    have hsmall : n < 10^3 := (Nat.log_lt_iff_lt_pow (by decide) hn).1 hlog
    exact base_entries hsmall ht
  · rcases hj with heven | hodd
    · obtain ⟨d⟩ := even_data (by omega) ht heven
      exact even_entries (by omega) hj' d ht
    · obtain ⟨d⟩ := odd_data (by omega) ht hodd
      exact odd_entries (by omega) hj' d ht

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem entries_sound {n : ℕ} (hn : n ∈ entries) : term n := by
  have hs : entries.all (fun x => decide (term x)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hs n hn)

end A384539

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @OMA.S_oeis_a384539.main := by
  refine ⟨fun n => ⟨A384539.entries_complete, A384539.entries_sound⟩, ?_, ?_⟩
  · decide +kernel
  · decide
