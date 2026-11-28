import OMAStatements.S_oeis_a001108
import Mathlib

/-!
The divisor sum is odd precisely when every odd prime has even exponent.
Thus an odd divisor sum of a triangular number forces it to be square or
2 times a square. The latter would make two positive consecutive integers
both squares. The square triangular numbers are then obtained from the
fundamental Pell solution (3,1) for d = 8.
-/

namespace OMA.SquareTriangularIndices

open ArithmeticFunction Finset

private theorem odd_cast (n : ℕ) : Odd n ↔ (n : ZMod 2) = 1 :=
  Nat.odd_iff.trans (ZMod.natCast_eq_natCast_iff n 1 2).symm

private theorem odd_prod {s : Finset ℕ} {f : ℕ → ℕ} :
    Odd (∏ p ∈ s, f p) ↔ ∀ p ∈ s, Odd (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s h ih => simp [prod_insert h, Nat.odd_mul, ih]

private theorem odd_geom {p : ℕ} (hp : p.Prime) (e : ℕ) :
    Odd (∑ j ∈ range (e+1), p^j) ↔ p=2 ∨ Even e := by
  rw [odd_cast, Nat.cast_sum]
  by_cases h : p=2
  · subst p
    simp [sum_range_succ', show (2 : ZMod 2) = 0 by decide, zero_pow]
  · have hp1 := (odd_cast p).mp (hp.odd_of_ne_two h)
    simp only [Nat.cast_pow, hp1, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, h, false_or]
    rw [← odd_cast, Nat.odd_add_one]
    exact Nat.not_odd_iff_even

private theorem sigma_odd_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (sigma 1 n) ↔ ∀ p : ℕ, p ≠ 2 → Even (n.factorization p) := by
  rw [sigma_one_apply, Nat.sum_divisors hn, odd_prod]
  constructor
  · intro h p hp
    by_cases hmem : p ∈ n.primeFactors
    · exact ((odd_geom (Nat.prime_of_mem_primeFactors hmem) _).mp (h p hmem)).resolve_left hp
    · have hzero : n.factorization p = 0 := by
        have heq := n.support_factorization
        rwa [← heq, Finsupp.notMem_support_iff] at hmem
      simp [hzero]
  · intro h p hp
    apply (odd_geom (Nat.prime_of_mem_primeFactors hp) _).mpr
    by_cases he : p=2
    · exact Or.inl he
    · exact Or.inr (h p he)

private theorem square_iff {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p : ℕ, Even (n.factorization p) := by
  constructor
  · rintro ⟨u, rfl⟩ p
    have hu : u ≠ 0 := by contrapose! hn; simp [hn]
    rw [Nat.factorization_mul hu hu, Finsupp.add_apply]
    exact ⟨_, rfl⟩
  · intro h
    let u := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
    refine ⟨u, ?_⟩
    calc
      n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
        simpa only [Finsupp.prod, Nat.support_factorization] using
          (Nat.prod_factorization_pow_eq_self hn).symm
      _ = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p / 2)) ^ 2 := by
        apply prod_congr rfl
        intro p hp
        have hh := Nat.even_iff.mp (h p)
        rw [← pow_mul, show n.factorization p / 2 * 2 = n.factorization p by omega]
      _ = u ^ 2 := by rw [prod_pow]
      _ = u * u := pow_two u

private theorem odd_sigma_shape {n : ℕ} (hn : n ≠ 0) (h : Odd (sigma 1 n)) :
    IsSquare n ∨ ∃ u : ℕ, n = 2*u^2 := by
  have hex := (sigma_odd_iff hn).mp h
  by_cases h2 : Even (n.factorization 2)
  · exact Or.inl ((square_iff hn).mpr (fun p => by by_cases he : p=2 <;> simp_all))
  have hpos : 1 ≤ n.factorization 2 := by
    by_contra! hh
    have he : n.factorization 2 = 0 := by omega
    simp [he] at h2
  obtain ⟨m, rfl⟩ := (Nat.prime_two.dvd_iff_one_le_factorization hn).mpr hpos
  have hm : m ≠ 0 := by contrapose! hn; simp [hn]
  have hs : IsSquare m := by
    apply (square_iff hm).mpr
    intro p
    by_cases hp : p=2
    · subst p
      rw [Nat.factorization_mul (by decide : 2 ≠ 0) hm, Finsupp.add_apply,
        Nat.prime_two.factorization, Finsupp.single_eq_same] at h2
      simp only [Nat.even_iff] at h2 ⊢
      omega
    · specialize hex p hp
      rwa [Nat.factorization_mul (by decide : 2 ≠ 0) hm, Finsupp.add_apply,
        Nat.prime_two.factorization, Finsupp.single_apply, if_neg (Ne.symm hp), zero_add] at hex
  obtain ⟨u, hu⟩ := hs
  exact Or.inr ⟨u, by rw [pow_two, ← hu]⟩

private def tri (n : ℕ) : ℕ := n*(n+1)/2

private theorem tri_product (n : ℕ) : 2*tri n = n*(n+1) := by
  have h : 2 ∣ n*(n+1) := by
    by_cases hn : 2 ∣ n
    · exact dvd_mul_of_dvd_left hn _
    · exact dvd_mul_of_dvd_right (by omega : 2 ∣ n+1) _
  exact Nat.mul_div_cancel' h

private theorem tri_pos {n : ℕ} (hn : 0<n) : 0 < tri n := by
  have h := tri_product n
  have hm : 0 < n*(n+1) := by positivity
  omega

private theorem factor_product_of_dvd {u v p : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hc : u.Coprime v) (hp : p.Prime) (hd : p ∣ u) :
    (u*v).factorization p = u.factorization p := by
  have hnot : ¬ p ∣ v := by
    intro ht
    have he := Nat.dvd_gcd hd ht
    rw [hc.gcd_eq_one] at he
    exact hp.not_dvd_one he
  rw [Nat.factorization_mul hu hv, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]

private theorem coprime_square_left {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hc : u.Coprime v) (hs : IsSquare (u*v)) : IsSquare u := by
  apply (square_iff hu).mpr
  intro p
  by_cases h : p.Prime ∧ p ∣ u
  · rw [← factor_product_of_dvd hu hv hc h.1 h.2]
    exact (square_iff (mul_ne_zero hu hv)).mp hs p
  · rcases not_and_or.mp h with hp | hd
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    · simp [Nat.factorization_eq_zero_of_not_dvd hd]

private theorem square_tri_iff (n : ℕ) (hn : 0<n) :
    (Odd (sigma 1 n) ∧ Odd (sigma 1 (tri n))) ↔ IsSquare (tri n) := by
  have ht := (tri_pos hn).ne'
  have hc : n.Coprime (n+1) := by simp
  constructor
  · intro h
    rcases odd_sigma_shape ht h.2 with hs | ⟨u, hu⟩
    · exact hs
    · have hs : IsSquare (n*(n+1)) := by
        refine ⟨2*u, ?_⟩
        rw [← tri_product, hu]
        ring
      obtain ⟨a, ha⟩ := coprime_square_left hn.ne' (by omega) hc hs
      have hrev : IsSquare ((n+1)*n) := by simpa only [mul_comm] using hs
      obtain ⟨b, hb⟩ := coprime_square_left (by omega) hn.ne' hc.symm hrev
      have hab : a < b := by
        by_contra! hle
        have hmul : b*b ≤ a*a := Nat.mul_le_mul hle hle
        omega
      have hpos : 1 ≤ a := by
        by_contra! ha0
        have h0 : a=0 := by omega
        rw [h0, zero_mul] at ha
        exact hn.ne' ha
      have hmul : (a+1)*(a+1) ≤ b*b := Nat.mul_le_mul hab hab
      nlinarith
  · intro hs
    have he := (square_iff ht).mp hs
    refine ⟨(sigma_odd_iff hn.ne').mpr ?_, (sigma_odd_iff ht).mpr (fun p _ => he p)⟩
    intro p hp
    by_cases h : p.Prime ∧ p ∣ n
    · rw [← factor_product_of_dvd hn.ne' (by omega) hc h.1 h.2, ← tri_product,
        Nat.factorization_mul (by decide : 2 ≠ 0) ht, Finsupp.add_apply, Nat.prime_two.factorization,
        Finsupp.single_apply, if_neg (Ne.symm hp), zero_add]
      exact he p
    · rcases not_and_or.mp h with hp | hd
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
      · simp [Nat.factorization_eq_zero_of_not_dvd hd]

private def baseSolution : Pell.Solution₁ 8 := Pell.Solution₁.mk 3 1 (by norm_num)

private theorem fundamental : Pell.IsFundamental baseSolution := by
  refine ⟨by decide, by decide, ?_⟩
  intro b hb
  change 3 ≤ b.x
  by_contra! h
  have hx : b.x = 2 := by omega
  have he := b.prop
  rw [hx] at he
  norm_num at he
  omega

private theorem x_step (k : ℕ) :
    (baseSolution^(k+1)).x = 3*(baseSolution^k).x + 8*(baseSolution^k).y := by
  rw [pow_succ, Pell.Solution₁.x_mul]
  simp only [baseSolution, Pell.Solution₁.x_mk, Pell.Solution₁.y_mk, mul_one]
  ring

private theorem y_step (k : ℕ) :
    (baseSolution^(k+1)).y = (baseSolution^k).x + 3*(baseSolution^k).y := by
  rw [pow_succ, Pell.Solution₁.y_mul]
  simp only [baseSolution, Pell.Solution₁.x_mk, Pell.Solution₁.y_mk, mul_one]
  ring

private theorem x_rec (k : ℕ) : (baseSolution^(k+2)).x =
    6*(baseSolution^(k+1)).x - (baseSolution^k).x := by
  rw [show k+2=k+1+1 by omega, x_step (k+1), y_step k, x_step k]
  ring

private theorem x_matches (k : ℕ) : (baseSolution^k).x = 2*OMA.S_oeis_a001108.a k+1 := by
  have hh (k : ℕ) : (baseSolution^k).x = 2*OMA.S_oeis_a001108.a k+1 ∧
      (baseSolution^(k+1)).x = 2*OMA.S_oeis_a001108.a (k+1)+1 := by
    induction k with
    | zero => norm_num [baseSolution, OMA.S_oeis_a001108.a]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      change (baseSolution^(k+2)).x = 2*OMA.S_oeis_a001108.a (k+2)+1
      rw [x_rec, ih.1, ih.2, OMA.S_oeis_a001108.a]
      ring
  exact (hh k).1

private theorem pell_nonneg (k : ℕ) : 0 ≤ (baseSolution^k).x ∧ 0 ≤ (baseSolution^k).y := by
  induction k with
  | zero => simp
  | succ k ih => rw [x_step, y_step]; exact ⟨by omega, by omega⟩

private theorem square_tri_classification (n : ℕ) (hn : 0<n) :
    IsSquare (tri n) ↔ ∃ k : ℕ, 1≤k ∧ OMA.S_oeis_a001108.a k=n := by
  have htri : 2*(tri n : ℤ) = (n:ℤ)*((n:ℤ)+1) := by exact_mod_cast tri_product n
  constructor
  · rintro ⟨t, ht⟩
    have ht' : (tri n : ℤ) = (t:ℤ)*(t:ℤ) := by exact_mod_cast ht
    let Q : Pell.Solution₁ 8 := Pell.Solution₁.mk (2*(n:ℤ)+1) (t:ℤ) (by nlinarith)
    have hx : 0 < Q.x := by simp [Q]
    have hy : 0 ≤ Q.y := by simp [Q]
    obtain ⟨k, hk⟩ := fundamental.eq_pow_of_nonneg hx hy
    have hxk := congrArg Pell.Solution₁.x hk
    simp only [Q, Pell.Solution₁.x_mk, x_matches] at hxk
    have hk0 : 1≤k := by
      by_contra! hh
      have hk' : k=0 := by omega
      rw [hk', OMA.S_oeis_a001108.a] at hxk
      omega
    exact ⟨k, hk0, by omega⟩
  · rintro ⟨k, hk, ha⟩
    have hy := (pell_nonneg k).2
    have hp := (baseSolution^k).prop
    have hx := x_matches k
    rw [ha] at hx
    rw [hx] at hp
    let y := ((baseSolution^k).y).toNat
    have hy' : (y:ℤ) = (baseSolution^k).y := Int.toNat_of_nonneg hy
    refine ⟨y, ?_⟩
    have hh : (tri n : ℤ) = (y:ℤ)*(y:ℤ) := by
      rw [hy']
      nlinarith
    exact_mod_cast hh

private theorem solution : type_of% @OMA.S_oeis_a001108.main := by
  intro n hn
  exact (square_tri_iff n hn).trans (square_tri_classification n hn)

end OMA.SquareTriangularIndices

theorem OMA.solution : type_of% @OMA.S_oeis_a001108.main := OMA.SquareTriangularIndices.solution
