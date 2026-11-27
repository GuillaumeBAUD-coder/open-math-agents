import OMAReductions.R_OeisA5258_conjecture_R1
import Mathlib.Algebra.Polynomial.Mirror
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! The prime-index split and the reciprocal Eisenstein argument are due to
jagong-cmu in reduction #1751. -/

open Polynomial Finset

private theorem central_choose_not_sq_dvd (n : ℕ) (hp : (n + 1).Prime) :
    ¬ (n + 1)^2 ∣ (n + n).choose n := by
  have hpos : 0 < (n + n).choose n := Nat.choose_pos (by omega)
  have hval : ((n + n).choose n).factorization (n + 1) ≤ 1 :=
    Nat.factorization_choose_le_one (by nlinarith)
  intro h
  have := (hp.pow_dvd_iff_le_factorization hpos.ne').mp h
  omega

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := by
  classical
  intro n hn hp
  let a (k : ℕ) := n.choose k ^ 2 * (n + k).choose k
  let f : ℤ[X] := ∑ k ∈ range (n + 1), C (a k : ℤ) * X ^ k
  have coeff (k : ℕ) : f.coeff k = if k ≤ n then (a k : ℤ) else 0 := by
    simp [f, finsetSum_coeff]
  have fzero : f.coeff 0 = 1 := by simp [coeff, a]
  have ftop : f.coeff n = ((n + n).choose n : ℤ) := by simp [coeff, a]
  have degree_f : f.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by simp [coeff, Nat.not_le.mpr hk]
    · rw [ftop]
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right n n)).ne'
  have trail : f.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (.inr (by simp [fzero]))
  have revcoeff (k : ℕ) (hk : k ≤ n) : f.mirror.coeff k = f.coeff (n - k) := by
    rw [coeff_mirror, degree_f, trail, add_zero, revAt_le hk]
  have monic : f.mirror.Monic := by
    change f.mirror.coeff f.mirror.natDegree = 1
    rw [mirror_natDegree, degree_f, revcoeff n le_rfl, Nat.sub_self, fzero]
  let P : Ideal ℤ := Ideal.span {((n+1 : ℕ) : ℤ)}
  have hprime : P.IsPrime := Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp)
  have hirr : Irreducible f.mirror := by
    apply irreducible_of_eisenstein_criterion hprime
    · rw [monic.leadingCoeff]
      exact fun h => hprime.ne_top ((Ideal.eq_top_iff_one P).mpr h)
    · intro k hk
      have hkn : k < n := by simpa [mirror_natDegree, degree_f] using coe_lt_degree.mp hk
      rw [revcoeff k hkn.le, coeff, if_pos (Nat.sub_le n k), Ideal.mem_span_singleton]
      have hd : n + 1 ∣ (n + (n-k)).choose (n-k) :=
        hp.dvd_choose (by omega) (by omega) (by omega)
      exact_mod_cast dvd_mul_of_dvd_right hd (n.choose (n-k) ^ 2)
    · apply natDegree_pos_iff_degree_pos.mp
      rw [mirror_natDegree, degree_f]
      omega
    · rw [revcoeff 0 (Nat.zero_le n), Nat.sub_zero, ftop]
      change _ ∉ (Ideal.span {((n+1 : ℕ) : ℤ)})^2
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact_mod_cast central_choose_not_sq_dvd n hp
    · exact monic.isPrimitive
  let e : ℤ[X] ≃* ℤ[X] :=
    { toFun := mirror, invFun := mirror, left_inv := mirror_mirror,
      right_inv := mirror_mirror, map_mul' := fun x y => mirror_mul_of_domain x y }
  have hi : Irreducible f := (MulEquiv.irreducible_iff e).mp hirr
  have prim : f.IsPrimitive := by
    rintro r ⟨g, hg⟩
    exact .of_mul_eq_one (g.coeff 0) (by rw [← coeff_C_mul, ← hg, fzero])
  have hmap : f.map (Int.castRingHom ℚ) = OeisA5258.aperyPoly n := by
    simp [f, a, OeisA5258.aperyPoly, Polynomial.map_sum]
  rw [← hmap]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast prim).mp hi
