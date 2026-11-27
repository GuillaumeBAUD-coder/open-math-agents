import OMAReductions.R_OeisA5258_conjecture_R1
import Mathlib

/-!
# Irreducibility of Apery polynomials when n + 1 is prime

When `p = n + 1` is prime and `1 ≤ n`, every coefficient of `aperyPoly n` of degree `1 ≤ k ≤ n`
is divisible by `p`, the constant term is `1`, and the leading coefficient `(2 * n).choose n`
is not divisible by `p ^ 2`. Consequently, the mirrored integer polynomial is `p`-Eisenstein,
so `aperyPoly n` is irreducible over `ℚ` by Gauss's lemma.
-/

namespace OeisA5258H1

open Polynomial

def aperyCoeff (n k : ℕ) : ℕ :=
  n.choose k ^ 2 * (n + k).choose k

lemma not_dvd_succ_ascFactorial {p : ℕ} (hp : p.Prime) :
    ∀ m : ℕ, m < p → ¬ p ∣ (p + 1).ascFactorial m
  | 0, _ => by
    rw [Nat.ascFactorial_zero]
    exact hp.not_dvd_one
  | m + 1, hm => by
    rw [Nat.ascFactorial_succ, hp.dvd_mul]
    rintro (h1 | h2)
    · have h1' : p ∣ p + (m + 1) := by
        have heq : p + 1 + m = p + (m + 1) := by omega
        rwa [← heq]
      have hdvd : p ∣ m + 1 := (Nat.dvd_add_right (dvd_refl p)).mp h1'
      have hle : p ≤ m + 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    · exact not_dvd_succ_ascFactorial hp m (by omega) h2

lemma prime_dvd_aperyCoeff {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hp : (n + 1).Prime) :
    (n + 1) ∣ aperyCoeff n k := by
  set p := n + 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hasc : p * (p + 1).ascFactorial m = (m + 1).factorial * (n + (m + 1)).choose (m + 1) := by
    have h1 := Nat.ascFactorial_mul_ascFactorial p 1 m
    have hp1 : p.ascFactorial 1 = p := by simp [Nat.ascFactorial]
    have hadd : 1 + m = m + 1 := by omega
    rw [hp1, hadd] at h1
    exact h1.trans (Nat.ascFactorial_eq_factorial_mul_choose n (m + 1))
  have hdvd_prod : p ∣ (m + 1).factorial * (n + (m + 1)).choose (m + 1) :=
    ⟨(p + 1).ascFactorial m, hasc.symm⟩
  have hnot_dvd_fact : ¬ p ∣ (m + 1).factorial := by
    rw [Nat.Prime.dvd_factorial hp]
    omega
  have hcop : p.Coprime (m + 1).factorial := hp.coprime_iff_not_dvd.mpr hnot_dvd_fact
  have hdvd_choose : p ∣ (n + (m + 1)).choose (m + 1) := hcop.dvd_of_dvd_mul_left hdvd_prod
  exact dvd_mul_of_dvd_right hdvd_choose _

lemma prime_sq_not_dvd_aperyCoeff_self {n : ℕ} (hn : 1 ≤ n) (hp : (n + 1).Prime) :
    ¬ (n + 1) ^ 2 ∣ aperyCoeff n n := by
  set p := n + 1
  have hcoeff : aperyCoeff n n = (n + n).choose n := by
    simp [aperyCoeff]
  rw [hcoeff]
  intro hsq
  obtain ⟨m, hnm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hasc : p * (p + 1).ascFactorial m = n.factorial * (n + n).choose n := by
    have h1 := Nat.ascFactorial_mul_ascFactorial p 1 m
    have hp1 : p.ascFactorial 1 = p := by simp [Nat.ascFactorial]
    have hadd : 1 + m = n := by omega
    rw [hp1, hadd] at h1
    exact h1.trans (Nat.ascFactorial_eq_factorial_mul_choose n n)
  have hdvd1 : p ^ 2 ∣ n.factorial * (n + n).choose n := dvd_mul_of_dvd_right hsq _
  rw [← hasc, sq] at hdvd1
  have hdvd2 : p ∣ (p + 1).ascFactorial m :=
    (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd1
  exact not_dvd_succ_ascFactorial hp m (by omega) hdvd2

noncomputable def aperyIntPoly (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (aperyCoeff n k : ℤ) * X ^ k

lemma coeff_aperyIntPoly (n j : ℕ) :
    (aperyIntPoly n).coeff j = if j ≤ n then (aperyCoeff n j : ℤ) else 0 := by
  simp only [aperyIntPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma coeff_aperyIntPoly_zero (n : ℕ) : (aperyIntPoly n).coeff 0 = 1 := by
  rw [coeff_aperyIntPoly, if_pos (Nat.zero_le n)]
  simp [aperyCoeff]

lemma aperyCoeff_self_pos (n : ℕ) : 0 < aperyCoeff n n := by
  simp only [aperyCoeff, Nat.choose_self, one_pow, one_mul]
  exact Nat.choose_pos (by omega)

lemma natDegree_aperyIntPoly (n : ℕ) : (aperyIntPoly n).natDegree = n := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_aperyIntPoly, if_neg (by omega)]
  · apply le_natDegree_of_ne_zero
    rw [coeff_aperyIntPoly, if_pos (le_refl n)]
    exact_mod_cast (aperyCoeff_self_pos n).ne'

lemma isPrimitive_aperyIntPoly (n : ℕ) : (aperyIntPoly n).IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  rcases hr with ⟨q, hq⟩
  have h0 := congr_arg (fun f : ℤ[X] => f.coeff 0) hq
  rw [coeff_aperyIntPoly_zero, coeff_C_mul] at h0
  exact isUnit_iff_exists_inv.mpr ⟨q.coeff 0, h0.symm⟩

lemma isPrimitive_mirror {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}
    (hf : f.IsPrimitive) : f.mirror.IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd] at hf ⊢
  intro r hr
  apply hf r
  rcases hr with ⟨q, hq⟩
  refine ⟨q.mirror, ?_⟩
  have hm := congr_arg mirror hq
  rwa [mirror_mirror, mirror_mul_of_domain, mirror_C] at hm

lemma isUnit_mirror_iff {R : Type*} [CommRing R] [NoZeroDivisors R] (f : R[X]) :
    IsUnit f.mirror ↔ IsUnit f := by
  have himp : ∀ g : R[X], IsUnit g → IsUnit g.mirror := by
    intro g hg
    rcases isUnit_iff_exists_inv.mp hg with ⟨b, hb⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨b.mirror, ?_⟩
    rw [← mirror_mul_of_domain, hb]
    simpa using mirror_C (1 : R)
  exact ⟨fun h => by simpa [mirror_mirror] using himp f.mirror h, himp f⟩

lemma irreducible_of_mirror_irreducible {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}
    (hf : Irreducible f.mirror) : Irreducible f := by
  refine ⟨fun hu => hf.not_isUnit ((isUnit_mirror_iff f).mpr hu), ?_⟩
  intro a b hab
  have hm : f.mirror = a.mirror * b.mirror := by
    rw [hab, mirror_mul_of_domain]
  rcases hf.isUnit_or_isUnit hm with ha | hb
  · exact Or.inl ((isUnit_mirror_iff a).mp ha)
  · exact Or.inr ((isUnit_mirror_iff b).mp hb)

lemma coeff_mirror_aperyIntPoly {n k : ℕ} (hk : k ≤ n) :
    (aperyIntPoly n).mirror.coeff k = (aperyCoeff n (n - k) : ℤ) := by
  have htrail : (aperyIntPoly n).natTrailingDegree = 0 := by
    apply natTrailingDegree_eq_zero.mpr
    right
    rw [coeff_aperyIntPoly_zero]
    decide
  rw [coeff_mirror, natDegree_aperyIntPoly, htrail, add_zero, revAt_le hk,
    coeff_aperyIntPoly, if_pos (Nat.sub_le n k)]

lemma irreducible_mirror_aperyIntPoly {n : ℕ} (hn : 1 ≤ n) (hp : (n + 1).Prime) :
    Irreducible (aperyIntPoly n).mirror := by
  set p : ℕ := n + 1
  set P : Ideal ℤ := Ideal.span {(p : ℤ)}
  set g : ℤ[X] := (aperyIntPoly n).mirror
  have hp_int_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP_prime : P.IsPrime := (Ideal.span_singleton_prime hp_int_ne).mpr hp_prime_int
  have hg_natDeg : g.natDegree = n := by
    rw [mirror_natDegree, natDegree_aperyIntPoly]
  have hg_ne_zero : g ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hg_natDeg
    omega
  have hg_deg : g.degree = (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hg_ne_zero, hg_natDeg]
  apply irreducible_of_eisenstein_criterion hP_prime
  · rw [leadingCoeff, hg_natDeg, coeff_mirror_aperyIntPoly (le_refl n), Nat.sub_self]
    simp only [P, aperyCoeff, Nat.choose_zero_right, one_pow, mul_one, add_zero, Nat.cast_one,
      Ideal.mem_span_singleton]
    intro hdvd
    have hdvd_nat : p ∣ 1 := Int.ofNat_dvd.mp hdvd
    exact hp.not_dvd_one hdvd_nat
  · intro k hk
    rw [hg_deg, Nat.cast_lt] at hk
    rw [coeff_mirror_aperyIntPoly (le_of_lt hk), Ideal.mem_span_singleton]
    exact Int.ofNat_dvd.mpr (prime_dvd_aperyCoeff (by omega) (Nat.sub_le n k) hp)
  · rw [hg_deg]
    exact Nat.cast_pos.mpr (by omega)
  · rw [coeff_mirror_aperyIntPoly (Nat.zero_le n), Nat.sub_zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro hdvd
    have hdvd_cast : ((p ^ 2 : ℕ) : ℤ) ∣ (aperyCoeff n n : ℤ) := by
      simpa only [Nat.cast_pow] using hdvd
    exact prime_sq_not_dvd_aperyCoeff_self hn hp (Int.ofNat_dvd.mp hdvd_cast)
  · exact isPrimitive_mirror (isPrimitive_aperyIntPoly n)

lemma map_aperyIntPoly (n : ℕ) :
    Polynomial.map (Int.castRingHom ℚ) (aperyIntPoly n) = OeisA5258.aperyPoly n := by
  rw [aperyIntPoly, OeisA5258.aperyPoly, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [aperyCoeff]

end OeisA5258H1

theorem prove_OeisA5258_H1 :
    ∀ n : ℕ, 1 ≤ n → (n + 1).Prime → Irreducible (OeisA5258.aperyPoly n) := by
  intro n hn hp
  rw [← OeisA5258H1.map_aperyIntPoly n]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (OeisA5258H1.isPrimitive_aperyIntPoly n)).mp
    (OeisA5258H1.irreducible_of_mirror_irreducible
      (OeisA5258H1.irreducible_mirror_aperyIntPoly hn hp))

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 :=
  prove_OeisA5258_H1
