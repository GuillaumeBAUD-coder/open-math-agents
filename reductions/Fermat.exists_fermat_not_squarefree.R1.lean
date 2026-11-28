import FormalConjectures.Wikipedia.Fermat

-- Reduction Fermat.exists_fermat_not_squarefree.R1 of Open questions about Fermat numbers — exists fermat not squarefree
-- Credit: @Miura-KR
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A non-squarefree Fermat number exists iff some Wieferich prime divides a Fermat number

For an odd prime `p` write `w(p) = v_p(2^(p-1) - 1) ≥ 1`; `p` is a base-2 Wieferich prime exactly
when `w(p) ≥ 2`. Lifting the exponent gives, for every odd prime `p ∣ 2^m + 1`,

  `v_p(2^m + 1) = w(p) + v_p(m)`.

At `m = 2^n` the term `v_p(2^n)` vanishes, so `v_p(F_n) = w(p)` for every prime `p ∣ F_n`
(Fermat numbers are odd). Hence `F_n` is not squarefree exactly when one of its prime factors is a
Wieferich prime.

* `H1` (elementary): the valuation formula above. It is word for word `H1` of
  `Erdos936.erdos_936.variants.two_pow_add_one.R1`, so one proof serves both.
* `H2` (open core): some base-2 Wieferich prime divides some Fermat number.

`main` is `H1 → H2 → target` and `lossless` proves `H1 → target → H2`: under the elementary `H1`
the open core is equivalent to the problem.

Remarks. A prime `p ∣ F_n` has `ord_p(2) = 2^(n+1)`, so `H2` asks for a Wieferich prime whose
base-2 order is a power of two. The two known Wieferich primes do not qualify:
`ord_1093(2) = 364` and `ord_3511(2) = 1755`. No further Wieferich prime exists below `2^64`
(PrimeGrid), so any witness for `H2` exceeds `2^64`.
-/

open Nat

namespace OMA.R_Fermat_exists_fermat_not_squarefree_R1

/-- Lifting the exponent: for an odd prime `p ∣ 2^n + 1`,
`v_p(2^n + 1) = v_p(2^(p-1) - 1) + v_p(n)`. -/
def H1 : Prop :=
  ∀ p n : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
    padicValNat p (2 ^ n + 1) = padicValNat p (2 ^ (p - 1) - 1) + padicValNat p n

/-- Some base-2 Wieferich prime divides some Fermat number. -/
def H2 : Prop :=
  ∃ n p : ℕ, p.Prime ∧ p ∣ n.fermatNumber ∧ p ^ 2 ∣ 2 ^ (p - 1) - 1

lemma two_pow_pred_sub_one_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ (p - 1) - 1 ≠ 0 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have : 2 ^ 2 ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma ne_two_of_dvd_fermat {p n : ℕ} (h : p ∣ n.fermatNumber) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ (2 ^ n) := dvd_pow_self 2 (pow_ne_zero _ (by norm_num))
  have : 2 ∣ 1 := (Nat.dvd_add_right h2).mp (by simpa [Nat.fermatNumber] using h)
  omega

/-- Under `H1`, the valuation of a Fermat number at a prime factor is `w(p)`. -/
lemma val_fermat (h1 : H1) {p n : ℕ} (hp : p.Prime) (hd : p ∣ n.fermatNumber) :
    padicValNat p n.fermatNumber = padicValNat p (2 ^ (p - 1) - 1) := by
  have hp2 := ne_two_of_dvd_fermat hd
  have hnd : ¬ p ∣ 2 ^ n := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have := h1 p (2 ^ n) hp hp2 (by simpa [Nat.fermatNumber] using hd)
  rw [padicValNat.eq_zero_of_not_dvd hnd, add_zero] at this
  simpa [Nat.fermatNumber] using this

theorem main : H1 → H2 → type_of% @Fermat.exists_fermat_not_squarefree := by
  intro h1 ⟨n, p, hp, hd, hw⟩
  have := Fact.mk hp
  have hp2 := ne_two_of_dvd_fermat hd
  refine ⟨n, fun hsq => ?_⟩
  have hv : 2 ≤ padicValNat p n.fermatNumber := by
    rw [val_fermat h1 hp hd]
    exact (padicValNat_dvd_iff_le (two_pow_pred_sub_one_ne_zero hp hp2)).mp hw
  have hpp : p * p ∣ n.fermatNumber := by
    rw [← pow_two]
    exact (padicValNat_dvd_iff_le (by simp [Nat.fermatNumber])).mpr hv
  exact hp.not_isUnit (hsq p hpp)

/-- The reduction loses nothing: under `H1`, the target implies `H2`. -/
theorem lossless : H1 → type_of% @Fermat.exists_fermat_not_squarefree → H2 := by
  intro h1 ⟨n, hn⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hn
  push_neg at hn
  obtain ⟨p, hp, hpp⟩ := hn
  have := Fact.mk hp
  have hd : p ∣ n.fermatNumber := dvd_trans (dvd_mul_right p p) hpp
  have hp2 := ne_two_of_dvd_fermat hd
  refine ⟨n, p, hp, hd, ?_⟩
  have hv : 2 ≤ padicValNat p n.fermatNumber :=
    (padicValNat_dvd_iff_le (by simp [Nat.fermatNumber])).mp (by rwa [pow_two])
  rw [val_fermat h1 hp hd] at hv
  exact (padicValNat_dvd_iff_le (two_pow_pred_sub_one_ne_zero hp hp2)).mpr hv

end OMA.R_Fermat_exists_fermat_not_squarefree_R1
