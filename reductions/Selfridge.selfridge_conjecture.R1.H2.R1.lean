import OMAReductions.R_Selfridge_selfridge_conjecture_R1
import Mathlib

/-!
# Prime factor restrictions for the Selfridge challenge

The cofactor sieve and simultaneous Wieferich and Fibonacci lifting obstruction follow
Andrew Shallue and Jonathan Webster, Fast tabulation of challenge pseudoprimes (2019),
Propositions 3, 4 and 6. Their Proposition 3 credits Bleichenbacher, Theorem 3.20.
The proof here specializes to the Fibonacci sequence.
The initial range through 10000 was settled separately by @ivillar.
-/

-- Credit: @MrSeizy

namespace OMA.R_Selfridge_selfridge_conjecture_R1_H2_R1

private lemma fib_binet {K : Type*} [Field K] {x y : K}
    (hx : x ^ 2 = x + 1) (hy : y ^ 2 = y + 1) (n : ℕ) :
    (x - y) * (n.fib : K) = x ^ n - y ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h h' =>
    rw [Nat.fib_add_two, Nat.cast_add, mul_add, h, h', pow_add x n 2, pow_add y n 2]
    simp only [pow_succ x n, pow_succ y n]
    rw [hx, hy]
    ring

/-- Frobenius fixes or exchanges the two distinct roots of X² − X − 1. -/
private lemma prime_fib_index {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) :
    p ∣ (p - 1).fib ∨ p ∣ (p + 1).fib := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  have hfive : (5 : K) ≠ 0 := by
    change ((5 : ℕ) : K) ≠ 0
    intro hz
    have h := (CharP.cast_eq_zero_iff K p 5).mp hz
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  obtain ⟨x, hxroot⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial K) (by
      have hd : (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial K).degree = 2 := by compute_degree!
      rw [hd]; decide)
  have hx : x ^ 2 = x + 1 := by
    simpa [Polynomial.IsRoot, sub_sub, sub_eq_zero] using hxroot
  let y : K := 1 - x
  have hy : y ^ 2 = y + 1 := by dsimp [y]; linear_combination hx
  have hxy : x * y = -1 := by dsimp [y]; linear_combination -hx
  have hne : x - y ≠ 0 := by
    intro h
    dsimp only [y] at h
    apply hfive
    linear_combination (2*x-1)*h - 4*hx
  have hx' : (x ^ p) ^ 2 = x ^ p + 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hx, add_pow_char, one_pow]
  have hr : (x ^ p - x) * (x ^ p - y) = 0 := by
    dsimp [y] at *
    linear_combination hx' - hx
  have hys : y ^ p = 1 - x ^ p := by simp [y, sub_pow_char]
  have hf (m : ℕ) (h : x ^ m = y ^ m) : p ∣ m.fib := by
    apply (CharP.cast_eq_zero_iff K p _).mp
    apply (mul_eq_zero.mp _).resolve_left hne
    rw [fib_binet hx hy, h, sub_self]
  rcases mul_eq_zero.mp hr with h | h
  · left
    have hxp := sub_eq_zero.mp h
    have hyp : y ^ p = y := by rw [hys, hxp]
    have hpow (a : K) (ha : a ≠ 0) (hap : a ^ p = a) : a ^ (p - 1) = 1 := by
      apply mul_right_cancel₀ ha
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hap, one_mul]
    apply hf
    rw [hpow x (by intro e; simp [e] at hxy) hxp, hpow y (by intro e; simp [e] at hxy) hyp]
  · right
    have hxp := sub_eq_zero.mp h
    have hyp : y ^ p = x := by rw [hys, hxp]; dsimp [y]; ring
    apply hf
    rw [pow_succ, pow_succ, hxp, hyp, mul_comm]

open QuadraticAlgebra

private lemma fib_coordinate {R : Type*} [CommRing R] (n : ℕ) :
    ((omega : QuadraticAlgebra R 1 1) ^ n).im = (n.fib : R) := by
  let w : QuadraticAlgebra R 1 1 := omega
  have hw : w ^ 2 = w + 1 := by simp [w, sq, omega_mul_omega_eq_add, add_comm]
  change (w ^ n).im = _
  induction n using Nat.twoStepInduction with
  | zero => simp [im_one]
  | one => simp [w]
  | more n h h' =>
    rw [pow_add, hw, mul_add, mul_one, ← pow_succ, im_add, h', h, Nat.fib_add_two, Nat.cast_add]
    exact add_comm _ _

/-- In the quadratic algebra modulo p², the nonscalar part of ωʳ is a multiple of p.
Raising to the pth power kills that part. -/
private lemma lift_fib_index {p r : ℕ} (h : p ∣ r.fib) : p ^ 2 ∣ (r * p).fib := by
  let R := ZMod (p ^ 2)
  let A := QuadraticAlgebra R 1 1
  let w : A := omega
  let c := algebraMap R A (w ^ r).re
  obtain ⟨k, hk⟩ := h
  let z : A := (k : A) * w
  have hw : w ^ r = c + (p : A) * z := by
    apply QuadraticAlgebra.ext
    · simp [c, z, w, A, R]
    · simp [c, z, w, A, R, fib_coordinate, hk]
  have hpR : (p : R) ^ 2 = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  have hpA : (p : A) ^ 2 = 0 := by
    have hh := congrArg (algebraMap R A) hpR
    simpa [A, R] using hh
  have hn := sq_dvd_add_pow_sub_sub ((p : A) * z) c p
  rw [mul_pow, hpA, zero_mul, zero_dvd_iff, ← hw] at hn
  have hd : c ^ (p - 1) * (p * z) * p = 0 := by
    linear_combination c ^ (p - 1) * z * hpA
  rw [hd, sub_zero, sub_eq_zero, ← pow_mul] at hn
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [← fib_coordinate, show (omega : A) = w from rfl, hn]
  simp only [c, ← map_pow]; rfl

/-- Intersect the two Fibonacci indices by strong divisibility and cancel the coprime p. -/
private lemma lower_fib_index {p r n : ℕ} (hp : p ∣ r.fib)
    (hn : p ^ 2 ∣ n.fib) (hc : p.Coprime n) : p ^ 2 ∣ r.fib := by
  have h := Nat.dvd_gcd (lift_fib_index hp) hn
  rw [← Nat.fib_gcd, Nat.Coprime.gcd_mul_right_cancel r hc] at h
  exact h.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_left _ _))

private lemma lower_fermat_index {p n : ℕ} (hp : p.Prime) (hc : Nat.Coprime 2 p)
    (hpc : p.Coprime n) (hn : 2 ^ n ≡ 1 [MOD p ^ 2]) :
    2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  let a : ZMod (p ^ 2) := 2
  have pow_iff (m : ℕ) : 2 ^ m ≡ 1 [MOD p ^ 2] ↔ orderOf a ∣ m := by
    rw [← ZMod.natCast_eq_natCast_iff, orderOf_dvd_iff_pow_eq_one]
    simp [a]
  have he := Nat.ModEq.pow_totient (hc.pow_right 2)
  rw [Nat.totient_prime_pow_succ hp 1, pow_one] at he
  exact (pow_iff _).mpr (((hpc.symm.of_dvd_left ((pow_iff _).mp hn))).dvd_of_dvd_mul_left
    ((pow_iff _).mp he))

private lemma cofactor_tests {p k : ℕ} (hp : p.Prime) (hk : 1 < k)
    (hc : Nat.Coprime 2 p) (hn : Selfridge.IsSelfridge (p * k))
    (hi : p ∣ (p - 1).fib ∨ p ∣ (p + 1).fib) :
    2 ^ (k - 1) ≡ 1 [MOD p] ∧
    (p ∣ (p - 1).fib.gcd (k + 1).fib ∨ p ∣ (p + 1).fib.gcd (k - 1).fib) := by
  have hpk : p ∣ p * k := dvd_mul_right _ _
  have hF := hpk.trans (Nat.modEq_zero_iff_dvd.mp hn.fib)
  have hP := Nat.ModEq.of_dvd hpk hn.pow_2
  have ha := congrArg (· * k) (Nat.sub_add_cancel hp.one_le : p - 1 + 1 = p)
  simp only [add_mul, one_mul] at ha
  have hb : p * k - 1 = (p - 1) * k + (k - 1) := by omega
  constructor
  · rw [hb, pow_add, pow_mul] at hP
    have hf := (Nat.ModEq.pow_card_sub_one_eq_one hp hc).pow k
    have ht := (hf.mul_right (2 ^ (k - 1))).symm.trans hP
    simpa using ht
  · have hdiv {r t : ℕ} (hr : p ∣ r.fib) (ht : r.gcd (p*k+1) ∣ t) : p ∣ t.fib := by
      apply Dvd.dvd.trans _ (Nat.fib_dvd _ _ ht)
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd hr hF
    rcases hi with hi | hi
    · left
      apply Nat.dvd_gcd hi (hdiv hi ?_)
      let d := (p-1).gcd (p*k+1)
      have hd : d ∣ (p-1)*k := dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
      have he : d ∣ p*k+1 := Nat.gcd_dvd_right _ _
      rw [show p*k+1 = (p-1)*k + (k+1) by omega] at he
      exact (Nat.dvd_add_right hd).mp he
    · right
      apply Nat.dvd_gcd hi (hdiv hi ?_)
      let d := (p+1).gcd (p*k+1)
      have hd : d ∣ (p+1)*k := dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
      have he : d ∣ p*k+1 := Nat.gcd_dvd_right _ _
      rw [show (p+1)*k = (p*k+1)+(k-1) by rw [add_mul, one_mul]; omega] at hd
      exact (Nat.dvd_add_right he).mp hd


/-- No squarefree cofactor passes both residual tests with a prime from either Fibonacci gcd. -/
def H1 : Prop :=
  ∀ k p : ℕ, 1 < k → Squarefree k → p.Prime → p.Coprime k →
    10000 < p * k → Odd (p * k) → (p * k ≡ 2 [MOD 5] ∨ p * k ≡ 3 [MOD 5]) →
    2 ^ (k - 1) ≡ 1 [MOD p] →
    (p ∣ (p - 1).fib.gcd (k + 1).fib ∨ p ∣ (p + 1).fib.gcd (k - 1).fib) →
    2 ^ (p * k - 1) ≡ 1 [MOD k] → ¬ k ∣ (p * k + 1).fib

/-- No odd prime away from 5 satisfies both prime-square lifting conditions. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ¬ (p ^ 2 ∣ (p - 1).fib ∨ p ^ 2 ∣ (p + 1).fib)

theorem main : H1 → H2 → OMA.R_Selfridge_selfridge_conjecture_R1.H2 := by
  intro h1 h2 n hn hs
  have h5n : ¬ 5 ∣ n := by
    have hm := hs.mod_5
    unfold Nat.ModEq at hm
    omega
  have hc2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hs.is_odd
  have exclude {p : ℕ} (hpn : p ∣ n) : p ≠ 2 ∧ p ≠ 5 := by
    constructor
    · rintro rfl
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hc2) hpn
    · rintro rfl
      exact h5n hpn
  have hsq : Squarefree n := by
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hpp
    have hpp' : p ^ 2 ∣ n := by simpa [sq] using hpp
    have hpn : p ∣ n := (dvd_mul_right p p).trans hpp
    obtain ⟨hp2, hp5⟩ := exclude hpn
    have hminus : p.Coprime (n - 1) := Nat.Coprime.of_dvd_left hpn
      ((Nat.coprime_self_sub_right (by omega : 1 ≤ n)).mpr (by simp))
    have hplus : p.Coprime (n + 1) := Nat.Coprime.of_dvd_left hpn (by simp)
    have hpow := lower_fermat_index hp (hc2.of_dvd_right hpn) hminus
      (Nat.ModEq.of_dvd hpp' hs.pow_2)
    apply h2 p hp hp2 hp5 hpow
    have hf := hpp'.trans (Nat.modEq_zero_iff_dvd.mp hs.fib)
    exact (prime_fib_index hp hp5).imp (fun h => lower_fib_index h hf hplus)
      (fun h => lower_fib_index h hf hplus)
  by_contra hnot
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hp5 := (exclude hpn).2
  have hc := hc2.of_dvd_right hpn
  obtain ⟨k, heq⟩ := hpn
  have hk : 1 < k := by
    rcases k with _ | _ | k
    · simp_all
    · simp_all
    · omega
  have hs' : Selfridge.IsSelfridge (p * k) := heq ▸ hs
  have hsq' : Squarefree (p * k) := heq ▸ hsq
  obtain ⟨ha, hb⟩ := cofactor_tests hp hk hc hs' (prime_fib_index hp hp5)
  have hkn : k ∣ p * k := dvd_mul_left _ _
  exact h1 k p hk hsq'.of_mul_right hp
    (Nat.coprime_iff_isRelPrime.mpr (IsRelPrime.of_squarefree_mul hsq'))
    (heq ▸ hn) hs'.is_odd hs'.mod_5 ha hb (Nat.ModEq.of_dvd hkn hs'.pow_2)
    (hkn.trans (Nat.modEq_zero_iff_dvd.mp hs'.fib))

end OMA.R_Selfridge_selfridge_conjecture_R1_H2_R1
