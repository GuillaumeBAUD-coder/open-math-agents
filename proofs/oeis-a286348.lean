import OMAStatements.S_oeis_a286348
import Mathlib

/-!
# OEIS A286348: when `(1 + y)^x + (-y)^x` can be prime

Put `a = 1 + y`, `b = -y`, so `a + b = 1`, and `N(x) = a^x + b^x`.

* If `{a, b} = {1, 0}` then `N(x) = 1` for `x ≥ 1`, never prime.
* Otherwise one of `a, b` is `v + 1` and the other is `-v` with `v ≥ 1`.
  If `x ≥ 1` is not a power of two, it has an odd prime factor `q`, say `x = q e`.
  Then `D = N(e)` divides `N(x) = (a^e)^q + (b^e)^q` because `q` is odd.
  For `e ≥ 2` we have `1 < D < N(x)`:
  - `e` even: `D = (v+1)^e + v^e`, `N(x) = (v+1)^x + v^x`, clear;
  - `e` odd: `D = (v+1)^e - v^e`, `N(x) = (v+1)^x - v^x`, and `n ↦ (v+1)^n - v^n` is strictly
    increasing with value `1` at `n = 1`.
  So `N(x)` is not prime unless `e = 1`, i.e. `x = q` is an odd prime.
* `x = 1` gives `N = 1`. That leaves `x = 0`, `x = 2^k` with `k ≥ 1`, or `x` an odd prime.
-/

namespace OMA.A286348

/-- `n ↦ (v+1)^n - v^n` is strictly increasing for `v ≥ 1`. -/
lemma diff_mono (v : ℤ) (hv : 1 ≤ v) (e d : ℕ) (hd : 1 ≤ d) :
    (v + 1) ^ e - v ^ e < (v + 1) ^ (e + d) - v ^ (e + d) := by
  have hU : v ^ e ≤ (v + 1) ^ e := pow_le_pow_left₀ (by linarith) (by linarith) e
  have hV : (1 : ℤ) ≤ v ^ e := one_le_pow₀ hv
  have hQ : (1 : ℤ) ≤ v ^ d := one_le_pow₀ hv
  have hPQ : v ^ d < (v + 1) ^ d := pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
  rw [pow_add, pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hU (by linarith : (0 : ℤ) ≤ v ^ d - 1),
    mul_pos (by linarith : (0 : ℤ) < (v + 1) ^ e) (by linarith : (0 : ℤ) < (v + 1) ^ d - v ^ d)]

/-- The main case: the two bases are `v + 1` and `-v` with `v ≥ 1`. -/
lemma core (v : ℤ) (hv : 1 ≤ v) (x : ℕ)
    (hpos : 0 < (v + 1) ^ x + (-v) ^ x) (hprime : ((v + 1) ^ x + (-v) ^ x).toNat.Prime) :
    x = 0 ∨ (∃ k ≥ 1, x = 2 ^ k) ∨ (x.Prime ∧ Odd x) := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd x with ⟨k, rfl⟩ | ⟨q, hq, hqx, hqodd⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- `x = 1`: the value is `1`
      exfalso
      have hval : (v + 1) ^ (2 ^ 0) + (-v) ^ (2 ^ 0) = 1 := by norm_num
      rw [hval, Int.toNat_one] at hprime
      exact Nat.not_prime_one hprime
    · exact Or.inr (Or.inl ⟨k, hk, rfl⟩)
  · obtain ⟨e, rfl⟩ := hqx
    rcases Nat.lt_or_ge e 2 with he | he
    · interval_cases e
      · left; simp
      · right; right
        rw [mul_one]
        exact ⟨hq, hqodd⟩
    · exfalso
      have hq3 : 3 ≤ q := by
        rcases hqodd with ⟨m, hm⟩
        have := hq.two_le
        omega
      have hlt : e < q * e := by nlinarith
      -- `N(e)` divides `N(q e)` because `q` is odd
      have hdvd : (v + 1) ^ e + (-v) ^ e ∣ (v + 1) ^ (q * e) + (-v) ^ (q * e) := by
        rw [mul_comm q e, pow_mul, pow_mul]
        exact Odd.add_dvd_pow_add_pow _ _ hqodd
      -- and `1 < N(e) < N(q e)`
      have hsize : 1 < (v + 1) ^ e + (-v) ^ e ∧
          (v + 1) ^ e + (-v) ^ e < (v + 1) ^ (q * e) + (-v) ^ (q * e) := by
        rcases Nat.even_or_odd e with hev | hod
        · have hx : Even (q * e) := hev.mul_left q
          rw [hev.neg_pow, hx.neg_pow]
          have h1 : (1 : ℤ) ≤ v ^ e := one_le_pow₀ hv
          have h2 : (1 : ℤ) < (v + 1) ^ e := one_lt_pow₀ (by linarith) (by omega)
          have h3 : (v + 1) ^ e < (v + 1) ^ (q * e) := pow_lt_pow_right₀ (by linarith) hlt
          have h4 : v ^ e ≤ v ^ (q * e) := pow_le_pow_right₀ hv hlt.le
          constructor <;> linarith
        · have hx : Odd (q * e) := hqodd.mul hod
          rw [hod.neg_pow, hx.neg_pow]
          have h1 := diff_mono v hv 1 (e - 1) (by omega)
          have h2 := diff_mono v hv e (q * e - e) (by omega)
          rw [show 1 + (e - 1) = e by omega, pow_one, pow_one] at h1
          rw [show e + (q * e - e) = q * e by omega] at h2
          constructor <;> linarith
      obtain ⟨hD1, hDN⟩ := hsize
      -- so `N(q e)` has a proper divisor
      have hNnat : ((((v + 1) ^ (q * e) + (-v) ^ (q * e)).toNat : ℕ) : ℤ)
          = (v + 1) ^ (q * e) + (-v) ^ (q * e) := Int.toNat_of_nonneg hpos.le
      have hDnat : ((((v + 1) ^ e + (-v) ^ e).toNat : ℕ) : ℤ) = (v + 1) ^ e + (-v) ^ e :=
        Int.toNat_of_nonneg (by linarith)
      have hdvd' : ((v + 1) ^ e + (-v) ^ e).toNat ∣ ((v + 1) ^ (q * e) + (-v) ^ (q * e)).toNat := by
        rw [← Int.natCast_dvd_natCast, hNnat, hDnat]
        exact hdvd
      rcases (Nat.dvd_prime hprime).mp hdvd' with h | h
      · have h' := congrArg (Nat.cast : ℕ → ℤ) h
        rw [hDnat] at h'
        norm_num at h'
        linarith
      · have h' := congrArg (Nat.cast : ℕ → ℤ) h
        rw [hDnat, hNnat] at h'
        linarith

end OMA.A286348

open OMA.A286348 in
theorem OMA.solution : type_of% @OMA.S_oeis_a286348.main := by
  intro y x hpos hprime
  rcases le_or_gt 1 y with hy | hy
  · -- `y ≥ 1`: bases `y + 1` and `-y`
    rw [add_comm 1 y] at hpos hprime
    exact core y hy x hpos hprime
  · rcases le_or_gt y (-2) with hy2 | hy2
    · -- `y ≤ -2`: bases `-y = v + 1` and `1 + y = -v` with `v = -y - 1`
      have e : (1 + y) ^ x + (-y) ^ x = ((-y - 1) + 1) ^ x + (-(-y - 1)) ^ x := by
        rw [show -y - 1 + 1 = -y by ring, show -(-y - 1) = 1 + y by ring, add_comm]
      rw [e] at hpos hprime
      exact core (-y - 1) (by linarith) x hpos hprime
    · -- `y = 0` or `y = -1`: the value is `1` unless `x = 0`
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · left; rfl
      · exfalso
        have hy' : y = 0 ∨ y = -1 := by omega
        have hval : (1 + y) ^ x + (-y) ^ x = 1 := by
          rcases hy' with rfl | rfl <;> simp [hx.ne']
        rw [hval, Int.toNat_one] at hprime
        exact Nat.not_prime_one hprime
