import OMAStatements.S_oeis_a179929
import Mathlib

/-!
# OEIS A179929: eventual periodicity modulo `k` with period `φ(k)`

Here `a(n) = ∑_{j ≤ n} (-1)^(n+j) 3^(n-j) 2^j · S(n, j) · j!`. Write `F(n, j) = S(n, j) · j!`
(the number of surjections from an `n`-set onto a `j`-set); for `j ≤ n` the `j`-th term is
`(-3)^(n-j) 2^j F(n, j)`.

**Step 1.** `i^n = ∑_{j ≤ i} C(i, j) F(n, j)` for all `n, i` (induction on `n`, using
`F(n+1, j+1) = (j+1) (F(n, j+1) + F(n, j))` and `(j+1) C(i, j+1) = (i-j) C(i, j)`).

**Step 2.** Solving Step 1 for `F(n, j)` by induction on `j`: if `k ∣ i^n' - i^n` for every `i`,
then `k ∣ F(n', j) - F(n, j)` for every `j`.

**Step 3.** For `n ≥ k ≥ 1` we have `k ∣ x^(n + φ(k)) - x^n` for every integer `x`: check each
prime power `p^e ∣ k`. If `p ∣ x` then `p^e ∣ x^n` because `e < k ≤ n`; otherwise Euler's
theorem gives `p^e ∣ x^φ(k) - 1`.

**Conclusion.** Take `N = 2k` and compare the two sums term by term.
* If `j ≥ k` then `k ∣ j!`, so both terms are divisible by `k`.
* If `j < k` then `n - j ≥ k`, so `(-3)^(n-j)` and `F(n, j)` are both unchanged modulo `k`
  when `n` is replaced by `n + φ(k)`.
-/

namespace OMA.A179929

/-- The four defining rules of the Stirling numbers of the second kind. -/
structure IsStirling (S : ℕ → ℕ → ℕ) : Prop where
  zero_zero : S 0 0 = 1
  succ_zero : ∀ n, S (n + 1) 0 = 0
  zero_succ : ∀ j, S 0 (j + 1) = 0
  succ_succ : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j

/-- `F(n, j) = S(n, j) · j!`, the number of surjections from `n` points onto `j` points. -/
def F (S : ℕ → ℕ → ℕ) (n j : ℕ) : ℤ := (S n j : ℤ) * (j.factorial : ℤ)

variable {S : ℕ → ℕ → ℕ}

lemma F_succ (hS : IsStirling S) (n j : ℕ) :
    F S (n + 1) (j + 1) = ((j : ℤ) + 1) * (F S n (j + 1) + F S n j) := by
  unfold F
  rw [hS.succ_succ, Nat.factorial_succ]
  push_cast
  ring

/-- `S(n, j) = 0` when `j > n`. -/
lemma S_eq_zero (hS : IsStirling S) : ∀ n j : ℕ, n < j → S n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact hS.zero_succ j'
  | succ n ih =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hS.succ_succ, ih (j' + 1) (by omega), ih j' (by omega), Nat.mul_zero]

lemma F_eq_zero (hS : IsStirling S) {n j : ℕ} (h : n < j) : F S n j = 0 := by
  unfold F
  rw [S_eq_zero hS n j h]
  simp

/-- Step 1: `i^n = ∑_{j ≤ i} C(i, j) F(n, j)`. -/
lemma pow_eq_sum (hS : IsStirling S) (n i : ℕ) :
    (i : ℤ) ^ n = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℤ) * F S n j := by
  induction n with
  | zero =>
    rw [Finset.sum_range_succ']
    simp [F, hS.zero_zero, hS.zero_succ]
  | succ n ih =>
    rw [pow_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    have h0 : F S (n + 1) 0 = 0 := by simp [F, hS.succ_zero]
    rw [h0, mul_zero, add_zero]
    -- expand `F(n+1, j+1)`
    have hA : ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * F S (n + 1) (j + 1)
        = ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n (j + 1)
          + ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [F_succ hS]; ring
    -- first part: shift the index
    have hB : ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n (j + 1)
        = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℤ) * (j : ℤ) * F S n j := by
      rw [Finset.sum_range_succ' _ i]
      simp
    -- second part: `(j+1) C(i, j+1) = (i-j) C(i, j)`
    have hC : ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n j
        = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℤ) * ((i : ℤ) - j) * F S n j := by
      rw [Finset.sum_range_succ _ i]
      simp only [sub_self, mul_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≤ i := (Finset.mem_range.mp hj).le
      have hc : (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) = (i.choose j : ℤ) * ((i : ℤ) - j) := by
        have h := congrArg (Nat.cast : ℕ → ℤ) (Nat.choose_succ_right_eq i j)
        push_cast [Nat.cast_sub hji] at h
        linarith
      rw [hc]
    rw [hA, hB, hC, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Step 2: a congruence between all `n`-th and `n'`-th powers passes to `F(n, ·)`, `F(n', ·)`. -/
lemma F_dvd_sub (hS : IsStirling S) (k : ℤ) (n n' : ℕ)
    (h : ∀ i : ℕ, k ∣ (i : ℤ) ^ n' - (i : ℤ) ^ n) : ∀ j : ℕ, k ∣ F S n' j - F S n j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have e1 := pow_eq_sum hS n j
    have e2 := pow_eq_sum hS n' j
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at e1 e2
    have key : F S n' j - F S n j = ((j : ℤ) ^ n' - (j : ℤ) ^ n)
        - ∑ l ∈ Finset.range j, (j.choose l : ℤ) * (F S n' l - F S n l) := by
      rw [e1, e2]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
    exact dvd_sub (h j)
      (Finset.dvd_sum fun l hl => Dvd.dvd.mul_left (ih l (Finset.mem_range.mp hl)) _)

/-- Step 3: `i^(n + φ(k)) ≡ i^n (mod k)` once `n ≥ k`. -/
lemma pow_period {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) (i : ℕ) :
    (k : ℤ) ∣ (i : ℤ) ^ (n + k.totient) - (i : ℤ) ^ n := by
  have hnat : k ∣ i ^ n * (i ^ k.totient - 1) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p e hp hpe
    by_cases hpi : p ∣ i
    · -- `p ∣ i`: then `p^e ∣ i^n` since `e < k ≤ n`
      have he : e ≤ n := by
        have h1 : p ^ e ≤ k := Nat.le_of_dvd (by omega) hpe
        have h2 : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        have h3 : e < 2 ^ e := Nat.lt_two_pow_self
        omega
      exact Dvd.dvd.mul_right ((pow_dvd_pow_of_dvd hpi e).trans (pow_dvd_pow i he)) _
    · -- `p ∤ i`: Euler's theorem modulo `p^e`
      have hcop : Nat.Coprime i (p ^ e) :=
        Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
      obtain ⟨m, hm⟩ := Nat.totient_dvd_of_dvd hpe
      have h1 : i ^ k.totient ≡ 1 [MOD p ^ e] := by
        rw [hm, pow_mul]
        simpa using (Nat.ModEq.pow_totient hcop).pow m
      have hipos : 1 ≤ i ^ k.totient :=
        Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => hpi (h0 ▸ dvd_zero p))
      exact Dvd.dvd.mul_left ((Nat.modEq_iff_dvd' hipos).mp h1.symm) _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h1 : n ≠ 0 := by omega
    simp [h1]
  · have hipos : 1 ≤ i ^ k.totient := Nat.one_le_pow _ _ hi
    have hcast : ((i ^ n * (i ^ k.totient - 1) : ℕ) : ℤ)
        = (i : ℤ) ^ (n + k.totient) - (i : ℤ) ^ n := by
      push_cast [Nat.cast_sub hipos]
      ring
    rw [← hcast]
    exact Int.natCast_dvd_natCast.mpr hnat

/-- For `n ≥ k ≥ 1`: `F(n + φ(k), j) ≡ F(n, j) (mod k)` for every `j`. -/
lemma F_period (hS : IsStirling S) {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) (j : ℕ) :
    (k : ℤ) ∣ F S (n + k.totient) j - F S n j :=
  F_dvd_sub hS k n (n + k.totient) (pow_period hk hn) j

/-- Step 3 for an integer base: reduce the base modulo `k` to a natural number. -/
lemma pow_period_int {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) (x : ℤ) :
    (k : ℤ) ∣ x ^ (n + k.totient) - x ^ n := by
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = x % k :=
    ⟨(x % k).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hkpos.ne')⟩
  have hx : x ≡ r [ZMOD k] := by rw [hr]; exact (Int.mod_modEq x k).symm
  have h1 := (hx.pow (n + k.totient)).sub (hx.pow n)
  exact Int.modEq_zero_iff_dvd.mp (h1.trans (Int.modEq_zero_iff_dvd.mpr (pow_period hk hn r)))

/-- `k ∣ F(n, j)` as soon as `j ≥ k`, because `k ∣ j!`. -/
lemma dvd_F (S : ℕ → ℕ → ℕ) {k j : ℕ} (hk : 1 ≤ k) (hkj : k ≤ j) (n : ℕ) :
    (k : ℤ) ∣ F S n j :=
  Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hk hkj)) _

/-- For `j ≤ m` the sign and the power of `3` combine to a power of `-3`. -/
lemma sign_pow {m j : ℕ} (h : j ≤ m) :
    (-1 : ℤ) ^ (m + j) * (3 : ℤ) ^ (m - j) = (-3 : ℤ) ^ (m - j) := by
  have hmj : m + j = (m - j) + 2 * j := by omega
  rw [neg_pow 3, hmj, pow_add, pow_mul]
  norm_num

open OMA.S_oeis_a179929 in
/-- The statement's `stirling2` obeys the four rules. -/
lemma isStirling : IsStirling stirling2 where
  zero_zero := by simp [stirling2]
  succ_zero := fun n => by simp [stirling2]
  zero_succ := fun j => by simp [stirling2]
  succ_succ := fun n j => by simp [stirling2]

end OMA.A179929

open OMA.A179929 OMA.S_oeis_a179929 in
theorem OMA.solution : type_of% @OMA.S_oeis_a179929.main := by
  intro k hk
  refine ⟨2 * k, fun n hn => ?_⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, k.totient = φ := ⟨_, rfl⟩
  rw [hφ]
  -- the `j`-th term of `a m`
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → ℤ, T = fun m j =>
      (-1 : ℤ) ^ (m + j) * (3 : ℤ) ^ (m - j) * (2 : ℤ) ^ j * F stirling2 m j := ⟨_, rfl⟩
  have e : ∀ m : ℕ, a m = ∑ j ∈ Finset.range (m + 1), T m j := by
    intro m
    rw [hT]
    rfl
  -- extend the sum for `a n`: the extra terms vanish
  have hext : ∑ j ∈ Finset.range (n + 1), T n j = ∑ j ∈ Finset.range (n + φ + 1), T n j := by
    refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
    · rw [Finset.mem_range] at hj ⊢; omega
    · rw [Finset.mem_range] at hj
      rw [hT]
      simp only
      rw [F_eq_zero isStirling (by omega), mul_zero]
  rw [Int.modEq_iff_dvd, e, e, hext, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j _ => ?_
  rw [hT]
  simp only
  rcases Nat.lt_or_ge j k with hjk | hjk
  · -- small `j`: everything is periodic
    have hF : (k : ℤ) ∣ F stirling2 (n + φ) j - F stirling2 n j := by
      rw [← hφ]; exact F_period isStirling hk (by omega) j
    have h3 : (k : ℤ) ∣ (-3 : ℤ) ^ (n - j + φ) - (-3 : ℤ) ^ (n - j) := by
      rw [← hφ]; exact pow_period_int hk (by omega) (-3)
    have hsub : n + φ - j = n - j + φ := by omega
    rw [sign_pow (by omega : j ≤ n), sign_pow (by omega : j ≤ n + φ), hsub]
    have key : (-3 : ℤ) ^ (n - j) * 2 ^ j * F stirling2 n j
          - (-3 : ℤ) ^ (n - j + φ) * 2 ^ j * F stirling2 (n + φ) j
        = -(((-3 : ℤ) ^ (n - j + φ) - (-3 : ℤ) ^ (n - j)) * (2 ^ j * F stirling2 (n + φ) j)
            + (-3 : ℤ) ^ (n - j) * 2 ^ j * (F stirling2 (n + φ) j - F stirling2 n j)) := by
      ring
    rw [key]
    exact (dvd_neg (a := (k : ℤ))).mpr
      (dvd_add (Dvd.dvd.mul_right h3 _) (Dvd.dvd.mul_left hF _))
  · -- large `j`: both terms are multiples of `k`
    exact dvd_sub (Dvd.dvd.mul_left (dvd_F stirling2 hk hjk n) _)
      (Dvd.dvd.mul_left (dvd_F stirling2 hk hjk (n + φ)) _)
