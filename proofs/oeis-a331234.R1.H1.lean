import OMAReductions.R_oeis_a331234_R1

/-!
Proves `oeis-a331234.R1.H1`: if `x` and `y` are primes satisfying the negative Pell equation
`x ^ 2 + 1 = 2 * y ^ 2`, then `(x, y)` is the `n`-th iterate of `(a, b) ↦ (a + 2b, a + b)`
starting from `(1, 0)` for a prime index `n`.

Proof outline:
1. Strong descent on `y` shows every positive solution `(x, y)` of `x ^ 2 - 2 * y ^ 2 = ±1`
   is an iterate `pell n` of `(a, b) ↦ (a + 2b, a + b)` from `(1, 0)`.
2. The norm invariant `(pell n).1 ^ 2 - 2 * (pell n).2 ^ 2 = (-1) ^ n` forces `n` to be odd.
3. Addition formula for `pell (m + n)` implies `(pell d).1 ∣ (pell (d * (2 * k + 1))).1`.
4. Strict monotonicity of `(pell n).1` for `n ≥ 1` with `(pell 1).1 = 1` forces `n = n.minFac`,
   so `n` is prime.
-/

namespace OMA.Proof_oeis_a331234_R1_H1

private def step (a : ℕ × ℕ) : ℕ × ℕ := (a.1 + 2 * a.2, a.1 + a.2)

private def pell (n : ℕ) : ℕ × ℕ := step^[n] (1, 0)

private lemma pell_zero : pell 0 = (1, 0) := rfl

private lemma pell_one : pell 1 = (1, 1) := rfl

private lemma pell_succ (n : ℕ) :
    pell (n + 1) = ((pell n).1 + 2 * (pell n).2, (pell n).1 + (pell n).2) := by
  simp [pell, Function.iterate_succ_apply', step]

private lemma pell_norm (n : ℕ) :
    ((pell n).1 : ℤ) ^ 2 - 2 * ((pell n).2 : ℤ) ^ 2 = (-1 : ℤ) ^ n := by
  induction n with
  | zero => simp [pell_zero]
  | succ n ih =>
    rw [pell_succ]
    dsimp only
    push_cast
    calc
      (((pell n).1 : ℤ) + 2 * ((pell n).2 : ℤ)) ^ 2 -
          2 * (((pell n).1 : ℤ) + ((pell n).2 : ℤ)) ^ 2
        = -(((pell n).1 : ℤ) ^ 2 - 2 * ((pell n).2 : ℤ) ^ 2) := by ring
      _ = -((-1 : ℤ) ^ n) := by rw [ih]
      _ = (-1 : ℤ) ^ (n + 1) := by rw [pow_succ]; ring

private lemma pell_add (m n : ℕ) :
    pell (m + n) =
      ((pell m).1 * (pell n).1 + 2 * (pell m).2 * (pell n).2,
       (pell m).1 * (pell n).2 + (pell m).2 * (pell n).1) := by
  induction n with
  | zero => simp [pell_zero]
  | succ n ih =>
    rw [← Nat.add_assoc, pell_succ, ih, pell_succ]
    ext <;> dsimp <;> ring

private lemma pell_fst_dvd_mul_odd (d k : ℕ) :
    (pell d).1 ∣ (pell (d * (2 * k + 1))).1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    have hidx : d * (2 * (k + 1) + 1) = d * (2 * k + 1) + (d + d) := by ring
    rw [hidx, pell_add, pell_add]
    dsimp only
    rw [hc]
    refine ⟨c * ((pell d).1 * (pell d).1 + 2 * (pell d).2 * (pell d).2) +
      4 * (pell (d * (2 * k + 1))).2 * (pell d).2, ?_⟩
    ring

private lemma pell_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ (pell n).1 ∧ 1 ≤ (pell n).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [pell_one]
    | succ m =>
      have h := ih (by omega)
      rw [pell_succ]
      dsimp only
      omega

private lemma pell_fst_lt_of_lt {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    (pell m).1 < (pell n).1 := by
  induction n with
  | zero => omega
  | succ k ih =>
    have hstep : (pell k).1 < (pell (k + 1)).1 := by
      have hk : 1 ≤ k := by omega
      have hp := (pell_pos hk).2
      rw [pell_succ]
      dsimp only
      omega
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hmn) with hlt | rfl
    · exact (ih hlt).trans hstep
    · exact hstep

private lemma exists_pell_of_norm (x y : ℕ)
    (h : (x : ℤ) ^ 2 - 2 * (y : ℤ) ^ 2 = 1 ∨ (x : ℤ) ^ 2 - 2 * (y : ℤ) ^ 2 = -1) :
    ∃ n : ℕ, pell n = (x, y) := by
  induction y using Nat.strong_induction_on generalizing x with
  | _ y ih =>
    by_cases hy : y = 0
    · subst hy
      simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, sub_zero] at h
      have hx : x = 1 := by
        rcases h with h1 | h2
        · nlinarith
        · nlinarith [sq_nonneg (x : ℤ)]
      exact ⟨0, by simp [pell_zero, hx]⟩
    · have hy1 : 1 ≤ y := Nat.pos_of_ne_zero hy
      have hyx : y ≤ x := by
        have hsq : (y : ℤ) ^ 2 ≤ (x : ℤ) ^ 2 := by
          rcases h with h1 | h2 <;> nlinarith
        nlinarith
      have hx2y : x < 2 * y := by
        have hsq : (x : ℤ) ^ 2 < (2 * (y : ℤ)) ^ 2 := by
          rcases h with h1 | h2 <;> nlinarith
        nlinarith
      let x' : ℕ := 2 * y - x
      let y' : ℕ := x - y
      have hy'lt : y' < y := by dsimp [y']; omega
      have hcast_x' : (x' : ℤ) = 2 * (y : ℤ) - (x : ℤ) := by
        dsimp [x']; omega
      have hcast_y' : (y' : ℤ) = (x : ℤ) - (y : ℤ) := by
        dsimp [y']; omega
      have hnorm' : (x' : ℤ) ^ 2 - 2 * (y' : ℤ) ^ 2 = 1 ∨ (x' : ℤ) ^ 2 - 2 * (y' : ℤ) ^ 2 = -1 := by
        have hid : (x' : ℤ) ^ 2 - 2 * (y' : ℤ) ^ 2 = -((x : ℤ) ^ 2 - 2 * (y : ℤ) ^ 2) := by
          rw [hcast_x', hcast_y']; ring
        rcases h with h1 | h2
        · right; linarith
        · left; linarith
      obtain ⟨m, hm⟩ := ih y' hy'lt x' hnorm'
      refine ⟨m + 1, ?_⟩
      rw [pell_succ, hm]
      ext <;> dsimp [x', y'] <;> omega

end OMA.Proof_oeis_a331234_R1_H1

theorem OMA.solution : OMA.R_oeis_a331234_R1.H1 := by
  intro x y hx _ hxy
  have hnorm : (x : ℤ) ^ 2 - 2 * (y : ℤ) ^ 2 = -1 := by
    have hz : (x : ℤ) ^ 2 + 1 = 2 * (y : ℤ) ^ 2 := by exact_mod_cast hxy
    linarith
  obtain ⟨n, hn⟩ := OMA.Proof_oeis_a331234_R1_H1.exists_pell_of_norm x y (Or.inr hnorm)
  have hodd : Odd n := by
    by_contra he
    rw [Nat.not_odd_iff_even] at he
    have hpow : (-1 : ℤ) ^ n = 1 := he.neg_one_pow
    have hpn := OMA.Proof_oeis_a331234_R1_H1.pell_norm n
    rw [hn] at hpn
    dsimp only at hpn
    linarith
  have hn1 : n ≠ 1 := by
    intro h1
    subst h1
    rw [OMA.Proof_oeis_a331234_R1_H1.pell_one] at hn
    have hx1 : x = 1 := (Prod.mk.inj hn).1.symm
    exact hx.ne_one hx1
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    rcases hodd with ⟨k, hk⟩
    omega
  have hn2 : 2 ≤ n := by omega
  let d := n.minFac
  have hd_prime : d.Prime := Nat.minFac_prime (by omega)
  have hd_dvd : d ∣ n := Nat.minFac_dvd n
  obtain ⟨k, hk⟩ := hd_dvd
  have hk_odd : Odd k := by
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hko
    · exfalso
      rcases hodd with ⟨t, ht⟩
      have : n = 2 * (d * j) := by rw [hk]; ring
      omega
    · exact hko
  rcases hk_odd with ⟨j, rfl⟩
  have hdiv : (OMA.Proof_oeis_a331234_R1_H1.pell d).1 ∣ x := by
    have h := OMA.Proof_oeis_a331234_R1_H1.pell_fst_dvd_mul_odd d j
    rw [← hk, hn] at h
    exact h
  have hd_gt1 : 1 < (OMA.Proof_oeis_a331234_R1_H1.pell d).1 := by
    have h := OMA.Proof_oeis_a331234_R1_H1.pell_fst_lt_of_lt (le_refl 1) hd_prime.one_lt
    simpa [OMA.Proof_oeis_a331234_R1_H1.pell_one] using h
  have hdx : (OMA.Proof_oeis_a331234_R1_H1.pell d).1 = x := by
    rcases hx.eq_one_or_self_of_dvd _ hdiv with h1 | hs
    · omega
    · exact hs
  have hdn : d = n := by
    have hd_le : d ≤ n := Nat.le_of_dvd (by omega) (Nat.minFac_dvd n)
    rcases lt_or_eq_of_le hd_le with hlt | heq
    · exfalso
      have hlt' := OMA.Proof_oeis_a331234_R1_H1.pell_fst_lt_of_lt hd_prime.pos hlt
      rw [hn] at hlt'
      dsimp only at hlt'
      omega
    · exact heq
  exact ⟨n, hdn ▸ hd_prime, hn⟩
