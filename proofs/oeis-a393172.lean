import OMAStatements.S_oeis_a393172
import Mathlib

/-!
# Proof of OEIS A393172 Conjecture

By strong induction on `n >= 1`, we prove `(a n : ZMod 4) = target n`, where
`target 1 = 1`, `target n = 2` if `n = 2^r` for some `r >= 1`, and `target n = 0` otherwise.
- For `n = 2`: direct calculation gives `a 2 = 2`.
- For `n >= 3`:
  1. In `∑_{j=1..n-1} a(j) * a(n - j)` mod `4`: terms with `2 <= j <= n - 2` have both factors even
     (hence `0 mod 4`), while the `j = 1` and `j = n - 1` terms sum to `2 * a(n - 1) ≡ 0 (mod 4)`.
  2. In `-∑_{k=1..n-1} (-1)^(n - k) C(k, n - k) a(k)` mod `4`:
     - `k = 1` gives `C(1, n - 1) = 0`.
     - `k >= 2` not a power of `2` has `a(k) ≡ 0 (mod 4)`.
     - `k = 2^r` (`r >= 1`) has `a(2^r) ≡ 2 (mod 4)`, and `C(2^r, n - 2^r)` is even unless
       `n - 2^r = 2^r` (i.e. `n = 2^(r + 1)`), where `C(2^r, 2^r) = 1` contributes `2 (mod 4)`.
-/

namespace OeisA393172Proof

open Finset OMA.S_oeis_a393172 Classical

private lemma two_dvd_choose_pow_two {r m : ℕ} (hm0 : 0 < m) (hmlt : m < 2 ^ r) :
    2 ∣ Nat.choose (2 ^ r) m := by
  have hpoly_all : ∀ k : ℕ, ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ (2 ^ k)) =
      1 + Polynomial.X ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih]
      have hsq : ∀ p q : Polynomial (ZMod 2), (p + q) ^ 2 = p ^ 2 + q ^ 2 := by
        intro p q
        have h2 : (2 : Polynomial (ZMod 2)) = 0 := by
          change ((2 : ℕ) : Polynomial (ZMod 2)) = 0
          rw [← Polynomial.C_eq_natCast, show ((2 : ℕ) : ZMod 2) = 0 by decide, map_zero]
        calc (p + q) ^ 2 = p ^ 2 + 2 * (p * q) + q ^ 2 := by ring
          _ = p ^ 2 + q ^ 2 := by rw [h2, zero_mul, add_zero]
      rw [hsq, one_pow, ← pow_mul, ← pow_succ]
  have hpoly := hpoly_all r
  have hcoeff := congrArg (fun P : Polynomial (ZMod 2) => P.coeff m) hpoly
  have hLHS : ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ (2 ^ r)).coeff m =
      (Nat.choose (2 ^ r) m : ZMod 2) := by
    rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single m]
    · simp [Polynomial.coeff_X_pow]
    · intro i _ hne
      simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hRHS : (1 + Polynomial.X ^ (2 ^ r) : Polynomial (ZMod 2)).coeff m = 0 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow]
    simp [show m ≠ 0 by omega, show m ≠ 2 ^ r by omega]
  rw [hLHS, hRHS] at hcoeff
  exact (ZMod.natCast_eq_zero_iff _ 2).mp hcoeff

private noncomputable def target (n : ℕ) : ZMod 4 :=
  if n = 1 then 1 else if ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k then 2 else 0

private lemma target_mul_two_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    (2 : ZMod 4) * target n = 0 := by
  unfold target
  have hne : n ≠ 1 := by omega
  simp only [hne, ↓reduceIte]
  split_ifs <;> decide

private lemma target_mul_target_eq_zero {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    target i * target j = 0 := by
  unfold target
  have hi1 : i ≠ 1 := by omega
  have hj1 : j ≠ 1 := by omega
  simp only [hi1, hj1, ↓reduceIte]
  split_ifs <;> decide

private lemma a_zmod4_eq_target : ∀ n : ℕ, 1 ≤ n → (a n : ZMod 4) = target n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    match n with
    | 0 => omega
    | 1 =>
      simp [OMA.S_oeis_a393172.a, target]
    | 2 =>
      have ha2 : OMA.S_oeis_a393172.a 2 = 2 := by
        unfold OMA.S_oeis_a393172.a
        simp [OMA.S_oeis_a393172.a]
      have ht2 : target 2 = 2 := by
        unfold target
        have hex : ∃ k : ℕ, 1 ≤ k ∧ 2 = 2 ^ k := ⟨1, le_refl 1, by norm_num⟩
        simp [hex]
      rw [ha2, ht2]; decide
    | m + 3 =>
      conv_lhs => unfold OMA.S_oeis_a393172.a
      push_cast
      have hconv :
          ∑ j : Fin (m + 2), (a (j.1 + 1) : ZMod 4) * (a (m + 2 - j.1) : ZMod 4) = 0 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        simp only [Fin.val_zero, zero_add, Nat.sub_zero, Fin.val_succ, Fin.val_last, Fin.val_castSucc]
        have hsub_last : m + 2 - (m + 1) = 1 := by omega
        rw [hsub_last]
        have h1 : (a 1 : ZMod 4) = 1 := by simp [OMA.S_oeis_a393172.a]
        have hm2 : (a (m + 2) : ZMod 4) = target (m + 2) := ih (m + 2) (by omega) (by omega)
        have hmid : ∑ i : Fin m,
            (a (i.1 + 1 + 1) : ZMod 4) * (a (m + 2 - (i.1 + 1)) : ZMod 4) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          have hi := i.2
          rw [ih (i.1 + 1 + 1) (by omega) (by omega), ih (m + 2 - (i.1 + 1)) (by omega) (by omega)]
          exact target_mul_target_eq_zero (by omega) (by omega)
        rw [hmid, zero_add, h1, hm2]
        calc (1 : ZMod 4) * target (m + 2) + target (m + 2) * 1
            = (2 : ZMod 4) * target (m + 2) := by ring
          _ = 0 := target_mul_two_eq_zero (by omega)
      rw [hconv, zero_sub]
      -- Now evaluate - ∑ k : Fin (m + 2), (-1)^(m + 2 - k) * C(k + 1, m + 2 - k) * a (k + 1)
      have hterm : ∀ k : Fin (m + 2),
          (-1 : ZMod 4) ^ (m + 2 - k.1) * (Nat.choose (k.1 + 1) (m + 2 - k.1) : ZMod 4) *
            (a (k.1 + 1) : ZMod 4) =
          if (∃ r : ℕ, 1 ≤ r ∧ k.1 + 1 = 2 ^ r) ∧ m + 3 = 2 * (k.1 + 1) then 2 else 0 := by
        intro k
        have hk := k.2
        rw [ih (k.1 + 1) (by omega) (by omega)]
        by_cases hk0 : k.1 = 0
        · rw [hk0]
          have hch0 : Nat.choose 1 (m + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have hne : ¬ (m + 3 = 2 * (0 + 1)) := by omega
          simp [hch0, hne]
        · unfold target
          have hk1 : k.1 + 1 ≠ 1 := by omega
          simp only [hk1, ↓reduceIte]
          by_cases hpow : ∃ r : ℕ, 1 ≤ r ∧ k.1 + 1 = 2 ^ r
          · simp only [hpow, ↓reduceIte, true_and]
            rcases hpow with ⟨r, hr1, hkr⟩
            by_cases hhalf : m + 3 = 2 * (k.1 + 1)
            · simp only [hhalf, ↓reduceIte]
              have hsub : m + 2 - k.1 = k.1 + 1 := by omega
              rw [hsub, Nat.choose_self, Nat.cast_one, mul_one]
              have h2eq : (-1 : ZMod 4) ^ (k.1 + 1) * 2 = 2 := by
                have hneg : (-1 : ZMod 4) * 2 = 2 := by decide
                have : ∀ e : ℕ, (-1 : ZMod 4) ^ e * 2 = 2 := by
                  intro e; induction e with
                  | zero => simp
                  | succ e ihe => rw [pow_succ, mul_assoc, hneg, ihe]
                exact this _
              exact h2eq
            · simp only [hhalf, ↓reduceIte]
              by_cases hgt : k.1 + 1 < m + 2 - k.1
              · rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero, mul_zero, zero_mul]
              · have hd : 2 ∣ Nat.choose (k.1 + 1) (m + 2 - k.1) := by
                  rw [hkr]
                  exact two_dvd_choose_pow_two (by omega) (by omega)
                rcases hd with ⟨q, hq⟩
                rw [hq]
                push_cast
                have h4 : (2 : ZMod 4) * 2 = 0 := by decide
                calc (-1 : ZMod 4) ^ (m + 2 - k.1) * ((2 : ZMod 4) * (q : ZMod 4)) * 2
                    = (-1 : ZMod 4) ^ (m + 2 - k.1) * (q : ZMod 4) * ((2 : ZMod 4) * 2) := by ring
                  _ = 0 := by rw [h4, mul_zero]
          · simp [hpow]
      have hsum_eq :
          ∑ k : Fin (m + 2),
            (-1 : ZMod 4) ^ (m + 2 - k.1) * (Nat.choose (k.1 + 1) (m + 2 - k.1) : ZMod 4) *
              (a (k.1 + 1) : ZMod 4) =
          ∑ k : Fin (m + 2),
            if (∃ r : ℕ, 1 ≤ r ∧ k.1 + 1 = 2 ^ r) ∧ m + 3 = 2 * (k.1 + 1) then (2 : ZMod 4) else 0 := by
        apply Finset.sum_congr rfl
        intro k _; exact hterm k
      rw [hsum_eq]
      unfold target
      have hne1 : m + 3 ≠ 1 := by omega
      simp only [hne1, ↓reduceIte]
      by_cases hex : ∃ r : ℕ, 1 ≤ r ∧ m + 3 = 2 ^ r
      · simp only [hex, ↓reduceIte]
        rcases hex with ⟨r, hr1, hmr⟩
        have hr2 : 2 ≤ r := by
          by_contra hlt
          have : r = 1 := by omega
          rw [this] at hmr; omega
        have hklt : 2 ^ (r - 1) - 1 < m + 2 := by
          have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
            have : r = (r - 1) + 1 := by omega
            conv_lhs => rw [this, pow_succ, mul_comm]
          have hpos : 2 ≤ 2 ^ (r - 1) := by
            have : 1 ≤ r - 1 := by omega
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        let k0 : Fin (m + 2) := ⟨2 ^ (r - 1) - 1, hklt⟩
        rw [Finset.sum_eq_single k0]
        · have hk0_eq : k0.1 + 1 = 2 ^ (r - 1) := by
            have : 1 ≤ 2 ^ (r - 1) := Nat.one_le_pow _ _ (by omega)
            simp [k0]; omega
          have hpow2 : m + 3 = 2 * (k0.1 + 1) := by
            rw [hk0_eq, hmr]
            have : r = (r - 1) + 1 := by omega
            conv_lhs => rw [this, pow_succ, mul_comm]
          have hcond : (∃ s : ℕ, 1 ≤ s ∧ k0.1 + 1 = 2 ^ s) ∧ m + 3 = 2 * (k0.1 + 1) :=
            ⟨⟨r - 1, by omega, hk0_eq⟩, hpow2⟩
          simp only [hcond]
          decide
        · intro k _ hne
          have hnot : ¬ ((∃ s : ℕ, 1 ≤ s ∧ k.1 + 1 = 2 ^ s) ∧ m + 3 = 2 * (k.1 + 1)) := by
            rintro ⟨_, h2k⟩
            apply hne
            apply Fin.ext
            have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
              have : r = (r - 1) + 1 := by omega
              conv_lhs => rw [this, pow_succ, mul_comm]
            have : 1 ≤ 2 ^ (r - 1) := Nat.one_le_pow _ _ (by omega)
            dsimp [k0]; omega
          simp [hnot]
        · intro h; exact absurd (Finset.mem_univ k0) h
      · simp only [hex, ↓reduceIte]
        have hzero : ∑ k : Fin (m + 2),
            (if (∃ r : ℕ, 1 ≤ r ∧ k.1 + 1 = 2 ^ r) ∧ m + 3 = 2 * (k.1 + 1) then (2 : ZMod 4) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          have hnot : ¬ ((∃ r : ℕ, 1 ≤ r ∧ k.1 + 1 = 2 ^ r) ∧ m + 3 = 2 * (k.1 + 1)) := by
            rintro ⟨⟨r, hr1, hkr⟩, h2k⟩
            apply hex
            refine ⟨r + 1, by omega, ?_⟩
            rw [h2k, hkr, pow_succ, mul_comm]
          simp [hnot]
        rw [hzero, neg_zero]

end OeisA393172Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a393172.main := by
  intro n hn
  have h := OeisA393172Proof.a_zmod4_eq_target n (by omega)
  constructor
  · rintro ⟨k, rfl⟩
    change OMA.S_oeis_a393172.a (2 ^ k) ≡ 2 [ZMOD ((4 : ℕ) : ℤ)]
    rw [← ZMod.intCast_eq_intCast_iff, h]
    unfold OeisA393172Proof.target
    have hk1 : 1 ≤ k := by
      cases k with
      | zero => simp at hn
      | succ k => omega
    have hk0 : k ≠ 0 := by omega
    simp [hk0, hk1]
  · intro hnot
    change OMA.S_oeis_a393172.a n ≡ 0 [ZMOD ((4 : ℕ) : ℤ)]
    rw [← ZMod.intCast_eq_intCast_iff, h]
    unfold OeisA393172Proof.target
    have hne : n ≠ 1 := by omega
    have hnot' : ¬ ∃ r : ℕ, 1 ≤ r ∧ n = 2 ^ r := by
      rintro ⟨r, _, hr⟩; exact hnot ⟨r, hr⟩
    simp [hne, hnot']
