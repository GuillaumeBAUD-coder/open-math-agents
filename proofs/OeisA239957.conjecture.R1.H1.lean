import OMAReductions.R_OeisA239957_conjecture_R1
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Proof of `OeisA239957.conjecture.R1.H1`

Proves that for every safe prime `p = 2 * q + 1` with `q > 2` prime, if
`p % 8 = 3 ∨ p % 5 = 2 ∨ p % 5 = 3`, then `OeisA239957.A p` holds, i.e., there exists `k : ℤ`
with `k ^ 2 + 1 < p` and `orderOf (k ^ 2 + 1 : ZMod p) = p - 1`.

For any quadratic non-residue `a` modulo a safe prime `p = 2 * q + 1` with `a ≢ 0, 1, -1 (mod p)`:
`orderOf (a : ZMod p)` divides `2 * q`, cannot be `1` or `2` (since `a ≠ ±1`), and cannot be `q`
(by Euler's criterion `a ^ q = legendreSym p a = -1 ≠ 1`), so `orderOf (a : ZMod p) = 2 * q = p - 1`.
- When `p % 8 = 3`, `2 = 1 ^ 2 + 1` is a quadratic non-residue by the second supplement.
- When `p % 5 = 2 ∨ p % 5 = 3`, `5 = 2 ^ 2 + 1` is a quadratic non-residue by quadratic reciprocity.
-/

namespace OeisA239957R1H1Proof

private lemma orderOf_eq_sub_one_of_safe_prime {q a : ℕ} (hq : q.Prime) (hq2 : 2 < q)
    (hp : (2 * q + 1).Prime) (ha0 : (a : ZMod (2 * q + 1)) ≠ 0)
    (ha1 : (a : ZMod (2 * q + 1)) ≠ 1) (ha_neg1 : (a : ZMod (2 * q + 1)) ≠ -1)
    (hnonsq : ¬ IsSquare (a : ZMod (2 * q + 1))) :
    orderOf (a : ZMod (2 * q + 1)) = 2 * q := by
  set p := 2 * q + 1
  have : Fact p.Prime := ⟨hp⟩
  have hflt : (a : ZMod p) ^ (2 * q) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one ha0
    simpa [p] using this
  have hdvd : orderOf (a : ZMod p) ∣ 2 * q := orderOf_dvd_of_pow_eq_one hflt
  have hne1 : orderOf (a : ZMod p) ≠ 1 := fun h1 => ha1 (orderOf_eq_one_iff.mp h1)
  have hne2 : orderOf (a : ZMod p) ≠ 2 := by
    intro h2
    have hsq : (a : ZMod p) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    have hfac : ((a : ZMod p) - 1) * ((a : ZMod p) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact ha1 (sub_eq_zero.mp h)
    · exact ha_neg1 (eq_neg_of_add_eq_zero_left h)
  have hneq : orderOf (a : ZMod p) ≠ q := by
    intro hq_ord
    have haq : (a : ZMod p) ^ q = 1 := by rw [← hq_ord]; exact pow_orderOf_eq_one _
    have hleg : legendreSym p (a : ℤ) = -1 := by
      rw [legendreSym.eq_neg_one_iff]
      simpa using hnonsq
    have heuler : ((legendreSym p (a : ℤ) : ℤ) : ZMod p) = (a : ZMod p) ^ (p / 2) := by
      simpa using (legendreSym.eq_pow p (a : ℤ))
    have hdiv : p / 2 = q := by dsimp [p]; omega
    rw [hleg, hdiv, haq] at heuler
    have h2zero : ((2 : ℕ) : ZMod p) = 0 := by
      have : (1 : ZMod p) - (-1 : ZMod p) = 0 := by
        rw [Int.cast_neg, Int.cast_one] at heuler; rw [heuler]; simp
      have h2eq : ((2 : ℕ) : ZMod p) = (1 : ZMod p) - (-1 : ZMod p) := by norm_num
      rw [h2eq]; exact this
    have := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h2zero)
    omega
  -- Divisors of 2 * q are 1, 2, q, 2 * q
  obtain ⟨d1, d2, hd1, hd2, hprod⟩ := Nat.dvd_mul.mp hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hd2 with rfl | rfl
  · simp at hprod; exact absurd hprod.symm hne1
  · simp at hprod; exact absurd hprod.symm hneq
  · simp at hprod; exact absurd hprod.symm hne2
  · exact hprod.symm

private lemma not_sq_2_mod5 : ¬ IsSquare (2 : ZMod 5) := by decide

private lemma not_sq_3_mod5 : ¬ IsSquare (3 : ZMod 5) := by decide

end OeisA239957R1H1Proof

theorem OMA.solution : OMA.R_OeisA239957_conjecture_R1.H1 := by
  intro q hq hq2 hp hcond
  set p := 2 * q + 1
  have hp7 : 7 ≤ p := by dsimp [p]; omega
  have : Fact p.Prime := ⟨hp⟩
  have hcast_ne0 : ∀ m : ℕ, 0 < m → m < p → (m : ZMod p) ≠ 0 := by
    intro m hm0 hmp h0
    have := Nat.le_of_dvd hm0 ((ZMod.natCast_eq_zero_iff m p).mp h0)
    omega
  rcases hcond with h8 | h5
  · -- Case p % 8 = 3: witness k = 1, k^2 + 1 = 2
    refine ⟨1, by omega, ?_⟩
    have h2_0 : (2 : ZMod p) ≠ 0 := hcast_ne0 2 (by decide) (by omega)
    have h2_1 : (2 : ZMod p) ≠ 1 := by
      intro h; have h10 : ((1 : ℕ) : ZMod p) = 0 := by
        have hsub : (2 : ZMod p) - 1 = 0 := sub_eq_zero.mpr h
        push_cast; linear_combination hsub
      exact hcast_ne0 1 (by decide) (by omega) h10
    have h2_neg1 : (2 : ZMod p) ≠ -1 := by
      intro h; have h30 : ((3 : ℕ) : ZMod p) = 0 := by
        have : (2 : ZMod p) + 1 = 0 := by linear_combination h
        have h3 : ((3 : ℕ) : ZMod p) = (2 : ZMod p) + 1 := by norm_num
        rw [h3]; exact this
      exact hcast_ne0 3 (by decide) (by omega) h30
    have hnonsq : ¬ IsSquare (2 : ZMod p) := by
      rw [ZMod.exists_sq_eq_two_iff (by omega : p ≠ 2)]
      omega
    have hord := OeisA239957R1H1Proof.orderOf_eq_sub_one_of_safe_prime hq hq2 hp h2_0 h2_1 h2_neg1 hnonsq
    have hcast : ((1 : ℤ) ^ 2 + 1 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_num
    rw [hcast, hord]
    dsimp [p]
  · -- Case p % 5 = 2 ∨ p % 5 = 3: witness k = 2, k^2 + 1 = 5
    refine ⟨2, by omega, ?_⟩
    have h5_0 : (5 : ZMod p) ≠ 0 := hcast_ne0 5 (by decide) (by omega)
    have h5_1 : (5 : ZMod p) ≠ 1 := by
      intro h; have h40 : ((4 : ℕ) : ZMod p) = 0 := by
        have : (5 : ZMod p) - 1 = 0 := sub_eq_zero.mpr h
        have h4 : ((4 : ℕ) : ZMod p) = (5 : ZMod p) - 1 := by norm_num
        rw [h4]; exact this
      exact hcast_ne0 4 (by decide) (by omega) h40
    have h5_neg1 : (5 : ZMod p) ≠ -1 := by
      intro h; have h60 : ((6 : ℕ) : ZMod p) = 0 := by
        have : (5 : ZMod p) + 1 = 0 := by linear_combination h
        have h6 : ((6 : ℕ) : ZMod p) = (5 : ZMod p) + 1 := by norm_num
        rw [h6]; exact this
      exact hcast_ne0 6 (by decide) (by omega) h60
    have hnonsq : ¬ IsSquare (5 : ZMod p) := by
      have : Fact (Nat.Prime 5) := ⟨by decide⟩
      have hqr : legendreSym p 5 = legendreSym 5 p := by
        have h := legendreSym.quadratic_reciprocity' (p := p) (q := 5) (by omega) (by decide)
        have h5mod : 5 % 4 = 1 := by decide
        have hsign : (-1 : ℤ) ^ (p / 2 * (5 / 2)) = 1 := by
          have : p / 2 * (5 / 2) = 2 * (p / 2) := by omega
          rw [this, pow_mul]
          norm_num
        rw [hsign, one_mul] at h
        exact h.symm
      have hleg5 : legendreSym 5 (p : ℤ) = -1 := by
        rw [legendreSym.mod 5 (p : ℤ)]
        have hmod : (p : ℤ) % 5 = 2 ∨ (p : ℤ) % 5 = 3 := by omega
        rw [Nat.cast_ofNat]
        rcases hmod with hm | hm
        · rw [hm, legendreSym.eq_neg_one_iff]; simpa using OeisA239957R1H1Proof.not_sq_2_mod5
        · rw [hm, legendreSym.eq_neg_one_iff]; simpa using OeisA239957R1H1Proof.not_sq_3_mod5
      have hlegp : legendreSym p (5 : ℤ) = -1 := by
        simpa using hqr.trans hleg5
      have := (legendreSym.eq_neg_one_iff p).mp hlegp
      simpa using this
    have hord := OeisA239957R1H1Proof.orderOf_eq_sub_one_of_safe_prime hq hq2 hp h5_0 h5_1 h5_neg1 hnonsq
    have hcast : ((2 : ℤ) ^ 2 + 1 : ZMod p) = ((5 : ℕ) : ZMod p) := by norm_num
    rw [hcast, hord]
    dsimp [p]
