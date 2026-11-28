import OMAStatements.S_mse_3587363
import Mathlib

/-!
# Reduction of n! + k = a^b (n > k > 3) to two special shapes of k

Proved inside `main`: if n! + k = a^b with b ≥ 2 and n > k > 3, then either
k = p is prime with p < n < 2p and (n-p)! ≡ 1 mod p, or k = c^b is a perfect
b-th power with the same exponent b. For every prime p dividing k the valuation
of n! is larger than that of k, so the valuation of n! + k equals that of k
and must be a multiple of b. For prime k with n ≥ 2k one gets valuation 1.
For p < n < 2p, Wilson's theorem gives n!/p ≡ -(n-p)! mod p.
-/

namespace OMA.R_mse_3587363_R1

/-- Prime k = p in the window p < n < 2p with the Wilson-type congruence (n-p)! ≡ 1 mod p. -/
def H1 : Prop :=
  ∀ n p a b : ℕ, p.Prime → 3 < p → p < n → n < 2 * p → 2 ≤ b →
    ((n - p).factorial : ZMod p) = 1 → n.factorial + p = a ^ b → False

/-- k = c^b a perfect power with the same exponent b. -/
def H2 : Prop :=
  ∀ n c a b : ℕ, 2 ≤ c → 2 ≤ b → 3 < c ^ b → c ^ b < n →
    n.factorial + c ^ b = a ^ b → False

theorem main : H1 → H2 → type_of% @OMA.S_mse_3587363.main := by
  intro h1 h2 n k a b hk hb h
  by_contra hnk
  push Not at hnk
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at h
    omega
  -- valuation lemma
  have val : ∀ p e x : ℕ, p.Prime → p ^ e ∣ x → ¬ p ^ (e + 1) ∣ x → x = a ^ b → b ∣ e := by
    intro p e x hp hx hx' hxa
    subst hxa
    have hne : a ^ b ≠ 0 := pow_ne_zero _ ha
    have h1 := (hp.pow_dvd_iff_le_factorization hne).mp hx
    have h2 : ¬ e + 1 ≤ (a ^ b).factorization p := fun hle =>
      hx' ((hp.pow_dvd_iff_le_factorization hne).mpr hle)
    have : (a ^ b).factorization p = e := by omega
    rw [Nat.factorization_pow] at this
    simp only [Finsupp.smul_apply, smul_eq_mul] at this
    exact ⟨a.factorization p, this.symm⟩
  by_cases hkp : k.Prime
  · -- prime case
    set p := k with hpdef
    by_cases h2p : 2 * p ≤ n
    · have hsq : p ^ 2 ∣ n.factorial := by
        have h2f : (2 * p).factorial = (2 * p) * (2 * p - 1).factorial := by
          rw [show 2 * p = (2 * p - 1) + 1 by omega, Nat.factorial_succ]
          congr 1
        have hd : p ∣ (2 * p - 1).factorial := Nat.dvd_factorial hkp.pos (by omega)
        have : p ^ 2 ∣ (2 * p).factorial := by
          rw [h2f, pow_two]
          exact Nat.mul_dvd_mul (Dvd.intro_left 2 rfl) hd
        exact this.trans (Nat.factorial_dvd_factorial h2p)
      have hb1 : b ∣ 1 := by
        refine val p 1 (n.factorial + p) hkp ?_ ?_ h
        · rw [pow_one]
          exact Nat.dvd_add (hkp.dvd_factorial.mpr (by omega)) dvd_rfl
        · intro hd
          have : p ^ 2 ∣ p := (Nat.dvd_add_right hsq).mp hd
          have := Nat.le_of_dvd hkp.pos this
          have : p * p ≤ p := by rw [pow_two] at *; assumption
          nlinarith [hkp.two_le]
      have := Nat.le_of_dvd one_pos hb1
      omega
    · push Not at h2p
      -- (p + m)! = p * M with M ≡ -(m!) mod p
      have key : ∀ m : ℕ, ∃ M : ℕ, (p + m).factorial = p * M ∧
          ((M : ℕ) : ZMod p) = -((m.factorial : ℕ) : ZMod p) := by
        intro m
        induction m with
        | zero =>
          refine ⟨(p - 1).factorial, ?_, ?_⟩
          · rw [Nat.add_zero, ← Nat.mul_factorial_pred hkp.ne_zero]
          · have := Fact.mk hkp
            rw [ZMod.wilsons_lemma]
            simp
        | succ m ih =>
          obtain ⟨M, hM, hMc⟩ := ih
          refine ⟨(p + m + 1) * M, ?_, ?_⟩
          · rw [show p + (m + 1) = (p + m) + 1 by omega, Nat.factorial_succ, hM]
            ring
          · push_cast
            rw [hMc, Nat.factorial_succ]
            push_cast
            rw [ZMod.natCast_self]
            ring
      obtain ⟨M, hM, hMc⟩ := key (n - p)
      rw [show p + (n - p) = n by omega] at hM
      by_cases hw : (((n - p).factorial : ℕ) : ZMod p) = 1
      · exact h1 n p a b hkp hk hnk h2p hb hw h
      · have hb1 : b ∣ 1 := by
          refine val p 1 (n.factorial + p) hkp ?_ ?_ h
          · rw [pow_one, hM]
            exact Nat.dvd_add (Dvd.intro M rfl) dvd_rfl
          · intro hd
            rw [hM, show p * M + p = p * (M + 1) by ring, pow_succ, pow_one] at hd
            have hd' : p ∣ M + 1 := Nat.dvd_of_mul_dvd_mul_left hkp.pos hd
            have : ((M + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd'
            push_cast at this
            rw [hMc] at this
            apply hw
            linear_combination -this
        have := Nat.le_of_dvd one_pos hb1
        omega
  · -- composite case
    have hk0 : k ≠ 0 := by omega
    have hdiv : ∀ p, b ∣ k.factorization p := by
      intro p
      by_cases hp : p.Prime
      · by_cases hpk : p ∣ k
        · have hplt : p < k := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpk)
            (fun he => hkp (he ▸ hp))
          refine val p (k.factorization p) (n.factorial + k) hp ?_ ?_ h
          · exact Nat.dvd_add
              ((Nat.ordProj_dvd k p).trans ((Nat.dvd_factorial (by omega) le_rfl).trans
                (Nat.factorial_dvd_factorial hnk.le)))
              (Nat.ordProj_dvd k p)
          · intro hd
            have hn : p ^ (k.factorization p + 1) ∣ n.factorial := by
              have hkf : k.factorial = k * (k - 1).factorial := by
                rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ]
                congr 1
              have hpd : p ∣ (k - 1).factorial := Nat.dvd_factorial hp.pos (by omega)
              have : p ^ (k.factorization p + 1) ∣ k.factorial := by
                rw [hkf, pow_succ]
                exact Nat.mul_dvd_mul (Nat.ordProj_dvd k p) hpd
              exact this.trans (Nat.factorial_dvd_factorial hnk.le)
            exact Nat.pow_succ_factorization_not_dvd hk0 hp ((Nat.dvd_add_right hn).mp hd)
        · rw [Nat.factorization_eq_zero_of_not_dvd hpk]
          exact dvd_zero b
      · rw [Nat.factorization_eq_zero_of_not_prime k hp]
        exact dvd_zero b
    set c := k.factorization.prod fun p e => p ^ (e / b) with hc
    have hck : c ^ b = k := by
      rw [hc, Finsupp.prod, ← Finset.prod_pow]
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hk0]
      rw [Finsupp.prod]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [← pow_mul, Nat.div_mul_cancel (hdiv p)]
    have hc2 : 2 ≤ c := by
      by_contra hc2
      interval_cases c
      · rw [zero_pow (by omega)] at hck; omega
      · rw [one_pow] at hck; omega
    exact h2 n c a b hc2 hb (hck ▸ hk) (hck ▸ hnk) (hck ▸ h)

end OMA.R_mse_3587363_R1
