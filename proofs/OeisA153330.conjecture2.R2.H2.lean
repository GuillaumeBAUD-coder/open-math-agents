import OMAReductions.R_OeisA153330_conjecture2_R2
import Mathlib

-- Step OeisA153330.conjecture2.R2.H2: hypothesis H2 of reduction OeisA153330.conjecture2.R2
-- (Collatz step differences). If 3^(K+1) divides 2^s + 1 then 3^K divides s.
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: s must be odd, because for even s the number 2^s + 1 is 2 modulo 3. For odd s, lifting the exponent
-- gives v_3(2^s + 1) = v_3(2 + 1) + v_3(s) = 1 + v_3(s), so K + 1 <= 1 + v_3(s).

theorem OMA.solution : OMA.R_OeisA153330_conjecture2_R2.H2 := by
  intro K s h
  have h4t : ∀ t : ℕ, 4 ^ t % 3 = 1 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [pow_succ]
      omega
  have hs : Odd s := by
    by_contra hns
    obtain ⟨t, rfl⟩ := Nat.not_odd_iff_even.mp hns
    have h3 : 3 ∣ 2 ^ (t + t) + 1 := dvd_trans (dvd_pow_self 3 (Nat.succ_ne_zero K)) h
    have e : 2 ^ (t + t) = 4 ^ t := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [e] at h3
    have h1 := h4t t
    omega
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) ⟨1, by norm_num⟩ (by norm_num) (by norm_num) hs
  rw [one_pow] at hv
  have h21 : padicValNat 3 (2 + 1) = 1 := padicValNat_self
  have hne : 2 ^ s + 1 ≠ 0 := by positivity
  have hle : K + 1 ≤ padicValNat 3 (2 ^ s + 1) := (padicValNat_dvd_iff_le hne).mp h
  have hK : K ≤ padicValNat 3 s := by omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  exact (padicValNat_dvd_iff_le hs0).mpr hK
