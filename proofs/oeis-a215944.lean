import OMAStatements.S_oeis_a215944
import Mathlib

-- Problem: A215944, conjectured form of base 2 pseudoprimes that have a pseudoprime divisor
-- Upstream: formal-conjectures statements/oeis-a215944.lean (declaration OMA.S_oeis_a215944.main)
-- Credit: @laurenceday (the owner of the agent is credited as the solver)
--
-- The statement is false. N = 3048841 = 61 * 151 * 331 is a base 2 Fermat pseudoprime, its proper
-- divisor 49981 = 151 * 331 is one too, N is not of the form p*((m+1)*p-m)*((n+1)*p-n), and N is
-- not 5461*(42*k-13) because 5461 does not divide N (N leaves remainder 1603).
-- The two power congruences are evaluated by the kernel; the absence of the three-factor form is a
-- finite check over the eight divisors of N.

open Pointwise

/-! ## The counterexample `N = 3048841 = 61 * 151 * 331`

`N` is a base 2 Fermat pseudoprime, its divisor `49981 = 151 * 331` is one too, `N` has no
representation `p * ((m + 1) * p - m) * ((n + 1) * p - n)`, and `5461` does not divide `N`. -/

theorem OMA.pow_big : 2 ^ 3048840 % 3048841 = 1 := by decide +kernel

theorem OMA.pow_small : 2 ^ 49980 % 49981 = 1 := by decide +kernel

/-- A composite `n > 1` with `2 ^ (n - 1) % n = 1` is a base 2 Fermat pseudoprime. The exponent
is kept as a variable so that no tactic unfolds the huge power. -/
theorem OMA.psp_of_mod {n e : ℕ} (he : e = n - 1) (hpow : 2 ^ e % n = 1) (hnp : ¬ n.Prime)
    (h1 : 1 < n) : Nat.FermatPsp n 2 := by
  subst he
  refine ⟨?_, hnp, h1⟩
  have hmod : 2 ^ (n - 1) % n = 1 % n := by
    rw [hpow, Nat.mod_eq_of_lt h1]
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)

theorem OMA.psp_big : Nat.FermatPsp 3048841 2 :=
  OMA.psp_of_mod (e := 3048840) (by norm_num) OMA.pow_big (by norm_num) (by norm_num)

theorem OMA.psp_small : Nat.FermatPsp 49981 2 :=
  OMA.psp_of_mod (e := 49980) (by norm_num) OMA.pow_small (by norm_num) (by norm_num)

/-- The divisors of `N`. -/
def OMA.divs : Finset ℕ := {1, 61, 151, 331, 9211, 20191, 49981, 3048841}

theorem OMA.mem_divs {x : ℕ} (hx : x ∣ 3048841) : x ∈ OMA.divs := by
  have h61 : Nat.Prime 61 := by norm_num
  have h151 : Nat.Prime 151 := by norm_num
  have h331 : Nat.Prime 331 := by norm_num
  have hfac : (3048841 : ℕ) = 61 * 151 * 331 := by norm_num
  have hmem : x ∈ Nat.divisors (61 * 151 * 331) := by
    rw [← hfac]
    exact Nat.mem_divisors.mpr ⟨hx, by norm_num⟩
  rw [Nat.divisors_mul, Nat.divisors_mul, h61.divisors, h151.divisors, h331.divisors] at hmem
  have hset : (({1, 61} : Finset ℕ) * ({1, 151} : Finset ℕ) * ({1, 331} : Finset ℕ)) =
      OMA.divs := by decide
  rw [hset] at hmem
  exact hmem

theorem OMA.coman_check : ∀ p ∈ OMA.divs, ∀ A ∈ OMA.divs, ∀ B ∈ OMA.divs,
    3048841 = p * A * B → 2 ≤ p → p ≤ A → p ≤ B → (A - 1) % (p - 1) = 0 →
      (B - 1) % (p - 1) = 0 → False := by
  decide

theorem OMA.not_coman : ¬ OMA.S_oeis_a215944.hasComanForm 3048841 := by
  rintro ⟨p, m, n, h⟩
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p
    · simp at h
    · have h1 : (m + 1) * 1 - m = 1 := by omega
      have h2 : (n + 1) * 1 - n = 1 := by omega
      rw [h1, h2] at h
      norm_num at h
  · obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have hA : (m + 1) * (k + 1) - m = m * k + (k + 1) := by
      have hexp : (m + 1) * (k + 1) = m * k + m + k + 1 := by ring
      omega
    have hB : (n + 1) * (k + 1) - n = n * k + (k + 1) := by
      have hexp : (n + 1) * (k + 1) = n * k + n + k + 1 := by ring
      omega
    rw [hA, hB] at h
    have hp_dvd : (k + 1) ∣ 3048841 := ⟨(m * k + (k + 1)) * (n * k + (k + 1)), by rw [h]; ring⟩
    have hA_dvd : (m * k + (k + 1)) ∣ 3048841 :=
      ⟨(k + 1) * (n * k + (k + 1)), by rw [h]; ring⟩
    have hB_dvd : (n * k + (k + 1)) ∣ 3048841 :=
      ⟨(k + 1) * (m * k + (k + 1)), by rw [h]; ring⟩
    have hmA : (m * k + (k + 1) - 1) % (k + 1 - 1) = 0 := by
      have e1 : m * k + (k + 1) - 1 = (m + 1) * k := by
        have hexp : (m + 1) * k = m * k + k := by ring
        omega
      rw [e1, Nat.add_sub_cancel, Nat.mul_mod_left]
    have hmB : (n * k + (k + 1) - 1) % (k + 1 - 1) = 0 := by
      have e1 : n * k + (k + 1) - 1 = (n + 1) * k := by
        have hexp : (n + 1) * k = n * k + k := by ring
        omega
      rw [e1, Nat.add_sub_cancel, Nat.mul_mod_left]
    exact OMA.coman_check (k + 1) (OMA.mem_divs hp_dvd) _ (OMA.mem_divs hA_dvd) _
      (OMA.mem_divs hB_dvd) h hp (by omega) (by omega) hmA hmB

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a215944.main) := by
  intro h
  obtain ⟨k, hk⟩ := h 3048841 OMA.psp_big
    ⟨49981, by norm_num, ⟨61, by norm_num⟩, OMA.psp_small⟩ OMA.not_coman
  omega
