import OMAReductions.R_OeisA108129_conjecture_R1

-- Step OeisA108129.conjecture.R1.H1: hypothesis H1 of reduction OeisA108129.conjecture.R1
-- Credit: @OrangeHeadz
-- H1 := OeisA108129.a 254602 = -1

/-!
`509203` is a Riesel number: every `509203 * 2 ^ m - 1` is divisible by one of
`3, 5, 7, 13, 17, 241`. Each of these primes divides `2 ^ 24 - 1`, so divisibility is periodic in
`m` with period `24`, and the residues `m < 24` are checked directly.
-/

namespace OMA

/-- `509203 * 2 ^ m - 1` has a factor in the covering set. -/
def Cov (m : ℕ) : Prop :=
  3 ∣ 509203 * 2 ^ m - 1 ∨ 5 ∣ 509203 * 2 ^ m - 1 ∨ 7 ∣ 509203 * 2 ^ m - 1 ∨
    13 ∣ 509203 * 2 ^ m - 1 ∨ 17 ∣ 509203 * 2 ^ m - 1 ∨ 241 ∣ 509203 * 2 ^ m - 1

theorem cov_base : ∀ m : ℕ, m < 24 → Cov m := by
  unfold Cov
  decide

theorem dvd_step (p : ℕ) (hp : p ∣ 16777215) (m : ℕ) (h : p ∣ 509203 * 2 ^ m - 1) :
    p ∣ 509203 * 2 ^ (m + 24) - 1 := by
  have hx : 1 ≤ 509203 * 2 ^ m := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero (by positivity))
  have e1 : 509203 * 2 ^ (m + 24) = 16777216 * (509203 * 2 ^ m) := by
    rw [pow_add]
    ring
  have e : 509203 * 2 ^ (m + 24) - 1 = 16777216 * (509203 * 2 ^ m - 1) + 16777215 := by
    rw [e1]
    omega
  rw [e]
  exact dvd_add (Dvd.dvd.mul_left h _) hp

theorem cov_step (m : ℕ) (h : Cov m) : Cov (m + 24) := by
  unfold Cov at h ⊢
  rcases h with h | h | h | h | h | h
  · exact Or.inl (dvd_step 3 (by decide) m h)
  · exact Or.inr (Or.inl (dvd_step 5 (by decide) m h))
  · exact Or.inr (Or.inr (Or.inl (dvd_step 7 (by decide) m h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (dvd_step 13 (by decide) m h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (dvd_step 17 (by decide) m h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (dvd_step 241 (by decide) m h)))))

theorem cov_all (m : ℕ) : Cov m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 24
    · exact cov_base m hm
    · have h1 := cov_step (m - 24) (ih (m - 24) (by omega))
      rwa [Nat.sub_add_cancel (by omega)] at h1

theorem not_prime (m : ℕ) (hm : m ≠ 0) : ¬ (509203 * 2 ^ m - 1).Prime := by
  intro hp
  have h2 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hm)
  have hN : 241 < 509203 * 2 ^ m - 1 := by omega
  have key : ∀ p : ℕ, p.Prime → p ≤ 241 → ¬ p ∣ 509203 * 2 ^ m - 1 := by
    intro p pp hle hdvd
    have := (Nat.prime_dvd_prime_iff_eq pp hp).mp hdvd
    omega
  rcases cov_all m with h | h | h | h | h | h
  · exact key 3 (by norm_num) (by norm_num) h
  · exact key 5 (by norm_num) (by norm_num) h
  · exact key 7 (by norm_num) (by norm_num) h
  · exact key 13 (by norm_num) (by norm_num) h
  · exact key 17 (by norm_num) (by norm_num) h
  · exact key 241 (by norm_num) (by norm_num) h

end OMA

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  have e : 2 * 254602 - 1 = 509203 := by norm_num
  have hno : ¬ ∃ m, m ≠ 0 ∧ ((2 * 254602 - 1) * 2 ^ m - 1).Prime := by
    intro h
    obtain ⟨m, hm0, hp⟩ := h
    rw [e] at hp
    exact OMA.not_prime m hm0 hp
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by norm_num), dif_neg hno]
