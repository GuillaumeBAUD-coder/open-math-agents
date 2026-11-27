import OMAReductions.R_Erdos384_erdos_384_R1

/-!
For k = 2 or 3, the falling factorial contains both n and n − 1, one of
which is even. Cancel from this even factor just its gcd with k!.
The remaining factor still divides the binomial coefficient. It is at most
n/2, and it exceeds one as soon as the even factor exceeds k!.
-/

namespace BinomialSmallPrime

private lemma afterCancellation {e a B n : ℕ} (ha : 0 < a) (hae : a < e)
    (hen : e ≤ n) (heven : 2 ∣ e) (haven : 2 ∣ a) (h : e ∣ a * B) :
    ∃ p : ℕ, p.Prime ∧ p ∣ B ∧ 2 * p ≤ n := by
  let g := e.gcd a
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ ha
  have hg2 : 2 ≤ g := Nat.le_of_dvd hg (Nat.dvd_gcd heven haven)
  have hga : g ≤ a := Nat.gcd_le_right _ ha
  have heq : g * (e / g) = e := by
    rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left e a)]
  have haq : g * (a / g) = a := by
    rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right e a)]
  have hq : 1 < e / g := by
    by_contra! hle
    have := Nat.mul_le_mul_left g hle
    omega
  have hd : e / g ∣ B := by
    apply (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left
    apply (Nat.mul_dvd_mul_iff_left hg).mp
    rwa [heq, ← Nat.mul_assoc, haq]
  refine ⟨(e / g).minFac, Nat.minFac_prime (by omega),
    (Nat.minFac_dvd _).trans hd, ?_⟩
  calc
    2 * (e / g).minFac ≤ g * (e / g) := Nat.mul_le_mul hg2 (Nat.minFac_le (by omega))
    _ = e := heq
    _ ≤ n := hen

theorem smallCases (n k : ℕ) (hk₂ : 2 ≤ k) (hk₃ : k ≤ 3)
    (hn : 2 * k ≤ n) (hex : (n,k) ≠ (7,3)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  let e := 2 * (n / 2)
  have he : e = n ∨ e = n - 1 := by dsimp [e]; omega
  have hen : e ≤ n := by dsimp [e]; omega
  have heven : 2 ∣ e := ⟨_, rfl⟩
  have htwo : e ∣ n.descFactorial 2 := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
    rcases he with h | h <;> rw [h] <;> simp
  have hk : k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl
  · apply afterCancellation (e := e) (a := 2) (by decide) (by dsimp [e]; omega) hen heven (by decide)
    rw [Nat.descFactorial_eq_factorial_mul_choose] at htwo
    exact htwo
  · by_cases hsmall : n < 8
    · have h6 : n = 6 := by
        have h7 : n ≠ 7 := fun h => hex (by simp [h])
        omega
      subst n
      exact ⟨2, by decide, by decide, by decide⟩
    apply afterCancellation (e := e) (a := 6) (by decide) (by dsimp [e]; omega) hen heven (by decide)
    have hthree : e ∣ n.descFactorial 3 := dvd_mul_of_dvd_right htwo (n - 2)
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hthree
    exact hthree

end BinomialSmallPrime

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H3 :=
  BinomialSmallPrime.smallCases
