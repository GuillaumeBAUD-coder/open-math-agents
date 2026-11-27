import OMAStatements.S_oeis_a057192

/-!
Disproof of Aguirre's conjecture (A057192): `271129` is a prime with `271129 % 3 = 1`, but it is a
Sierpinski number: every `1 + 271129 * 2^m` has a divisor in `{3, 5, 7, 13, 17, 241}` (a covering
set; `2^24 - 1 = 3^2 * 5 * 7 * 13 * 17 * 241`, so the divisor found for `m` also works for `m + 24`).
Hence `a(n) = -1` (odd) for the index `n` of `271129`, while `prime(n) % 3 = 1`.
-/

namespace OMA.D_a057192

/-- Every `1 + 271129 * 2^m` has a divisor in the covering set `{3, 5, 7, 13, 17, 241}`. -/
theorem cover (m : ℕ) : ∃ q ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), q ∣ 1 + 271129 * 2 ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 24
    · interval_cases m <;> decide
    · obtain ⟨q, hq, hdvd⟩ := ih (m - 24) (by omega)
      refine ⟨q, hq, ?_⟩
      have hsplit : 1 + 271129 * 2 ^ m =
          (1 + 271129 * 2 ^ (m - 24)) + 271129 * 2 ^ (m - 24) * (2 ^ 24 - 1) := by
        have : m = (m - 24) + 24 := by omega
        rw [this, pow_add]
        simp only [Nat.add_sub_cancel]
        have h24 : (2 : ℕ) ^ 24 = (2 ^ 24 - 1) + 1 := by norm_num
        rw [h24]
        ring
      rw [hsplit]
      have hq24 : q ∣ 2 ^ 24 - 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact dvd_add hdvd (Dvd.dvd.mul_left hq24 _)

/-- `1 + 271129 * 2^m` is never prime. -/
theorem not_prime (m : ℕ) : ¬ (1 + 271129 * 2 ^ m).Prime := by
  intro hp
  obtain ⟨q, hq, hdvd⟩ := cover m
  have hq_le : q ≤ 241 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hq_ge : 2 ≤ q := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  rcases hp.eq_one_or_self_of_dvd q hdvd with h | h
  · omega
  · have : 271129 ≤ 271129 * 2 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
    omega

theorem prime_271129 : Nat.Prime 271129 := by norm_num

theorem disproof : ¬ (∀ n : ℕ, 1 < n →
    (Even (OMA.S_oeis_a057192.a n) ↔ Nat.nth Nat.Prime (n - 1) % 3 = 1)) := by
  intro h
  set n := Nat.count Nat.Prime 271129 + 1 with hn
  have hnth : Nat.nth Nat.Prime (n - 1) = 271129 := by
    rw [hn, Nat.add_sub_cancel]
    exact Nat.nth_count prime_271129
  have hpos : 0 < Nat.count Nat.Prime 271129 :=
    Nat.pos_of_ne_zero (Nat.count_ne_iff_exists.mpr ⟨2, by norm_num, Nat.prime_two⟩)
  have hn1 : 1 < n := by omega
  have ha : OMA.S_oeis_a057192.a n = -1 := by
    unfold OMA.S_oeis_a057192.a
    rw [dif_neg]
    rintro ⟨m, hm⟩
    rw [hnth] at hm
    exact not_prime m hm
  have := h n hn1
  rw [ha, hnth] at this
  have hodd : ¬ Even (-1 : ℤ) := by decide
  exact hodd (this.mpr (by norm_num))

end OMA.D_a057192

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a057192.main) := OMA.D_a057192.disproof
