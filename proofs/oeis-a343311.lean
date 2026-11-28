import OMAStatements.S_oeis_a343311
import Mathlib

namespace A343311

lemma chk4 : ∀ x < 4, ∀ y < 4, ¬ (0 < x ∧ 0 < y ∧ x + y < 4 ∧ x ≠ y ∧ x ≠ 4 - x - y ∧
    y ≠ 4 - x - y ∧ 4 ∣ x * y * (4 - x - y)) := by decide

lemma chk8 : ∀ x < 8, ∀ y < 8, ¬ (0 < x ∧ 0 < y ∧ x + y < 8 ∧ x ≠ y ∧ x ≠ 8 - x - y ∧
    y ≠ 8 - x - y ∧ 8 ∣ x * y * (8 - x - y)) := by decide

lemma chk9 : ∀ x < 9, ∀ y < 9, ¬ (0 < x ∧ 0 < y ∧ x + y < 9 ∧ x ≠ y ∧ x ≠ 9 - x - y ∧
    y ≠ 9 - x - y ∧ 9 ∣ x * y * (9 - x - y)) := by decide

set_option maxRecDepth 100000 in
lemma chk25 : ∀ x < 25, ∀ y < 25, ¬ (0 < x ∧ 0 < y ∧ x + y < 25 ∧ x ≠ y ∧ x ≠ 25 - x - y ∧
    y ≠ 25 - x - y ∧ 25 ∣ x * y * (25 - x - y)) := by decide

lemma not_rep (n : ℕ)
    (h : ∀ x < n, ∀ y < n, ¬ (0 < x ∧ 0 < y ∧ x + y < n ∧ x ≠ y ∧ x ≠ n - x - y ∧
      y ≠ n - x - y ∧ n ∣ x * y * (n - x - y))) :
    ¬ OMA.S_oeis_a343311.represented n := by
  rintro ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, hs, hd⟩
  have hz' : z = n - x - y := by omega
  subst hz'
  exact h x (by omega) y (by omega) ⟨hx, hy, by omega, hxy, hxz, hyz, hd⟩

lemma rep_of_lt (d c : ℕ) (h8 : (d + 2) * (d + 3 + c) ≠ 8) :
    OMA.S_oeis_a343311.represented ((d + 2) * (d + 3 + c)) := by
  refine ⟨d + 2, d + 3 + c, 1 + 3 * d + c + d * d + d * c, by omega, by omega, by omega,
    by omega, ?_, ?_, by ring, Dvd.intro _ rfl⟩
  · intro h
    rcases d with _ | d
    · have hc : c = 1 := by
        simp at h
        omega
      subst hc
      exact h8 rfl
    · have := Nat.zero_le ((d + 1) * (d + 1))
      have := Nat.zero_le ((d + 1) * c)
      omega
  · intro h
    rcases d with _ | d
    · simp at h
    · have h1 : 0 < (d + 1) * (d + 1) := Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos d)
      have h2 := Nat.zero_le ((d + 1) * c)
      omega

lemma rep_of_sq (e : ℕ) : OMA.S_oeis_a343311.represented ((e + 7) * (e + 7)) := by
  refine ⟨e + 7, 2 * (e + 7), 28 + 11 * e + e * e, by omega, by omega, by omega,
    by omega, ?_, ?_, by ring, ⟨2 * (28 + 11 * e + e * e), by ring⟩⟩
  · have := Nat.zero_le (e * e)
    omega
  · have := Nat.zero_le (e * e)
    omega

end A343311

theorem OMA.solution : type_of% @OMA.S_oeis_a343311.main := by
  intro n
  constructor
  · intro hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨x, y, z, hx, hy, hz, -, -, -, hs, -⟩ := hr
      omega
    · obtain ⟨x, y, z, hx, hy, hz, -, -, -, hs, hd⟩ := hr
      intro hp
      rcases (hp.dvd_mul).mp hd with h | h
      · rcases (hp.dvd_mul).mp h with h | h
        · have := Nat.le_of_dvd hx h
          omega
        · have := Nat.le_of_dvd hy h
          omega
      · have := Nat.le_of_dvd hz h
        omega
    · rintro rfl
      exact A343311.not_rep 4 A343311.chk4 hr
    · rintro rfl
      exact A343311.not_rep 8 A343311.chk8 hr
    · rintro rfl
      exact A343311.not_rep 9 A343311.chk9 hr
    · rintro rfl
      exact A343311.not_rep 25 A343311.chk25 hr
  · rintro ⟨h1, hnp, h4, h8, h9, h25⟩
    obtain ⟨p, hp, ⟨b, hb⟩, hsq⟩ : ∃ p, p.Prime ∧ p ∣ n ∧ p ^ 2 ≤ n :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n,
        Nat.minFac_sq_le_self (by omega) hnp⟩
    have hp2 := hp.two_le
    have hpb : p ≤ b := by
      rw [hb, pow_two] at hsq
      exact Nat.le_of_mul_le_mul_left hsq (by omega)
    subst hb
    rcases Nat.lt_or_eq_of_le hpb with hlt | heq
    · obtain ⟨d, rfl⟩ : ∃ d, p = d + 2 := ⟨p - 2, by omega⟩
      obtain ⟨c, rfl⟩ : ∃ c, b = d + 3 + c := ⟨b - d - 3, by omega⟩
      exact A343311.rep_of_lt d c h8
    · subst heq
      have q2 : p ≠ 2 := by
        rintro rfl
        exact h4 rfl
      have q3 : p ≠ 3 := by
        rintro rfl
        exact h9 rfl
      have q5 : p ≠ 5 := by
        rintro rfl
        exact h25 rfl
      have q4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      have q6 : p ≠ 6 := by
        rintro rfl
        norm_num at hp
      obtain ⟨e, rfl⟩ : ∃ e, p = e + 7 := ⟨p - 7, by omega⟩
      exact A343311.rep_of_sq e
