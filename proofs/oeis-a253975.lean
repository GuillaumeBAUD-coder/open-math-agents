import OMAStatements.S_oeis_a253975
import Mathlib

open OMA.S_oeis_a253975 in
theorem OMA.solution : type_of% @OMA.S_oeis_a253975.main := by
  intro n hn
  let e := 2 * n + 1
  let k := 3 ^ e - 1
  have hone (j : ℕ) : 1 ≤ 3 ^ j := Nat.succ_le_of_lt (pow_pos (by decide) j)
  have hk : k + 1 = 3 ^ e := Nat.sub_add_cancel (hone e)
  have hp {a b : ℕ} : 3 ^ a ≤ 3 ^ b ↔ a ≤ b := Nat.pow_le_pow_iff_right (by decide)
  have hinj := Nat.pow_right_injective (a := 3) (by decide)
  let F (i : Fin n) : Representations k := by
    let j := i.val + 1
    have hj : j ≤ e - j := by dsimp [j, e]; omega
    have hj₁ : 3 ≤ 3 ^ j := hp.mpr (by dsimp [j]; omega : 1 ≤ j)
    have hpow : 3 ^ (e - j) * 3 ^ j = 3 ^ e := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : j ≤ e)]
    refine ⟨(3 ^ (e - j) - 1, 3 ^ j - 1), ?_, ?_, ?_⟩
    · omega
    · exact Nat.sub_le_sub_right (hp.mpr hj) _
    · have hh : (3 ^ (e - j) - 1 + 1) * (3 ^ j - 1 + 1) = k + 1 := by
        rw [Nat.sub_add_cancel (hone _), Nat.sub_add_cancel (hone _), hk, hpow]
      nlinarith only [hh]
  refine ⟨k, ⟨Equiv.ofBijective F ⟨?_, ?_⟩⟩⟩
  · intro i j h
    have he : 3 ^ (i.val + 1) - 1 = 3 ^ (j.val + 1) - 1 :=
      congrArg (fun v : Representations k => v.val.2) h
    have hpow : 3 ^ (i.val + 1) = 3 ^ (j.val + 1) := by
      have hi := hone (i.val + 1)
      have hj := hone (j.val + 1)
      omega
    have he' := hinj hpow
    apply Fin.ext
    omega
  · rintro ⟨⟨x, y⟩, hy, hxy, h⟩
    change 1 < y at hy
    change y ≤ x at hxy
    change x * y + x + y = k at h
    have hpw : (x + 1) * (y + 1) = 3 ^ e := by
      rw [← hk]
      nlinarith only [h]
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show y + 1 ∣ 3 ^ e by rw [← hpw]; exact dvd_mul_left _ _)
    obtain ⟨l, _, hl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show x + 1 ∣ 3 ^ e by rw [← hpw]; exact dvd_mul_right _ _)
    have hsum : l + j = e := by
      rw [hj, hl, ← pow_add] at hpw
      exact hinj hpw
    have hle : j ≤ l := hp.mp (by omega)
    have hj₀ : 0 < j := by
      by_contra! hn
      have hz : j = 0 := by omega
      rw [hz, pow_zero] at hj
      omega
    have hjn : j ≤ n := by dsimp [e] at hsum; omega
    refine ⟨⟨j - 1, by omega⟩, ?_⟩
    apply Subtype.ext
    change (3 ^ (e - (j - 1 + 1)) - 1, 3 ^ (j - 1 + 1) - 1) = (x, y)
    rw [Nat.sub_add_cancel (show 1 ≤ j by omega), show e - j = l by omega, ← hj, ← hl]
    simp