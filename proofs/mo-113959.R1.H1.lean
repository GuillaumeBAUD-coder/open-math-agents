import OMAReductions.R_mo_113959_R1

-- Step mo-113959.R1.H1: hypothesis H1 of reduction mo-113959.R1
-- Credit: @Lenqth (Claude Code, claude-opus-5-5)

/-! Write `n - 2 = 2^k u` with `u` odd. For even `v > 2` we have `minFac v = 2`, so
`f v = v + v/2 - 1`; hence `2 + 2^(i+1) 3^j u ↦ 2 + 2^i 3^(j+1) u`. By induction
`f^[j] n = 2 + 2^(k-j) 3^j u` for `j ≤ k`, these are even for `j < k`, and `2 + 3^k u` is odd. -/

open OMA.S_mo_113959

theorem OMA.solution : OMA.R_mo_113959_R1.H1 := by
  intro n hn
  obtain ⟨k, u, hu, hku⟩ := Nat.exists_eq_two_pow_mul_odd (n := n - 2) (by omega)
  have hn' : n = 2 + 2 ^ k * u := by omega
  have step : ∀ i j : ℕ, f (2 + 2 ^ (i + 1) * 3 ^ j * u) = 2 + 2 ^ i * 3 ^ (j + 1) * u := by
    intro i j
    have hev : 2 ∣ 2 + 2 ^ (i + 1) * 3 ^ j * u := ⟨1 + 2 ^ i * 3 ^ j * u, by ring⟩
    have hmf : (2 + 2 ^ (i + 1) * 3 ^ j * u).minFac = 2 :=
      (Nat.minFac_eq_two_iff _).mpr hev
    unfold f
    rw [hmf]
    have : (2 + 2 ^ (i + 1) * 3 ^ j * u) / 2 = 1 + 2 ^ i * 3 ^ j * u := by
      rw [show 2 + 2 ^ (i + 1) * 3 ^ j * u = 2 * (1 + 2 ^ i * 3 ^ j * u) by ring]
      simp
    rw [this]
    have h3 : 2 ^ i * 3 ^ (j + 1) * u = 3 * (2 ^ i * 3 ^ j * u) := by ring
    rw [show 2 ^ (i + 1) * 3 ^ j * u = 2 * (2 ^ i * 3 ^ j * u) by ring, h3]
    omega
  have formula : ∀ j ≤ k, f^[j] n = 2 + 2 ^ (k - j) * 3 ^ j * u := by
    intro j
    induction j with
    | zero => intro _; simp [hn']
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega),
        show k - j = (k - (j + 1)) + 1 by omega, step]
  have hodd3 : Odd (3 ^ k * u) := (Odd.pow (by decide)).mul hu
  refine ⟨k, u, hu, hn', formula, fun j hj => ?_, ?_⟩
  · rw [formula j hj.le, show k - j = (k - j - 1) + 1 by omega]
    exact ⟨1 + 2 ^ (k - j - 1) * 3 ^ j * u, by ring⟩
  · rw [formula k le_rfl, Nat.sub_self, pow_zero, one_mul]
    exact Even.add_odd (by decide) hodd3
