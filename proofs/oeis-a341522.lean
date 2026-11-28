import OMAStatements.S_oeis_a341522
import Mathlib

namespace OMA.Helpers

/-- Doubling the argument `v` times multiplies the value by `2 ^ v`. -/
theorem doudnaA341522_two_pow (doudna : ℕ → ℕ)
    (hd : ∀ k : ℕ, 1 ≤ k → doudna (2 * k) = 2 * doudna k) (t : ℕ) (ht : 1 ≤ t) :
    ∀ v : ℕ, doudna (2 ^ v * t) = 2 ^ v * doudna t := by
  intro v
  induction v with
  | zero => simp
  | succ v ih =>
    have hpos : 1 ≤ 2 ^ v * t := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
    calc doudna (2 ^ (v + 1) * t) = doudna (2 * (2 ^ v * t)) := by rw [pow_succ]; ring_nf
      _ = 2 * doudna (2 ^ v * t) := hd _ hpos
      _ = 2 ^ (v + 1) * doudna t := by rw [ih, pow_succ]; ring

/-- Tripling the value at an odd argument `m` gives the value at `2 * m + 1`. -/
theorem doudnaA341522_odd (primeShift doudna : ℕ → ℕ)
    (hs : ∀ x : ℕ, primeShift (2 * x) = 3 * primeShift x)
    (hd : ∀ k : ℕ, 1 ≤ k → doudna (2 * k) = 2 * doudna k)
    (ho : ∀ k : ℕ, doudna (2 * k + 1) = primeShift (doudna (k + 1))) (j : ℕ) :
    3 * doudna (2 * j + 1) = doudna (2 * (2 * j + 1) + 1) := by
  rw [ho j, ← hs, ← hd (j + 1) (by omega), ho (2 * j + 1)]
  ring_nf

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a341522.main := by
  intro primeShift doudna invDoudna _ hs _ hd ho hinv n
  set v := padicValNat 2 (n + 1) with hv
  have hdvd : 2 ^ v ∣ n + 1 := pow_padicValNat_dvd
  have hndvd : ¬ 2 ^ (v + 1) ∣ n + 1 := pow_succ_padicValNat_not_dvd (by omega)
  obtain ⟨m, hm⟩ := hdvd
  have hmodd : m % 2 = 1 := by
    by_contra h
    apply hndvd
    refine ⟨m / 2, ?_⟩
    rw [hm, pow_succ]
    have : m = 2 * (m / 2) := by omega
    conv_lhs => rw [this]
    ring
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
  have h1 : doudna (n + 1) = 2 ^ v * doudna (2 * j + 1) := by
    rw [hm]; exact OMA.Helpers.doudnaA341522_two_pow doudna hd _ (by omega) v
  have h2 : 3 * doudna (n + 1) = doudna (2 ^ v * (2 * (2 * j + 1) + 1)) := by
    rw [h1, OMA.Helpers.doudnaA341522_two_pow doudna hd _ (by omega) v,
      ← OMA.Helpers.doudnaA341522_odd primeShift doudna hs hd ho j]
    ring
  have hpos : 1 ≤ 2 ^ v * (2 * (2 * j + 1) + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
  rw [h2, hinv _ hpos]
  have e : 2 ^ v * (2 * (2 * j + 1) + 1) = 2 * (2 ^ v * (2 * j + 1)) + 2 ^ v := by ring
  rw [e, ← hm]
  omega
