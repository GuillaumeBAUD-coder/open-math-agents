import OMAStatements.S_mse_4553718
import Mathlib

-- Problem: mse-4553718, the least k > 0 after which k perfect out-shuffles of 2n cards return
-- the two colours (first n positions / last n positions) is the order of 2 modulo 2n - 1.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- On positions i < 2n - 1 one out-shuffle is i -> 2i mod (2n - 1), and position 2n - 1 is
-- fixed, so k shuffles act as i -> 2^k i mod (2n - 1). If 2^k = 1 mod (2n - 1) every position
-- returns. Conversely let u = 2^k mod (2n - 1) and suppose the colours return (n >= 2).
-- Position 1 gives u < n, position n gives u != 0. If u >= 2, let i be least with i u >= n;
-- then i < n and n <= i u < n + u <= 2n - 1, so position i (first half) goes to i u (second
-- half), a contradiction. Hence u = 1, and the order of 2 divides k.

namespace MSE4553718

open OMA.S_mse_4553718

theorem shuffle_eq (n i : ℕ) (hi : i < 2 * n - 1) :
    outShuffle n i = (2 * i) % (2 * n - 1) := by
  unfold outShuffle
  split_ifs with h
  · exact (Nat.mod_eq_of_lt (by omega)).symm
  · have h2 : 2 * n - 1 ≤ 2 * i := by omega
    have h3 : 2 * i - (2 * n - 1) < 2 * n - 1 := by omega
    rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt h3]
    omega

theorem iter_eq (n : ℕ) (hn : 0 < n) (k i : ℕ) (hi : i < 2 * n - 1) :
    (outShuffle n)^[k] i = (2 ^ k * i) % (2 * n - 1) := by
  have hm : 0 < 2 * n - 1 := by omega
  induction k with
  | zero => simp [Nat.mod_eq_of_lt hi]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      shuffle_eq n (2 ^ k * i % (2 * n - 1)) (Nat.mod_lt _ hm), Nat.mul_mod_mod, pow_succ]
    congr 1
    ring

theorem iter_top (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (outShuffle n)^[k] (2 * n - 1) = 2 * n - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hpos : 0 < n := hn
    unfold outShuffle
    split_ifs <;> omega

theorem pow_mod_of_return (n k : ℕ) (hn2 : 2 ≤ n)
    (hf : ∀ i, i < 2 * n - 1 → ((2 ^ k * i) % (2 * n - 1) < n ↔ i < n)) :
    2 ^ k % (2 * n - 1) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, u = 2 ^ k % (2 * n - 1) := ⟨_, rfl⟩
  have hmul : ∀ i, (2 ^ k * i) % (2 * n - 1) = (u * i) % (2 * n - 1) := by
    intro i
    rw [hu, Nat.mod_mul_mod]
  rw [← hu]
  have hum : u < 2 * n - 1 := by
    rw [hu]
    exact Nat.mod_lt _ (by omega)
  have h1 := hf 1 (by omega)
  rw [hmul, mul_one, Nat.mod_eq_of_lt hum] at h1
  have hun : u < n := h1.mpr (by omega)
  have hn' := hf n (by omega)
  rw [hmul] at hn'
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, zero_mul, Nat.zero_mod] at hn'
    omega
  by_contra hne
  have hu2 : 2 ≤ u := by omega
  have hex : ∃ i, n ≤ i * u := ⟨n, Nat.le_mul_of_pos_right n (by omega)⟩
  obtain ⟨i₀, hi₀, hmin⟩ : ∃ i₀, n ≤ i₀ * u ∧ ∀ j, j < i₀ → ¬ n ≤ j * u :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hi1 : 1 ≤ i₀ := by
    rcases Nat.eq_zero_or_pos i₀ with h | h
    · rw [h, zero_mul] at hi₀
      omega
    · exact h
  have hprev := hmin (i₀ - 1) (by omega)
  have hexp : i₀ * u = (i₀ - 1) * u + u := by
    obtain ⟨j, rfl⟩ : ∃ j, i₀ = j + 1 := ⟨i₀ - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
  have hlt : i₀ * u < 2 * n - 1 := by omega
  have hi₀n : i₀ < n := by
    by_contra hge
    have hmm := Nat.mul_le_mul (show n - 1 ≤ i₀ - 1 by omega) hu2
    omega
  have hfin := hf i₀ (by omega)
  rw [hmul, mul_comm u i₀, Nat.mod_eq_of_lt hlt] at hfin
  have hbad := hfin.mpr hi₀n
  omega

end MSE4553718

theorem OMA.solution : type_of% @OMA.S_mse_4553718.main := by
  intro n hn
  have hm : 0 < 2 * n - 1 := by omega
  have key : ∀ k, (2 : ZMod (2 * n - 1)) ^ k = 1 ↔
      2 ^ k % (2 * n - 1) = 1 % (2 * n - 1) := by
    intro k
    constructor
    · intro hk
      exact (ZMod.natCast_eq_natCast_iff' (2 ^ k) 1 (2 * n - 1)).mp (by exact_mod_cast hk)
    · intro hk
      exact_mod_cast (ZMod.natCast_eq_natCast_iff' (2 ^ k) 1 (2 * n - 1)).mpr hk
  have hcop : Nat.Coprime 2 (2 * n - 1) := Nat.coprime_two_left.mpr ⟨n - 1, by omega⟩
  have htot : (2 : ZMod (2 * n - 1)) ^ Nat.totient (2 * n - 1) = 1 :=
    (key _).mpr (Nat.ModEq.pow_totient hcop)
  have hd : 0 < orderOf (2 : ZMod (2 * n - 1)) :=
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one htot) (Nat.totient_pos.mpr hm)
  constructor
  · show 0 < orderOf (2 : ZMod (2 * n - 1)) ∧
      OMA.S_mse_4553718.colorsReturn n (orderOf (2 : ZMod (2 * n - 1)))
    refine ⟨hd, ?_⟩
    have hk := (key _).mp (pow_orderOf_eq_one (2 : ZMod (2 * n - 1)))
    unfold OMA.S_mse_4553718.colorsReturn
    intro i hi
    rcases Nat.lt_or_ge i (2 * n - 1) with hlt | hge
    · rw [MSE4553718.iter_eq n hn _ i hlt, Nat.mul_mod, hk, ← Nat.mul_mod, one_mul,
        Nat.mod_eq_of_lt hlt]
    · have hi' : i = 2 * n - 1 := by omega
      rw [hi', MSE4553718.iter_top n hn]
  · rintro k ⟨hk0, hret⟩
    have hf : ∀ i, i < 2 * n - 1 → ((2 ^ k * i) % (2 * n - 1) < n ↔ i < n) := by
      intro i hi
      have h := hret i (by omega)
      rwa [MSE4553718.iter_eq n hn k i hi] at h
    have hpow : 2 ^ k % (2 * n - 1) = 1 % (2 * n - 1) := by
      rcases Nat.lt_or_ge 1 n with hn2 | hn1
      · rw [MSE4553718.pow_mod_of_return n k hn2 hf, Nat.mod_eq_of_lt (by omega)]
      · have h1 : n = 1 := by omega
        subst h1
        have e : 2 * 1 - 1 = 1 := rfl
        rw [e, Nat.mod_one, Nat.mod_one]
    exact Nat.le_of_dvd hk0 (orderOf_dvd_of_pow_eq_one ((key k).mpr hpow))
