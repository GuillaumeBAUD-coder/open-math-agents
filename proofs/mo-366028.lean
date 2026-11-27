import OMAStatements.S_mo_366028
import Mathlib

-- Problem: mo-366028, nine horses with distinct constant speeds on a circular track of unit
-- length such that any two of them only ever meet at the starting point.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take integer speeds w_1, ..., w_9 such that every difference w_i - w_j divides w_i. If
-- horses i and j meet at time t, then (w_i - w_j) t = k is an integer, and with
-- w_i = c (w_i - w_j) we get w_i t = c k, an integer, so they are at the start. Such a set is
-- built from the 7-element set 25740, 25896, 25920, 25935, 25974, 26000, 26208 by twice
-- passing from S to {L} together with {L + s : s in S}, where L is the least common multiple
-- of S.

theorem OMA.solution : type_of% @OMA.S_mo_366028.main := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 9 → ℤ, w = ![530922909029849074445378294469795202876022467658678035062813673909161482256000,
      530922909029849074445378294469795202876022467658678035062813673947009444408000,
      530922909029849074445378294469795202876022467658678035062813673947009444433740,
      530922909029849074445378294469795202876022467658678035062813673947009444433896,
      530922909029849074445378294469795202876022467658678035062813673947009444433920,
      530922909029849074445378294469795202876022467658678035062813673947009444433935,
      530922909029849074445378294469795202876022467658678035062813673947009444433974,
      530922909029849074445378294469795202876022467658678035062813673947009444434000,
      530922909029849074445378294469795202876022467658678035062813673947009444434208] := ⟨_, rfl⟩
  have hinj : Function.Injective w := by
    rw [hw]
    decide +kernel
  have hpos : ∀ i, 0 < w i := by
    rw [hw]
    decide +kernel
  have hdvd : ∀ i j, i ≠ j → (w i - w j) ∣ w i := by
    rw [hw]
    decide +kernel
  refine ⟨fun i => (w i : ℝ), ?_, ?_, ?_⟩
  · intro i j h
    have h' : (w i : ℝ) = (w j : ℝ) := h
    exact hinj (Int.cast_injective h')
  · intro i
    show (0 : ℝ) < (w i : ℝ)
    exact Int.cast_pos.mpr (hpos i)
  · intro i j hij t _ hk
    obtain ⟨k, hk⟩ := hk
    obtain ⟨c, hc⟩ := hdvd i j hij
    refine ⟨c * k, ?_⟩
    have h1 : ((w i : ℝ) - (w j : ℝ)) * t = k := by linarith
    have h2 : (w i : ℝ) = ((w i : ℝ) - (w j : ℝ)) * c := by exact_mod_cast hc
    calc (w i : ℝ) * t = ((w i : ℝ) - (w j : ℝ)) * c * t := by rw [← h2]
      _ = c * (((w i : ℝ) - (w j : ℝ)) * t) := by ring
      _ = c * k := by rw [h1]
      _ = ((c * k : ℤ) : ℝ) := by push_cast; ring
