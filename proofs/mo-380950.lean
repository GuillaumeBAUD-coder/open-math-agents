import OMAStatements.S_mo_380950
import Mathlib

theorem OMA.descent (k : ℕ) : ∀ x y m : ℤ, m.natAbs = k →
    2 * (x ^ 2 + x * y + y ^ 2) = m ^ 2 → m = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x y m hk he
    by_contra hm
    have h4 : ∀ a b q : ZMod 4, 2 * (a ^ 2 + a * b + b ^ 2) = q ^ 2 →
        a + a = 0 ∧ b + b = 0 ∧ q + q = 0 := by decide
    obtain ⟨hx, hy, hq⟩ := h4 x y m (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 4) he)
    have ev : ∀ a : ℤ, (a : ZMod 4) + a = 0 → ∃ c, a = 2 * c := fun a ha => by
      obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a + a) 4).1 (by exact_mod_cast ha)
      exact ⟨c, by omega⟩
    obtain ⟨x, rfl⟩ := ev x hx
    obtain ⟨y, rfl⟩ := ev y hy
    obtain ⟨m, rfl⟩ := ev m hq
    exact hm (by simp [ih m.natAbs (by omega) x y m rfl (by nlinarith)])

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_380950.main) := fun h => by
  obtain ⟨x, y, z, m, hm, he, hp⟩ := h 1 1 1
  exact hm (OMA.descent _ x y m rfl (by rw [← he, show z = -x - y by linarith]; ring))
