import OMAStatements.S_mo_380950
import Mathlib



open OMA.S_mo_380950

private theorem even_mod_four (x y z m : ZMod 4)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = m ^ 2) (hp : x + y + z = 0) :
    x + x = 0 ∧ y + y = 0 ∧ z + z = 0 ∧ m + m = 0 := by
  have hcheck : ∀ a b q : ZMod 4, a ^ 2 + b ^ 2 + (-(a + b)) ^ 2 = q ^ 2 →
      a + a = 0 ∧ b + b = 0 ∧ -(a + b) + -(a + b) = 0 ∧ q + q = 0 := by decide
  have hz : z = -(x + y) := eq_neg_of_add_eq_zero_right hp
  subst z
  exact hcheck x y m h

private theorem even_of_cast_add (a : ℤ) (ha : (a : ZMod 4) + (a : ZMod 4) = 0) :
    (2 : ℤ) ∣ a := by
  have hz : ((a + a : ℤ) : ZMod 4) = 0 := by simpa only [Int.cast_add] using ha
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (a + a) 4).mp hz
  obtain ⟨k, hk⟩ := hd
  exact ⟨k, by omega⟩

private theorem plane_descent (k : ℕ) :
    ∀ x y z m : ℤ, m.natAbs = k →
      x ^ 2 + y ^ 2 + z ^ 2 = m ^ 2 → x + y + z = 0 → m = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x y z m hk he hp
    by_contra hm
    have he' : (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2 =
        (m : ZMod 4) ^ 2 := by
      simpa only [Int.cast_add, Int.cast_pow] using congrArg (fun a : ℤ => (a : ZMod 4)) he
    have hp' : (x : ZMod 4) + (y : ZMod 4) + (z : ZMod 4) = 0 := by
      simpa only [Int.cast_add, Int.cast_zero] using congrArg (fun a : ℤ => (a : ZMod 4)) hp
    obtain ⟨hx, hy, hz, hm'⟩ := even_mod_four _ _ _ _ he' hp'
    obtain ⟨x', rfl⟩ := even_of_cast_add x hx
    obtain ⟨y', rfl⟩ := even_of_cast_add y hy
    obtain ⟨z', rfl⟩ := even_of_cast_add z hz
    obtain ⟨m', rfl⟩ := even_of_cast_add m hm'
    rw [Int.natAbs_mul] at hk
    have hlt : m'.natAbs < k := by
      have hh : m'.natAbs ≠ 0 := by intro h; simp [Int.natAbs_eq_zero.mp h] at hm
      change 2 * m'.natAbs = k at hk
      omega
    have hm0 := ih m'.natAbs hlt x' y' z' m' rfl (by nlinarith only [he]) (by omega)
    exact hm (by simp [hm0])

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_380950.main) := by
  intro h
  obtain ⟨x, y, z, m, hm, he, hp⟩ := h 1 1 1
  exact hm (plane_descent m.natAbs _ _ _ _ rfl he (by simpa only [one_mul] using hp))
