import OMAStatements.S_oeis_a028231
import Mathlib

namespace SquareQuotientRecurrence

open OMA.S_oeis_a028231

private theorem term_iff (k : ℕ) : IsTerm k ↔ ∃ y : ℕ, k ^ 2 + k + 1 = 3 * y ^ 2 := by
  constructor
  · rintro ⟨hd, y, hy⟩
    have h := Nat.mul_div_cancel' hd
    rw [hy] at h
    exact ⟨y, by simpa [pow_two] using h.symm⟩
  · rintro ⟨y, hy⟩
    rw [IsTerm, hy]
    refine ⟨dvd_mul_right _ _, ⟨y, ?_⟩⟩
    simp [pow_two]

private def orbit : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => let (k, y) := orbit n; (7 * k + 12 * y + 3, 4 * k + 7 * y + 2)

private theorem orbit_eq (n : ℕ) : (orbit n).1 ^ 2 + (orbit n).1 + 1 = 3 * (orbit n).2 ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [orbit]
    rcases he : orbit n with ⟨k, y⟩
    change (7 * k + 12 * y + 3) ^ 2 + (7 * k + 12 * y + 3) + 1 =
      3 * (4 * k + 7 * y + 2) ^ 2
    rw [he] at ih
    nlinarith

private theorem small (k y : ℕ) (h : k ^ 2 + k + 1 = 3 * y ^ 2) : k = 1 ∨ 22 ≤ k := by
  by_cases hk : k < 22
  · left
    have hy : y ≤ k + 1 := (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp (by nlinarith)
    have finite : ∀ u : Fin 22, ∀ v : Fin 23,
        u.val ^ 2 + u.val + 1 = 3 * v.val ^ 2 → u.val = 1 := by decide +kernel
    exact finite ⟨k, hk⟩ ⟨y, by omega⟩ h
  · omega

private theorem orbit_surj (k y : ℕ) (h : k ^ 2 + k + 1 = 3 * y ^ 2) :
    ∃ n, orbit n = (k, y) := by
  induction k using Nat.strong_induction_on generalizing y with
  | h k ih =>
    rcases small k y h with hk | hk
    · subst k
      have hy : y = 1 := by
        have h₁ : y ≤ 1 := (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp (by nlinarith)
        have h₂ : 1 ≤ y := (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp (by nlinarith)
        omega
      subst y
      exact ⟨0, rfl⟩
    let x : ℤ := k
    let z : ℤ := y
    have hxy : x ^ 2 + x + 1 = 3 * z ^ 2 := by
      dsimp [x, z]
      exact_mod_cast h
    have hx : 22 ≤ x := by
      dsimp [x]
      exact_mod_cast hk
    have hz : 0 ≤ z := by exact Int.natCast_nonneg _
    let u : ℤ := 7 * x - 12 * z + 3
    let v : ℤ := 7 * z - 4 * x - 2
    have hu : 0 ≤ u := by
      have hsq : (12 * z) ^ 2 ≤ (7 * x + 2) ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ x - 22 by omega) (show 0 ≤ x + 2 by omega)]
      have hp := (sq_le_sq₀ (show 0 ≤ 12 * z by omega) (show 0 ≤ 7 * x + 2 by omega)).mp hsq
      dsimp [u]
      omega
    have hv : 0 ≤ v := by
      have hsq : (4 * x + 2) ^ 2 ≤ (7 * z) ^ 2 := by nlinarith [sq_nonneg x]
      have hp := (sq_le_sq₀ (show 0 ≤ 4 * x + 2 by omega) (show 0 ≤ 7 * z by omega)).mp hsq
      dsimp [v]
      omega
    have hsmall : u < x := by
      have hsq : (6 * x + 3) ^ 2 < (12 * z) ^ 2 := by nlinarith [sq_nonneg x]
      have hp := (sq_lt_sq₀ (show 0 ≤ 6 * x + 3 by omega) (show 0 ≤ 12 * z by omega)).mp hsq
      dsimp [u]
      omega
    have huCast : (u.toNat : ℤ) = u := Int.toNat_of_nonneg hu
    have hvCast : (v.toNat : ℤ) = v := Int.toNat_of_nonneg hv
    have hnat : u.toNat ^ 2 + u.toNat + 1 = 3 * v.toNat ^ 2 := by
      have heq : u ^ 2 + u + 1 = 3 * v ^ 2 := by
        dsimp [u, v]
        linear_combination hxy
      rw [← huCast, ← hvCast] at heq
      exact_mod_cast heq
    have hlt : u.toNat < k := by
      have he : (u.toNat : ℤ) < k := huCast ▸ hsmall
      exact_mod_cast he
    obtain ⟨n, hn⟩ := ih u.toNat hlt v.toNat hnat
    refine ⟨n + 1, ?_⟩
    rw [orbit, hn]
    apply Prod.ext
    · have he : (7 : ℤ) * u + 12 * v + 3 = x := by dsimp [u, v]; ring
      rw [← huCast, ← hvCast] at he
      change (7 : ℤ) * (u.toNat : ℤ) + 12 * (v.toNat : ℤ) + 3 = (k : ℤ) at he
      change 7 * u.toNat + 12 * v.toNat + 3 = k
      exact_mod_cast he
    · have he : (4 : ℤ) * u + 7 * v + 2 = z := by dsimp [u, v]; ring
      rw [← huCast, ← hvCast] at he
      change (4 : ℤ) * (u.toNat : ℤ) + 7 * (v.toNat : ℤ) + 2 = (y : ℤ) at he
      change 4 * u.toNat + 7 * v.toNat + 2 = y
      exact_mod_cast he

private theorem nth_eq_orbit (n : ℕ) : a n = (orbit n).1 := by
  let f (n : ℕ) := (orbit n).1
  have hm : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro k
    change (orbit k).1 < (orbit (k + 1)).1
    simp only [orbit]
    rcases orbit k with ⟨x, z⟩
    change x < 7 * x + 12 * z + 3
    omega
  have ht (k : ℕ) : IsTerm (f k) := (term_iff _).mpr ⟨(orbit k).2, orbit_eq k⟩
  have hi : (Set.ofPred IsTerm).Infinite :=
    (Set.infinite_range_of_injective hm.injective).mono (by rintro _ ⟨k, rfl⟩; exact ht k)
  have he := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := IsTerm) f
    (fun k hk => by
      obtain ⟨y, hy⟩ := (term_iff k).mp hk
      obtain ⟨j, hj⟩ := orbit_surj k y hy
      exact ⟨j, fun hfin => (hi hfin).elim, congrArg Prod.fst hj⟩)
    (fun k _ => ht k) (hm.strictMonoOn _)
  exact (he (show ∀ hfin : (Set.ofPred IsTerm).Finite, n < hfin.toFinset.card from
    fun hfin => (hi hfin).elim)).symm

end SquareQuotientRecurrence

theorem OMA.solution : type_of% @OMA.S_oeis_a028231.main := by
  intro n
  simp only [SquareQuotientRecurrence.nth_eq_orbit, SquareQuotientRecurrence.orbit]
  rcases SquareQuotientRecurrence.orbit n with ⟨k, y⟩
  push_cast
  ring