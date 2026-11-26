import OMAReductions.R_Green40_green_40_upper_bound_f_two_R1

/-! # Density estimate for a binary radius-two covering code -/
-- Credit: @steveDOTdigital

open Green40
open scoped NNReal ENNReal

namespace OMA.BinaryBall

-- A binary vector is determined by its support. At radius two there are
-- only the empty set, singletons, and two-element subsets.
theorem card_bound (n : ℕ) : Nat.card (hammingBall n 2) ≤ 1 + n + n.choose 2 := by
  classical
  let U := (Finset.univ : Finset (Fin n))
  let S := (U.powersetCard 0 ∪ U.powersetCard 1) ∪ U.powersetCard 2
  let supp (x : hammingBall n 2) := U.filter (fun i => x.val i ≠ 0)
  have hs (x : hammingBall n 2) : supp x ∈ S := by
    have h : (supp x).card ≤ 2 := x.property
    have hc : (supp x).card = 0 ∨ (supp x).card = 1 ∨ (supp x).card = 2 := by omega
    simpa [S, U, Finset.mem_powersetCard, or_assoc] using hc
  let F (x : hammingBall n 2) : ↥S := ⟨supp x, hs x⟩
  have hinj : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    funext i
    have he : supp x = supp y := congrArg Subtype.val h
    have hm : i ∈ supp x ↔ i ∈ supp y := he ▸ Iff.rfl
    have hb : x.val i ≠ 0 ↔ y.val i ≠ 0 := by simpa [supp, U] using hm
    exact (by decide : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b) _ _ hb
  have hcount := Nat.card_le_card_of_injective F hinj
  calc
    Nat.card (hammingBall n 2) ≤ S.card := by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcount
    _ ≤ ((U.powersetCard 0).card + (U.powersetCard 1).card) + (U.powersetCard 2).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ = _ := by simp [U, Finset.card_powersetCard]

theorem density_of_nat_bound (a d : ℕ) (hd : 0 < d) (h : 5*a ≤ 7*d) :
    (a : ℝ≥0∞) / (d : ℝ≥0∞) ≤ 1.4238 := by
  have hr : (5 : ℝ) * a ≤ 7 * d := by exact_mod_cast h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by exact_mod_cast hd.ne'))
    (show ((1.4238 : ℝ≥0) : ℝ≥0∞) ≠ ⊤ from ENNReal.coe_ne_top)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  apply (div_le_iff₀ hd').mpr
  change (a : ℝ) ≤ (1.4238 : ℝ) * (d : ℝ)
  linarith

end OMA.BinaryBall

theorem OMA.solution : OMA.R_Green40_green_40_upper_bound_f_two_R1.H2 := by
  intro b
  let k := b + 10
  let t := 2 ^ k
  let n := 26 * t - 1
  let r := 2 * (k + 4)
  have ht : k < t := Nat.lt_two_pow_self
  have hn : n + 1 = 26 * t := by dsimp [n]; omega
  have hr : r ≤ n := by dsimp [r]; omega
  refine ⟨k, by dsimp [k]; omega, by change b ≤ n; dsimp [k] at ht; omega, ?_⟩
  have hball := OMA.BinaryBall.card_bound n
  have hc : 2 * n.choose 2 ≤ n * n := by
    rw [Nat.choose_two_right]
    have := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    omega
  have hs : 2 * Nat.card (hammingBall n 2) ≤ (n + 1)^2 + 1 := by nlinarith
  rw [hn] at hs
  have hp : (2 : ℕ)^r = t^2 * 256 := by
    dsimp [r, t]
    rw [Nat.mul_comm 2 _, pow_mul, pow_add]
    ring
  have hb : 5 * Nat.card (hammingBall n 2) ≤ 7 * 2 ^ r := by
    rw [hp]
    have htpos : 0 < t := by dsimp [t]; positivity
    nlinarith [show 0 < t^2 by positivity]
  have hsplit : (2 : ℕ)^n = 2^(n-r) * 2^r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  have hnat : 5 * (2^(n-r) * Nat.card (hammingBall n 2)) ≤ 7 * 2^n := by
    calc
      _ = 2^(n-r) * (5 * Nat.card (hammingBall n 2)) := by ring
      _ ≤ 2^(n-r) * (7 * 2^r) := Nat.mul_le_mul_left _ hb
      _ = _ := by rw [hsplit]; ring
  change ((2^(n-r) : ℕ) : ℝ≥0∞) * (Nat.card (hammingBall n 2) : ℝ≥0∞) / (2^n : ℝ≥0∞) ≤ _
  have hfinal := OMA.BinaryBall.density_of_nat_bound
    (2^(n-r) * Nat.card (hammingBall n 2)) (2^n) (by positivity) hnat
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hfinal
