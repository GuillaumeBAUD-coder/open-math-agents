import OMAReductions.R_oeis_a352259_R1
import Mathlib

private def mask63 : ℕ := 288872697407275667
private def mask65 : ℕ := 20863489977805260307

private theorem residue63 : ∀ i : Fin 63,
    mask63.testBit ((i.val * i.val) % 63) = true := by decide +kernel

private theorem residue65 : ∀ i : Fin 65,
    mask65.testBit ((i.val * i.val) % 65) = true := by decide +kernel

private def passesSquare (d : ℕ) : Bool :=
  mask63.testBit (d % 63) && mask65.testBit (d % 65) &&
    (d.sqrt * d.sqrt == d)

private theorem square_passes (x : ℕ) : passesSquare (x * x) = true := by
  have h63 : mask63.testBit ((x * x) % 63) = true := by
    rw [Nat.mul_mod]
    exact residue63 ⟨x % 63, Nat.mod_lt _ (by decide)⟩
  have h65 : mask65.testBit ((x * x) % 65) = true := by
    rw [Nat.mul_mod]
    exact residue65 ⟨x % 65, Nat.mod_lt _ (by decide)⟩
  simp [passesSquare, Nat.sqrt_eq, h63, h65]

private def base (y z : ℕ) : ℕ := 2 * y ^ 2 + 3 * z ^ 2

private def noRoots (n y z : ℕ) : Bool :=
  if n < base y z then true
  else
    !passesSquare ((y * z) ^ 2 + 4 * (n - base y z)) &&
      (if n = base y z then true
       else !passesSquare ((y * z) ^ 2 + 4 * (n - base y z - 1)))

private def block (n q : ℕ) : Bool :=
  (List.range 16).all fun r =>
    (List.range ((n / 3).sqrt + 1)).all fun z =>
      noRoots n (q * 16 + r) z

private theorem excluded (n : ℕ)
    (cert : ∀ q : ℕ, q ≤ (n / 2).sqrt / 16 → block n q = true) :
    ¬ ∃ w x y z : ℕ, w ≤ 1 ∧ w + x^2 + 2*y^2 + 3*z^2 + x*y*z = n := by
  rintro ⟨w, x, y, z, hw, hs⟩
  have hy : y ≤ (n / 2).sqrt := Nat.le_sqrt'.mpr
    ((Nat.le_div_iff_mul_le (by decide)).2 (by omega))
  have hz : z ≤ (n / 3).sqrt := Nat.le_sqrt'.mpr
    ((Nat.le_div_iff_mul_le (by decide)).2 (by omega))
  have covered := cert (y / 16) (Nat.div_le_div_right hy)
  have one := List.all_eq_true.mp covered (y % 16)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have two := List.all_eq_true.mp one z (List.mem_range.mpr (by omega))
  have index : y / 16 * 16 + y % 16 = y := by omega
  rw [index] at two
  have hd : n - base y z = w + (x^2 + x*y*z) := by
    dsimp [base]
    omega
  have hd₀ : ¬ n < base y z := by
    dsimp [base]
    omega
  have algebra : (y * z) ^ 2 + 4 * (x^2 + x*y*z) = (2*x + y*z) * (2*x + y*z) := by
    ring
  rw [noRoots, if_neg hd₀, Bool.and_eq_true] at two
  by_cases h0 : w = 0
  · have e : n - base y z = x^2 + x*y*z := by omega
    rw [e, algebra, square_passes] at two
    exact Bool.false_ne_true two.1
  · have h1 : w = 1 := by omega
    have e : n - base y z - 1 = x^2 + x*y*z := by omega
    have he : n ≠ base y z := by omega
    rw [if_neg he, e, algebra, square_passes] at two
    exact Bool.false_ne_true two.2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check106_0 : block 106 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check744_0 : block 744 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check744_1 : block 744 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check5469_0 : block 5469 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check5469_1 : block 5469 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check5469_2 : block 5469 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check5469_3 : block 5469 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_0 : block 331269 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_1 : block 331269 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_2 : block 331269 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_3 : block 331269 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_4 : block 331269 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_5 : block 331269 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_6 : block 331269 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_7 : block 331269 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_8 : block 331269 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_9 : block 331269 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_10 : block 331269 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_11 : block 331269 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_12 : block 331269 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_13 : block 331269 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_14 : block 331269 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_15 : block 331269 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_16 : block 331269 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_17 : block 331269 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_18 : block 331269 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_19 : block 331269 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_20 : block 331269 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_21 : block 331269 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_22 : block 331269 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_23 : block 331269 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_24 : block 331269 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check331269_25 : block 331269 25 = true := by decide +kernel

private theorem all106 (q : ℕ) (hq : q ≤ (106 / 2).sqrt / 16) : block 106 q = true := by
  have bound : (106 / 2 : ℕ).sqrt / 16 = 0 := by decide +kernel
  rw [bound] at hq
  interval_cases q
  · exact check106_0

private theorem all744 (q : ℕ) (hq : q ≤ (744 / 2).sqrt / 16) : block 744 q = true := by
  have bound : (744 / 2 : ℕ).sqrt / 16 = 1 := by decide +kernel
  rw [bound] at hq
  interval_cases q
  · exact check744_0
  · exact check744_1

private theorem all5469 (q : ℕ) (hq : q ≤ (5469 / 2).sqrt / 16) : block 5469 q = true := by
  have bound : (5469 / 2 : ℕ).sqrt / 16 = 3 := by decide +kernel
  rw [bound] at hq
  interval_cases q
  · exact check5469_0
  · exact check5469_1
  · exact check5469_2
  · exact check5469_3

private theorem all331269 (q : ℕ) (hq : q ≤ (331269 / 2).sqrt / 16) : block 331269 q = true := by
  have bound : (331269 / 2 : ℕ).sqrt / 16 = 25 := by decide +kernel
  rw [bound] at hq
  interval_cases q
  · exact check331269_0
  · exact check331269_1
  · exact check331269_2
  · exact check331269_3
  · exact check331269_4
  · exact check331269_5
  · exact check331269_6
  · exact check331269_7
  · exact check331269_8
  · exact check331269_9
  · exact check331269_10
  · exact check331269_11
  · exact check331269_12
  · exact check331269_13
  · exact check331269_14
  · exact check331269_15
  · exact check331269_16
  · exact check331269_17
  · exact check331269_18
  · exact check331269_19
  · exact check331269_20
  · exact check331269_21
  · exact check331269_22
  · exact check331269_23
  · exact check331269_24
  · exact check331269_25

theorem OMA.solution : OMA.R_oeis_a352259_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact excluded 106 all106
  · exact excluded 744 all744
  · exact excluded 5469 all5469
  · exact excluded 331269 all331269