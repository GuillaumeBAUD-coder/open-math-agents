import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

-- Reduction Erdos338.erdos_338.variants.squares.R1.H2.R1 of step Erdos338.erdos_338.variants.squares.R1.H2
-- Credit: @gunnerhowe
--
-- Step H2 (Pall): every sufficiently large integer is a sum of at most 5 distinct squares.
-- This reduction proves it from two classical cases of the Gauss-Legendre three-square theorem:
--   H1: every n with n % 8 = 1 is a sum of three squares,
--   H2: every n with n % 8 = 3 is a sum of three squares.
-- Argument. For large n choose a > b (about 3 sqrt n / 4 and sqrt n / 2, in residue classes
-- mod 200 read off a finite table) so that r = n - a^2 - b^2 satisfies 0 < r < b^2,
-- r % 8 = 1 or 3, and r % 25 is 5, 10, 15 or 20 (5 divides r exactly once).
-- Since -2 is not a square mod 5, such an r is never X^2 + 2 Y^2, so in any representation
-- r = x^2 + y^2 + z^2 the numbers x, y, z are pairwise distinct; all are below b < a,
-- so a^2, b^2, x^2, y^2, z^2 are five distinct squares summing to n.

namespace OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1

open Filter Erdos338

/-- Every positive integer that is 1 mod 8 is a sum of three squares (Gauss-Legendre). -/
def H1 : Prop := ∀ n : ℕ, n % 8 = 1 → ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n

/-- Every positive integer that is 3 mod 8 is a sum of three squares (Gauss-Legendre). -/
def H2 : Prop := ∀ n : ℕ, n % 8 = 3 → ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n

lemma mod5_zero (X Y : ℕ) (h : (X ^ 2 + 2 * Y ^ 2) % 5 = 0) : X % 5 = 0 ∧ Y % 5 = 0 := by
  have e : (X ^ 2 + 2 * Y ^ 2) % 5 = ((X % 5) ^ 2 + 2 * (Y % 5) ^ 2) % 5 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  rw [e] at h
  have hx : X % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hy : Y % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize X % 5 = u at h hx ⊢
  generalize Y % 5 = v at h hy ⊢
  interval_cases u <;> interval_cases v <;> simp_all

/-- If `5` divides `r` exactly once then `r` is not of the form `X ^ 2 + 2 * Y ^ 2`. -/
lemma not_form (r X Y : ℕ) (hr : r % 25 = 5 ∨ r % 25 = 10 ∨ r % 25 = 15 ∨ r % 25 = 20)
    (h : X ^ 2 + 2 * Y ^ 2 = r) : False := by
  have h5 : (X ^ 2 + 2 * Y ^ 2) % 5 = 0 := by omega
  obtain ⟨hx, hy⟩ := mod5_zero X Y h5
  obtain ⟨u, rfl⟩ := Nat.dvd_of_mod_eq_zero hx
  obtain ⟨v, rfl⟩ := Nat.dvd_of_mod_eq_zero hy
  have e : (5 * u) ^ 2 + 2 * (5 * v) ^ 2 = 25 * (u ^ 2 + 2 * v ^ 2) := by ring
  omega

lemma table (c : ℕ) (hc : c < 200) : ∃ α β ρ : ℕ,
    α < 200 ∧ β < 200 ∧ ρ < 200 ∧ (ρ % 8 = 1 ∨ ρ % 8 = 3) ∧
    (ρ % 25 = 5 ∨ ρ % 25 = 10 ∨ ρ % 25 = 15 ∨ ρ % 25 = 20) ∧
    (α ^ 2 + β ^ 2 + ρ) % 200 = c := by
  interval_cases c
  · exact ⟨1, 2, 195, by norm_num⟩
  · exact ⟨0, 4, 185, by norm_num⟩
  · exact ⟨1, 4, 185, by norm_num⟩
  · exact ⟨2, 2, 195, by norm_num⟩
  · exact ⟨0, 3, 195, by norm_num⟩
  · exact ⟨0, 10, 105, by norm_num⟩
  · exact ⟨1, 10, 105, by norm_num⟩
  · exact ⟨4, 6, 155, by norm_num⟩
  · exact ⟨2, 3, 195, by norm_num⟩
  · exact ⟨0, 8, 145, by norm_num⟩
  · exact ⟨0, 5, 185, by norm_num⟩
  · exact ⟨0, 4, 195, by norm_num⟩
  · exact ⟨1, 4, 195, by norm_num⟩
  · exact ⟨2, 8, 145, by norm_num⟩
  · exact ⟨2, 5, 185, by norm_num⟩
  · exact ⟨0, 10, 115, by norm_num⟩
  · exact ⟨1, 10, 115, by norm_num⟩
  · exact ⟨4, 4, 185, by norm_num⟩
  · exact ⟨3, 8, 145, by norm_num⟩
  · exact ⟨0, 8, 155, by norm_num⟩
  · exact ⟨0, 5, 195, by norm_num⟩
  · exact ⟨0, 6, 185, by norm_num⟩
  · exact ⟨1, 6, 185, by norm_num⟩
  · exact ⟨2, 8, 155, by norm_num⟩
  · exact ⟨2, 5, 195, by norm_num⟩
  · exact ⟨2, 6, 185, by norm_num⟩
  · exact ⟨0, 9, 145, by norm_num⟩
  · exact ⟨1, 9, 145, by norm_num⟩
  · exact ⟨3, 8, 155, by norm_num⟩
  · exact ⟨0, 18, 105, by norm_num⟩
  · exact ⟨1, 18, 105, by norm_num⟩
  · exact ⟨0, 6, 195, by norm_num⟩
  · exact ⟨1, 6, 195, by norm_num⟩
  · exact ⟨2, 18, 105, by norm_num⟩
  · exact ⟨0, 7, 185, by norm_num⟩
  · exact ⟨0, 0, 35, by norm_num⟩
  · exact ⟨0, 1, 35, by norm_num⟩
  · exact ⟨1, 1, 35, by norm_num⟩
  · exact ⟨2, 7, 185, by norm_num⟩
  · exact ⟨0, 2, 35, by norm_num⟩
  · exact ⟨1, 2, 35, by norm_num⟩
  · exact ⟨0, 16, 185, by norm_num⟩
  · exact ⟨1, 16, 185, by norm_num⟩
  · exact ⟨2, 2, 35, by norm_num⟩
  · exact ⟨0, 3, 35, by norm_num⟩
  · exact ⟨0, 10, 145, by norm_num⟩
  · exact ⟨1, 10, 145, by norm_num⟩
  · exact ⟨4, 6, 195, by norm_num⟩
  · exact ⟨2, 3, 35, by norm_num⟩
  · exact ⟨0, 8, 185, by norm_num⟩
  · exact ⟨1, 8, 185, by norm_num⟩
  · exact ⟨0, 4, 35, by norm_num⟩
  · exact ⟨1, 4, 35, by norm_num⟩
  · exact ⟨2, 8, 185, by norm_num⟩
  · exact ⟨3, 10, 145, by norm_num⟩
  · exact ⟨0, 10, 155, by norm_num⟩
  · exact ⟨1, 10, 155, by norm_num⟩
  · exact ⟨4, 16, 185, by norm_num⟩
  · exact ⟨3, 8, 185, by norm_num⟩
  · exact ⟨0, 8, 195, by norm_num⟩
  · exact ⟨0, 5, 35, by norm_num⟩
  · exact ⟨0, 14, 65, by norm_num⟩
  · exact ⟨1, 14, 65, by norm_num⟩
  · exact ⟨2, 8, 195, by norm_num⟩
  · exact ⟨2, 5, 35, by norm_num⟩
  · exact ⟨0, 0, 65, by norm_num⟩
  · exact ⟨0, 1, 65, by norm_num⟩
  · exact ⟨1, 1, 65, by norm_num⟩
  · exact ⟨3, 8, 195, by norm_num⟩
  · exact ⟨0, 2, 65, by norm_num⟩
  · exact ⟨1, 2, 65, by norm_num⟩
  · exact ⟨0, 6, 35, by norm_num⟩
  · exact ⟨1, 6, 35, by norm_num⟩
  · exact ⟨2, 2, 65, by norm_num⟩
  · exact ⟨0, 3, 65, by norm_num⟩
  · exact ⟨1, 3, 65, by norm_num⟩
  · exact ⟨0, 9, 195, by norm_num⟩
  · exact ⟨1, 9, 195, by norm_num⟩
  · exact ⟨2, 3, 65, by norm_num⟩
  · exact ⟨0, 18, 155, by norm_num⟩
  · exact ⟨1, 18, 155, by norm_num⟩
  · exact ⟨0, 4, 65, by norm_num⟩
  · exact ⟨1, 4, 65, by norm_num⟩
  · exact ⟨2, 18, 155, by norm_num⟩
  · exact ⟨0, 7, 35, by norm_num⟩
  · exact ⟨0, 10, 185, by norm_num⟩
  · exact ⟨1, 10, 185, by norm_num⟩
  · exact ⟨4, 6, 35, by norm_num⟩
  · exact ⟨2, 7, 35, by norm_num⟩
  · exact ⟨0, 12, 145, by norm_num⟩
  · exact ⟨0, 5, 65, by norm_num⟩
  · exact ⟨0, 16, 35, by norm_num⟩
  · exact ⟨1, 16, 35, by norm_num⟩
  · exact ⟨2, 12, 145, by norm_num⟩
  · exact ⟨2, 5, 65, by norm_num⟩
  · exact ⟨0, 10, 195, by norm_num⟩
  · exact ⟨1, 10, 195, by norm_num⟩
  · exact ⟨4, 4, 65, by norm_num⟩
  · exact ⟨3, 12, 145, by norm_num⟩
  · exact ⟨0, 8, 35, by norm_num⟩
  · exact ⟨1, 8, 35, by norm_num⟩
  · exact ⟨0, 6, 65, by norm_num⟩
  · exact ⟨1, 6, 65, by norm_num⟩
  · exact ⟨2, 8, 35, by norm_num⟩
  · exact ⟨3, 10, 195, by norm_num⟩
  · exact ⟨0, 0, 105, by norm_num⟩
  · exact ⟨0, 1, 105, by norm_num⟩
  · exact ⟨1, 1, 105, by norm_num⟩
  · exact ⟨3, 8, 35, by norm_num⟩
  · exact ⟨0, 2, 105, by norm_num⟩
  · exact ⟨1, 2, 105, by norm_num⟩
  · exact ⟨0, 14, 115, by norm_num⟩
  · exact ⟨1, 14, 115, by norm_num⟩
  · exact ⟨2, 2, 105, by norm_num⟩
  · exact ⟨0, 3, 105, by norm_num⟩
  · exact ⟨0, 0, 115, by norm_num⟩
  · exact ⟨0, 1, 115, by norm_num⟩
  · exact ⟨1, 1, 115, by norm_num⟩
  · exact ⟨2, 3, 105, by norm_num⟩
  · exact ⟨0, 2, 115, by norm_num⟩
  · exact ⟨1, 2, 115, by norm_num⟩
  · exact ⟨0, 4, 105, by norm_num⟩
  · exact ⟨1, 4, 105, by norm_num⟩
  · exact ⟨2, 2, 115, by norm_num⟩
  · exact ⟨0, 3, 115, by norm_num⟩
  · exact ⟨1, 3, 115, by norm_num⟩
  · exact ⟨5, 6, 65, by norm_num⟩
  · exact ⟨4, 14, 115, by norm_num⟩
  · exact ⟨2, 3, 115, by norm_num⟩
  · exact ⟨0, 8, 65, by norm_num⟩
  · exact ⟨0, 5, 105, by norm_num⟩
  · exact ⟨0, 4, 115, by norm_num⟩
  · exact ⟨1, 4, 115, by norm_num⟩
  · exact ⟨2, 8, 65, by norm_num⟩
  · exact ⟨2, 5, 105, by norm_num⟩
  · exact ⟨0, 10, 35, by norm_num⟩
  · exact ⟨1, 10, 35, by norm_num⟩
  · exact ⟨4, 4, 105, by norm_num⟩
  · exact ⟨3, 8, 65, by norm_num⟩
  · exact ⟨0, 12, 195, by norm_num⟩
  · exact ⟨0, 5, 115, by norm_num⟩
  · exact ⟨0, 6, 105, by norm_num⟩
  · exact ⟨1, 6, 105, by norm_num⟩
  · exact ⟨2, 12, 195, by norm_num⟩
  · exact ⟨2, 5, 115, by norm_num⟩
  · exact ⟨0, 0, 145, by norm_num⟩
  · exact ⟨0, 1, 145, by norm_num⟩
  · exact ⟨1, 1, 145, by norm_num⟩
  · exact ⟨3, 12, 195, by norm_num⟩
  · exact ⟨0, 2, 145, by norm_num⟩
  · exact ⟨1, 2, 145, by norm_num⟩
  · exact ⟨0, 6, 115, by norm_num⟩
  · exact ⟨1, 6, 115, by norm_num⟩
  · exact ⟨2, 2, 145, by norm_num⟩
  · exact ⟨0, 3, 145, by norm_num⟩
  · exact ⟨0, 0, 155, by norm_num⟩
  · exact ⟨0, 1, 155, by norm_num⟩
  · exact ⟨1, 1, 155, by norm_num⟩
  · exact ⟨2, 3, 145, by norm_num⟩
  · exact ⟨0, 2, 155, by norm_num⟩
  · exact ⟨1, 2, 155, by norm_num⟩
  · exact ⟨0, 4, 145, by norm_num⟩
  · exact ⟨1, 4, 145, by norm_num⟩
  · exact ⟨2, 2, 155, by norm_num⟩
  · exact ⟨0, 3, 155, by norm_num⟩
  · exact ⟨0, 10, 65, by norm_num⟩
  · exact ⟨1, 10, 65, by norm_num⟩
  · exact ⟨4, 6, 115, by norm_num⟩
  · exact ⟨2, 3, 155, by norm_num⟩
  · exact ⟨0, 8, 105, by norm_num⟩
  · exact ⟨0, 5, 145, by norm_num⟩
  · exact ⟨0, 4, 155, by norm_num⟩
  · exact ⟨1, 4, 155, by norm_num⟩
  · exact ⟨2, 8, 105, by norm_num⟩
  · exact ⟨2, 5, 145, by norm_num⟩
  · exact ⟨2, 4, 155, by norm_num⟩
  · exact ⟨5, 6, 115, by norm_num⟩
  · exact ⟨4, 4, 145, by norm_num⟩
  · exact ⟨3, 8, 105, by norm_num⟩
  · exact ⟨0, 8, 115, by norm_num⟩
  · exact ⟨0, 5, 155, by norm_num⟩
  · exact ⟨0, 6, 145, by norm_num⟩
  · exact ⟨1, 6, 145, by norm_num⟩
  · exact ⟨2, 8, 115, by norm_num⟩
  · exact ⟨2, 5, 155, by norm_num⟩
  · exact ⟨0, 0, 185, by norm_num⟩
  · exact ⟨0, 1, 185, by norm_num⟩
  · exact ⟨1, 1, 185, by norm_num⟩
  · exact ⟨3, 8, 115, by norm_num⟩
  · exact ⟨0, 2, 185, by norm_num⟩
  · exact ⟨1, 2, 185, by norm_num⟩
  · exact ⟨0, 6, 155, by norm_num⟩
  · exact ⟨1, 6, 155, by norm_num⟩
  · exact ⟨2, 2, 185, by norm_num⟩
  · exact ⟨0, 3, 185, by norm_num⟩
  · exact ⟨0, 0, 195, by norm_num⟩
  · exact ⟨0, 1, 195, by norm_num⟩
  · exact ⟨1, 1, 195, by norm_num⟩
  · exact ⟨2, 3, 185, by norm_num⟩
  · exact ⟨0, 2, 195, by norm_num⟩

lemma sq_shift (α s : ℕ) : ∃ K, (α + 200 * s) ^ 2 = α ^ 2 + 200 * K :=
  ⟨2 * α * s + 200 * s ^ 2, by ring⟩

lemma lt_of_sq_lt {x b : ℕ} (h : x ^ 2 < b ^ 2) : x < b := by
  by_contra hx
  have : b ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (not_lt.mp hx) 2
  omega

theorem main : H1 → H2 → OMA.R_Erdos338_erdos_338_variants_squares_R1.H2 := by
  intro h1 h2
  show HasRestrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) 5
  unfold HasRestrictedOrder
  rw [Filter.eventually_atTop]
  refine ⟨12000 ^ 2, fun n hn => ?_⟩
  obtain ⟨α, β, ρ, hα, hβ, hρ, hρ8, hρ25, hmod⟩ := table (n % 200) (Nat.mod_lt _ (by norm_num))
  set q := Nat.sqrt n with hq
  have hq1 : q * q ≤ n := Nat.sqrt_le n
  have hq2 : n < (q + 1) * (q + 1) := Nat.lt_succ_sqrt n
  have hq0 : 12000 ≤ q := Nat.le_sqrt.mpr (by simpa [sq] using hn)
  set A := α + 200 * (3 * q / 800) with hA
  set B := β + 200 * (q / 400) with hB
  have hA1 : 3 * q ≤ 4 * A + 799 := by omega
  have hA2 : 4 * A < 3 * q + 800 := by omega
  have hB1 : q ≤ 2 * B + 399 := by omega
  have hB2 : 2 * B < q + 400 := by omega
  have hBA : B < A := by omega
  have hB0 : 0 < B := by omega
  have hsum : A ^ 2 + B ^ 2 ≤ n := by nlinarith
  have hlt : n < A ^ 2 + 2 * B ^ 2 := by nlinarith
  set r := n - A ^ 2 - B ^ 2 with hr
  have hrn : r + A ^ 2 + B ^ 2 = n := by omega
  have hrB : r < B ^ 2 := by omega
  obtain ⟨K1, hK1⟩ := sq_shift α (3 * q / 800)
  obtain ⟨K2, hK2⟩ := sq_shift β (q / 400)
  have hr200 : r % 200 = ρ := by
    rw [← hA] at hK1; rw [← hB] at hK2
    omega
  have hr8 : r % 8 = 1 ∨ r % 8 = 3 := by omega
  have hr25 : r % 25 = 5 ∨ r % 25 = 10 ∨ r % 25 = 15 ∨ r % 25 = 20 := by omega
  obtain ⟨x, y, z, hxyz⟩ : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = r := by
    rcases hr8 with h | h
    · exact h1 r h
    · exact h2 r h
  have hxy : x ^ 2 ≠ y ^ 2 := fun e => not_form r z x hr25 (by rw [← hxyz, e]; ring)
  have hxz : x ^ 2 ≠ z ^ 2 := fun e => not_form r y x hr25 (by rw [← hxyz, e]; ring)
  have hyz : y ^ 2 ≠ z ^ 2 := fun e => not_form r x y hr25 (by rw [← hxyz, e]; ring)
  have hxB : x ^ 2 < B ^ 2 := by omega
  have hyB : y ^ 2 < B ^ 2 := by omega
  have hzB : z ^ 2 < B ^ 2 := by omega
  have hBA2 : B ^ 2 < A ^ 2 := Nat.pow_lt_pow_left hBA (by norm_num)
  refine ⟨{A ^ 2, B ^ 2, x ^ 2, y ^ 2, z ^ 2}, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · have c1 := Finset.card_insert_le (A ^ 2) ({B ^ 2, x ^ 2, y ^ 2, z ^ 2} : Finset ℕ)
    have c2 := Finset.card_insert_le (B ^ 2) ({x ^ 2, y ^ 2, z ^ 2} : Finset ℕ)
    have c3 := Finset.card_insert_le (x ^ 2) ({y ^ 2, z ^ 2} : Finset ℕ)
    have c4 := Finset.card_insert_le (y ^ 2) ({z ^ 2} : Finset ℕ)
    have c5 := Finset.card_singleton (z ^ 2)
    omega
  · rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton]
    omega

end OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1
