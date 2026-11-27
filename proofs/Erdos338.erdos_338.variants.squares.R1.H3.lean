import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

-- Step Erdos338.erdos_338.variants.squares.R1.H3: hypothesis H3 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @gunnerhowe
-- H3 := not every sufficiently large integer is a sum of at most 4 distinct squares.
-- Proof: 8 * 4 ^ j is never a sum of at most 4 distinct squares. For j = 0 only 0, 1, 4 fit.
-- A sum of at most 4 squares that is 0 mod 8 has all summands divisible by 4 (odd squares are
-- 1 mod 8), so dividing every summand by 4 descends from j + 1 to j.

namespace OMA.Step338H3

open Filter Erdos338

abbrev Sq : Set ℕ := Set.range fun k : ℕ ↦ k ^ 2

lemma sq_mod8 (k : ℕ) : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by
  have h : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [Nat.pow_mod]
  interval_cases (k % 8) <;> simp

/-- minimal number of squares (mod 8) needed to reach each residue -/
lemma sq_cases {x : ℕ} (hx : x ∈ Sq) : x % 8 = 1 ∨ 4 ∣ x := by
  obtain ⟨k, rfl⟩ := hx
  dsimp only
  rcases sq_mod8 k with h | h | h <;> omega

lemma div4_sq {x : ℕ} (hx : x ∈ Sq) (h4 : 4 ∣ x) : x / 4 ∈ Sq := by
  obtain ⟨k, rfl⟩ := hx
  have h2 : 2 ∣ k := Nat.prime_two.dvd_of_dvd_pow (Nat.dvd_trans (by norm_num) h4)
  obtain ⟨m, rfl⟩ := h2
  exact ⟨m, by dsimp only; ring_nf; omega⟩

lemma all_div4 (S : Finset ℕ) (hS : ∀ x ∈ S, x ∈ Sq) (hc : S.card ≤ 4)
    (h8 : (∑ x ∈ S, x) % 8 = 0) : ∀ x ∈ S, 4 ∣ x := by
  classical
  let O := S.filter (fun x => x % 8 = 1)
  let E := S.filter (fun x => ¬ x % 8 = 1)
  have hsplit : ∑ x ∈ O, x + ∑ x ∈ E, x = ∑ x ∈ S, x :=
    Finset.sum_filter_add_sum_filter_not S _ _
  have hcard : O.card + E.card = S.card := Finset.card_filter_add_card_filter_not _
  have hO : (∑ x ∈ O, x) % 8 = O.card % 8 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro x hx; exact (Finset.mem_filter.mp hx).2
  have hE : (∑ x ∈ E, x) % 4 = 0 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl (g := fun _ => 0)]
    · simp
    · intro x hx
      obtain ⟨hxS, hx1⟩ := Finset.mem_filter.mp hx
      have := (sq_cases (hS x hxS)).resolve_left hx1
      exact Nat.eq_zero_of_dvd_of_lt (Nat.dvd_mod_iff (by norm_num) |>.mpr this) (Nat.mod_lt _ (by norm_num)) |>.symm ▸ rfl
  have hOc : O.card = 0 := by
    have hmod4 : O.card % 4 = 0 := by omega
    rcases (by omega : O.card = 0 ∨ O.card = 4) with h | h
    · exact h
    · exfalso
      have hE0 : E.card = 0 := by omega
      have hEe : E = ∅ := Finset.card_eq_zero.mp hE0
      rw [hEe, Finset.sum_empty] at hsplit
      omega
  intro x hx
  have hxO : x ∉ O := by rw [Finset.card_eq_zero.mp hOc]; simp
  have hx1 : ¬ x % 8 = 1 := fun h => hxO (Finset.mem_filter.mpr ⟨hx, h⟩)
  exact (sq_cases (hS x hx)).resolve_left hx1

lemma no_rep (j : ℕ) : ∀ S : Finset ℕ, (∀ x ∈ S, x ∈ Sq) → S.card ≤ 4 →
    ∑ x ∈ S, x ≠ 8 * 4 ^ j := by
  induction j with
  | zero =>
    intro S hS _ hsum
    simp at hsum
    have hsub : S ⊆ {0, 1, 4} := by
      intro x hx
      have hle0 : x ≤ ∑ y ∈ S, y := Finset.single_le_sum (f := fun y : ℕ => y) (fun _ _ => Nat.zero_le _) hx
      have hle : x ≤ 8 := by omega
      obtain ⟨k, rfl⟩ := hS x hx
      simp only at hle ⊢
      have hk : k ≤ 2 := by
        by_contra h
        have : 9 ≤ k ^ 2 := by nlinarith
        omega
      interval_cases k <;> simp
    have := Finset.sum_le_sum_of_subset (f := fun y : ℕ => y) hsub
    rw [hsum] at this
    simp at this
  | succ j ih =>
    intro S hS hc hsum
    classical
    have h8 : (∑ x ∈ S, x) % 8 = 0 := by rw [hsum, pow_succ]; omega
    have h4 := all_div4 S hS hc h8
    have hinj : Set.InjOn (fun x => x / 4) S := by
      intro a ha b hb hab
      have := Nat.div_mul_cancel (h4 a ha)
      have := Nat.div_mul_cancel (h4 b hb)
      simp only at hab
      omega
    apply ih (S.image (fun x => x / 4))
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact div4_sq (hS x hx) (h4 x hx)
    · rw [Finset.card_image_of_injOn hinj]; exact hc
    · rw [Finset.sum_image hinj]
      have hmul : ∑ x ∈ S, x = 4 * ∑ x ∈ S, x / 4 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x hx => (Nat.mul_div_cancel' (h4 x hx)).symm
      rw [hmul, pow_succ] at hsum
      omega

theorem H3 : ¬ HasRestrictedOrder Sq 4 := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  have hbig : N ≤ 8 * 4 ^ N := by
    have : N < 4 ^ N := Nat.lt_pow_self (by norm_num)
    omega
  obtain ⟨S, hS, hc, hsum⟩ := hN _ hbig
  exact no_rep N S hS hc hsum

end OMA.Step338H3

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H3 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H3
  exact OMA.Step338H3.H3
