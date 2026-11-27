import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

-- Step Erdos338.erdos_338.variants.squares.R1.H3: hypothesis H3 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @ivillar
-- H3 := ¬ HasRestrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) 4

namespace OMA.E338H3

/-- Squares are `0`, `1` or `4` modulo `8`. -/
lemma sq_mod8 (r : ℕ) : r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 1 ∨ r ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have hlt : r % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases r % 8 <;> simp

/-- `2 * 4 ^ k` is never a sum of at most four distinct squares. If such a sum is divisible
by `8`, the number of odd squares in it is `0` or `4` modulo `4`, and four odd squares sum to `4`
modulo `8`; so all the squares are even and dividing by `4` descends to `2 * 4 ^ (k - 1)`. -/
lemma no_rep (k : ℕ) : ∀ S : Finset ℕ, (∀ x ∈ S, ∃ r, r ^ 2 = x) → S.card ≤ 4 →
    ∑ x ∈ S, x ≠ 2 * 4 ^ k := by
  induction k with
  | zero =>
    intro S hS _ hsum
    have hsum' : ∑ x ∈ S, x = 2 := by simpa using hsum
    have hsub : S ⊆ {0, 1} := by
      intro x hx
      have hle : x ≤ ∑ y ∈ S, y := Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
      obtain ⟨r, rfl⟩ := hS x hx
      have hr : r ≤ 1 := by nlinarith
      interval_cases r <;> simp
    have := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
    simp at this
    omega
  | succ k ih =>
    intro S hS hc hsum
    classical
    have hpow : 2 * 4 ^ (k + 1) = 8 * 4 ^ k := by ring
    have hmodS : ∀ x ∈ S, x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 4 := by
      intro x hx; obtain ⟨r, rfl⟩ := hS x hx; exact sq_mod8 r
    have hsplit : ∑ x ∈ S, x = ∑ x ∈ S.filter (fun x => x % 2 = 1), x +
        ∑ x ∈ S.filter (fun x => ¬ x % 2 = 1), x :=
      (Finset.sum_filter_add_sum_filter_not S _ _).symm
    have hcard : (S.filter (fun x => x % 2 = 1)).card +
        (S.filter (fun x => ¬ x % 2 = 1)).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have hOmod : (∑ x ∈ S.filter (fun x => x % 2 = 1), x) % 8 =
        (S.filter (fun x => x % 2 = 1)).card % 8 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl (g := fun _ => 1)]
      · simp
      · intro x hx
        rw [Finset.mem_filter] at hx
        have := hmodS x hx.1
        omega
    have hEmod : (∑ x ∈ S.filter (fun x => ¬ x % 2 = 1), x) % 4 = 0 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl (g := fun _ => 0)]
      · simp
      · intro x hx
        rw [Finset.mem_filter] at hx
        have := hmodS x hx.1
        omega
    have hE0 : (S.filter (fun x => ¬ x % 2 = 1)).card = 0 →
        ∑ x ∈ S.filter (fun x => ¬ x % 2 = 1), x = 0 := by
      intro h; rw [Finset.card_eq_zero.mp h]; simp
    rw [hpow] at hsum
    have hOc : (S.filter (fun x => x % 2 = 1)).card = 0 := by
      by_cases hc0 : (S.filter (fun x => ¬ x % 2 = 1)).card = 0
      · have := hE0 hc0; omega
      · omega
    have hall : ∀ x ∈ S, x % 4 = 0 := by
      intro x hx
      have hxO : x ∉ S.filter (fun x => x % 2 = 1) := by
        rw [Finset.card_eq_zero.mp hOc]; simp
      rw [Finset.mem_filter] at hxO
      have h2 : ¬ x % 2 = 1 := fun h => hxO ⟨hx, h⟩
      have := hmodS x hx
      omega
    have hinj : Set.InjOn (fun x => x / 4) S := by
      intro x hx y hy hxy
      have := hall x hx
      have := hall y hy
      simp only at hxy
      omega
    refine ih (S.image (· / 4)) ?_ ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨r, rfl⟩ := hS x hx
      have h4 := hall _ hx
      have he : Even (r ^ 2) :=
        Nat.even_iff.mpr (by rw [← Nat.mod_mod_of_dvd (r ^ 2) (by norm_num : 2 ∣ 4), h4])
      obtain ⟨s, hs⟩ := (Nat.even_pow.mp he).1
      refine ⟨s, ?_⟩
      rw [hs, show (s + s) ^ 2 = 4 * s ^ 2 by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    · rw [Finset.card_image_of_injOn hinj]; exact hc
    · rw [Finset.sum_image hinj]
      have h4sum : ∑ x ∈ S, x = 4 * ∑ x ∈ S, x / 4 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have := hall x hx
        omega
      rw [hsum] at h4sum
      omega

end OMA.E338H3

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H3 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H3
  intro h
  rw [Erdos338.HasRestrictedOrder, Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : 2 ^ N ≤ 4 ^ N := Nat.pow_le_pow_left (by norm_num) N
  obtain ⟨S, hS, hc, hsum⟩ := hN (2 * 4 ^ N) (by omega)
  refine OMA.E338H3.no_rep N S ?_ hc hsum
  intro x hx
  obtain ⟨r, hr⟩ := hS x hx
  exact ⟨r, hr⟩
