import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

/-! # `2 * 4 ^ k` is not a sum of at most four distinct squares

A sum of at most four squares that is divisible by `8` has all its terms divisible by `4`,
so a representation of `2 * 4 ^ (k + 1)` by distinct squares descends to one of `2 * 4 ^ k`.
The descent ends at `2`, which is not a sum of distinct squares.
-/

namespace OMA338

open Finset

lemma sq_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
  have h8 : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [h]
  interval_cases (a % 8) <;> simp

/-- If at most four squares sum to a multiple of `8`, each of them is a multiple of `4`. -/
lemma four_dvd_of_sum (S : Finset ℕ) (hsq : ∀ x ∈ S, ∃ a : ℕ, a ^ 2 = x) (hcard : S.card ≤ 4)
    (hsum : (∑ x ∈ S, x) % 8 = 0) : ∀ x ∈ S, 4 ∣ x := by
  have hmod : ∀ x ∈ S, x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 4 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hsq x hx
    exact sq_mod_eight a
  have hrew : ∑ x ∈ S, x % 8 =
      (S.filter (fun x => x % 8 = 1)).card + 4 * (S.filter (fun x => x % 8 = 4)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rcases hmod x hx with h | h | h <;> simp [h]
  have hle : (S.filter (fun x => x % 8 = 1)).card + (S.filter (fun x => x % 8 = 4)).card
      ≤ S.card := by
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    · rw [Finset.disjoint_filter]
      intro x _ h1 h4
      omega
  have hsum' : (∑ x ∈ S, x % 8) % 8 = 0 := by
    rw [← Finset.sum_nat_mod]
    exact hsum
  have hO : (S.filter (fun x => x % 8 = 1)).card = 0 := by
    rw [hrew] at hsum'
    omega
  intro x hx
  have hx1 : x % 8 ≠ 1 := by
    intro h1
    have hmem : x ∈ S.filter (fun x => x % 8 = 1) := Finset.mem_filter.2 ⟨hx, h1⟩
    rw [Finset.card_eq_zero] at hO
    rw [hO] at hmem
    exact absurd hmem (Finset.notMem_empty x)
  rcases hmod x hx with h | h | h
  · omega
  · exact absurd h hx1
  · omega

lemma key (k : ℕ) : ∀ S : Finset ℕ, (∀ x ∈ S, ∃ a : ℕ, a ^ 2 = x) → S.card ≤ 4 →
    ∑ x ∈ S, x = 2 * 4 ^ k → False := by
  induction k with
  | zero =>
    intro S hsq _ hsum
    have hsub : S ⊆ ({0, 1} : Finset ℕ) := by
      intro x hx
      have hle : x ≤ ∑ y ∈ S, y := Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
      obtain ⟨a, rfl⟩ := hsq x hx
      have ha : a ≤ 1 := by
        by_contra hlt
        have h2 : 2 ≤ a := by omega
        have : 4 ≤ a ^ 2 := by nlinarith
        omega
      interval_cases a <;> simp
    have := Finset.sum_le_sum_of_subset (f := fun y : ℕ => y) hsub
    simp at this
    omega
  | succ k ih =>
    intro S hsq hcard hsum
    have h8 : (∑ x ∈ S, x) % 8 = 0 := by
      rw [hsum, pow_succ]
      omega
    have h4 := four_dvd_of_sum S hsq hcard h8
    apply ih (S.image (fun x => x / 4))
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨a, rfl⟩ := hsq x hx
      have h2 : 2 ∣ a := by
        have : 2 ∣ a ^ 2 := Dvd.dvd.trans (by norm_num) (h4 _ hx)
        exact Nat.prime_two.dvd_of_dvd_pow this
      obtain ⟨b, rfl⟩ := h2
      refine ⟨b, ?_⟩
      have : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    · exact Finset.card_image_le.trans hcard
    · rw [Finset.sum_image]
      · have hmul : 4 * ∑ x ∈ S, x / 4 = ∑ x ∈ S, x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          exact Nat.mul_div_cancel' (h4 x hx)
        rw [hsum, pow_succ] at hmul
        omega
      · intro x hx y hy hxy
        have hx4 := h4 x hx
        have hy4 := h4 y hy
        simp only at hxy
        omega

end OMA338

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H3 := by
  intro h
  unfold Erdos338.HasRestrictedOrder at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  have hbig : N ≤ 2 * 4 ^ N := by
    have : N < 4 ^ N := Nat.lt_pow_self (by norm_num)
    omega
  obtain ⟨S, hS, hcard, hsum⟩ := hN (2 * 4 ^ N) hbig
  refine OMA338.key N S ?_ hcard hsum
  intro x hx
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a, ha⟩
