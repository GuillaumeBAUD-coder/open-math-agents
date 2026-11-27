import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1
import Mathlib

-- Step Erdos338.erdos_338.variants.squares.R1.H3: hypothesis H3 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @luciusacarr

/-! `2 * 4 ^ k` is never a sum of at most four distinct squares: `2` is not, and a representation
of `8m` by at most four squares uses only even squares, so it halves to one of `2m`. -/

namespace OMA338sqH3

open Erdos338 Filter

lemma sq_mod8' (k : ℕ) : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by
  have h : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have : k ^ 2 % 8 = (k % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  rw [this]
  interval_cases (k % 8) <;> simp

/-- Four residues in `{0, 1, 4}` mod `8` summing to `0` mod `8` are all `0` mod `4`. -/
lemma all_mod4 (S : Multiset ℕ) (hS : ∀ x ∈ S, x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 4)
    (hc : S.card ≤ 4) (hs : S.sum % 8 = 0) : ∀ x ∈ S, x % 4 = 0 := by
  have key : ∀ a b c d : ℕ, a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 4 →
      b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 4 → c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 4 →
      d % 8 = 0 ∨ d % 8 = 1 ∨ d % 8 = 4 → (a + (b + (c + d))) % 8 = 0 →
      a % 4 = 0 ∧ b % 4 = 0 ∧ c % 4 = 0 ∧ d % 4 = 0 := by intros; omega
  have h0 : (0 : ℕ) % 8 = 0 ∨ (0 : ℕ) % 8 = 1 ∨ (0 : ℕ) % 8 = 4 := Or.inl rfl
  intro x hx
  have hpos : 0 < S.card := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
  rcases Nat.lt_or_ge S.card 4 with h4 | h4
  · rcases Nat.lt_or_ge S.card 3 with h3 | h3
    · rcases Nat.lt_or_ge S.card 2 with h2 | h2
      · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp (show S.card = 1 by omega)
        simp only [Multiset.mem_singleton] at hx; subst hx
        simp only [Multiset.sum_singleton] at hs
        exact (key x 0 0 0 (hS x (by simp)) h0 h0 h0 (by simpa using hs)).1
      · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp (show S.card = 2 by omega)
        simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
          Multiset.mem_cons, Multiset.mem_singleton] at hs hx
        have := key a b 0 0 (hS a (by simp)) (hS b (by simp)) h0 h0 (by simpa using hs)
        rcases hx with rfl | rfl
        · exact this.1
        · exact this.2.1
    · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp (show S.card = 3 by omega)
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
        Multiset.mem_cons, Multiset.mem_singleton] at hs hx
      have := key a b c 0 (hS a (by simp)) (hS b (by simp)) (hS c (by simp)) h0
        (by simpa using hs)
      rcases hx with rfl | rfl | rfl
      · exact this.1
      · exact this.2.1
      · exact this.2.2.1
  · obtain ⟨T, rfl⟩ := Multiset.exists_cons_of_mem hx
    have hT : T.card = 3 := by simp at hc h4; omega
    obtain ⟨b, c, d, rfl⟩ := Multiset.card_eq_three.mp hT
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hs
    exact (key x b c d (hS x (by simp)) (hS b (by simp)) (hS c (by simp)) (hS d (by simp))
      hs).1

/-- `n` is a sum of at most four distinct squares. -/
def Rep4 (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ Set.range fun k : ℕ ↦ k ^ 2) ∧ S.card ≤ 4 ∧ ∑ x ∈ S, x = n

lemma rep4_descent {m : ℕ} (hm : m % 2 = 0) (h : Rep4 (4 * m)) : Rep4 m := by
  obtain ⟨S, hS, hc, hs⟩ := h
  have hmod : ∀ x ∈ S, x % 4 = 0 := by
    have := all_mod4 S.val (fun x hx => by
        obtain ⟨k, rfl⟩ := hS x hx
        exact sq_mod8' k) (by simpa using hc)
      (by have e : (∑ x ∈ S, x) = S.val.sum := by rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
          omega)
    exact fun x hx => this x hx
  refine ⟨S.image (· / 4), ?_, (Finset.card_image_le).trans hc, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, rfl⟩ := hS x hx
    have h4 := hmod _ hx
    have hk : k % 2 = 0 := by
      have : k ^ 2 % 4 = (k % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
      have hk4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [this] at h4
      interval_cases hh : (k % 4) <;> simp_all <;> omega
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    exact ⟨j, by simp only; ring_nf; omega⟩
  · rw [Finset.sum_image]
    · have : ∑ x ∈ S, x = ∑ x ∈ S, 4 * (x / 4) :=
        Finset.sum_congr rfl fun x hx => by have := hmod x hx; omega
      rw [this, ← Finset.mul_sum] at hs
      omega
    · intro x hx y hy hxy
      have := hmod x hx; have := hmod y hy
      simp only at hxy
      omega

lemma not_rep4_two : ¬ Rep4 2 := by
  rintro ⟨S, hS, -, hs⟩
  have hsub : S ⊆ {0, 1} := by
    intro x hx
    have hle : x ≤ ∑ y ∈ S, y := Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
    obtain ⟨k, rfl⟩ := hS x hx
    have : k ≤ 1 := by nlinarith [hs]
    interval_cases k <;> simp
  have := Finset.sum_le_sum_of_subset hsub (f := id)
  simp at this
  omega

lemma not_rep4_pow (k : ℕ) : ¬ Rep4 (2 * 4 ^ k) := by
  induction k with
  | zero => simpa using not_rep4_two
  | succ k ih =>
    intro h
    apply ih
    apply rep4_descent (by rw [Nat.mul_mod]; simp)
    rwa [pow_succ, show 2 * (4 ^ k * 4) = 4 * (2 * 4 ^ k) by ring] at h

theorem main_H3 : OMA.R_Erdos338_erdos_338_variants_squares_R1.H3 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H3
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hle : N ≤ 2 * 4 ^ N := by
    have := Nat.lt_pow_self (show 1 < 4 by norm_num) (n := N)
    omega
  exact not_rep4_pow N (hN _ hle)

end OMA338sqH3

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H3 := OMA338sqH3.main_H3
