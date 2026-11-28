import OMAStatements.S_oeis_a029858

-- Problem: A029858, (3^n - 3)/2 counts the integers in [1, 10^(n-1)) whose digits are all 7, 8 or 9.
-- Credit: @ShoQo
-- Proof: with B k = {m < 10^k : every digit >= 7} (0 included vacuously), splitting off the last
-- digit gives B (k+1) = {0} ∪ {10q + r : q ∈ B k, r ∈ {7,8,9}}, so 2|B k| + 1 = 3^(k+1).

namespace OMA_A029858_Proof

abbrev P (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7

lemma P_step (q r : ℕ) (hr : r < 10) (hr0 : 10 * q + r ≠ 0) :
    P (10 * q + r) ↔ r ∉ Finset.range 7 ∧ P q := by
  unfold P
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hr0)]
  have h1 : (10 * q + r) % 10 = r := by omega
  have h2 : (10 * q + r) / 10 = q := by omega
  simp [h1, h2]

/-- `B k`: numbers below `10^k` all of whose digits are ≥ 7 (0 included vacuously). -/
def B (k : ℕ) : Finset ℕ := (Finset.range (10 ^ k)).filter P

lemma B_succ (k : ℕ) :
    B (k + 1) = insert 0 ((B k ×ˢ ({7, 8, 9} : Finset ℕ)).image (fun x => 10 * x.1 + x.2)) := by
  ext m
  simp only [B, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨hm, hP⟩
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact Or.inl rfl
    right
    refine ⟨m / 10, m % 10, ⟨⟨?_, ?_⟩, ?_⟩, by omega⟩
    · rw [pow_succ] at hm; omega
    · have := (P_step (m / 10) (m % 10) (by omega) (by omega)).mp (by rwa [show 10 * (m / 10) + m % 10 = m by omega])
      exact this.2
    · have := (P_step (m / 10) (m % 10) (by omega) (by omega)).mp (by rwa [show 10 * (m / 10) + m % 10 = m by omega])
      have h7 := this.1
      simp only [Finset.mem_range, not_lt] at h7
      have : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
      simp; omega
  · rintro (rfl | ⟨q, r, ⟨⟨hq, hPq⟩, hr⟩, rfl⟩)
    · exact ⟨by positivity, by simp [P]⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      have hr' : 7 ≤ r ∧ r < 10 := by omega
      refine ⟨by rw [pow_succ]; omega, ?_⟩
      exact (P_step q r (by omega) (by omega)).mpr ⟨by simp; omega, hPq⟩

lemma card_B (k : ℕ) : 2 * (B k).card + 1 = 3 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [B_succ, Finset.card_insert_of_notMem, Finset.card_image_of_injOn, Finset.card_product]
    · simp; rw [pow_succ]; omega
    · rintro ⟨q, r⟩ hx ⟨q', r'⟩ hy h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton] at hx hy
      simp only at h
      simp only [Prod.mk.injEq]; omega
    · simp only [Finset.mem_image, Finset.mem_product, Prod.exists, not_exists, not_and,
        Finset.mem_insert, Finset.mem_singleton]
      intro q r _ hr; omega

end OMA_A029858_Proof

open OMA_A029858_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a029858.main := by
  show ∀ n : ℕ, 1 ≤ n → ((Finset.range (10 ^ (n - 1))).filter
      (fun m => m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7)).card = (3 ^ n - 3) / 2
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hfilter : (Finset.range (10 ^ (k + 1 - 1))).filter
      (fun m => m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7) = (B k).erase 0 := by
    ext m; simp only [B, P, Finset.mem_filter, Finset.mem_erase, Finset.mem_range]; tauto
  have h0 : 0 ∈ B k := by simp [B, P]
  rw [hfilter, Finset.card_erase_of_mem h0]
  have := card_B k
  have hpos : 1 ≤ (B k).card := Finset.card_pos.mpr ⟨0, h0⟩
  omega

