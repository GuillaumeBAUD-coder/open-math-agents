import FormalConjectures.ErdosProblems.«877»

-- Problem: Erdős Problem 877 — cameron erdos
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/877.lean:83 (declaration Erdos877.erdos_877.variants.cameron_erdos)

open Filter Erdos877 Finset Real

private def B (e : ℕ) (T : Finset ℕ) : Finset ℕ :=
  insert (2 * e) ((range (e / 2)).image fun i => if i ∈ T then 2 * i + 1 else 2 * e - (2 * i + 1))

theorem OMA.solution : type_of% @Erdos877.erdos_877.variants.cameron_erdos := by
  classical
  rw [eventually_atTop]
  refine ⟨24, fun n hn => ?_⟩
  have hE : ∀ e T, ∃ M, 1 ≤ e ∧ 2 * e ≤ n → IsMaximalSumFree n M ∧ B e T ⊆ M := fun e T => by
    by_cases h : 1 ≤ e ∧ 2 * e ≤ n
    · obtain ⟨M, hBM, hM, hmax⟩ :=
        ((Icc 1 n).powerset.filter fun A : Finset ℕ => IsSumFree (A : Set ℕ)).exists_le_maximal (a := B e T) <| by
          simp [isSumFree_iff]
          refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
          · simp [B] at hx; rcases hx with rfl | ⟨i, _, rfl⟩ <;> simp <;> grind only
          · simp [B] at hx hy hxy
            rcases hx with rfl | ⟨i, _, rfl⟩ <;> rcases hy with rfl | ⟨j, _, rfl⟩ <;>
              rcases hxy with _ | ⟨k, _, _⟩ <;> grind only
      simp at hM
      exact ⟨M, fun _ => ⟨⟨hM.1, hM.2, fun A hA hAs hMA => hMA.antisymm (hmax (by simp [hA, hAs]) hMA)⟩, hBM⟩⟩
    · exact ⟨∅, (absurd · h)⟩
  choose E hE using hE
  have hodd : ∀ {e i T M}, B e T ⊆ M → i < e / 2 → (i ∈ T → 2 * i + 1 ∈ M) ∧ (i ∉ T → 2 * e - (2 * i + 1) ∈ M) :=
    fun h hi => by constructor <;> intro ht <;> exact h (by simp [B]; right; exact ⟨_, hi, by simp [ht]⟩)
  have hsf : ∀ {M x y z}, IsMaximalSumFree n M → x ∈ M → y ∈ M → z ∈ M → x + y ≠ z :=
    fun h hx hy hz heq => isSumFree_iff.1 h.2.1 _ hx _ hy (heq ▸ hz)
  let fam (e : ℕ) := (range (e / 2)).powerset.image (E e)
  have hcf : ∀ e, 1 ≤ e ∧ 2 * e ≤ n → (fam e).card = 2 ^ (e / 2) := fun e he => by
    dsimp [fam]; rw [card_image_of_injOn, card_powerset, card_range]
    intro T hT T' hT' hEq
    rw [mem_coe, mem_powerset] at hT hT'
    obtain ⟨hM, h1⟩ := hE e T he
    have hr : ∀ {A}, A ⊆ range (e / 2) → B e A ⊆ E e T → ∀ i, i ∈ A ↔ i < e / 2 ∧ 2 * i + 1 ∈ E e T :=
      fun hAs hA i =>
        ⟨fun hiA => let hi := mem_range.1 (hAs hiA); ⟨hi, (hodd hA hi).1 hiA⟩,
         fun ⟨hi, hm⟩ => by_contra fun hiA => hsf hM hm ((hodd hA hi).2 hiA) (h1 (mem_insert_self _ _)) (by omega)⟩
    ext i; rw [hr hT h1, hr hT' (hEq ▸ (hE e T' he).2)]
  set e := n / 2
  have hov : (fam e ∩ fam (e - 1)).card ≤ e / 2 + 1 := by
    refine (card_le_card (t := (range (e / 2 + 1)).image fun k => E e (Ico k (e / 2))) ?_).trans
      (card_image_le.trans (by simp))
    intro M hM
    simp [fam, subset_iff] at hM
    obtain ⟨⟨T, hT, rfl⟩, ⟨T', -, hEq⟩⟩ := hM
    obtain ⟨hM, h1⟩ := hE e T (by omega)
    simp
    rcases T.eq_empty_or_nonempty with rfl | hne
    · exact ⟨e / 2, by omega, by simp⟩
    · refine ⟨T.min' hne, (hT (T.min'_mem hne)).le, ?_⟩
      congr 1; ext j; rw [mem_Ico]
      refine ⟨?_, fun hj => ⟨T.min'_le j hj, hT hj⟩⟩
      rintro ⟨hlo, hhi⟩
      induction j, hlo using Nat.le_induction with
      | base => exact T.min'_mem hne
      | succ k _ ih =>
        exact by_contra fun hk =>
          hsf hM ((hodd h1 (by omega)).1 (ih (by omega))) ((hodd h1 hhi).2 hk)
            (hEq ▸ (hE (e - 1) T' (by omega)).2 (mem_insert_self _ _)) (by omega)
  have hle : (fam e ∪ fam (e - 1)).card ≤ fm n := card_le_card fun M hM => by
    simp [fam] at hM ⊢
    rcases hM with ⟨T, -, rfl⟩ | ⟨T, -, rfl⟩ <;> exact ⟨(hE _ T (by omega)).1.1, (hE _ T (by omega)).1⟩
  have hcnt := card_union_add_card_inter (fam e) (fam (e - 1))
  rw [hcf e (by omega), hcf (e - 1) (by omega)] at hcnt
  suffices 2 ^ n < fm n ^ 4 from lt_of_pow_lt_pow_left₀ 4 (Nat.cast_nonneg _) <| by
    rw [← rpow_mul_natCast zero_le_two, show (n : ℝ) / 4 * (4 : ℕ) = n by ring, rpow_natCast]
    exact_mod_cast this
  set q := e / 2 - 3
  have := q.lt_two_pow_self
  rw [show e / 2 = q + 3 by omega, show (e - 1) / 2 = q + (2 + e % 2) by omega, pow_add, pow_add] at hcnt
  refine (Nat.pow_le_pow_right (by omega) (show n ≤ 13 + 2 * (e % 2) + 4 * q by omega)).trans_lt ?_
  rw [pow_add, mul_comm 4, pow_mul]
  refine (mul_lt_mul_of_pos_right (c := (10 + 4 * (e % 2)) ^ 4) ?_ (by positivity)).trans_le
    (mul_pow _ (2 ^ q) 4 ▸ Nat.pow_le_pow_left (m := fm n) ?_ 4) <;>
    (rcases Nat.mod_two_eq_zero_or_one e with h | h <;> rw [h] at hcnt ⊢ <;> norm_num <;> omega)
