import FormalConjectures.ErdosProblems.«787»

/-! A descending greedy selection gives the logarithmic Klarner bound. -/

open Erdos787 Filter

lemma OMA.klarner_greedy (A : Finset ℝ) (hA : ∀ x ∈ A, 0 < x) (k : ℕ) :
    ∀ S : Finset ℝ, S ⊆ A → 2 ^ k * ((A \ S).card + 1) ≤ A.card + 1 →
      ∃ B ⊆ S, k ≤ B.card ∧
        ∀ x ∈ B, ∀ y ∈ B, x ≠ y → x + y ∉ A := by
  induction k with
  | zero =>
    intro S _ _
    exact ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp⟩
  | succ k ih =>
    intro S hSA hbudget
    have hS : S.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hp : 2 ≤ (2 : ℕ) ^ (k + 1) := by
        rw [pow_succ']
        have hpow : 0 < (2 : ℕ) ^ k := by positivity
        omega
      have hmul := (Nat.mul_le_mul_right ((A \ S).card + 1) hp).trans hbudget
      simp [he] at hmul
    let x := S.max' hS
    have hx : x ∈ S := S.max'_mem hS
    let bad := S.filter fun y => x + y ∈ A
    have hbad : bad.card ≤ (A \ S).card := by
      apply Finset.card_le_card_of_injOn (fun y => x + y)
      · intro y hy
        obtain ⟨hyS, hyA⟩ := Finset.mem_filter.mp hy
        refine Finset.mem_sdiff.mpr ⟨hyA, ?_⟩
        intro hsum
        have hyl := hA y (hSA hyS)
        have hmax : x + y ≤ x := S.le_max' _ hsum
        linarith
      · intro a _ b _ hab
        exact add_left_cancel hab
    let R := insert x bad
    have hRS : R ⊆ S := Finset.insert_subset hx (Finset.filter_subset _ _)
    let S' := S \ R
    have hS'S : S' ⊆ S := Finset.sdiff_subset
    have hstep : (A \ S').card + 1 ≤ 2 * ((A \ S).card + 1) := by
      have hR : R.card ≤ bad.card + 1 := Finset.card_insert_le _ _
      have hR' : R.card ≤ S.card := Finset.card_le_card hRS
      have hSA' : S.card ≤ A.card := Finset.card_le_card hSA
      have he : S'.card = S.card - R.card := Finset.card_sdiff_of_subset hRS
      rw [Finset.card_sdiff_of_subset (hS'S.trans hSA), Finset.card_sdiff_of_subset hSA, he]
      rw [Finset.card_sdiff_of_subset hSA] at hbad
      omega
    have hbudget' : 2 ^ k * ((A \ S').card + 1) ≤ A.card + 1 := by
      calc
        2 ^ k * ((A \ S').card + 1) ≤ 2 ^ k * (2 * ((A \ S).card + 1)) :=
          Nat.mul_le_mul_left _ hstep
        _ = 2 ^ (k + 1) * ((A \ S).card + 1) := by rw [pow_succ, mul_assoc]
        _ ≤ A.card + 1 := hbudget
    obtain ⟨B, hB, hcard, hfree⟩ := ih S' (hS'S.trans hSA) hbudget'
    have hxB : x ∉ B := by
      intro h
      exact (Finset.mem_sdiff.mp (hB h)).2 (Finset.mem_insert_self _ _)
    have hnew (y : ℝ) (hy : y ∈ B) : x + y ∉ A := by
      intro h
      obtain ⟨hyS, hyR⟩ := Finset.mem_sdiff.mp (hB hy)
      apply hyR
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyS, h⟩)
    refine ⟨insert x B, Finset.insert_subset hx (hB.trans hS'S), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hxB]
      omega
    · intro a ha b hb hne
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (hne rfl).elim
        · exact hnew b hb
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [add_comm]
          exact hnew a ha
        · exact hfree a ha b hb hne

lemma OMA.klarner_positive (A : Finset ℝ) (hA : ∀ x ∈ A, 0 < x)
    (k : ℕ) (hk : 2 ^ k ≤ A.card + 1) :
    ∃ B ⊆ A, k ≤ B.card ∧ ∀ x ∈ B, ∀ y ∈ B, x ≠ y → x + y ∉ A :=
  OMA.klarner_greedy A hA k A (by rfl) (by simpa using hk)

lemma OMA.klarner_sign_partition (A : Finset ℝ) :
    A.card ≤ (A.filter (fun a => 0 < a)).card +
      (A.filter (fun a => a < 0)).card + 1 := by
  let P := A.filter fun a => 0 < a
  let N := A.filter fun a => a < 0
  let Z := A.filter fun a => a = 0
  have heq : P ∪ N ∪ Z = A := by
    ext a
    simp only [P, N, Z, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((ha | ha) | ha) <;> exact ha.1
    · intro ha
      rcases lt_trichotomy a 0 with hn | hz | hp
      · left
        right
        exact ⟨ha, hn⟩
      · right
        exact ⟨ha, hz⟩
      · left
        left
        exact ⟨ha, hp⟩
  have hzsub : Z ⊆ ({0} : Finset ℝ) := by
    intro a ha
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp ha).2
  have hz : Z.card ≤ 1 := by simpa using Finset.card_le_card hzsub
  change A.card ≤ P.card + N.card + 1
  rw [← heq]
  have hPN := Finset.card_union_le P N
  have hPNZ := Finset.card_union_le (P ∪ N) Z
  omega

lemma OMA.klarner_log_card (n : ℕ) (hn : 2 ≤ n) : Nat.log 2 (n / 2) ≤ g ℝ n := by
  let k := Nat.log 2 (n / 2)
  have hpow : 2 ^ k ≤ n / 2 := Nat.pow_log_le_self 2 (by omega)
  apply le_g
  intro A hA
  let P := A.filter fun a => 0 < a
  let N := A.filter fun a => a < 0
  have hpartition : n ≤ P.card + N.card + 1 := by
    rw [← hA]
    exact OMA.klarner_sign_partition A
  by_cases hPN : N.card ≤ P.card
  · have hp : 2 ^ k ≤ P.card + 1 := by omega
    obtain ⟨B, hB, hc, hf⟩ := OMA.klarner_positive P
      (fun _ ha => (Finset.mem_filter.mp ha).2) k hp
    refine ⟨B, hB.trans (Finset.filter_subset _ _), hc, ?_⟩
    apply (disjoint_restrictedSumset_iff A B).mpr
    intro a ha b hb hne hs
    have hap : 0 < a := (Finset.mem_filter.mp (hB ha)).2
    have hbp : 0 < b := (Finset.mem_filter.mp (hB hb)).2
    exact hf a ha b hb hne (Finset.mem_filter.mpr ⟨hs, add_pos hap hbp⟩)
  · let neg : ℝ ↪ ℝ := ⟨fun x => -x, neg_injective⟩
    let M := N.map neg
    have hM : M.card = N.card := Finset.card_map neg
    have hm : 2 ^ k ≤ M.card + 1 := by omega
    have hMP (a : ℝ) (ha : a ∈ M) : 0 < a := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      exact neg_pos.mpr (Finset.mem_filter.mp hx).2
    obtain ⟨C, hC, hcard, hfree⟩ := OMA.klarner_positive M hMP k hm
    let B := C.map neg
    have back (a : ℝ) (ha : a ∈ C) : -a ∈ N := by
      obtain ⟨y, hy, hya⟩ := Finset.mem_map.mp (hC ha)
      change -y = a at hya
      simpa [← hya] using hy
    refine ⟨B, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      exact (Finset.mem_filter.mp (back x hx)).1
    · change k ≤ B.card
      rw [show B.card = C.card from Finset.card_map neg]
      exact hcard
    · apply (disjoint_restrictedSumset_iff A B).mpr
      intro a ha b hb hne hs
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
      have huv : u ≠ v := fun h => hne (congrArg neg h)
      change -u + -v ∈ A at hs
      have hpos := add_pos (hMP u (hC hu)) (hMP v (hC hv))
      have hmem : -(u + v) ∈ N := by
        rw [neg_add]
        exact Finset.mem_filter.mpr ⟨hs, by linarith⟩
      exact hfree u hu v hv huv (Finset.mem_map.mpr ⟨-(u + v), hmem, neg_neg _⟩)

theorem OMA.solution : type_of% @Erdos787.erdos_787.variants.klarner := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  let k := Nat.log 2 (n / 2)
  have hk : 0 < k := Nat.log_pos (by decide : 1 < 2) (by omega)
  have hcount : (k : ℝ) ≤ (g ℝ n : ℝ) := by
    exact_mod_cast OMA.klarner_log_card n (by omega)
  have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n / 2)
  change n / 2 < 2 ^ (k + 1) at hlt
  have hpow : n ≤ 2 ^ (k + 3) := by
    calc
      n ≤ 3 * (n / 2) := by omega
      _ ≤ 3 * 2 ^ (k + 1) := Nat.mul_le_mul_left _ hlt.le
      _ ≤ 4 * 2 ^ (k + 1) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by rw [show k + 3 = (k + 1) + 2 by omega, pow_add]; ring
  have hlog : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ (k + 3)) :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hmul := mul_le_mul_of_nonneg_left hlog2
    (show (0 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) by positivity)
  have hkℝ : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  push_cast at hlog hmul
  linarith only [hcount, hlog, hmul, hkℝ]