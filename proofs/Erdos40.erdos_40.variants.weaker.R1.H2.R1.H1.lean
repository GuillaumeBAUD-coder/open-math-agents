import OMAReductions.R_Erdos40_erdos_40_variants_weaker_R1_H2_R1

/-!
# Proof of `Erdos40.erdos_40.variants.weaker.R1.H2.R1.H1`

Given `h ≥ 2` and `A : Set ℕ` with `∀ n, sumRep A n ≤ 2 * h + 1`, we construct
`B ⊆ A` with `∀ n, sumRep B n ≤ 2 * h` and `∀ n, (A ∩ Icc 1 n).ncard ≤ 2 * (B ∩ Icc 1 n).ncard`.

Method (pure left-to-right greedy + midpoint injection):
1. Build finite prefixes `B_n ⊆ Icc 1 n` recursively on `n`: include `n + 1` in `B_{n+1}`
   iff `n + 1 ∈ A` and `∀ s, sumRep (insert (n + 1) (B_n : Set ℕ)) s ≤ 2 * h`.
   Set `B = {y | y ∈ B_y}`. Then `B ⊆ A`, `B ∩ Icc 1 n = B_n`, and `∀ s, sumRep B s ≤ 2 * h`.
2. For each rejected `y ∈ (A ∩ Icc 1 n) \ B_n`, there is some `s` with
   `sumRep (insert y B_{y-1}) s = 2 * h + 1`. Since `2 * h + 1` is odd, `s = 2 * x` for
   some `x ∈ insert y B_{y-1}`, and `x ≠ y` because all elements of `insert y B_{y-1}` are
   `≤ y` (so `sumRep (insert y B_{y-1}) (2 * y) = 1 < 2 * h + 1`). Hence `x ∈ B_{y-1} ⊆ B_n`.
3. The map `y ↦ x` is injective on `(A ∩ Icc 1 n) \ B_n`: if `y₁ < y₂` mapped to the same
   `x`, then `insert y₁ B_{y₁-1}` already supplies `2 * h + 1` ordered pairs summing to
   `2 * x` with both coordinates `≤ y₁`, while `y₂` must participate in an additional
   ordered pair in `insert y₂ B_{y₂-1} ⊆ A` summing to `2 * x` with a coordinate `= y₂ > y₁`,
   forcing `sumRep A (2 * x) ≥ 2 * h + 2`, contradiction.
4. Hence `|(A ∩ Icc 1 n) \ B_n| ≤ |B_n|`, giving `|A ∩ Icc 1 n| ≤ 2 * |B_n|`.
-/

namespace OMA.P_Erdos40_erdos_40_variants_weaker_R1_H2_R1_H1

open Finset Set AdditiveCombinatorics
open scoped Classical

/-- Ordered sum-representation fiber of `S` at `m`. -/
private noncomputable def fiber (S : Set ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (_root_.Finset.HasAntidiagonal.antidiagonal m).filter (fun p ↦ p.1 ∈ S ∧ p.2 ∈ S)

private lemma card_fiber (S : Set ℕ) (m : ℕ) : (fiber S m).card = sumRep S m :=
  (sumRep_def S m).symm

private lemma mem_fiber {S : Set ℕ} {m : ℕ} {p : ℕ × ℕ} :
    p ∈ fiber S m ↔ p.1 + p.2 = m ∧ p.1 ∈ S ∧ p.2 ∈ S := by
  simp [fiber]

private lemma fiber_mono {S T : Set ℕ} (hST : S ⊆ T) (m : ℕ) : fiber S m ⊆ fiber T m := by
  intro p hp
  rw [mem_fiber] at hp ⊢
  exact ⟨hp.1, hST hp.2.1, hST hp.2.2⟩

private lemma sumRep_mono {S T : Set ℕ} (hST : S ⊆ T) (m : ℕ) : sumRep S m ≤ sumRep T m := by
  rw [← card_fiber, ← card_fiber]
  exact Finset.card_le_card (fiber_mono hST m)

/-- If `sumRep S m` is odd, then `m` is even and `m / 2 ∈ S`. -/
private lemma exists_midpoint_of_odd_sumRep {S : Set ℕ} {m : ℕ} (hodd : Odd (sumRep S m)) :
    ∃ x ∈ S, m = 2 * x := by
  by_contra hno
  push Not at hno
  let F := fiber S m
  have hnod : ∀ p ∈ F, p.1 ≠ p.2 := by
    intro p hp heq
    have hm := mem_fiber.mp hp
    exact hno p.1 hm.2.1 (by omega)
  let swap : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.1)
  let F₁ := F.filter (fun p => p.1 < p.2)
  let F₂ := F.filter (fun p => p.2 < p.1)
  have hdisj : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    omega
  have hunion : F₁ ∪ F₂ = F := by
    ext p
    simp only [F₁, F₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      have hne := hnod p hp
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hp, hlt⟩
      · exact Or.inr ⟨hp, hgt⟩
  have hcard_eq : F₂.card = F₁.card := by
    refine Finset.card_bij (fun p _ => swap p) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpF, hlt⟩ := Finset.mem_filter.mp hp
      have hm := mem_fiber.mp hpF
      refine Finset.mem_filter.mpr ⟨mem_fiber.mpr ⟨by dsimp [swap]; omega, hm.2.2, hm.2.1⟩, hlt⟩
    · intro p _ q _ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      exact Prod.ext h2 h1
    · intro p hp
      obtain ⟨hpF, hlt⟩ := Finset.mem_filter.mp hp
      have hm := mem_fiber.mp hpF
      refine ⟨swap p, Finset.mem_filter.mpr
        ⟨mem_fiber.mpr ⟨by dsimp [swap]; omega, hm.2.2, hm.2.1⟩, hlt⟩, by simp [swap]⟩
  have heven : Even (sumRep S m) := by
    rw [← card_fiber, show fiber S m = F from rfl, ← hunion,
      Finset.card_union_of_disjoint hdisj, hcard_eq]
    exact ⟨F₁.card, rfl⟩
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Greedy finite prefix `greedyPrefix h A n ⊆ Finset.Icc 1 n`. -/
private noncomputable def greedyPrefix (h : ℕ) (A : Set ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
    let prev := greedyPrefix h A n
    if (n + 1 ∈ A ∧ ∀ s, sumRep (insert (n + 1) (prev : Set ℕ)) s ≤ 2 * h) then
      insert (n + 1) prev
    else
      prev

private lemma greedyPrefix_subset_Icc (h : ℕ) (A : Set ℕ) :
    ∀ n, greedyPrefix h A n ⊆ Finset.Icc 1 n
  | 0 => by simp [greedyPrefix]
  | n + 1 => by
    dsimp only [greedyPrefix]
    split_ifs
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
      · have := Finset.mem_Icc.mp (greedyPrefix_subset_Icc h A n hx')
        exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
    · intro x hx
      have := Finset.mem_Icc.mp (greedyPrefix_subset_Icc h A n hx)
      exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩

private lemma greedyPrefix_subset_A (h : ℕ) (A : Set ℕ) :
    ∀ n, (greedyPrefix h A n : Set ℕ) ⊆ A
  | 0 => by simp [greedyPrefix]
  | n + 1 => by
    dsimp only [greedyPrefix]
    split_ifs with hcond
    · intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx'
      · exact hcond.1
      · exact greedyPrefix_subset_A h A n hx'
    · exact greedyPrefix_subset_A h A n

private lemma greedyPrefix_cap (h : ℕ) (A : Set ℕ) :
    ∀ n s, sumRep (greedyPrefix h A n : Set ℕ) s ≤ 2 * h
  | 0, s => by
    have h0 : fiber (greedyPrefix h A 0 : Set ℕ) s = ∅ := by
      ext p; simp [fiber, greedyPrefix]
    rw [← card_fiber, h0, Finset.card_empty]
    exact Nat.zero_le _
  | n + 1, s => by
    dsimp only [greedyPrefix]
    split_ifs with hcond
    · simpa only [Finset.coe_insert] using hcond.2 s
    · exact greedyPrefix_cap h A n s

private lemma greedyPrefix_mono {h : ℕ} {A : Set ℕ} :
    ∀ {m n : ℕ}, m ≤ n → greedyPrefix h A m ⊆ greedyPrefix h A n := by
  intro m n hmn
  induction hmn with
  | refl => exact Finset.Subset.rfl
  | @step k _ ih =>
    intro x hx
    have hx' := ih hx
    dsimp only [greedyPrefix]
    split_ifs
    · exact Finset.mem_insert_of_mem hx'
    · exact hx'

private lemma greedyPrefix_mem_iff_le {h : ℕ} {A : Set ℕ} {x m n : ℕ}
    (hxm : x ≤ m) (hmn : m ≤ n) :
    x ∈ greedyPrefix h A m ↔ x ∈ greedyPrefix h A n := by
  constructor
  · exact fun hx => greedyPrefix_mono hmn hx
  · intro hx
    induction hmn with
    | refl => exact hx
    | @step k hmk ih =>
      apply ih
      dsimp only [greedyPrefix] at hx
      split_ifs at hx
      · rcases Finset.mem_insert.mp hx with rfl | hx'
        · have : m ≤ k := hmk
          omega
        · exact hx'
      · exact hx

/-- The greedy subset `B ⊆ A`. -/
private def greedySet (h : ℕ) (A : Set ℕ) : Set ℕ :=
  {x : ℕ | x ∈ greedyPrefix h A x}

private lemma greedySet_inter_Icc (h : ℕ) (A : Set ℕ) (n : ℕ) :
    greedySet h A ∩ Set.Icc 1 n = (greedyPrefix h A n : Set ℕ) := by
  ext x
  simp only [Set.mem_inter_iff, greedySet, Set.mem_ofPred_eq, Set.mem_Icc, Finset.mem_coe]
  constructor
  · rintro ⟨hx, _, hxn⟩
    exact (greedyPrefix_mem_iff_le le_rfl hxn).mp hx
  · intro hx
    have hIcc := Finset.mem_Icc.mp (greedyPrefix_subset_Icc h A n hx)
    exact ⟨(greedyPrefix_mem_iff_le le_rfl hIcc.2).mpr hx, hIcc.1, hIcc.2⟩

private lemma greedySet_subset (h : ℕ) (A : Set ℕ) : greedySet h A ⊆ A := by
  intro x hx
  exact greedyPrefix_subset_A h A x hx

private lemma greedySet_cap (h : ℕ) (A : Set ℕ) (s : ℕ) :
    sumRep (greedySet h A) s ≤ 2 * h := by
  have hsub : fiber (greedySet h A) s ⊆ fiber (greedyPrefix h A s : Set ℕ) s := by
    intro p hp
    rw [mem_fiber] at hp ⊢
    have h1 : p.1 ∈ greedyPrefix h A s := by
      have hp1 := greedyPrefix_subset_Icc h A p.1 hp.2.1
      exact (greedyPrefix_mem_iff_le le_rfl (by omega : p.1 ≤ s)).mp hp.2.1
    have h2 : p.2 ∈ greedyPrefix h A s := by
      have hp2 := greedyPrefix_subset_Icc h A p.2 hp.2.2
      exact (greedyPrefix_mem_iff_le le_rfl (by omega : p.2 ≤ s)).mp hp.2.2
    exact ⟨hp.1, h1, h2⟩
  rw [← card_fiber]
  calc (fiber (greedySet h A) s).card
      ≤ (fiber (greedyPrefix h A s : Set ℕ) s).card := Finset.card_le_card hsub
    _ = sumRep (greedyPrefix h A s : Set ℕ) s := card_fiber _ _
    _ ≤ 2 * h := greedyPrefix_cap h A s s

/-- Every rejected element `y ∈ (A ∩ [1, n]) \ B_n` has a witness midpoint `x ∈ B_{y-1}`
whose `2 * x` fiber in `insert y B_{y-1}` has size `2 * h + 1`. -/
private lemma rejected_midpoint {h : ℕ} (hh : 1 ≤ h) {A : Set ℕ}
    (hcap : ∀ s, sumRep A s ≤ 2 * h + 1) {y : ℕ} (hy1 : 1 ≤ y) (hyA : y ∈ A)
    (hyB : y ∉ greedyPrefix h A y) :
    ∃ x ∈ greedyPrefix h A (y - 1),
      sumRep (insert y (greedyPrefix h A (y - 1) : Set ℕ)) (2 * x) = 2 * h + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 1 := ⟨y - 1, by omega⟩
  have hnot : ¬ (k + 1 ∈ A ∧ ∀ s, sumRep (insert (k + 1) (greedyPrefix h A k : Set ℕ)) s ≤ 2 * h) := by
    intro hcond
    apply hyB
    dsimp only [greedyPrefix]
    rw [if_pos hcond]
    exact Finset.mem_insert_self _ _
  push Not at hnot
  obtain ⟨s, hs_gt⟩ := hnot hyA
  have hsubA : insert (k + 1) (greedyPrefix h A k : Set ℕ) ⊆ A := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz'
    · exact hyA
    · exact greedyPrefix_subset_A h A k hz'
  have hs_le : sumRep (insert (k + 1) (greedyPrefix h A k : Set ℕ)) s ≤ 2 * h + 1 :=
    le_trans (sumRep_mono hsubA s) (hcap s)
  have hs_eq : sumRep (insert (k + 1) (greedyPrefix h A k : Set ℕ)) s = 2 * h + 1 := by omega
  have hodd : Odd (sumRep (insert (k + 1) (greedyPrefix h A k : Set ℕ)) s) := ⟨h, hs_eq⟩
  obtain ⟨x, hx_mem, rfl⟩ := exists_midpoint_of_odd_sumRep hodd
  have hx_ne : x ≠ k + 1 := by
    rintro rfl
    have hfib : fiber (insert (k + 1) (greedyPrefix h A k : Set ℕ)) (2 * (k + 1)) ⊆
        {(k + 1, k + 1)} := by
      intro p hp
      have hm := mem_fiber.mp hp
      have hp1 : p.1 ≤ k + 1 := by
        rcases Set.mem_insert_iff.mp hm.2.1 with h1 | h1
        · omega
        · have := (Finset.mem_Icc.mp (greedyPrefix_subset_Icc h A k h1)).2; omega
      have hp2 : p.2 ≤ k + 1 := by
        rcases Set.mem_insert_iff.mp hm.2.2 with h2 | h2
        · omega
        · have := (Finset.mem_Icc.mp (greedyPrefix_subset_Icc h A k h2)).2; omega
      exact Finset.mem_singleton.mpr (Prod.ext (by omega) (by omega))
    have hcard : sumRep (insert (k + 1) (greedyPrefix h A k : Set ℕ)) (2 * (k + 1)) ≤ 1 := by
      rw [← card_fiber]
      exact (Finset.card_le_card hfib).trans (by simp)
    omega
  have hx_prev : x ∈ greedyPrefix h A k := by
    rcases Set.mem_insert_iff.mp hx_mem with rfl | hx'
    · exact absurd rfl hx_ne
    · exact hx'
  exact ⟨x, by simpa using hx_prev, by simpa using hs_eq⟩

/-- Prefix domination: every positive prefix retains at least half its elements. -/
private lemma greedySet_prefix_dom {h : ℕ} (hh : 1 ≤ h) {A : Set ℕ}
    (hcap : ∀ s, sumRep A s ≤ 2 * h + 1) (n : ℕ) :
    (A ∩ Set.Icc 1 n).ncard ≤ 2 * (greedySet h A ∩ Set.Icc 1 n).ncard := by
  let An : Finset ℕ := (Finset.Icc 1 n).filter (fun x => x ∈ A)
  let Bn : Finset ℕ := greedyPrefix h A n
  have hAn_coe : (An : Set ℕ) = A ∩ Set.Icc 1 n := by
    ext x
    simp only [An, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff, Set.mem_Icc]
    tauto
  have hBn_coe : (Bn : Set ℕ) = greedySet h A ∩ Set.Icc 1 n :=
    (greedySet_inter_Icc h A n).symm
  rw [← hAn_coe, ← hBn_coe, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hBn_sub : Bn ⊆ An := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨greedyPrefix_subset_Icc h A n hx, greedyPrefix_subset_A h A n hx⟩
  let R : Finset ℕ := An \ Bn
  have hR_card : R.card ≤ Bn.card := by
    have hex : ∀ y ∈ R, ∃ x ∈ Bn,
        sumRep (insert y (greedyPrefix h A (y - 1) : Set ℕ)) (2 * x) = 2 * h + 1 := by
      intro y hy
      have hyAn : y ∈ An := (Finset.mem_sdiff.mp hy).1
      have hyBn : y ∉ Bn := (Finset.mem_sdiff.mp hy).2
      have hyIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hyAn).1
      have hyA : y ∈ A := (Finset.mem_filter.mp hyAn).2
      have hy_not : y ∉ greedyPrefix h A y := fun hmem =>
        hyBn ((greedyPrefix_mem_iff_le le_rfl hyIcc.2).mp hmem)
      obtain ⟨x, hx_prev, hsr⟩ := rejected_midpoint hh hcap hyIcc.1 hyA hy_not
      exact ⟨x, greedyPrefix_mono (by omega : y - 1 ≤ n) hx_prev, hsr⟩
    choose f hf_mem hf_sr using hex
    refine Finset.card_le_card_of_injOn (fun y => if hy : y ∈ R then f y hy else 0) ?_ ?_
    · intro y hy
      have hy' : y ∈ R := Finset.mem_coe.mp hy
      simp only [dif_pos hy', Finset.mem_coe]
      exact hf_mem y hy'
    · intro y₁ hy₁ y₂ hy₂ heq
      have hy₁' : y₁ ∈ R := Finset.mem_coe.mp hy₁
      have hy₂' : y₂ ∈ R := Finset.mem_coe.mp hy₂
      simp only [dif_pos hy₁', dif_pos hy₂'] at heq
      by_contra hne
      -- WLOG `y₁ < y₂`
      suffices ∀ a b (ha : a ∈ R) (hb : b ∈ R), a < b → f a ha = f b hb → False by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact this y₁ y₂ hy₁' hy₂' hlt heq
        · exact this y₂ y₁ hy₂' hy₁' hgt heq.symm
      intro a b ha hb hab hfab
      let x := f a ha
      have haA : a ∈ A := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2
      have hbA : b ∈ A := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
      let Fa := fiber (insert a (greedyPrefix h A (a - 1) : Set ℕ)) (2 * x)
      let Fb := fiber (insert b (greedyPrefix h A (b - 1) : Set ℕ)) (2 * x)
      let Fb₀ := fiber (greedyPrefix h A (b - 1) : Set ℕ) (2 * x)
      have hFa_card : Fa.card = 2 * h + 1 := by
        rw [card_fiber]; exact hf_sr a ha
      have hFb_card : Fb.card = 2 * h + 1 := by
        rw [card_fiber]; rw [show x = f b hb from hfab]; exact hf_sr b hb
      have hFb₀_le : Fb₀.card ≤ 2 * h := by
        rw [card_fiber]; exact greedyPrefix_cap h A (b - 1) (2 * x)
      have hdiff_ne : (Fb \ Fb₀).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
        have := Finset.card_le_card hempty
        omega
      obtain ⟨p, hp⟩ := hdiff_ne
      have hpFb := (Finset.mem_sdiff.mp hp).1
      have hpFb₀ := (Finset.mem_sdiff.mp hp).2
      have hpm := mem_fiber.mp hpFb
      have hp_has_b : p.1 = b ∨ p.2 = b := by
        by_contra hnb
        push Not at hnb
        have h1 : p.1 ∈ (greedyPrefix h A (b - 1) : Set ℕ) := by
          rcases Set.mem_insert_iff.mp hpm.2.1 with he | hmem
          · exact absurd he hnb.1
          · exact hmem
        have h2 : p.2 ∈ (greedyPrefix h A (b - 1) : Set ℕ) := by
          rcases Set.mem_insert_iff.mp hpm.2.2 with he | hmem
          · exact absurd he hnb.2
          · exact hmem
        exact hpFb₀ (mem_fiber.mpr ⟨hpm.1, h1, h2⟩)
      have hp_not_Fa : p ∉ Fa := by
        intro hpFa
        have hma := mem_fiber.mp hpFa
        have hp1_le : p.1 ≤ a := by
          rcases Set.mem_insert_iff.mp hma.2.1 with h1 | h1
          · omega
          · have := (Finset.mem_Icc.mp (greedyPrefix_subset_Icc h A (a - 1) h1)).2; omega
        have hp2_le : p.2 ≤ a := by
          rcases Set.mem_insert_iff.mp hma.2.2 with h2 | h2
          · omega
          · have := (Finset.mem_Icc.mp (greedyPrefix_subset_Icc h A (a - 1) h2)).2; omega
        omega
      have hsubA_a : insert a (greedyPrefix h A (a - 1) : Set ℕ) ⊆ A := by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz'
        · exact haA
        · exact greedyPrefix_subset_A h A (a - 1) hz'
      have hsubA_b : insert b (greedyPrefix h A (b - 1) : Set ℕ) ⊆ A := by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz'
        · exact hbA
        · exact greedyPrefix_subset_A h A (b - 1) hz'
      have hins_sub : insert p Fa ⊆ fiber A (2 * x) := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqFa
        · exact fiber_mono hsubA_b (2 * x) hpFb
        · exact fiber_mono hsubA_a (2 * x) hqFa
      have hge : 2 * h + 2 ≤ sumRep A (2 * x) := by
        rw [← card_fiber]
        calc 2 * h + 2 = Fa.card + 1 := by omega
          _ = (insert p Fa).card := (Finset.card_insert_of_notMem hp_not_Fa).symm
          _ ≤ (fiber A (2 * x)).card := Finset.card_le_card hins_sub
      have hle := hcap (2 * x)
      omega
  have hpart : R.card + Bn.card = An.card := by
    dsimp only [R]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBn_sub]
    exact Nat.sub_add_cancel (Finset.card_le_card hBn_sub)
  omega

end OMA.P_Erdos40_erdos_40_variants_weaker_R1_H2_R1_H1

theorem OMA.solution : OMA.R_Erdos40_erdos_40_variants_weaker_R1_H2_R1.H1 := by
  intro h hh A hcap
  refine ⟨OMA.P_Erdos40_erdos_40_variants_weaker_R1_H2_R1_H1.greedySet h A,
    OMA.P_Erdos40_erdos_40_variants_weaker_R1_H2_R1_H1.greedySet_subset h A,
    OMA.P_Erdos40_erdos_40_variants_weaker_R1_H2_R1_H1.greedySet_cap h A,
    OMA.P_Erdos40_erdos_40_variants_weaker_R1_H2_R1_H1.greedySet_prefix_dom (by omega) hcap⟩
