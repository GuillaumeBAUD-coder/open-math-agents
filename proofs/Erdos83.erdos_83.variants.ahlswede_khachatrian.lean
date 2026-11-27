import FormalConjectures.ErdosProblems.«83»

/-!
# Complete Intersection Theorem (Ahlswede-Khachatrian)

Formal proof of `Erdos83.erdos_83.variants.ahlswede_khachatrian`.
-/

-- Problem: Erdős Problem 83 — ahlswede khachatrian
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/83.lean:88 (declaration Erdos83.erdos_83.variants.ahlswede_khachatrian)
-- Credit: @skhakim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace AKProof

open Finset

/- ### Section 1: Basic definitions and combinatorial helpers -/

abbrev SetFam (m : ℕ) := Finset (Finset (Fin m))

def IsUniform {m : ℕ} (k : ℕ) (F : SetFam m) : Prop :=
  ∀ A ∈ F, A.card = k

def IsTInt {m : ℕ} (t : ℕ) (F : SetFam m) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, t ≤ (A ∩ B).card

def initSeg (m l : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i : Fin m => (i : ℕ) < l

def franklFam (m k t r : ℕ) : SetFam m :=
  Finset.univ.filter fun A : Finset (Fin m) =>
    A.card = k ∧ t + r ≤ (A.filter fun i : Fin m => (i : ℕ) < t + 2 * r).card

lemma mem_initSeg {m l : ℕ} {i : Fin m} : i ∈ initSeg m l ↔ (i : ℕ) < l := by
  simp [initSeg]

lemma initSeg_subset_mono {m l₁ l₂ : ℕ} (h : l₁ ≤ l₂) : initSeg m l₁ ⊆ initSeg m l₂ := by
  intro i hi
  rw [mem_initSeg] at hi ⊢
  omega

lemma initSeg_eq_univ {m l : ℕ} (h : m ≤ l) : initSeg m l = Finset.univ := by
  ext i
  simp [initSeg, lt_of_lt_of_le i.isLt h]

lemma card_initSeg {m l : ℕ} (hl : l ≤ m) : (initSeg m l).card = l := by
  have hbij : (initSeg m l).card = (Finset.range l).card := by
    refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
    · intro i hi
      rw [mem_initSeg] at hi
      exact Finset.mem_range.mpr hi
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro n hn
      rw [Finset.mem_range] at hn
      exact ⟨⟨n, lt_of_lt_of_le hn hl⟩, mem_initSeg.mpr hn, rfl⟩
  rw [hbij, Finset.card_range]

lemma filter_lt_eq_inter_initSeg {m l : ℕ} (A : Finset (Fin m)) :
    (A.filter fun i : Fin m => (i : ℕ) < l) = A ∩ initSeg m l := by
  ext i
  simp [initSeg]

lemma card_sdiff_sub {α : Type*} [DecidableEq α] {s t : Finset α} (h : t ⊆ s) :
    (s \ t).card = s.card - t.card := by
  have := Finset.card_sdiff_add_card_eq_card h
  omega

lemma card_erase_insert {α : Type*} [DecidableEq α] {A : Finset α} {i j : α}
    (hj : j ∈ A) (hi : i ∉ A) :
    ((insert i (A.erase j))).card = A.card := by
  have hi' : i ∉ A.erase j := fun h => hi (Finset.mem_of_mem_erase h)
  have h1 := Finset.card_erase_add_one hj
  simp [hi']
  omega

lemma sum_val_erase_insert {m : ℕ} {A : Finset (Fin m)} {i j : Fin m}
    (hij : i < j) (hj : j ∈ A) (hi : i ∉ A) :
    ∑ x ∈ (insert i (A.erase j)), (x : ℕ) < ∑ x ∈ A, (x : ℕ) := by
  have hi' : i ∉ A.erase j := fun h => hi (Finset.mem_of_mem_erase h)
  rw [Finset.sum_insert hi']
  have hsum : ∑ x ∈ A.erase j, (x : ℕ) + (j : ℕ) = ∑ x ∈ A, (x : ℕ) :=
    Finset.sum_erase_add A (fun x => (x : ℕ)) hj
  have hlt : (i : ℕ) < (j : ℕ) := hij
  omega

lemma choose_mul_succ (n r : ℕ) : (r + 1) * n.choose (r + 1) = (n - r) * n.choose r := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rcases r with _ | r
    · simp
    · rw [Nat.choose_succ_succ, Nat.choose_succ_succ]
      have h1 := ih (r + 1)
      have h2 := ih r
      by_cases h : r + 1 ≤ n
      · have hsub1 : n + 1 - (r + 1) = n - r := by omega
        have hsub2 : n - r = (n - (r + 1)) + 1 := by omega
        rw [hsub1]
        nlinarith
      · have hlt : n < r + 1 := by omega
        have hc1 : n.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt hlt
        have hc2 : n.choose (r + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        by_cases heq : n = r
        · subst heq
          simp [Nat.choose_eq_zero_of_lt (by omega : n < n + 1 + 1)]
        · have hc3 : n.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [hc1, hc2, hc3]

lemma succ_mul_choose_succ (n k : ℕ) :
    (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · simp
    · simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k + 1 + 1)]
  | succ n ih =>
    rcases k with _ | k
    · simp
    · rw [Nat.choose_succ_succ (n + 1) (k + 1)]
      have h1 := ih k
      have h2 := ih (k + 1)
      have h3 := Nat.choose_succ_succ n k
      simp only [Nat.succ_eq_add_one] at h3 ⊢
      calc (k + 1 + 1) * ((n + 1).choose (k + 1) + (n + 1).choose (k + 1 + 1))
          = (k + 1) * (n + 1).choose (k + 1) + (n + 1).choose (k + 1) +
              (k + 1 + 1) * (n + 1).choose (k + 1 + 1) := by ring
        _ = (n + 1) * n.choose k + (n + 1).choose (k + 1) + (n + 1) * n.choose (k + 1) := by rw [h1, h2]
        _ = (n + 1) * (n.choose k + n.choose (k + 1)) + (n + 1).choose (k + 1) := by ring
        _ = (n + 1) * (n + 1).choose (k + 1) + (n + 1).choose (k + 1) := by rw [← h3]
        _ = (n + 1 + 1) * (n + 1).choose (k + 1) := by ring

/-- Given `S ⊆ U` and `d ≤ U.card`, there exists `D ⊆ U` of size `d` minimizing `|S ∩ D|`. -/
lemma exists_subset_min_inter {α : Type*} [DecidableEq α] {U S : Finset α} (hSU : S ⊆ U)
    {d : ℕ} (hd : d ≤ U.card) :
    ∃ D ⊆ U, D.card = d ∧ (S ∩ D).card = d - min d (U.card - S.card) := by
  set a := min d (U.card - S.card)
  have ha1 : a ≤ (U \ S).card := by
    rw [card_sdiff_sub hSU]
    exact min_le_right _ _
  have ha2 : d - a ≤ S.card := by
    have hScard : S.card ≤ U.card := Finset.card_le_card hSU
    omega
  obtain ⟨D₁, hD₁sub, hD₁card⟩ := Finset.exists_subset_card_eq ha1
  obtain ⟨D₂, hD₂sub, hD₂card⟩ := Finset.exists_subset_card_eq ha2
  have hdisj : Disjoint D₁ D₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exact (Finset.mem_sdiff.mp (hD₁sub hx₁)).2 (hD₂sub hx₂)
  refine ⟨D₁ ∪ D₂, Finset.union_subset (hD₁sub.trans Finset.sdiff_subset) (hD₂sub.trans hSU), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hD₁card, hD₂card]
    have : a ≤ d := min_le_left _ _
    omega
  · have hSD : S ∩ (D₁ ∪ D₂) = D₂ := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxS, hx₁ | hx₂⟩
        · exact absurd hxS (Finset.mem_sdiff.mp (hD₁sub hx₁)).2
        · exact hx₂
      · intro hx₂
        exact ⟨hD₂sub hx₂, Or.inr hx₂⟩
    rw [hSD, hD₂card]

/- ### Section 2: Left-compression (shifting) -/

def shiftSet {m : ℕ} (i j : Fin m) (A : Finset (Fin m)) : Finset (Fin m) :=
  if j ∈ A ∧ i ∉ A then (insert i (A.erase j)) else A

def shiftFam {m : ℕ} (i j : Fin m) (F : SetFam m) : SetFam m :=
  F.image fun A => if shiftSet i j A ∈ F then A else shiftSet i j A

def IsLeftCompressed {m : ℕ} (F : SetFam m) : Prop :=
  ∀ A ∈ F, ∀ i j : Fin m, i < j → j ∈ A → i ∉ A → (insert i (A.erase j)) ∈ F

def potential {m : ℕ} (F : SetFam m) : ℕ :=
  ∑ A ∈ F, ∑ x ∈ A, (x : ℕ)

lemma shiftSet_card {m : ℕ} (i j : Fin m) (A : Finset (Fin m)) :
    (shiftSet i j A).card = A.card := by
  unfold shiftSet
  split_ifs with h
  · exact card_erase_insert h.1 h.2
  · rfl

lemma shiftFam_map_injOn {m : ℕ} (i j : Fin m) (F : SetFam m) :
    Set.InjOn (fun A => if shiftSet i j A ∈ F then A else shiftSet i j A) (F : Set (Finset (Fin m))) := by
  intro A hA B hB hEq
  simp only at hEq
  split_ifs at hEq with h1 h2 h2
  · exact hEq
  · exfalso
    exact h2 (hEq ▸ hA)
  · exfalso
    exact h1 (hEq.symm ▸ hB)
  · unfold shiftSet at hEq h1 h2
    have hA' : j ∈ A ∧ i ∉ A := by
      by_contra hc
      simp [hc] at h1
      exact h1 hA
    have hB' : j ∈ B ∧ i ∉ B := by
      by_contra hc
      simp [hc] at h2
      exact h2 hB
    simp only [hA', hB'] at hEq
    have hij : i ≠ j := fun h => hA'.2 (h ▸ hA'.1)
    ext x
    by_cases hxi : x = i
    · subst hxi; simp [hA'.2, hB'.2]
    · by_cases hxj : x = j
      · subst hxj; simp [hA'.1, hB'.1]
      · have hx := Finset.ext_iff.mp hEq x
        simp [hxi, hxj] at hx
        exact hx

lemma shiftFam_card {m : ℕ} (i j : Fin m) (F : SetFam m) :
    (shiftFam i j F).card = F.card := by
  unfold shiftFam
  exact Finset.card_image_of_injOn (shiftFam_map_injOn i j F)

lemma shiftFam_uniform {m k : ℕ} (i j : Fin m) {F : SetFam m} (hF : IsUniform k F) :
    IsUniform k (shiftFam i j F) := by
  intro B hB
  rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
  split_ifs
  · exact hF A hA
  · rw [shiftSet_card]; exact hF A hA

lemma shiftFam_mem_not_mem {m : ℕ} {i j : Fin m} {F : SetFam m} {A : Finset (Fin m)}
    (h1 : A ∈ shiftFam i j F) (h2 : A ∉ F) :
    i ∈ A ∧ j ∉ A ∧ (insert j (A.erase i)) ∈ F := by
  rcases Finset.mem_image.mp h1 with ⟨A₀, hA₀, hEq⟩
  split_ifs at hEq with hs
  · exact absurd (hEq ▸ hA₀) h2
  · have hA₀' : j ∈ A₀ ∧ i ∉ A₀ := by
      by_contra hc
      unfold shiftSet at hs
      simp [hc] at hs
      exact hs hA₀
    unfold shiftSet at hEq
    simp only [hA₀'] at hEq
    have hij : i ≠ j := fun h => hA₀'.2 (h ▸ hA₀'.1)
    have hAi : i ∈ A := by rw [← hEq]; simp
    have hAj : j ∉ A := by rw [← hEq]; simp [hij.symm]
    have hback : (insert j (A.erase i)) = A₀ := by
      rw [← hEq]
      ext x
      by_cases hxi : x = i
      · subst hxi; simp [hij, hA₀'.2]
      · by_cases hxj : x = j
        · subst hxj; simp [hA₀'.1]
        · simp [hxi, hxj]
    exact ⟨hAi, hAj, hback.symm ▸ hA₀⟩

lemma shiftFam_mem_of_both {m : ℕ} {i j : Fin m} {F : SetFam m} {A : Finset (Fin m)}
    (h1 : A ∈ shiftFam i j F) (h2 : A ∈ F) (hj : j ∈ A) (hi : i ∉ A) :
    (insert i (A.erase j)) ∈ F := by
  rcases Finset.mem_image.mp h1 with ⟨A₀, hA₀, hEq⟩
  split_ifs at hEq with hs
  · subst hEq
    unfold shiftSet at hs
    simpa [hj, hi] using hs
  · exfalso
    have hA₀' : j ∈ A₀ ∧ i ∉ A₀ := by
      by_contra hc
      unfold shiftSet at hs
      simp [hc] at hs
      exact hs hA₀
    unfold shiftSet at hEq
    simp only [hA₀'] at hEq
    exact hi (hEq ▸ Finset.mem_insert_self i _)

lemma shiftFam_tInt_mixed {m t : ℕ} {i j : Fin m} {F : SetFam m} (hF : IsTInt t F)
    {A B : Finset (Fin m)} (hA : A ∈ shiftFam i j F) (hAF : A ∈ F)
    (hB : B ∈ shiftFam i j F) (hBF : B ∉ F) :
    t ≤ (A ∩ B).card := by
  obtain ⟨hBi, hBj, hB'⟩ := shiftFam_mem_not_mem hB hBF
  set B' := (insert j (B.erase i))
  have hij : i ≠ j := fun h => hBj (h ▸ hBi)
  by_cases hAj : j ∈ A
  · by_cases hAi : i ∈ A
    · have hEq : A ∩ B' = (insert j ((A ∩ B).erase i)) := by
        ext x
        by_cases hxi : x = i
        · subst hxi; simp [B', hij]
        · by_cases hxj : x = j
          · subst hxj; simp [B', hAj]
          · simp [B', hxi, hxj]
      have hcard : (A ∩ B').card = (A ∩ B).card := by
        rw [hEq]
        exact card_erase_insert (Finset.mem_inter.mpr ⟨hAi, hBi⟩) (by simp [hBj])
      rw [← hcard]
      exact hF A hAF B' hB'
    · have hA' : (insert i (A.erase j)) ∈ F := shiftFam_mem_of_both hA hAF hAj hAi
      have hsub : ((insert i (A.erase j))) ∩ B' ⊆ A ∩ B := by
        intro x hx
        rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
        have hxi : x ≠ i := by
          intro h; subst h
          rcases Finset.mem_insert.mp hx2 with h1 | h2
          · exact hij h1
          · exact (Finset.mem_erase.mp h2).1 rfl
        have hxj : x ≠ j := by
          intro h; subst h
          rcases Finset.mem_insert.mp hx1 with h1 | h2
          · exact hij h1.symm
          · exact (Finset.mem_erase.mp h2).1 rfl
        simp only [Finset.mem_insert, Finset.mem_erase, hxi, hxj, false_or, ne_eq,
          not_false_eq_true, true_and, B'] at hx1 hx2
        exact Finset.mem_inter.mpr ⟨hx1, hx2⟩
      exact (hF _ hA' B' hB').trans (Finset.card_le_card hsub)
  · have hsub : A ∩ B' ⊆ A ∩ B := by
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxA, hxB'⟩
      rcases Finset.mem_insert.mp hxB' with rfl | hxBe
      · exact absurd hxA hAj
      · exact Finset.mem_inter.mpr ⟨hxA, Finset.mem_of_mem_erase hxBe⟩
    exact (hF A hAF B' hB').trans (Finset.card_le_card hsub)

lemma shiftFam_tInt {m t : ℕ} (i j : Fin m) {F : SetFam m} (hF : IsTInt t F) :
    IsTInt t (shiftFam i j F) := by
  intro A hA B hB
  by_cases hAF : A ∈ F <;> by_cases hBF : B ∈ F
  · exact hF A hAF B hBF
  · exact shiftFam_tInt_mixed hF hA hAF hB hBF
  · rw [Finset.inter_comm]
    exact shiftFam_tInt_mixed hF hB hBF hA hAF
  · obtain ⟨hAi, hAj, hA'⟩ := shiftFam_mem_not_mem hA hAF
    obtain ⟨hBi, hBj, hB'⟩ := shiftFam_mem_not_mem hB hBF
    have hij : i ≠ j := fun h => hAj (h ▸ hAi)
    have hEq : (insert j (A.erase i)) ∩ (insert j (B.erase i)) = (insert j ((A ∩ B).erase i)) := by
      ext x
      by_cases hxi : x = i
      · subst hxi; simp [hij]
      · by_cases hxj : x = j
        · subst hxj; simp
        · simp [hxi, hxj]
    have hcard : ((insert j (A.erase i)) ∩ (insert j (B.erase i))).card = (A ∩ B).card := by
      rw [hEq]
      exact card_erase_insert (Finset.mem_inter.mpr ⟨hAi, hBi⟩) (by simp [hAj])
    rw [← hcard]
    exact hF _ hA' _ hB'

lemma shiftFam_potential_lt {m : ℕ} {i j : Fin m} (hij : i < j) {F : SetFam m}
    {A₀ : Finset (Fin m)} (hA₀ : A₀ ∈ F) (hj : j ∈ A₀) (hi : i ∉ A₀)
    (hnot : (insert i (A₀.erase j)) ∉ F) :
    potential (shiftFam i j F) < potential F := by
  unfold potential shiftFam
  rw [Finset.sum_image (shiftFam_map_injOn i j F)]
  refine Finset.sum_lt_sum ?_ ⟨A₀, hA₀, ?_⟩
  · intro A _
    split_ifs with h
    · exact le_rfl
    · unfold shiftSet
      split_ifs with hA
      · exact le_of_lt (sum_val_erase_insert hij hA.1 hA.2)
      · exact le_rfl
  · have hs : shiftSet i j A₀ = (insert i (A₀.erase j)) := by
      unfold shiftSet; simp [hj, hi]
    rw [hs, if_neg hnot]
    exact sum_val_erase_insert hij hj hi

lemma exists_leftCompressed_eq_card {m k t : ℕ} (F : SetFam m)
    (hU : IsUniform k F) (hT : IsTInt t F) :
    ∃ G : SetFam m, IsUniform k G ∧ IsTInt t G ∧ IsLeftCompressed G ∧ G.card = F.card := by
  suffices h : ∀ p : ℕ, ∀ F : SetFam m, potential F = p → IsUniform k F → IsTInt t F →
      ∃ G : SetFam m, IsUniform k G ∧ IsTInt t G ∧ IsLeftCompressed G ∧ G.card = F.card by
    exact h (potential F) F rfl hU hT
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro F hp hU hT
    by_cases hLC : IsLeftCompressed F
    · exact ⟨F, hU, hT, hLC, rfl⟩
    · unfold IsLeftCompressed at hLC
      push Not at hLC
      obtain ⟨A, hAF, i, j, hij, hj, hi, hnot⟩ := hLC
      have hlt : potential (shiftFam i j F) < p :=
        hp ▸ shiftFam_potential_lt hij hAF hj hi hnot
      obtain ⟨G, hGU, hGT, hGLC, hGcard⟩ :=
        ih (potential (shiftFam i j F)) hlt (shiftFam i j F) rfl
          (shiftFam_uniform i j hU) (shiftFam_tInt i j hT)
      exact ⟨G, hGU, hGT, hGLC, hGcard.trans (shiftFam_card i j F)⟩

lemma exists_max_leftCompressed {m k t : ℕ} (F₀ : SetFam m)
    (hU₀ : IsUniform k F₀) (hT₀ : IsTInt t F₀) :
    ∃ F : SetFam m, IsUniform k F ∧ IsTInt t F ∧ IsLeftCompressed F ∧
      F₀.card ≤ F.card ∧ ∀ G : SetFam m, IsUniform k G → IsTInt t G → G.card ≤ F.card := by
  classical
  let P : ℕ → Prop := fun n => ∃ G : SetFam m, IsUniform k G ∧ IsTInt t G ∧ G.card = n
  let M := (Finset.univ.powersetCard k : SetFam m).card
  have hbound : ∀ G : SetFam m, IsUniform k G → G.card ≤ M := by
    intro G hG
    refine Finset.card_le_card ?_
    intro A hA
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hG A hA⟩
  have hP0 : P F₀.card := ⟨F₀, hU₀, hT₀, rfl⟩
  let best := Nat.findGreatest P M
  have hbest_P : P best := Nat.findGreatest_spec (m := F₀.card) (hbound F₀ hU₀) hP0
  obtain ⟨G₀, hGU, hGT, hGcard⟩ := hbest_P
  obtain ⟨F, hFU, hFT, hFLC, hFcard⟩ := exists_leftCompressed_eq_card G₀ hGU hGT
  refine ⟨F, hFU, hFT, hFLC, ?_, ?_⟩
  · rw [hFcard, hGcard]
    exact Nat.le_findGreatest (hbound F₀ hU₀) hP0
  · intro G hG1 hG2
    rw [hFcard, hGcard]
    exact Nat.le_findGreatest (hbound G hG1) ⟨G, hG1, hG2, rfl⟩

/- ### Section 3: Erdős–Ko–Rado theorem (for the boundary case `m = 2k - t + 1`) -/

lemma ekr_bound : ∀ (m k : ℕ), 1 ≤ k → 2 * k ≤ m →
    ∀ G : SetFam m, IsUniform k G → IsTInt 1 G → G.card ≤ (m - 1).choose (k - 1) := by
  intro m
  induction m with
  | zero =>
    intro k hk h2k
    omega
  | succ m ih =>
    intro k hk h2k G hU hT
    by_cases heq : 2 * k = m + 1
    · -- Complement pairing when m + 1 = 2k
      let comp : Finset (Fin (m + 1)) → Finset (Fin (m + 1)) := fun A => Finset.univ \ A
      have hcomp_inj : Set.InjOn comp (G : Set (Finset (Fin (m + 1)))) := by
        intro A _ B _ hAB
        have h1 := congrArg (fun S => Finset.univ \ S) hAB
        simpa [comp, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using h1
      have hdisj : Disjoint G (G.image comp) := by
        rw [Finset.disjoint_left]
        intro A hAG hAimg
        rcases Finset.mem_image.mp hAimg with ⟨B, hBG, hBA⟩
        have h1 := hT A hAG B hBG
        have hempty : A ∩ B = ∅ := by
          rw [← hBA]
          ext x
          simp [comp]
        rw [hempty] at h1
        simp at h1
      have hsub : G ∪ G.image comp ⊆ Finset.univ.powersetCard k := by
        intro A hA
        rcases Finset.mem_union.mp hA with hAG | hAimg
        · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hU A hAG⟩
        · rcases Finset.mem_image.mp hAimg with ⟨B, hBG, rfl⟩
          refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
          rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hU B hBG]
          omega
      have hcard_le : 2 * G.card ≤ (m + 1).choose k := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hcomp_inj,
            Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
        omega
      have hch : k * (m + 1).choose k = (m + 1) * m.choose (k - 1) := by
        cases k with
        | zero => omega
        | succ k' => exact succ_mul_choose_succ m k'
      have h2ch : (m + 1).choose k = 2 * m.choose (k - 1) := by
        have : k * (m + 1).choose k = k * (2 * m.choose (k - 1)) := by
          rw [hch, ← heq]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) this
      simpa using (by omega : G.card ≤ m.choose (k - 1))
    · have h2k_le : 2 * k ≤ m := by omega
      by_cases hk1 : k = 1
      · subst hk1
        have hsub : G.card ≤ 1 := by
          rw [Finset.card_le_one]
          intro A hA B hB
          have h1 := hT A hA B hB
          have hA1 := hU A hA
          have hB1 := hU B hB
          have hle1 : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
          have hAB1 : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          have hAB2 : A ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
          exact hAB1.symm.trans hAB2
        simpa using hsub
      · have hk2 : 2 ≤ k := by omega
        obtain ⟨G', hU', hT', hLC', hcard'⟩ := exists_leftCompressed_eq_card G hU hT
        rw [← hcard']
        let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
        let emb : Fin m ↪ Fin (m + 1) := Fin.castSuccEmb
        let toDown : Finset (Fin (m + 1)) → Finset (Fin m) :=
          fun A => A.preimage emb (Set.injOn_of_injective emb.injective)
        have htoDown_map : ∀ A : Finset (Fin (m + 1)), last ∉ A → (toDown A).map emb = A := by
          intro A hlast
          ext x
          simp only [toDown, Finset.mem_map, Finset.mem_preimage]
          constructor
          · rintro ⟨y, hy, rfl⟩; exact hy
          · intro hx
            have hxlt : (x : ℕ) < m := by
              have hne : x ≠ last := fun h => hlast (h ▸ hx)
              have : (x : ℕ) ≠ m := fun h => hne (Fin.ext h)
              omega
            exact ⟨⟨x.val, hxlt⟩, hx, rfl⟩
        have htoDown_card : ∀ A : Finset (Fin (m + 1)), last ∉ A → (toDown A).card = A.card := by
          intro A hlast
          have := congrArg Finset.card (htoDown_map A hlast)
          simpa [Finset.card_map] using this
        have htoDown_inter : ∀ A B : Finset (Fin (m + 1)),
            last ∉ A → last ∉ B → (toDown A ∩ toDown B).card = (A ∩ B).card := by
          intro A B hA hB
          have hmap : (toDown A ∩ toDown B).map emb = A ∩ B := by
            rw [Finset.map_inter, htoDown_map A hA, htoDown_map B hB]
          have := congrArg Finset.card hmap
          simpa [Finset.card_map] using this
        let G₀_raw := G'.filter (fun A => last ∉ A)
        let G₁_raw := G'.filter (fun A => last ∈ A)
        let G₀ : SetFam m := G₀_raw.image toDown
        let G₁ : SetFam m := G₁_raw.image (fun A => toDown (A.erase last))
        have hG₀_card : G₀.card = G₀_raw.card := by
          refine Finset.card_image_of_injOn ?_
          intro A hA B hB hEq
          have hAl := (Finset.mem_filter.mp hA).2
          have hBl := (Finset.mem_filter.mp hB).2
          rw [← htoDown_map A hAl, ← htoDown_map B hBl, hEq]
        have hG₁_card : G₁.card = G₁_raw.card := by
          refine Finset.card_image_of_injOn ?_
          intro A hA B hB hEq
          have hAl := (Finset.mem_filter.mp hA).2
          have hBl := (Finset.mem_filter.mp hB).2
          have hAe : last ∉ A.erase last := Finset.notMem_erase last A
          have hBe : last ∉ B.erase last := Finset.notMem_erase last B
          have hEq' : A.erase last = B.erase last := by
            dsimp only at hEq
            rw [← htoDown_map _ hAe, ← htoDown_map _ hBe, hEq]
          rw [← Finset.insert_erase hAl, ← Finset.insert_erase hBl, hEq']
        have hG₀_U : IsUniform k G₀ := by
          intro A hA
          rcases Finset.mem_image.mp hA with ⟨A₀, hA₀, rfl⟩
          have h1 := Finset.mem_filter.mp hA₀
          rw [htoDown_card A₀ h1.2, hU' A₀ h1.1]
        have hG₀_T : IsTInt 1 G₀ := by
          intro A hA B hB
          rcases Finset.mem_image.mp hA with ⟨A₀, hA₀, rfl⟩
          rcases Finset.mem_image.mp hB with ⟨B₀, hB₀, rfl⟩
          have h1 := Finset.mem_filter.mp hA₀
          have h2 := Finset.mem_filter.mp hB₀
          rw [htoDown_inter A₀ B₀ h1.2 h2.2]
          exact hT' A₀ h1.1 B₀ h2.1
        have hG₁_U : IsUniform (k - 1) G₁ := by
          intro A hA
          rcases Finset.mem_image.mp hA with ⟨A₀, hA₀, rfl⟩
          have h1 := Finset.mem_filter.mp hA₀
          rw [htoDown_card _ (Finset.notMem_erase last A₀), Finset.card_erase_of_mem h1.2,
              hU' A₀ h1.1]
        have hG₁_T : IsTInt 1 G₁ := by
          intro A hA B hB
          rcases Finset.mem_image.mp hA with ⟨A₀, hA₀, rfl⟩
          rcases Finset.mem_image.mp hB with ⟨B₀, hB₀, rfl⟩
          have h1 := Finset.mem_filter.mp hA₀
          have h2 := Finset.mem_filter.mp hB₀
          rw [htoDown_inter _ _ (Finset.notMem_erase last A₀) (Finset.notMem_erase last B₀)]
          by_contra hlt
          have hzero : (A₀.erase last ∩ B₀.erase last).card = 0 := by omega
          have hinter : (A₀ ∩ B₀).card = 1 := by
            have hEq : (A₀ ∩ B₀).erase last = A₀.erase last ∩ B₀.erase last := by
              ext x; simp [Finset.mem_erase, and_left_comm]
            have hmem : last ∈ A₀ ∩ B₀ := Finset.mem_inter.mpr ⟨h1.2, h2.2⟩
            have := Finset.card_erase_add_one hmem
            rw [hEq, hzero] at this
            omega
          have hunion : (A₀ ∪ B₀).card < m + 1 := by
            have := Finset.card_inter_add_card_union A₀ B₀
            rw [hU' A₀ h1.1, hU' B₀ h2.1, hinter] at this
            omega
          have hne : (Finset.univ \ (A₀ ∪ B₀)).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hempty
            have hsub : (Finset.univ : Finset (Fin (m + 1))) ⊆ A₀ ∪ B₀ :=
              Finset.sdiff_eq_empty_iff_subset.mp hempty
            have := Finset.card_le_card hsub
            rw [Finset.card_univ, Fintype.card_fin] at this
            omega
          obtain ⟨x, hx⟩ := hne
          have hxAB : x ∉ A₀ ∪ B₀ := (Finset.mem_sdiff.mp hx).2
          have hxA : x ∉ A₀ := fun h => hxAB (Finset.mem_union_left _ h)
          have hxB : x ∉ B₀ := fun h => hxAB (Finset.mem_union_right _ h)
          have hxlt : x < last := by
            have hne : x ≠ last := fun h => hxA (h ▸ h1.2)
            have : (x : ℕ) ≠ m := fun h => hne (Fin.ext h)
            exact Fin.mk_lt_mk.mpr (by omega)
          have hA' : (insert x (A₀.erase last)) ∈ G' := hLC' A₀ h1.1 x last hxlt h1.2 hxA
          have hdisj' : ((insert x (A₀.erase last))) ∩ B₀ = ∅ := by
            ext y
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, Finset.notMem_empty,
              iff_false, not_and]
            rintro (rfl | ⟨hyl, hyA⟩) hyB
            · exact hxB hyB
            · have hyin : y ∈ A₀.erase last ∩ B₀.erase last :=
                Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hyl, hyA⟩,
                  Finset.mem_erase.mpr ⟨hyl, hyB⟩⟩
              have hpos := Finset.card_pos.mpr ⟨y, hyin⟩
              omega
          have := hT' _ hA' B₀ h2.1
          rw [hdisj'] at this
          simp at this
        have hsplit : G'.card = G₀_raw.card + G₁_raw.card := by
          have := Finset.card_filter_add_card_filter_not (s := G') (p := fun A => last ∉ A)
          simpa [G₀_raw, G₁_raw] using this.symm
        have hb0 := ih k hk h2k_le G₀ hG₀_U hG₀_T
        have hb1 := ih (k - 1) (by omega) (by omega) G₁ hG₁_U hG₁_T
        have hpas : (m - 1).choose (k - 1) + (m - 1).choose (k - 2) = m.choose (k - 1) := by
          cases m with
          | zero => omega
          | succ m' =>
            cases k with
            | zero => omega
            | succ k' =>
              cases k' with
              | zero => omega
              | succ k'' =>
                rw [show m' + 1 - 1 = m' by omega, show k'' + 1 + 1 - 1 = k'' + 1 by omega,
                    show k'' + 1 + 1 - 2 = k'' by omega, add_comm]
                exact (Nat.choose_succ_succ m' k'').symm
        have hsubk : k - 1 - 1 = k - 2 := by omega
        rw [hsubk] at hb1
        simp only [Nat.add_sub_cancel]
        omega

/- ### Section 4: Generating sets and extent `l` (Part 1 for `m ≥ 2k - t + 2`) -/

def extFam (m k l : ℕ) (H : SetFam m) : SetFam m :=
  (Finset.univ.powersetCard k).filter fun A => A ∩ initSeg m l ∈ H

lemma extFam_uniform {m k l : ℕ} {H : SetFam m} : IsUniform k (extFam m k l H) := by
  intro A hA
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2

lemma extFam_tInt {m k l t : ℕ} {H : SetFam m} (hH : IsTInt t H) :
    IsTInt t (extFam m k l H) := by
  intro A hA B hB
  have h1 := (Finset.mem_filter.mp hA).2
  have h2 := (Finset.mem_filter.mp hB).2
  have hsub : (A ∩ initSeg m l) ∩ (B ∩ initSeg m l) ⊆ A ∩ B := by
    intro x hx
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨hx.1.1, hx.2.1⟩
  exact (hH _ h1 _ h2).trans (Finset.card_le_card hsub)

lemma card_extFam {m k l : ℕ} (hl : l ≤ m) {H : SetFam m}
    (hHsub : ∀ B ∈ H, B ⊆ initSeg m l ∧ B.card ≤ k) :
    (extFam m k l H).card = ∑ B ∈ H, (m - l).choose (k - B.card) := by
  have hmap : ∀ A ∈ extFam m k l H, A ∩ initSeg m l ∈ H :=
    fun A hA => (Finset.mem_filter.mp hA).2
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBl, hBk⟩ := hHsub B hB
  have hbij : ((extFam m k l H).filter fun A => A ∩ initSeg m l = B).card =
      ((Finset.univ \ initSeg m l).powersetCard (k - B.card)).card := by
    refine Finset.card_bij (fun A _ => A \ initSeg m l) ?_ ?_ ?_
    · intro A hA
      have hA1 := (Finset.mem_filter.mp hA).1
      have hA2 := (Finset.mem_filter.mp hA).2
      have hAk : A.card = k := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA1).1).2
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
      · have hsplit := Finset.card_sdiff_add_card_inter A (initSeg m l)
        rw [hA2, hAk] at hsplit
        omega
    · intro A₁ hA₁ A₂ hA₂ hEq
      have h1 := (Finset.mem_filter.mp hA₁).2
      have h2 := (Finset.mem_filter.mp hA₂).2
      rw [← Finset.sdiff_union_inter A₁ (initSeg m l), ← Finset.sdiff_union_inter A₂ (initSeg m l),
          h1, h2, hEq]
    · intro C hC
      obtain ⟨hCsub, hCcard⟩ := Finset.mem_powersetCard.mp hC
      have hdisj : Disjoint B C := by
        rw [Finset.disjoint_left]
        intro x hxB hxC
        exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (hBl hxB)
      have hBC_inter : (B ∪ C) ∩ initSeg m l = B := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxB | hxC, hxl⟩
          · exact hxB
          · exact absurd hxl (Finset.mem_sdiff.mp (hCsub hxC)).2
        · intro hxB
          exact ⟨Or.inl hxB, hBl hxB⟩
      have hBC_sdiff : (B ∪ C) \ initSeg m l = C := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxB | hxC, hxl⟩
          · exact absurd (hBl hxB) hxl
          · exact hxC
        · intro hxC
          exact ⟨Or.inr hxC, (Finset.mem_sdiff.mp (hCsub hxC)).2⟩
      have hBC_card : (B ∪ C).card = k := by
        rw [Finset.card_union_of_disjoint hdisj, hCcard]
        omega
      refine ⟨B ∪ C, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hBC_card⟩, hBC_inter.symm ▸ hB⟩,
        hBC_inter⟩, hBC_sdiff⟩
  rw [hbij, Finset.card_powersetCard, card_sdiff_sub (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, card_initSeg hl]

/-- The family of subsets `B ⊆ initSeg m l` of size `≤ k` whose entire `k`-upset lies in `F`. -/
def genUpper {m : ℕ} (F : SetFam m) (k l : ℕ) : SetFam m :=
  (initSeg m l).powerset.filter fun B =>
    B.card ≤ k ∧ ∀ A : Finset (Fin m), A.card = k → B ⊆ A → A ∈ F

def minElems {m : ℕ} (H : SetFam m) : SetFam m :=
  H.filter fun E => ∀ E' ∈ H, E' ⊆ E → E' = E

lemma exists_minElem_subset {m : ℕ} {H : SetFam m} {B : Finset (Fin m)} (hB : B ∈ H) :
    ∃ E ∈ minElems H, E ⊆ B := by
  suffices h : ∀ c : ℕ, ∀ B ∈ H, B.card = c → ∃ E ∈ minElems H, E ⊆ B from h B.card B hB rfl
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro B hB hc
    by_cases hmin : ∀ E' ∈ H, E' ⊆ B → E' = B
    · exact ⟨B, Finset.mem_filter.mpr ⟨hB, hmin⟩, Finset.Subset.refl B⟩
    · push Not at hmin
      obtain ⟨E', hE'H, hE'sub, hE'ne⟩ := hmin
      have hlt : E'.card < c := hc ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hE'sub, hE'ne⟩)
      obtain ⟨E, hEmin, hEE'⟩ := ih E'.card hlt E' hE'H rfl
      exact ⟨E, hEmin, hEE'.trans hE'sub⟩

/-- Lemma B: When `2k - t < m`, `genUpper F k l` is `t`-intersecting. -/
lemma genUpper_tInt {m k t l : ℕ} (hkm : k ≤ m) (h2k : 2 * k - t < m)
    {F : SetFam m} (hT : IsTInt t F) :
    IsTInt t (genUpper F k l) := by
  intro E₁ hE₁ E₂ hE₂
  obtain ⟨_, hE₁k, hE₁U⟩ := Finset.mem_filter.mp hE₁
  obtain ⟨_, hE₂k, hE₂U⟩ := Finset.mem_filter.mp hE₂
  by_contra hlt
  have hlt' : (E₁ ∩ E₂).card < t := by omega
  set U := (Finset.univ : Finset (Fin m)) \ (E₁ ∪ E₂)
  have hUcard : U.card = m - (E₁ ∪ E₂).card := by
    rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hEU := Finset.card_inter_add_card_union E₁ E₂
  by_cases hcase : 2 * k ≤ m + (E₁ ∩ E₂).card
  · -- Extend E₁ and E₂ disjointly inside U
    have hneed : (k - E₁.card) + (k - E₂.card) ≤ U.card := by omega
    obtain ⟨C₁, hC₁sub, hC₁card⟩ := Finset.exists_subset_card_eq (by omega : k - E₁.card ≤ U.card)
    have hU2 : k - E₂.card ≤ (U \ C₁).card := by
      rw [card_sdiff_sub hC₁sub, hC₁card]; omega
    obtain ⟨C₂, hC₂sub, hC₂card⟩ := Finset.exists_subset_card_eq hU2
    have hC₁E₁ : Disjoint E₁ C₁ := by
      rw [Finset.disjoint_left]
      intro x hx1 hxC
      exact (Finset.mem_sdiff.mp (hC₁sub hxC)).2 (Finset.mem_union_left _ hx1)
    have hC₂E₂ : Disjoint E₂ C₂ := by
      rw [Finset.disjoint_left]
      intro x hx2 hxC
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hC₂sub hxC)).1).2 (Finset.mem_union_right _ hx2)
    have hA₁ : E₁ ∪ C₁ ∈ F := hE₁U (E₁ ∪ C₁) (by rw [Finset.card_union_of_disjoint hC₁E₁, hC₁card]; omega)
      Finset.subset_union_left
    have hA₂ : E₂ ∪ C₂ ∈ F := hE₂U (E₂ ∪ C₂) (by rw [Finset.card_union_of_disjoint hC₂E₂, hC₂card]; omega)
      Finset.subset_union_left
    have hinter : (E₁ ∪ C₁) ∩ (E₂ ∪ C₂) ⊆ E₁ ∩ E₂ := by
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
      rcases Finset.mem_union.mp hx1 with hx1 | hx1 <;> rcases Finset.mem_union.mp hx2 with hx2 | hx2
      · exact Finset.mem_inter.mpr ⟨hx1, hx2⟩
      · exact absurd (Finset.mem_union_left _ hx1) (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hC₂sub hx2)).1).2
      · exact absurd (Finset.mem_union_right _ hx2) (Finset.mem_sdiff.mp (hC₁sub hx1)).2
      · exact absurd hx1 (Finset.mem_sdiff.mp (hC₂sub hx2)).2
    have := (hT _ hA₁ _ hA₂).trans (Finset.card_le_card hinter)
    omega
  · -- Choose disjoint complements D₁ ⊆ univ \ E₁ and D₂ ⊆ univ \ E₂ of size m - k
    set d₁ := min (E₂ \ E₁).card (m - k)
    set d₂ := min (E₁ \ E₂).card (m - k)
    set r₁ := (m - k) - d₁
    set r₂ := (m - k) - d₂
    have hr12 : r₁ + r₂ ≤ U.card := by
      have hs1 : (E₂ \ E₁).card = E₂.card - (E₁ ∩ E₂).card := by
        have := Finset.card_sdiff_add_card_inter E₂ E₁
        rw [Finset.inter_comm] at this; omega
      have hs2 : (E₁ \ E₂).card = E₁.card - (E₁ ∩ E₂).card := by
        have := Finset.card_sdiff_add_card_inter E₁ E₂; omega
      omega
    obtain ⟨P₁, hP₁sub, hP₁card⟩ := Finset.exists_subset_card_eq (min_le_left (E₂ \ E₁).card (m - k))
    obtain ⟨P₂, hP₂sub, hP₂card⟩ := Finset.exists_subset_card_eq (min_le_left (E₁ \ E₂).card (m - k))
    obtain ⟨Q₁, hQ₁sub, hQ₁card⟩ := Finset.exists_subset_card_eq (by omega : r₁ ≤ U.card)
    have hU2 : r₂ ≤ (U \ Q₁).card := by rw [card_sdiff_sub hQ₁sub, hQ₁card]; omega
    obtain ⟨Q₂, hQ₂sub, hQ₂card⟩ := Finset.exists_subset_card_eq hU2
    set D₁ := P₁ ∪ Q₁
    set D₂ := P₂ ∪ Q₂
    have hP₁Q₁ : Disjoint P₁ Q₁ := by
      rw [Finset.disjoint_left]; intro x hxP hxQ
      exact (Finset.mem_sdiff.mp (hQ₁sub hxQ)).2 (Finset.mem_union_right _ (Finset.mem_sdiff.mp (hP₁sub hxP)).1)
    have hP₂Q₂ : Disjoint P₂ Q₂ := by
      rw [Finset.disjoint_left]; intro x hxP hxQ
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hQ₂sub hxQ)).1).2
        (Finset.mem_union_left _ (Finset.mem_sdiff.mp (hP₂sub hxP)).1)
    have hD₁card : D₁.card = m - k := by
      rw [Finset.card_union_of_disjoint hP₁Q₁, hP₁card, hQ₁card]; have := min_le_right (E₂ \ E₁).card (m - k); omega
    have hD₂card : D₂.card = m - k := by
      rw [Finset.card_union_of_disjoint hP₂Q₂, hP₂card, hQ₂card]; have := min_le_right (E₁ \ E₂).card (m - k); omega
    have hD₁E₁ : Disjoint D₁ E₁ := by
      rw [Finset.disjoint_left]; intro x hxD hx1
      rcases Finset.mem_union.mp hxD with hxP | hxQ
      · exact (Finset.mem_sdiff.mp (hP₁sub hxP)).2 hx1
      · exact (Finset.mem_sdiff.mp (hQ₁sub hxQ)).2 (Finset.mem_union_left _ hx1)
    have hD₂E₂ : Disjoint D₂ E₂ := by
      rw [Finset.disjoint_left]; intro x hxD hx2
      rcases Finset.mem_union.mp hxD with hxP | hxQ
      · exact (Finset.mem_sdiff.mp (hP₂sub hxP)).2 hx2
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hQ₂sub hxQ)).1).2 (Finset.mem_union_right _ hx2)
    have hD₁D₂ : Disjoint D₁ D₂ := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      rcases Finset.mem_union.mp hx1 with hxP1 | hxQ1 <;> rcases Finset.mem_union.mp hx2 with hxP2 | hxQ2
      · exact (Finset.mem_sdiff.mp (hP₁sub hxP1)).2 (Finset.mem_sdiff.mp (hP₂sub hxP2)).1
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hQ₂sub hxQ2)).1).2
          (Finset.mem_union_right _ (Finset.mem_sdiff.mp (hP₁sub hxP1)).1)
      · exact (Finset.mem_sdiff.mp (hQ₁sub hxQ1)).2
          (Finset.mem_union_left _ (Finset.mem_sdiff.mp (hP₂sub hxP2)).1)
      · exact (Finset.mem_sdiff.mp (hQ₂sub hxQ2)).2 hxQ1
    set A₁ := Finset.univ \ D₁
    set A₂ := Finset.univ \ D₂
    have hA₁card : A₁.card = k := by
      rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hD₁card]; omega
    have hA₂card : A₂.card = k := by
      rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hD₂card]; omega
    have hE₁A₁ : E₁ ⊆ A₁ := fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.disjoint_right.mp hD₁E₁ hx⟩
    have hE₂A₂ : E₂ ⊆ A₂ := fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.disjoint_right.mp hD₂E₂ hx⟩
    have hA₁F : A₁ ∈ F := hE₁U A₁ hA₁card hE₁A₁
    have hA₂F : A₂ ∈ F := hE₂U A₂ hA₂card hE₂A₂
    have hunion : A₁ ∪ A₂ = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true, A₁, A₂]
      by_cases hx1 : x ∈ D₁
      · exact Or.inr (Finset.disjoint_left.mp hD₁D₂ hx1)
      · exact Or.inl hx1
    have hcard_inter : (A₁ ∩ A₂).card = 2 * k - m := by
      have := Finset.card_inter_add_card_union A₁ A₂
      rw [hA₁card, hA₂card, hunion, Finset.card_univ, Fintype.card_fin] at this
      omega
    have := hT A₁ hA₁F A₂ hA₂F
    omega

lemma genUpper_leftCompressed {m k l : ℕ} {F : SetFam m} (hLC : IsLeftCompressed F) :
    IsLeftCompressed (genUpper F k l) := by
  intro E hE i j hij hj hi
  obtain ⟨hEl, hEk, hEU⟩ := Finset.mem_filter.mp hE
  rw [Finset.mem_powerset] at hEl
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxe
    · rw [mem_initSeg]
      have hjl : (j : ℕ) < l := mem_initSeg.mp (hEl hj)
      have : (x : ℕ) < (j : ℕ) := hij
      omega
    · exact hEl (Finset.mem_of_mem_erase hxe)
  · rw [card_erase_insert hj hi]; exact hEk
  · intro A hAk hsub
    by_cases hjA : j ∈ A
    · refine hEU A hAk ?_
      intro x hx
      by_cases hxj : x = j
      · exact hxj ▸ hjA
      · exact hsub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxj, hx⟩))
    · have hiA : i ∈ A := hsub (Finset.mem_insert_self i _)
      set A' := (insert j (A.erase i))
      have hA'k : A'.card = k := by rw [card_erase_insert hiA hjA, hAk]
      have hEA' : E ⊆ A' := by
        intro x hx
        by_cases hxj : x = j
        · exact hxj ▸ Finset.mem_insert_self j _
        · have hxi : x ≠ i := fun h => hi (h ▸ hx)
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi,
            hsub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxj, hx⟩))⟩)
      have hA'F : A' ∈ F := hEU A' hA'k hEA'
      have hback : (insert i (A'.erase j)) = A := by
        ext x
        have hne : i ≠ j := ne_of_lt hij
        by_cases hxi : x = i
        · subst hxi; simp [A', hiA]
        · by_cases hxj : x = j
          · subst hxj; simp [A', hne.symm, hjA]
          · simp [A', hxi, hxj]
      have hjA' : j ∈ A' := Finset.mem_insert_self j _
      have hiA' : i ∉ A' := by simp [A', ne_of_lt hij]
      exact hback ▸ hLC A' hA'F i j hij hjA' hiA'

set_option maxHeartbeats 800000 in
/-- Structure theorem for the extent `l` of a maximum left-compressed `t`-intersecting family
when `m ≥ 2k - t + 2`. -/
lemma extent_structure {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hm : 2 * k - t + 2 ≤ m)
    {F : SetFam m} (hU : IsUniform k F) (hT : IsTInt t F) (hLC : IsLeftCompressed F)
    (hmax : ∀ G : SetFam m, IsUniform k G → IsTInt t G → G.card ≤ F.card) :
    ∃ (l r : ℕ), l = t + 2 * r ∧ t + r ≤ k ∧ l + 2 ≤ m ∧
      F = extFam m k l (genUpper F k l) ∧
      (∀ E ∈ minElems (genUpper F k l),
        ∀ x ∈ E, (x : ℕ) = l - 1 → E.card = t + r) ∧
      (∃ E ∈ minElems (genUpper F k l), ∃ x ∈ E, (x : ℕ) = l - 1) ∧
      (1 ≤ r → r * (m + 2 * t - 2 * k - 2) ≤ (t - 1) * (k - t + 1)) := by
  classical
  have hkm : k ≤ m := by omega
  have h2k : 2 * k - t < m := by omega
  -- F is nonempty because franklFam m k t 0 is nonempty
  have hFne : F.Nonempty := by
    have hF0_sub : initSeg m t ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
    have hcard_sdiff : k - t ≤ (Finset.univ \ initSeg m t).card := by
      rw [card_sdiff_sub hF0_sub, Finset.card_univ, Fintype.card_fin, card_initSeg (by omega)]
      omega
    obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hcard_sdiff
    have hdisj : Disjoint (initSeg m t) C := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (hCsub hx2)).2 hx1
    set A₀ := initSeg m t ∪ C
    have hA₀k : A₀.card = k := by
      rw [Finset.card_union_of_disjoint hdisj, card_initSeg (by omega), hCcard]; omega
    have h1 : ({A₀} : SetFam m).card ≤ F.card :=
      hmax {A₀} (by intro A hA; rw [Finset.mem_singleton.mp hA]; exact hA₀k)
        (by intro A hA B hB; rw [Finset.mem_singleton.mp hA, Finset.mem_singleton.mp hB, Finset.inter_self, hA₀k]; omega)
    rw [Finset.card_singleton] at h1
    exact Finset.card_pos.mp (by omega)
  -- Existence of l ≤ m such that F = extFam m k l (genUpper F k l)
  let P : ℕ → Prop := fun l => l ≤ m ∧ F = extFam m k l (genUpper F k l)
  have hPm : P m := by
    refine ⟨le_rfl, ?_⟩
    ext A
    simp only [extFam, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      initSeg_eq_univ le_rfl, Finset.inter_univ, genUpper, Finset.mem_powerset]
    constructor
    · intro hAF
      refine ⟨hU A hAF, hU A hAF |>.le, ?_⟩
      intro B hBk hAB
      have hEq : A = B := Finset.eq_of_subset_of_card_le hAB (by rw [hU A hAF, hBk])
      exact hEq ▸ hAF
    · rintro ⟨hAk, _, hU'⟩
      exact hU' A hAk (Finset.Subset.refl A)
  have hexP : ∃ l, P l := ⟨m, hPm⟩
  let l := Nat.find hexP
  have hPl : P l := Nat.find_spec hexP
  have hl_le : l ≤ m := hPl.1
  have hF_ext : F = extFam m k l (genUpper F k l) := hPl.2
  have hl_min : ∀ l' < l, ¬ P l' := fun l' hlt => Nat.find_min hexP hlt
  set H := genUpper F k l
  have hHsub : ∀ B ∈ H, B ⊆ initSeg m l ∧ B.card ≤ k := by
    intro B hB
    have := Finset.mem_filter.mp hB
    exact ⟨Finset.mem_powerset.mp this.1, this.2.1⟩
  have hHT : IsTInt t H := genUpper_tInt hkm h2k hT
  have hHLC : IsLeftCompressed H := genUpper_leftCompressed hLC
  have hHup : ∀ B ∈ H, ∀ B' : Finset (Fin m), B ⊆ B' → B' ⊆ initSeg m l → B'.card ≤ k → B' ∈ H := by
    intro B hB B' hBB' hB'l hB'k
    have hBU := (Finset.mem_filter.mp hB).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hB'l, hB'k,
      fun A hAk hB'A => hBU A hAk (hBB'.trans hB'A)⟩
  -- H is nonempty, hence l ≥ t ≥ 2
  have hHne : H.Nonempty := by
    obtain ⟨A, hAF⟩ := hFne
    rw [hF_ext] at hAF
    exact ⟨A ∩ initSeg m l, (Finset.mem_filter.mp hAF).2⟩
  have hl_ge_t : t ≤ l := by
    obtain ⟨B, hBH⟩ := hHne
    have h1 := hHT B hBH B hBH
    rw [Finset.inter_self] at h1
    have h2 := Finset.card_le_card (hHsub B hBH).1
    rw [card_initSeg hl_le] at h2
    omega
  set el : Fin m := ⟨l - 1, by omega⟩
  have hel_mem : el ∈ initSeg m l := by rw [mem_initSeg]; simp [el]; omega
  set g := minElems H
  set gStar := g.filter (fun E => el ∈ E)
  -- gStar is nonempty by minimality of l
  have hgStar_ne : gStar.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hl_min (l - 1) (by omega)
    refine ⟨by omega, ?_⟩
    ext A
    simp only [extFam, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro hAF
      have hAk := hU A hAF
      have hAF' : A ∩ initSeg m l ∈ H := by
        rw [hF_ext] at hAF
        exact (Finset.mem_filter.mp hAF).2
      obtain ⟨E, hEg, hEA⟩ := exists_minElem_subset hAF'
      have helE : el ∉ E := by
        intro hel
        have : E ∈ gStar := Finset.mem_filter.mpr ⟨hEg, hel⟩
        rw [hempty] at this
        exact Finset.notMem_empty E this
      have hEl' : E ⊆ initSeg m (l - 1) := by
        intro x hx
        have hxl : (x : ℕ) < l := mem_initSeg.mp ((hHsub E (Finset.mem_filter.mp hEg).1).1 hx)
        have hne : (x : ℕ) ≠ l - 1 := fun h => helE (by convert hx; exact Fin.ext h.symm)
        rw [mem_initSeg]; omega
      have hE_in : E ⊆ A ∩ initSeg m (l - 1) :=
        Finset.subset_inter (hEA.trans Finset.inter_subset_left) hEl'
      refine ⟨hAk, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        (Finset.card_le_card Finset.inter_subset_left).trans_eq hAk, ?_⟩⟩
      intro B hBk hsub
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hEg).1).2.2 B hBk (hE_in.trans hsub)
    · rintro ⟨hAk, hmem⟩
      exact (Finset.mem_filter.mp hmem).2.2 A hAk Finset.inter_subset_left
  -- Feasibility: for every E ∈ gStar, k - E.card + 1 ≤ m - l
  have hgStar_feas : ∀ E ∈ gStar, k - E.card + 1 ≤ m - l := by
    intro E hE
    have hEg := (Finset.mem_filter.mp hE).1
    have helE := (Finset.mem_filter.mp hE).2
    have hEH := (Finset.mem_filter.mp hEg).1
    have hEmin := (Finset.mem_filter.mp hEg).2
    have hEsub := (hHsub E hEH).1
    have hEk := (hHsub E hEH).2
    by_contra hlt
    -- Show E.erase el ∈ H, contradicting minimality
    have hEeH : E.erase el ∈ H := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((Finset.erase_subset el E).trans hEsub),
        by have := Finset.card_erase_of_mem helE; omega, ?_⟩
      · intro A hAk hsub
        have hsplit := Finset.card_sdiff_add_card_inter A (initSeg m l)
        have hsdiff_le : (A \ initSeg m l).card ≤ m - l := by
          have h1 : A \ initSeg m l ⊆ Finset.univ \ initSeg m l :=
            Finset.sdiff_subset_sdiff (Finset.subset_univ A) (Finset.Subset.refl _)
          have h2 := Finset.card_le_card h1
          rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
              card_initSeg hl_le] at h2
          exact h2
        have hsub' : E.erase el ⊆ A ∩ initSeg m l :=
          Finset.subset_inter hsub ((Finset.erase_subset el E).trans hEsub)
        have hcard_lt : (E.erase el).card < (A ∩ initSeg m l).card := by
          have hEpos : 1 ≤ E.card := Finset.card_pos.mpr ⟨el, helE⟩
          rw [hAk] at hsplit
          rw [Finset.card_erase_of_mem helE]
          omega
        obtain ⟨x, hxAl, hxEe⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
        have hxA : x ∈ A := (Finset.mem_inter.mp hxAl).1
        have hxl : x ∈ initSeg m l := (Finset.mem_inter.mp hxAl).2
        by_cases hxel : x = el
        · have hEA : E ⊆ A := by
            intro y hy
            by_cases hyel : y = el
            · exact hyel ▸ hxel ▸ hxA
            · exact hsub (Finset.mem_erase.mpr ⟨hyel, hy⟩)
          exact (Finset.mem_filter.mp hEH).2.2 A hAk hEA
        · have hxlt : x < el := by
            have h1 : (x : ℕ) < l := mem_initSeg.mp hxl
            have h2 : (x : ℕ) ≠ l - 1 := fun h => hxel (Fin.ext h)
            exact Fin.mk_lt_mk.mpr (by omega)
          have hxE : x ∉ E := fun hx => hxEe (Finset.mem_erase.mpr ⟨hxel, hx⟩)
          have hshiftH : (insert x (E.erase el)) ∈ H := hHLC E hEH x el hxlt helE hxE
          have hshiftA : (insert x (E.erase el)) ⊆ A := Finset.insert_subset_iff.mpr ⟨hxA, hsub⟩
          exact (Finset.mem_filter.mp hshiftH).2.2 A hAk hshiftA
    have hEq := hEmin (E.erase el) hEeH (Finset.erase_subset el E)
    exact Finset.notMem_erase el E (hEq.symm ▸ helE)
  -- Lemma 1.1: E₁, E₂ ∈ gStar with |E₁ ∩ E₂| = t implies E₁ ∪ E₂ = initSeg m l and |E₁| + |E₂| = l + t
  have hgStar_union : ∀ E₁ ∈ gStar, ∀ E₂ ∈ gStar, (E₁ ∩ E₂).card = t →
      E₁ ∪ E₂ = initSeg m l ∧ E₁.card + E₂.card = l + t := by
    intro E₁ hE₁ E₂ hE₂ hint
    have hE₁H := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₁).1).1
    have hE₂H := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₂).1).1
    have hel₁ := (Finset.mem_filter.mp hE₁).2
    have hel₂ := (Finset.mem_filter.mp hE₂).2
    have hunion : E₁ ∪ E₂ = initSeg m l := by
      refine Finset.Subset.antisymm (Finset.union_subset (hHsub E₁ hE₁H).1 (hHsub E₂ hE₂H).1) ?_
      intro x hxl
      by_contra hnot
      have hx1 : x ∉ E₁ := fun h => hnot (Finset.mem_union_left _ h)
      have hx2 : x ∉ E₂ := fun h => hnot (Finset.mem_union_right _ h)
      have hxne : x ≠ el := fun h => hx1 (h ▸ hel₁)
      have hxlt : x < el := by
        have h1 : (x : ℕ) < l := mem_initSeg.mp hxl
        have h2 : (x : ℕ) ≠ l - 1 := fun h => hxne (Fin.ext h)
        exact Fin.mk_lt_mk.mpr (by omega)
      have hE₁' : (insert x (E₁.erase el)) ∈ H := hHLC E₁ hE₁H x el hxlt hel₁ hx1
      have hinter' : ((insert x (E₁.erase el))) ∩ E₂ = (E₁ ∩ E₂).erase el := by
        ext y
        by_cases hyx : y = x
        · subst hyx; simp [hx2]
        · by_cases hyel : y = el
          · subst hyel; simp [hxne.symm]
          · simp [hyx, hyel]
      have hge := hHT _ hE₁' E₂ hE₂H
      rw [hinter', Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hel₁, hel₂⟩), hint] at hge
      omega
    have hcard := Finset.card_inter_add_card_union E₁ E₂
    rw [hint, hunion, card_initSeg hl_le] at hcard
    exact ⟨hunion, by omega⟩
  -- Lemma C: exact conflict characterization
  have hgStar_conflict : ∀ E ∈ gStar, ∀ B ∈ H, ((E.erase el) ∩ B).card < t →
      B ∈ gStar ∧ (E ∩ B).card = t ∧ E.card + B.card = l + t := by
    intro E hE B hBH hlt
    have hEH := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
    have helE := (Finset.mem_filter.mp hE).2
    obtain ⟨E₀, hE₀g, hE₀B⟩ := exists_minElem_subset hBH
    have hE₀H := (Finset.mem_filter.mp hE₀g).1
    by_cases hel0 : el ∈ E₀
    · have hE₀s : E₀ ∈ gStar := Finset.mem_filter.mpr ⟨hE₀g, hel0⟩
      have hge := hHT E hEH E₀ hE₀H
      have hle : ((E.erase el) ∩ E₀).card < t :=
        lt_of_le_of_lt (Finset.card_le_card (Finset.inter_subset_inter_left hE₀B)) hlt
      have hEq_inter : (E ∩ E₀).erase el = (E.erase el) ∩ E₀ := by
        ext x; simp [Finset.mem_erase, and_left_comm]
      have hcard_int : (E ∩ E₀).card = t := by
        have := Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨helE, hel0⟩)
        rw [hEq_inter] at this
        omega
      obtain ⟨hunion, hsum⟩ := hgStar_union E hE E₀ hE₀s hcard_int
      have hBE₀ : B = E₀ := by
        by_contra hne
        have hss : E₀ ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hE₀B, Ne.symm hne⟩
        obtain ⟨x, hxB, hxE₀⟩ := Finset.exists_of_ssubset hss
        have hxl : x ∈ initSeg m l := (hHsub B hBH).1 hxB
        rw [← hunion] at hxl
        have hxE : x ∈ E := (Finset.mem_union.mp hxl).resolve_right hxE₀
        have hxel : x ≠ el := fun h => hxE₀ (h ▸ hel0)
        have hsub : (insert x ((E ∩ E₀).erase el)) ⊆ (E.erase el) ∩ B := by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hye
          · exact Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxel, hxE⟩, hxB⟩
          · obtain ⟨hyel, hyint⟩ := Finset.mem_erase.mp hye
            obtain ⟨hyE, hyE₀⟩ := Finset.mem_inter.mp hyint
            exact Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hyel, hyE⟩, hE₀B hyE₀⟩
        have hxnot : x ∉ (E ∩ E₀).erase el := fun h => hxE₀ (Finset.mem_inter.mp (Finset.mem_of_mem_erase h)).2
        have hcard1 := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hxnot, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨helE, hel0⟩),
            hcard_int] at hcard1
        omega
      subst hBE₀
      exact ⟨hE₀s, hcard_int, hsum⟩
    · exfalso
      have hEq : (E.erase el) ∩ E₀ = E ∩ E₀ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hxE⟩, hx0⟩; exact ⟨hxE, hx0⟩
        · rintro ⟨hxE, hx0⟩; exact ⟨⟨fun h => hel0 (h ▸ hx0), hxE⟩, hx0⟩
      have h1 := hHT E hEH E₀ hE₀H
      have h2 := Finset.card_le_card (Finset.inter_subset_inter_left hE₀B : (E.erase el) ∩ E₀ ⊆ (E.erase el) ∩ B)
      rw [hEq] at h2
      omega
  -- Helper: pushing a conflict-free subset X ⊆ gStar down and removing Y ⊆ gStar
  have hpush_pull : ∀ (X Y : SetFam m), X ⊆ gStar → Y ⊆ gStar →
      (∀ E ∈ X, ∀ B ∈ H \ Y, t ≤ ((E.erase el) ∩ B).card) →
      (∀ E₁ ∈ X, ∀ E₂ ∈ X, t ≤ ((E₁.erase el) ∩ (E₂.erase el)).card) →
      ∑ E ∈ X, (m - l).choose (k - (E.card - 1)) ≤ ∑ E ∈ Y, (m - l).choose (k - E.card) := by
    intro X Y hXg hYg hXB hXX
    let X' := X.image (fun E => E.erase el)
    let H' := (H \ Y) ∪ X'
    have hX'_inj : Set.InjOn (fun E => E.erase el) (X : Set (Finset (Fin m))) := by
      intro E₁ h1 E₂ h2 hEq
      have hel1 := (Finset.mem_filter.mp (hXg h1)).2
      have hel2 := (Finset.mem_filter.mp (hXg h2)).2
      dsimp only at hEq
      rw [← Finset.insert_erase hel1, ← Finset.insert_erase hel2, hEq]
    have hX'_disj_H : Disjoint H X' := by
      rw [Finset.disjoint_left]
      intro B hBH hBX'
      rcases Finset.mem_image.mp hBX' with ⟨E, hEX, hEq⟩
      have hEg := (Finset.mem_filter.mp (hXg hEX)).1
      have helE := (Finset.mem_filter.mp (hXg hEX)).2
      have hEmin := (Finset.mem_filter.mp hEg).2
      have := hEmin B hBH (hEq ▸ Finset.erase_subset el E)
      exact Finset.notMem_erase el E (hEq.symm ▸ this.symm ▸ helE)
    have hYH : Y ⊆ H := fun E hE => (Finset.mem_filter.mp (Finset.mem_filter.mp (hYg hE)).1).1
    have hH'sub : ∀ B ∈ H', B ⊆ initSeg m l ∧ B.card ≤ k := by
      intro B hB
      rcases Finset.mem_union.mp hB with hB1 | hB2
      · exact hHsub B (Finset.mem_sdiff.mp hB1).1
      · rcases Finset.mem_image.mp hB2 with ⟨E, hEX, rfl⟩
        have hEH := (Finset.mem_filter.mp (Finset.mem_filter.mp (hXg hEX)).1).1
        exact ⟨(Finset.erase_subset el E).trans (hHsub E hEH).1,
          (Finset.card_erase_le).trans (hHsub E hEH).2⟩
    have hH'T : IsTInt t H' := by
      intro A hA B hB
      rcases Finset.mem_union.mp hA with hA1 | hA2 <;> rcases Finset.mem_union.mp hB with hB1 | hB2
      · exact hHT A (Finset.mem_sdiff.mp hA1).1 B (Finset.mem_sdiff.mp hB1).1
      · rcases Finset.mem_image.mp hB2 with ⟨E, hEX, rfl⟩
        rw [Finset.inter_comm]
        exact hXB E hEX A hA1
      · rcases Finset.mem_image.mp hA2 with ⟨E, hEX, rfl⟩
        exact hXB E hEX B hB1
      · rcases Finset.mem_image.mp hA2 with ⟨E₁, hE₁X, rfl⟩
        rcases Finset.mem_image.mp hB2 with ⟨E₂, hE₂X, rfl⟩
        exact hXX E₁ hE₁X E₂ hE₂X
    have hle : (extFam m k l H').card ≤ F.card :=
      hmax (extFam m k l H') extFam_uniform (extFam_tInt hH'T)
    rw [card_extFam hl_le hH'sub, hF_ext, card_extFam hl_le hHsub] at hle
    have hdisj' : Disjoint (H \ Y) X' := Disjoint.mono_left Finset.sdiff_subset hX'_disj_H
    rw [Finset.sum_union hdisj'] at hle
    have hHsplit : ∑ B ∈ H \ Y, (m - l).choose (k - B.card) +
        ∑ B ∈ Y, (m - l).choose (k - B.card) = ∑ B ∈ H, (m - l).choose (k - B.card) :=
      Finset.sum_sdiff hYH
    have hX'sum : ∑ B ∈ X', (m - l).choose (k - B.card) =
        ∑ E ∈ X, (m - l).choose (k - (E.card - 1)) := by
      rw [Finset.sum_image hX'_inj]
      refine Finset.sum_congr rfl fun E hEX => ?_
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mp (hXg hEX)).2]
    omega
  -- Lemma 1.2: Every E ∈ gStar has 2 * E.card = l + t
  have hgStar_size : ∀ E ∈ gStar, 2 * E.card = l + t := by
    intro E₀ hE₀
    by_contra hne
    set a := E₀.card
    set b := l + t - a
    have ha_le : a ≤ l := by
      have hEH := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₀).1).1
      exact (Finset.card_le_card (hHsub E₀ hEH).1).trans_eq (card_initSeg hl_le)
    have ha_ge : t ≤ a := by
      have hEH := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₀).1).1
      have := hHT E₀ hEH E₀ hEH
      rwa [Finset.inter_self] at this
    have hab : a + b = l + t := by omega
    have hane : a ≠ b := by omega
    set Ga := gStar.filter (fun E => E.card = a)
    set Gb := gStar.filter (fun E => E.card = b)
    have hGa_pos : 0 < Ga.card := Finset.card_pos.mpr ⟨E₀, Finset.mem_filter.mpr ⟨hE₀, rfl⟩⟩
    have h1 := hpush_pull Ga Gb (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (fun E hE B hB => by
        by_contra hlt
        obtain ⟨hBg, _, hsum⟩ := hgStar_conflict E (Finset.mem_filter.mp hE).1 B (Finset.mem_sdiff.mp hB).1 (by omega)
        have hEa := (Finset.mem_filter.mp hE).2
        exact (Finset.mem_sdiff.mp hB).2 (Finset.mem_filter.mpr ⟨hBg, by omega⟩))
      (fun E₁ h1 E₂ h2 => by
        by_contra hlt
        have hE₂H := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).1).1
        have hlt' : ((E₁.erase el) ∩ E₂).card < t := by
          have hsub : (E₁.erase el) ∩ (E₂.erase el) = (E₁.erase el) ∩ E₂ := by
            ext x; simp [Finset.mem_erase, and_left_comm]
          rw [← hsub]; omega
        obtain ⟨_, _, hsum⟩ := hgStar_conflict E₁ (Finset.mem_filter.mp h1).1 E₂ hE₂H hlt'
        have h1a := (Finset.mem_filter.mp h1).2
        have h2a := (Finset.mem_filter.mp h2).2
        omega)
    have h2 := hpush_pull Gb Ga (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (fun E hE B hB => by
        by_contra hlt
        obtain ⟨hBg, _, hsum⟩ := hgStar_conflict E (Finset.mem_filter.mp hE).1 B (Finset.mem_sdiff.mp hB).1 (by omega)
        have hEb := (Finset.mem_filter.mp hE).2
        exact (Finset.mem_sdiff.mp hB).2 (Finset.mem_filter.mpr ⟨hBg, by omega⟩))
      (fun E₁ h1 E₂ h2 => by
        by_contra hlt
        have hE₂H := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).1).1
        have hlt' : ((E₁.erase el) ∩ E₂).card < t := by
          have hsub : (E₁.erase el) ∩ (E₂.erase el) = (E₁.erase el) ∩ E₂ := by
            ext x; simp [Finset.mem_erase, and_left_comm]
          rw [← hsub]; omega
        obtain ⟨_, _, hsum⟩ := hgStar_conflict E₁ (Finset.mem_filter.mp h1).1 E₂ hE₂H hlt'
        have h1b := (Finset.mem_filter.mp h1).2
        have h2b := (Finset.mem_filter.mp h2).2
        omega)
    have hak : a ≤ k := (hHsub E₀ (Finset.mem_filter.mp (Finset.mem_filter.mp hE₀).1).1).2
    have hsum1 : ∑ E ∈ Ga, (m - l).choose (k - (E.card - 1)) = Ga.card * (m - l).choose (k - a + 1) := by
      rw [Finset.sum_congr rfl fun E hE => by rw [(Finset.mem_filter.mp hE).2, show k - (a - 1) = k - a + 1 by omega]]
      rw [Finset.sum_const, smul_eq_mul]
    have hsum2 : ∑ E ∈ Gb, (m - l).choose (k - E.card) = Gb.card * (m - l).choose (k - b) := by
      rw [Finset.sum_congr rfl fun E hE => by rw [(Finset.mem_filter.mp hE).2]]
      rw [Finset.sum_const, smul_eq_mul]
    rw [hsum1, hsum2] at h1
    have hfa : k - a + 1 ≤ m - l := hgStar_feas E₀ hE₀
    have hch_a_pos : 0 < (m - l).choose (k - a + 1) := Nat.choose_pos hfa
    have hGb_pos : 0 < Gb.card := by
      by_contra h0
      have hGb0 : Gb.card = 0 := by omega
      rw [hGb0, zero_mul] at h1
      have : 0 < Ga.card * (m - l).choose (k - a + 1) := Nat.mul_pos hGa_pos hch_a_pos
      omega
    obtain ⟨E₁, hE₁Gb⟩ := Finset.card_pos.mp hGb_pos
    have hE₁g := (Finset.mem_filter.mp hE₁Gb).1
    have hE₁b := (Finset.mem_filter.mp hE₁Gb).2
    have hbk : b ≤ k := hE₁b ▸ (hHsub E₁ (Finset.mem_filter.mp (Finset.mem_filter.mp hE₁g).1).1).2
    have hb_ge : t ≤ b := by
      have hE₁H := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₁g).1).1
      have := hHT E₁ hE₁H E₁ hE₁H
      rw [Finset.inter_self, hE₁b] at this; exact this
    have hsum3 : ∑ E ∈ Gb, (m - l).choose (k - (E.card - 1)) = Gb.card * (m - l).choose (k - b + 1) := by
      rw [Finset.sum_congr rfl fun E hE => by rw [(Finset.mem_filter.mp hE).2, show k - (b - 1) = k - b + 1 by omega]]
      rw [Finset.sum_const, smul_eq_mul]
    have hsum4 : ∑ E ∈ Ga, (m - l).choose (k - E.card) = Ga.card * (m - l).choose (k - a) := by
      rw [Finset.sum_congr rfl fun E hE => by rw [(Finset.mem_filter.mp hE).2]]
      rw [Finset.sum_const, smul_eq_mul]
    rw [hsum3, hsum4] at h2
    have hfb : k - b + 1 ≤ m - l := hE₁b ▸ hgStar_feas E₁ hE₁g
    have hprod : (Ga.card * Gb.card) * ((m - l).choose (k - a + 1) * (m - l).choose (k - b + 1)) ≤
        (Ga.card * Gb.card) * ((m - l).choose (k - b) * (m - l).choose (k - a)) := by
      calc (Ga.card * Gb.card) * ((m - l).choose (k - a + 1) * (m - l).choose (k - b + 1))
          = (Ga.card * (m - l).choose (k - a + 1)) * (Gb.card * (m - l).choose (k - b + 1)) := by ring
        _ ≤ (Gb.card * (m - l).choose (k - b)) * (Ga.card * (m - l).choose (k - a)) :=
            Nat.mul_le_mul h1 h2
        _ = (Ga.card * Gb.card) * ((m - l).choose (k - b) * (m - l).choose (k - a)) := by ring
    have hch_ineq : (m - l).choose (k - a + 1) * (m - l).choose (k - b + 1) ≤
        (m - l).choose (k - b) * (m - l).choose (k - a) :=
      Nat.le_of_mul_le_mul_left hprod (Nat.mul_pos hGa_pos hGb_pos)
    have hca := choose_mul_succ (m - l) (k - a)
    have hcb := choose_mul_succ (m - l) (k - b)
    have hpos_a : 0 < (m - l).choose (k - a) := Nat.choose_pos (by omega)
    have hpos_b : 0 < (m - l).choose (k - b) := Nat.choose_pos (by omega)
    have hstep : ((m - l) - (k - a)) * ((m - l) - (k - b)) * ((m - l).choose (k - a) * (m - l).choose (k - b)) ≤
        (k - a + 1) * (k - b + 1) * ((m - l).choose (k - a) * (m - l).choose (k - b)) := by
      calc ((m - l) - (k - a)) * ((m - l) - (k - b)) * ((m - l).choose (k - a) * (m - l).choose (k - b))
          = (((m - l) - (k - a)) * (m - l).choose (k - a)) * (((m - l) - (k - b)) * (m - l).choose (k - b)) := by ring
        _ = ((k - a + 1) * (m - l).choose (k - a + 1)) * ((k - b + 1) * (m - l).choose (k - b + 1)) := by
            rw [← hca, ← hcb]
        _ = (k - a + 1) * (k - b + 1) * ((m - l).choose (k - a + 1) * (m - l).choose (k - b + 1)) := by ring
        _ ≤ (k - a + 1) * (k - b + 1) * ((m - l).choose (k - b) * (m - l).choose (k - a)) :=
            Nat.mul_le_mul_left _ hch_ineq
        _ = (k - a + 1) * (k - b + 1) * ((m - l).choose (k - a) * (m - l).choose (k - b)) := by ring
    have hfinal := Nat.le_of_mul_le_mul_right hstep (Nat.mul_pos hpos_a hpos_b)
    have hlt1 : k - b + 1 < (m - l) - (k - a) := by omega
    have hlt2 : k - a + 1 < (m - l) - (k - b) := by omega
    nlinarith
  -- Deduce l = t + 2 * r
  obtain ⟨E₀, hE₀⟩ := hgStar_ne
  have hE₀_2 := hgStar_size E₀ hE₀
  have hE₀_k : E₀.card ≤ k := (hHsub E₀ (Finset.mem_filter.mp (Finset.mem_filter.mp hE₀).1).1).2
  have hE₀_t : t ≤ E₀.card := by
    have hEH := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₀).1).1
    have := hHT E₀ hEH E₀ hEH
    rwa [Finset.inter_self] at this
  set r := E₀.card - t
  have hl_eq : l = t + 2 * r := by omega
  have htr_k : t + r ≤ k := by omega
  have hl2_m : l + 2 ≤ m := by omega
  have hgStar_card : ∀ E ∈ gStar, E.card = t + r := by
    intro E hE
    have := hgStar_size E hE
    omega
  refine ⟨l, r, hl_eq, htr_k, hl2_m, hF_ext, ?_, ?_, ?_⟩
  · intro E hEg x hxE hxl
    have hxeq : x = el := Fin.ext hxl
    exact hgStar_card E (Finset.mem_filter.mpr ⟨hEg, hxeq ▸ hxE⟩)
  · exact ⟨E₀, (Finset.mem_filter.mp hE₀).1, el, (Finset.mem_filter.mp hE₀).2, rfl⟩
  · -- Lemma 1.3: averaging over x ∈ initSeg m (l - 1)
    intro hr1
    have hper_x : ∀ x ∈ initSeg m (l - 1),
        (gStar.filter (fun E => x ∉ E)).card * (m - l).choose (k - (t + r) + 1) ≤
        (gStar.filter (fun E => x ∈ E)).card * (m - l).choose (k - (t + r)) := by
      intro x hx
      set Xx := gStar.filter (fun E => x ∉ E)
      set Yx := gStar.filter (fun E => x ∈ E)
      have hpp := hpush_pull Xx Yx (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        (fun E hE B hB => by
          by_contra hlt
          obtain ⟨hBg, hint, _⟩ := hgStar_conflict E (Finset.mem_filter.mp hE).1 B (Finset.mem_sdiff.mp hB).1 (by omega)
          obtain ⟨hunion, _⟩ := hgStar_union E (Finset.mem_filter.mp hE).1 B hBg hint
          have hxl : x ∈ initSeg m l := initSeg_subset_mono (by omega) hx
          rw [← hunion] at hxl
          have hxB : x ∈ B := (Finset.mem_union.mp hxl).resolve_left (Finset.mem_filter.mp hE).2
          exact (Finset.mem_sdiff.mp hB).2 (Finset.mem_filter.mpr ⟨hBg, hxB⟩))
        (fun E₁ h1 E₂ h2 => by
          by_contra hlt
          have hE₁s := (Finset.mem_filter.mp h1).1
          have hE₂s := (Finset.mem_filter.mp h2).1
          have hE₂H := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₂s).1).1
          have hlt' : ((E₁.erase el) ∩ E₂).card < t := by
            have hsub : (E₁.erase el) ∩ (E₂.erase el) = (E₁.erase el) ∩ E₂ := by
              ext y; simp [Finset.mem_erase, and_left_comm]
            rw [← hsub]; omega
          obtain ⟨_, hint, _⟩ := hgStar_conflict E₁ hE₁s E₂ hE₂H hlt'
          obtain ⟨hunion, _⟩ := hgStar_union E₁ hE₁s E₂ hE₂s hint
          have hxl : x ∈ initSeg m l := initSeg_subset_mono (by omega) hx
          rw [← hunion] at hxl
          rcases Finset.mem_union.mp hxl with hx1 | hx2
          · exact (Finset.mem_filter.mp h1).2 hx1
          · exact (Finset.mem_filter.mp h2).2 hx2)
      have hs1 : ∑ E ∈ Xx, (m - l).choose (k - (E.card - 1)) =
          Xx.card * (m - l).choose (k - (t + r) + 1) := by
        rw [Finset.sum_congr rfl fun E hE => by
          rw [hgStar_card E (Finset.mem_filter.mp hE).1, show k - (t + r - 1) = k - (t + r) + 1 by omega]]
        rw [Finset.sum_const, smul_eq_mul]
      have hs2 : ∑ E ∈ Yx, (m - l).choose (k - E.card) =
          Yx.card * (m - l).choose (k - (t + r)) := by
        rw [Finset.sum_congr rfl fun E hE => by rw [hgStar_card E (Finset.mem_filter.mp hE).1]]
        rw [Finset.sum_const, smul_eq_mul]
      omega
    have hsum_le : (∑ x ∈ initSeg m (l - 1), (gStar.filter (fun E => x ∉ E)).card) *
        (m - l).choose (k - (t + r) + 1) ≤
        (∑ x ∈ initSeg m (l - 1), (gStar.filter (fun E => x ∈ E)).card) *
        (m - l).choose (k - (t + r)) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_le_sum hper_x
    have hcount_in : ∑ x ∈ initSeg m (l - 1), (gStar.filter (fun E => x ∈ E)).card =
        gStar.card * (t + r - 1) := by
      calc ∑ x ∈ initSeg m (l - 1), (gStar.filter (fun E => x ∈ E)).card
          = ∑ x ∈ initSeg m (l - 1), ∑ E ∈ gStar, if x ∈ E then 1 else 0 := by
              refine Finset.sum_congr rfl fun x _ => Finset.card_filter _ _
        _ = ∑ E ∈ gStar, ∑ x ∈ initSeg m (l - 1), if x ∈ E then 1 else 0 := Finset.sum_comm
        _ = ∑ E ∈ gStar, (E.erase el).card := by
              refine Finset.sum_congr rfl fun E hE => ?_
              have hEH := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
              have hEq : (initSeg m (l - 1)).filter (fun x => x ∈ E) = E.erase el := by
                ext x
                simp only [Finset.mem_filter, mem_initSeg, Finset.mem_erase]
                constructor
                · rintro ⟨hxlt, hxE⟩
                  exact ⟨fun h => by subst h; simp [el] at hxlt, hxE⟩
                · rintro ⟨hxne, hxE⟩
                  have hxl : (x : ℕ) < l := mem_initSeg.mp ((hHsub E hEH).1 hxE)
                  have hne' : (x : ℕ) ≠ l - 1 := fun h => hxne (Fin.ext h)
                  exact ⟨by omega, hxE⟩
              rw [← Finset.card_filter, hEq]
        _ = ∑ E ∈ gStar, (t + r - 1) := by
              refine Finset.sum_congr rfl fun E hE => ?_
              rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hE).2, hgStar_card E hE]
        _ = gStar.card * (t + r - 1) := by rw [Finset.sum_const, smul_eq_mul]
    have hcount_out : ∑ x ∈ initSeg m (l - 1), (gStar.filter (fun E => x ∉ E)).card =
        gStar.card * r := by
      have htot : ∑ x ∈ initSeg m (l - 1),
          ((gStar.filter (fun E => x ∈ E)).card + (gStar.filter (fun E => x ∉ E)).card) =
          (l - 1) * gStar.card := by
        rw [Finset.sum_congr rfl fun x _ => Finset.card_filter_add_card_filter_not (s := gStar) (p := fun E => x ∈ E)]
        rw [Finset.sum_const, smul_eq_mul, card_initSeg (by omega : l - 1 ≤ m)]
      rw [Finset.sum_add_distrib, hcount_in] at htot
      have hltot : (l - 1) * gStar.card = gStar.card * (t + r - 1) + gStar.card * r := by
        have : l - 1 = (t + r - 1) + r := by omega
        rw [this]; ring
      omega
    rw [hcount_in, hcount_out] at hsum_le
    have hg_pos : 0 < gStar.card := Finset.card_pos.mpr ⟨E₀, hE₀⟩
    have hch_le : r * (m - l).choose (k - (t + r) + 1) ≤ (t + r - 1) * (m - l).choose (k - (t + r)) := by
      have : gStar.card * (r * (m - l).choose (k - (t + r) + 1)) ≤
          gStar.card * ((t + r - 1) * (m - l).choose (k - (t + r))) := by
        linarith
      exact Nat.le_of_mul_le_mul_left this hg_pos
    have hch_id := choose_mul_succ (m - l) (k - (t + r))
    have hch_pos : 0 < (m - l).choose (k - (t + r)) := Nat.choose_pos (by omega)
    have hmul : r * ((m - l) - (k - (t + r))) * (m - l).choose (k - (t + r)) ≤
        (t + r - 1) * (k - (t + r) + 1) * (m - l).choose (k - (t + r)) := by
      calc r * ((m - l) - (k - (t + r))) * (m - l).choose (k - (t + r))
          = r * (((m - l) - (k - (t + r))) * (m - l).choose (k - (t + r))) := by ring
        _ = r * ((k - (t + r) + 1) * (m - l).choose (k - (t + r) + 1)) := by rw [← hch_id]
        _ = (k - (t + r) + 1) * (r * (m - l).choose (k - (t + r) + 1)) := by ring
        _ ≤ (k - (t + r) + 1) * ((t + r - 1) * (m - l).choose (k - (t + r))) :=
            Nat.mul_le_mul_left _ hch_le
        _ = (t + r - 1) * (k - (t + r) + 1) * (m - l).choose (k - (t + r)) := by ring
    have hfin := Nat.le_of_mul_le_mul_right hmul hch_pos
    have hsub1 : (m - l) - (k - (t + r)) = m - k - r := by omega
    rw [hsub1] at hfin
    -- Rearrange r * (m - k - r) ≤ (t + r - 1) * (k - (t + r) + 1)
    -- into r * (m - 2*k + 2*t - 2) ≤ (t - 1) * (k - t + 1)
    have hfin_int : (r : ℤ) * ((m : ℤ) - (k : ℤ) - (r : ℤ)) ≤ ((t : ℤ) + (r : ℤ) - 1) * ((k : ℤ) - ((t : ℤ) + (r : ℤ)) + 1) := by
      zify [show k ≤ m by omega, show r ≤ m - k by omega, show t + r ≤ k by omega, show 1 ≤ t + r by omega] at hfin
      linarith only [hfin]
    zify [show 2 * k ≤ m + 2 * t by omega, show 2 ≤ m + 2 * t - 2 * k by omega,
          show 1 ≤ t by omega, show t ≤ k by omega]
    nlinarith only [hfin_int]

/- ### Section 5: Symmetric extent `ℓ`, pushing–pulling, and endgame -/

def IsSymOn {m : ℕ} (F : SetFam m) (ℓ : ℕ) : Prop :=
  ∀ A ∈ F, ∀ i j : Fin m, (i : ℕ) < ℓ → (j : ℕ) < ℓ → i ∈ A → j ∉ A →
    (insert j (A.erase i)) ∈ F

lemma isSymOn_card_eq {m ℓ : ℕ} {F : SetFam m} (hSym : IsSymOn F ℓ) :
    ∀ (A B : Finset (Fin m)), A ∈ F →
      A \ initSeg m ℓ = B \ initSeg m ℓ →
      (A ∩ initSeg m ℓ).card = (B ∩ initSeg m ℓ).card → B ∈ F := by
  suffices h : ∀ d : ℕ, ∀ A B : Finset (Fin m), A ∈ F →
      A \ initSeg m ℓ = B \ initSeg m ℓ →
      (A ∩ initSeg m ℓ).card = (B ∩ initSeg m ℓ).card →
      ((A ∩ initSeg m ℓ) \ (B ∩ initSeg m ℓ)).card = d → B ∈ F by
    intro A B hA hrest hcard
    exact h _ A B hA hrest hcard rfl
  intro d
  induction d with
  | zero =>
    intro A B hA hrest hcard hd
    have hsub : A ∩ initSeg m ℓ ⊆ B ∩ initSeg m ℓ :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hd)
    have hEq_int : A ∩ initSeg m ℓ = B ∩ initSeg m ℓ :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    have hAB : A = B := by
      rw [← Finset.sdiff_union_inter A (initSeg m ℓ), ← Finset.sdiff_union_inter B (initSeg m ℓ),
          hrest, hEq_int]
    exact hAB ▸ hA
  | succ d ih =>
    intro A B hA hrest hcard hd
    have hne1 : ((A ∩ initSeg m ℓ) \ (B ∩ initSeg m ℓ)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hne1
    have hiA : i ∈ A := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hi).1).1
    have hiℓ : (i : ℕ) < ℓ := mem_initSeg.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hi).1).2
    have hiB : i ∉ B := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mpr ⟨h, mem_initSeg.mpr hiℓ⟩)
    have hne2 : ((B ∩ initSeg m ℓ) \ (A ∩ initSeg m ℓ)).Nonempty := by
      have h1 := Finset.card_sdiff_add_card_inter (A ∩ initSeg m ℓ) (B ∩ initSeg m ℓ)
      have h2 := Finset.card_sdiff_add_card_inter (B ∩ initSeg m ℓ) (A ∩ initSeg m ℓ)
      rw [Finset.inter_comm (B ∩ initSeg m ℓ)] at h2
      exact Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hne2
    have hjB : j ∈ B := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hj).1).1
    have hjℓ : (j : ℕ) < ℓ := mem_initSeg.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hj).1).2
    have hjA : j ∉ A := fun h => (Finset.mem_sdiff.mp hj).2 (Finset.mem_inter.mpr ⟨h, mem_initSeg.mpr hjℓ⟩)
    set A' := (insert j (A.erase i))
    have hA'F : A' ∈ F := hSym A hA i j hiℓ hjℓ hiA hjA
    have hA'rest : A' \ initSeg m ℓ = B \ initSeg m ℓ := by
      rw [← hrest]
      ext x
      simp only [Finset.mem_sdiff, mem_initSeg, Finset.mem_insert, Finset.mem_erase, A']
      constructor
      · rintro ⟨rfl | ⟨_, hxA⟩, hxge⟩
        · omega
        · exact ⟨hxA, hxge⟩
      · rintro ⟨hxA, hxge⟩
        exact ⟨Or.inr ⟨fun h => by subst h; omega, hxA⟩, hxge⟩
    have hA'int : A' ∩ initSeg m ℓ = (insert j ((A ∩ initSeg m ℓ).erase i)) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, mem_initSeg, A']
      constructor
      · rintro ⟨rfl | ⟨hxi, hxA⟩, hxℓ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hxi, hxA, hxℓ⟩
      · rintro (rfl | ⟨hxi, hxA, hxℓ⟩)
        · exact ⟨Or.inl rfl, hjℓ⟩
        · exact ⟨Or.inr ⟨hxi, hxA⟩, hxℓ⟩
    have hA'card : (A' ∩ initSeg m ℓ).card = (B ∩ initSeg m ℓ).card := by
      rw [hA'int, card_erase_insert (Finset.mem_inter.mpr ⟨hiA, mem_initSeg.mpr hiℓ⟩)
          (fun h => hjA (Finset.mem_inter.mp h).1), hcard]
    have hA'diff : ((A' ∩ initSeg m ℓ) \ (B ∩ initSeg m ℓ)) =
        ((A ∩ initSeg m ℓ) \ (B ∩ initSeg m ℓ)).erase i := by
      rw [hA'int]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_inter, mem_initSeg]
      constructor
      · rintro ⟨rfl | ⟨hxi, hxA, hxℓ⟩, hxnot⟩
        · exact absurd ⟨hjB, hjℓ⟩ hxnot
        · exact ⟨hxi, ⟨hxA, hxℓ⟩, hxnot⟩
      · rintro ⟨hxi, ⟨hxA, hxℓ⟩, hxnot⟩
        exact ⟨Or.inr ⟨hxi, hxA, hxℓ⟩, hxnot⟩
    have hA'd : ((A' ∩ initSeg m ℓ) \ (B ∩ initSeg m ℓ)).card = d := by
      rw [hA'diff, Finset.card_erase_of_mem hi, hd]
      simp
    exact ih A' B hA'F hA'rest hA'card hA'd

def prodFam {m : ℕ} (L R : SetFam m) : SetFam m :=
  (L ×ˢ R).image fun p => p.1 ∪ p.2

lemma card_prodFam {m : ℕ} {U : Finset (Fin m)} {L R : SetFam m}
    (hL : ∀ A ∈ L, A ⊆ U) (hR : ∀ B ∈ R, Disjoint B U) :
    (prodFam L R).card = L.card * R.card := by
  unfold prodFam
  rw [Finset.card_image_of_injOn, Finset.card_product]
  intro p hp q hq hEq
  simp only [Finset.mem_coe, Finset.mem_product] at hp hq
  have h1 : (p.1 ∪ p.2) ∩ U = p.1 := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx1 | hx2, hxU⟩
      · exact hx1
      · exact absurd hxU (Finset.disjoint_left.mp (hR p.2 hp.2) hx2)
    · intro hx1; exact ⟨Or.inl hx1, hL p.1 hp.1 hx1⟩
  have h2 : (q.1 ∪ q.2) ∩ U = q.1 := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx1 | hx2, hxU⟩
      · exact hx1
      · exact absurd hxU (Finset.disjoint_left.mp (hR q.2 hq.2) hx2)
    · intro hx1; exact ⟨Or.inl hx1, hL q.1 hq.1 hx1⟩
  have h3 : (p.1 ∪ p.2) \ U = p.2 := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx1 | hx2, hxU⟩
      · exact absurd (hL p.1 hp.1 hx1) hxU
      · exact hx2
    · intro hx2; exact ⟨Or.inr hx2, Finset.disjoint_left.mp (hR p.2 hp.2) hx2⟩
  have h4 : (q.1 ∪ q.2) \ U = q.2 := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx1 | hx2, hxU⟩
      · exact absurd (hL q.1 hq.1 hx1) hxU
      · exact hx2
    · intro hx2; exact ⟨Or.inr hx2, Finset.disjoint_left.mp (hR q.2 hq.2) hx2⟩
  dsimp only at hEq
  exact Prod.ext (by rw [← h1, ← h2, hEq]) (by rw [← h3, ← h4, hEq])

set_option maxHeartbeats 600000 in
/-- Endgame when `ℓ = l - 2` and `l = t + 2 * r` with `r ≥ 1`. -/
lemma endgame_l_sub_2 {m k t l r ℓ : ℕ} (ht : 2 ≤ t) (htr_k : t + r ≤ k)
    (hl_eq : l = t + 2 * r) (hl2_m : l + 2 ≤ m) (hr1 : 1 ≤ r) (hℓ_eq_l2 : ℓ = l - 2)
    {F : SetFam m} (hU : IsUniform k F) (hℓ_sym : IsSymOn F ℓ)
    (hF_ext : F = extFam m k l (genUpper F k l))
    (hHT : IsTInt t (genUpper F k l)) (hHLC : IsLeftCompressed (genUpper F k l)) :
    ∃ r' : ℕ, F.card ≤ (franklFam m k t r').card := by
  classical
  set H := genUpper F k l
  have hHsub : ∀ B ∈ H, B ⊆ initSeg m l ∧ B.card ≤ k := by
    intro B hB
    exact ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1, (Finset.mem_filter.mp hB).2.1⟩
  have hHup : ∀ B ∈ H, ∀ B' : Finset (Fin m), B ⊆ B' → B' ⊆ initSeg m l → B'.card ≤ k → B' ∈ H := by
    intro B hB B' hBB' hB'l hB'k
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hB'l, hB'k,
      fun A hAk hB'A => (Finset.mem_filter.mp hB).2.2 A hAk (hBB'.trans hB'A)⟩
  /- ### Endgame: `ℓ = l - 2`, symmetry on `initSeg m (l - 2)` -/
  set eA : Fin m := ⟨l - 2, by omega⟩
  set eB : Fin m := ⟨l - 1, by omega⟩
  have heA_not : eA ∉ initSeg m ℓ := by rw [mem_initSeg]; simp [eA]; omega
  have heB_not : eB ∉ initSeg m ℓ := by rw [mem_initSeg]; simp [eB]; omega
  have heA_in : eA ∈ initSeg m l := by rw [mem_initSeg]; simp [eA]; omega
  have heB_in : eB ∈ initSeg m l := by rw [mem_initSeg]; simp [eB]; omega
  have heAB_ne : eA ≠ eB := fun h => by have := congrArg Fin.val h; simp [eA, eB] at this; omega
  -- Prove IsSymOn H ℓ directly from IsSymOn F ℓ
  have hH_symOn : IsSymOn H ℓ := by
    intro B hBH i j hiℓ hjℓ hiB hjB
    obtain ⟨hBl, hBk, hBU⟩ := Finset.mem_filter.mp hBH
    rw [Finset.mem_powerset] at hBl
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, by rw [card_erase_insert hiB hjB]; exact hBk, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxe
      · exact mem_initSeg.mpr (by omega)
      · exact hBl (Finset.mem_of_mem_erase hxe)
    · intro A hAk hsub
      by_cases hiA : i ∈ A
      · refine hBU A hAk ?_
        intro x hx
        by_cases hxi : x = i
        · exact hxi ▸ hiA
        · exact hsub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hx⟩))
      · have hjA : j ∈ A := hsub (Finset.mem_insert_self j _)
        set A' := (insert i (A.erase j))
        have hA'k : A'.card = k := by rw [card_erase_insert hjA hiA, hAk]
        have hBA' : B ⊆ A' := by
          intro x hx
          by_cases hxi : x = i
          · exact hxi ▸ Finset.mem_insert_self i _
          · have hxj : x ≠ j := fun h => hjB (h ▸ hx)
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxj,
              hsub (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hx⟩))⟩)
        have hA'F : A' ∈ F := hBU A' hA'k hBA'
        have hij : i ≠ j := fun h => hjB (h ▸ hiB)
        have hback : (insert j (A'.erase i)) = A := by
          ext x
          by_cases hxj : x = j
          · subst hxj; simp [A', hjA]
          · by_cases hxi : x = i
            · subst hxi; simp [A', hij, hiA]
            · simp [A', hxi, hxj]
        exact hback ▸ hℓ_sym A' hA'F i j hiℓ hjℓ (Finset.mem_insert_self i _)
          (by simp [A', hij.symm])
  -- Now check whether there exists B ∈ H with eA ∈ B, eB ∈ B, and (B ∩ initSeg m ℓ).card = t + r - 2
  by_cases hhas_d : ∃ B ∈ H, eA ∈ B ∧ eB ∈ B ∧ (B ∩ initSeg m ℓ).card ≤ t + r - 2
  · -- Subcase B: there is B₀ ∈ H with {eA, eB} ⊆ B₀ and |B₀ ∩ initSeg m ℓ| ≤ t + r - 2.
    -- First show |B₀ ∩ initSeg m ℓ| = t + r - 2 (cannot be smaller!)
    obtain ⟨B₀, hB₀H, heAB₀, heBB₀, hB₀le⟩ := hhas_d
    set D₀ := B₀ ∩ initSeg m ℓ
    set d := D₀.card
    -- Every D ⊆ initSeg m ℓ of size d has D ∪ {eA, eB} ∈ H
    have hall_d : ∀ D ⊆ initSeg m ℓ, D.card = d → D ∪ {eA, eB} ∈ H := by
      intro D hDℓ hDcard
      have hB₀_eq : B₀ = D₀ ∪ {eA, eB} := by
        ext x; simp only [Finset.mem_union, Finset.mem_inter, mem_initSeg, Finset.mem_insert,
          Finset.mem_singleton, D₀]
        constructor
        · intro hxB
          have hxl : (x : ℕ) < l := mem_initSeg.mp ((hHsub B₀ hB₀H).1 hxB)
          by_cases hxℓ : (x : ℕ) < ℓ
          · exact Or.inl ⟨hxB, hxℓ⟩
          · by_cases hxA : x = eA
            · exact Or.inr (Or.inl hxA)
            · have hneA : (x : ℕ) ≠ l - 2 := fun h => hxA (Fin.ext h)
              have : x = eB := Fin.ext (by dsimp [eB]; omega)
              exact Or.inr (Or.inr this)
        · rintro (⟨hxB, _⟩ | rfl | rfl)
          · exact hxB
          · exact heAB₀
          · exact heBB₀
      refine isSymOn_card_eq hH_symOn B₀ (D ∪ {eA, eB}) hB₀H ?_ ?_
      · rw [hB₀_eq]
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_inter, D₀]
        constructor
        · rintro ⟨⟨_, hxℓ⟩ | rfl | rfl, hnot⟩
          · exact absurd hxℓ hnot
          · exact ⟨Or.inr (Or.inl rfl), hnot⟩
          · exact ⟨Or.inr (Or.inr rfl), hnot⟩
        · rintro ⟨hxD | rfl | rfl, hnot⟩
          · exact absurd (hDℓ hxD) hnot
          · exact ⟨Or.inr (Or.inl rfl), hnot⟩
          · exact ⟨Or.inr (Or.inr rfl), hnot⟩
      · have h1 : (D ∪ {eA, eB}) ∩ initSeg m ℓ = D := by
          ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hxD | rfl | rfl, hxℓ⟩
            · exact hxD
            · exact absurd hxℓ heA_not
            · exact absurd hxℓ heB_not
          · intro hxD; exact ⟨Or.inl hxD, hDℓ hxD⟩
        rw [h1, hDcard]
    -- Prove d = t + r - 2 (by showing d ≥ t + r - 2 via left-compression of eA, eB into initSeg m ℓ)
    have hd_ge : t + r - 2 ≤ d := by
      by_cases hsmall : ℓ - d < 2
      · omega
      · have htwo : 2 ≤ (initSeg m ℓ \ D₀).card := by
          have hd_def : d = (B₀ ∩ initSeg m ℓ).card := rfl
          rw [card_sdiff_sub Finset.inter_subset_right, card_initSeg (by omega)]; omega
        obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq htwo
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hPcard
        have hxℓ : x ∈ initSeg m ℓ := (Finset.mem_sdiff.mp (hPsub (by simp))).1
        have hyℓ : y ∈ initSeg m ℓ := (Finset.mem_sdiff.mp (hPsub (by simp))).1
        have hxB₀ : x ∉ B₀ := fun h => (Finset.mem_sdiff.mp (hPsub (by simp))).2 (Finset.mem_inter.mpr ⟨h, hxℓ⟩)
        have hyB₀ : y ∉ B₀ := fun h => (Finset.mem_sdiff.mp (hPsub (by simp))).2 (Finset.mem_inter.mpr ⟨h, hyℓ⟩)
        have hxltA : x < eA := Fin.mk_lt_mk.mpr (by have := mem_initSeg.mp hxℓ; omega)
        have hyltB : y < eB := Fin.mk_lt_mk.mpr (by have := mem_initSeg.mp hyℓ; omega)
        have hB1 : (insert x (B₀.erase eA)) ∈ H := hHLC B₀ hB₀H x eA hxltA heAB₀ hxB₀
        have heB_in1 : eB ∈ (insert x (B₀.erase eA)) :=
          Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨heAB_ne.symm, heBB₀⟩)
        have hy_not1 : y ∉ (insert x (B₀.erase eA)) := by
          simp [hxy.symm, hyB₀]
        have hB2 : (insert y (((insert x (B₀.erase eA))).erase eB)) ∈ H :=
          hHLC _ hB1 y eB hyltB heB_in1 hy_not1
        set B₂ := (insert y (((insert x (B₀.erase eA))).erase eB))
        have hB₂ℓ : B₂ ⊆ initSeg m ℓ := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_erase, B₂] at hz
          rcases hz with rfl | ⟨hzB, rfl | ⟨hzA, hzB₀⟩⟩
          · exact hyℓ
          · exact hxℓ
          · have hzl : (z : ℕ) < l := mem_initSeg.mp ((hHsub B₀ hB₀H).1 hzB₀)
            have hneA : (z : ℕ) ≠ l - 2 := fun h => hzA (Fin.ext h)
            have hneB : (z : ℕ) ≠ l - 1 := fun h => hzB (Fin.ext h)
            exact mem_initSeg.mpr (by omega)
        have hB₂card : B₂.card = d + 2 := by
          have h1 : B₀.card = d + 2 := by
            have hsplit := Finset.card_sdiff_add_card_inter B₀ (initSeg m ℓ)
            have hsdiff : B₀ \ initSeg m ℓ = {eA, eB} := by
              ext z; simp only [Finset.mem_sdiff, mem_initSeg, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨hzB, hzge⟩
                have hzl : (z : ℕ) < l := mem_initSeg.mp ((hHsub B₀ hB₀H).1 hzB)
                by_cases h1' : z = eA
                · exact Or.inl h1'
                · have hneA : (z : ℕ) ≠ l - 2 := fun h => h1' (Fin.ext h)
                  exact Or.inr (Fin.ext (by dsimp [eB]; omega))
              · rintro (rfl | rfl)
                · exact ⟨heAB₀, by simp [eA]; omega⟩
                · exact ⟨heBB₀, by simp [eB]; omega⟩
            have hd_def : d = (B₀ ∩ initSeg m ℓ).card := rfl
            rw [hsdiff, Finset.card_pair heAB_ne] at hsplit
            omega
          rw [card_erase_insert heB_in1 hy_not1, card_erase_insert heAB₀ hxB₀, h1]
        obtain ⟨D, hDℓ, hDcard, hDint⟩ := exists_subset_min_inter hB₂ℓ
          (by rw [card_initSeg (by omega)]; omega : d ≤ (initSeg m ℓ).card)
        have hDH := hall_d D hDℓ hDcard
        have hint := hHT B₂ hB2 (D ∪ {eA, eB}) hDH
        have hEq : B₂ ∩ (D ∪ {eA, eB}) = B₂ ∩ D := by
          ext z; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hzB, hzD | rfl | rfl⟩
            · exact ⟨hzB, hzD⟩
            · exact absurd (hB₂ℓ hzB) heA_not
            · exact absurd (hB₂ℓ hzB) heB_not
          · rintro ⟨hzB, hzD⟩; exact ⟨hzB, Or.inl hzD⟩
        rw [hEq, hDint, hB₂card, card_initSeg (by omega)] at hint
        omega
    have hd_eq : d = t + r - 2 := by omega
    -- Show every B ∈ H has B.card ≥ t + r, so F ⊆ franklFam m k t r
    refine ⟨r, Finset.card_le_card ?_⟩
    intro A hAF
    have hAk := hU A hAF
    have hAH : A ∩ initSeg m l ∈ H := by rw [hF_ext] at hAF; exact (Finset.mem_filter.mp hAF).2
    set B := A ∩ initSeg m l
    have hB_card : t + r ≤ B.card := by
      have hBsplit : B.card = (B ∩ initSeg m ℓ).card + (B ∩ {eA, eB}).card := by
        have h1 := Finset.card_sdiff_add_card_inter B (initSeg m ℓ)
        have h2 : B \ initSeg m ℓ = B ∩ {eA, eB} := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_inter, mem_initSeg, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hxB, hxge⟩
            have hxl : (x : ℕ) < l := mem_initSeg.mp ((hHsub B hAH).1 hxB)
            by_cases h1' : x = eA
            · exact ⟨hxB, Or.inl h1'⟩
            · have hneA : (x : ℕ) ≠ l - 2 := fun h => h1' (Fin.ext h)
              exact ⟨hxB, Or.inr (Fin.ext (by dsimp [eB]; omega))⟩
          · rintro ⟨hxB, rfl | rfl⟩
            · exact ⟨hxB, by simp [eA]; omega⟩
            · exact ⟨hxB, by simp [eB]; omega⟩
        rw [h2] at h1; omega
      obtain ⟨D, hDℓ, hDcard, hDint⟩ := exists_subset_min_inter
        (Finset.inter_subset_right : B ∩ initSeg m ℓ ⊆ initSeg m ℓ)
        (by rw [card_initSeg (by omega)]; omega : d ≤ (initSeg m ℓ).card)
      have hDH := hall_d D hDℓ hDcard
      have hint := hHT B hAH (D ∪ {eA, eB}) hDH
      have hsub : B ∩ (D ∪ {eA, eB}) ⊆ ((B ∩ initSeg m ℓ) ∩ D) ∪ (B ∩ {eA, eB}) := by
        intro x hx
        rcases Finset.mem_inter.mp hx with ⟨hxB, hx2⟩
        rcases Finset.mem_union.mp hx2 with hxD | hxAB
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxB, hDℓ hxD⟩, hxD⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxB, hxAB⟩)
      have hle_u := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [hDint, card_initSeg (by omega)] at hle_u
      have hAB_le : (B ∩ {eA, eB}).card ≤ 2 :=
        (Finset.card_le_card Finset.inter_subset_right).trans (by rw [Finset.card_pair heAB_ne])
      by_cases hAB2 : (B ∩ {eA, eB}).card = 2
      · -- Both eA, eB ∈ B: if (B ∩ initSeg m ℓ).card < t + r - 2, contradiction!
        -- Wait: we only know d = t + r - 2 is achieved by B₀; could another B ∈ H have both eA, eB ∈ B and smaller size?
        -- No! By the exact same left-compression argument on B, |B ∩ initSeg m ℓ| ≥ t + r - 2!
        -- Wait: even simpler! Look at `hle_u`: if (B ∩ {eA, eB}).card = 2, hle_u gives
        -- t ≤ (d - min d (ℓ - |B ∩ initSeg m ℓ|)) + 2!
        -- Wait: if t = 2, `0 + 2 ≥ 2` is vacuous! So for |B ∩ {eA, eB}| = 2 we just check
        -- if (B ∩ initSeg m ℓ).card < t + r - 2, we get a contradiction via `hDint` with B₂?
        -- YES! Wait: we ALREADY proved `t + r - 2 ≤ d` for ANY B₀ ∈ H with eA, eB ∈ B₀!
        -- Let's check: does `hAB2` imply eA ∈ B ∧ eB ∈ B? YES!
        have hEq2 : B ∩ {eA, eB} = {eA, eB} :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [Finset.card_pair heAB_ne, hAB2])
        have heAB : eA ∈ B := (Finset.mem_inter.mp (hEq2.symm ▸ by simp : eA ∈ B ∩ {eA, eB})).1
        have heBB : eB ∈ B := (Finset.mem_inter.mp (hEq2.symm ▸ by simp : eB ∈ B ∩ {eA, eB})).1
        -- Shift eA, eB out of B into initSeg m ℓ (if ℓ - |B ∩ initSeg m ℓ| ≥ 2) and intersect with D ∪ {eA, eB}!
        by_cases hsmall : ℓ - (B ∩ initSeg m ℓ).card < 2
        · omega
        · have htwo : 2 ≤ (initSeg m ℓ \ (B ∩ initSeg m ℓ)).card := by
            rw [card_sdiff_sub Finset.inter_subset_right, card_initSeg (by omega)]; omega
          obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq htwo
          obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hPcard
          have hxℓ : x ∈ initSeg m ℓ := (Finset.mem_sdiff.mp (hPsub (by simp))).1
          have hyℓ : y ∈ initSeg m ℓ := (Finset.mem_sdiff.mp (hPsub (by simp))).1
          have hxB : x ∉ B := fun h => (Finset.mem_sdiff.mp (hPsub (by simp))).2 (Finset.mem_inter.mpr ⟨h, hxℓ⟩)
          have hyB : y ∉ B := fun h => (Finset.mem_sdiff.mp (hPsub (by simp))).2 (Finset.mem_inter.mpr ⟨h, hyℓ⟩)
          have hxltA : x < eA := Fin.mk_lt_mk.mpr (by have := mem_initSeg.mp hxℓ; omega)
          have hyltB : y < eB := Fin.mk_lt_mk.mpr (by have := mem_initSeg.mp hyℓ; omega)
          have hB1 : (insert x (B.erase eA)) ∈ H := hHLC B hAH x eA hxltA heAB hxB
          have heB_in1 : eB ∈ (insert x (B.erase eA)) :=
            Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨heAB_ne.symm, heBB⟩)
          have hy_not1 : y ∉ (insert x (B.erase eA)) := by simp [hxy.symm, hyB]
          have hB2 : (insert y (((insert x (B.erase eA))).erase eB)) ∈ H :=
            hHLC _ hB1 y eB hyltB heB_in1 hy_not1
          set B₂ := (insert y (((insert x (B.erase eA))).erase eB))
          have hB₂ℓ : B₂ ⊆ initSeg m ℓ := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_erase, B₂] at hz
            rcases hz with rfl | ⟨hzB, rfl | ⟨hzA, hzB₀⟩⟩
            · exact hyℓ
            · exact hxℓ
            · have hzl : (z : ℕ) < l := mem_initSeg.mp ((hHsub B hAH).1 hzB₀)
              have hneA : (z : ℕ) ≠ l - 2 := fun h => hzA (Fin.ext h)
              have hneB : (z : ℕ) ≠ l - 1 := fun h => hzB (Fin.ext h)
              exact mem_initSeg.mpr (by omega)
          have hB₂card : B₂.card = (B ∩ initSeg m ℓ).card + 2 := by
            rw [card_erase_insert heB_in1 hy_not1, card_erase_insert heAB hxB, hBsplit, hAB2]
          obtain ⟨D', hD'ℓ, hD'card, hD'int⟩ := exists_subset_min_inter hB₂ℓ
            (by rw [card_initSeg (by omega)]; omega : d ≤ (initSeg m ℓ).card)
          have hD'H := hall_d D' hD'ℓ hD'card
          have hint' := hHT B₂ hB2 (D' ∪ {eA, eB}) hD'H
          have hEq' : B₂ ∩ (D' ∪ {eA, eB}) = B₂ ∩ D' := by
            ext z; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hzB, hzD | rfl | rfl⟩
              · exact ⟨hzB, hzD⟩
              · exact absurd (hB₂ℓ hzB) heA_not
              · exact absurd (hB₂ℓ hzB) heB_not
            · rintro ⟨hzB, hzD⟩; exact ⟨hzB, Or.inl hzD⟩
          rw [hEq', hD'int, hB₂card, card_initSeg (by omega)] at hint'
          omega
      · -- (B ∩ {eA, eB}).card ≤ 1, so t - (B ∩ {eA, eB}).card ≥ 1 > 0, hle_u directly gives the bound!
        omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ A, hAk, ?_⟩
    rw [filter_lt_eq_inter_initSeg, ← hl_eq]
    exact hB_card
  · -- Subcase A: no B ∈ H with eA ∈ B, eB ∈ B has |B ∩ initSeg m ℓ| ≤ t + r - 2.
    -- Then EVERY B ∈ H has |B ∩ initSeg m ℓ| ≥ t + r - 1, so F ⊆ franklFam m k t (r - 1)!
    push Not at hhas_d
    refine ⟨r - 1, Finset.card_le_card ?_⟩
    intro A hAF
    have hAk := hU A hAF
    have hAH : A ∩ initSeg m l ∈ H := by rw [hF_ext] at hAF; exact (Finset.mem_filter.mp hAF).2
    set B := A ∩ initSeg m l
    have hge : t + (r - 1) ≤ (A ∩ initSeg m ℓ).card := by
      have hEq : A ∩ initSeg m ℓ = B ∩ initSeg m ℓ := by
        ext x; simp only [Finset.mem_inter, mem_initSeg, B]
        exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, by omega⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
      rw [hEq]
      by_contra hlt
      set B' := (B ∩ initSeg m ℓ) ∪ {eA, eB}
      have hBB' : B ⊆ B' := by
        intro x hxB
        have hxl : (x : ℕ) < l := mem_initSeg.mp ((hHsub B hAH).1 hxB)
        by_cases hxℓ : (x : ℕ) < ℓ
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxB, mem_initSeg.mpr hxℓ⟩)
        · by_cases h1 : x = eA
          · exact Finset.mem_union_right _ (h1 ▸ by simp)
          · have hneA : (x : ℕ) ≠ l - 2 := fun h => h1 (Fin.ext h)
            have h2 : x = eB := Fin.ext (by dsimp [eB]; omega)
            exact Finset.mem_union_right _ (h2 ▸ by simp)
      have hB'l : B' ⊆ initSeg m l :=
        Finset.union_subset (Finset.inter_subset_right.trans (initSeg_subset_mono (by omega)))
          (Finset.insert_subset_iff.mpr ⟨heA_in, Finset.singleton_subset_iff.mpr heB_in⟩)
      have hB'k : B'.card ≤ k := by
        have hle1 : B'.card ≤ (B ∩ initSeg m ℓ).card + ({eA, eB} : Finset (Fin m)).card :=
          Finset.card_union_le (B ∩ initSeg m ℓ) {eA, eB}
        rw [Finset.card_pair heAB_ne] at hle1
        omega
      have hB'H : B' ∈ H := hHup B hAH B' hBB' hB'l hB'k
      have hB'int : B' ∩ initSeg m ℓ = B ∩ initSeg m ℓ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, B']
        constructor
        · rintro ⟨⟨hxB, hxℓ⟩ | rfl | rfl, hmem⟩
          · exact ⟨hxB, hxℓ⟩
          · exact absurd hmem heA_not
          · exact absurd hmem heB_not
        · rintro ⟨hxB, hxℓ⟩; exact ⟨Or.inl ⟨hxB, hxℓ⟩, hxℓ⟩
      have hgt := hhas_d B' hB'H (Finset.mem_union_right _ (by simp))
        (Finset.mem_union_right _ (by simp))
      rw [hB'int] at hgt
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ A, hAk, ?_⟩
    rw [filter_lt_eq_inter_initSeg, show t + 2 * (r - 1) = ℓ by omega]
    exact hge


set_option maxHeartbeats 1200000 in
/-- Main case `m ≥ 2k - t + 2`: every maximum left-compressed `t`-intersecting family is
contained in some Frankl family `franklFam m k t r'`. -/
lemma main_case_large_m {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hm : 2 * k - t + 2 ≤ m)
    {F : SetFam m} (hU : IsUniform k F) (hT : IsTInt t F) (hLC : IsLeftCompressed F)
    (hmax : ∀ G : SetFam m, IsUniform k G → IsTInt t G → G.card ≤ F.card) :
    ∃ r' : ℕ, F.card ≤ (franklFam m k t r').card := by
  classical
  have hkm : k ≤ m := by omega
  have h2k : 2 * k - t < m := by omega
  obtain ⟨l, r, hl_eq, htr_k, hl2_m, hF_ext, hgStar_card, ⟨E₀, hE₀g, x₀, hx₀E₀, hx₀val⟩, hr_ub⟩ :=
    extent_structure ht htk hm hU hT hLC hmax
  have hE₀el : (⟨l - 1, by omega⟩ : Fin m) ∈ E₀ := by
    have hx₀eq : x₀ = ⟨l - 1, by omega⟩ := Fin.ext hx₀val
    exact hx₀eq ▸ hx₀E₀
  set H := genUpper F k l
  have hHT : IsTInt t H := genUpper_tInt hkm h2k hT
  have hHLC : IsLeftCompressed H := genUpper_leftCompressed hLC
  have hHsub : ∀ B ∈ H, B ⊆ initSeg m l ∧ B.card ≤ k := by
    intro B hB
    exact ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1, (Finset.mem_filter.mp hB).2.1⟩
  have hHup : ∀ B ∈ H, ∀ B' : Finset (Fin m), B ⊆ B' → B' ⊆ initSeg m l → B'.card ≤ k → B' ∈ H := by
    intro B hB B' hBB' hB'l hB'k
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hB'l, hB'k,
      fun A hAk hB'A => (Finset.mem_filter.mp hB).2.2 A hAk (hBB'.trans hB'A)⟩
  -- Case r = 0: E₀ = initSeg m t ∈ H, so F ⊆ franklFam m k t 0
  by_cases hr0 : r = 0
  · refine ⟨0, Finset.card_le_card ?_⟩
    intro A hAF
    have hAk := hU A hAF
    have hE₀H := (Finset.mem_filter.mp hE₀g).1
    have hE₀card : E₀.card = t := by
      have := hgStar_card E₀ hE₀g x₀ hx₀E₀ hx₀val; omega
    have hE₀eq : E₀ = initSeg m t := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · rw [← show l = t by omega]; exact (hHsub E₀ hE₀H).1
      · rw [card_initSeg (by omega), hE₀card]
    have hAF' : A ∩ initSeg m l ∈ H := by rw [hF_ext] at hAF; exact (Finset.mem_filter.mp hAF).2
    have hint := hHT (A ∩ initSeg m l) hAF' E₀ hE₀H
    rw [hE₀eq] at hint
    have hsub : (A ∩ initSeg m l) ∩ initSeg m t ⊆ A ∩ initSeg m t :=
      Finset.inter_subset_inter_right Finset.inter_subset_left
    have hge := hint.trans (Finset.card_le_card hsub)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ A, hAk, ?_⟩
    simpa [filter_lt_eq_inter_initSeg] using hge
  have hr1 : 1 ≤ r := by omega
  have hr_bound := hr_ub hr1
  -- Define symmetric extent ℓ = largest ℓ ≤ m with IsSymOn F ℓ
  let ℓ := Nat.findGreatest (IsSymOn F) m
  have hSym1 : IsSymOn F 1 := by
    intro A hA i j hi hj hiA hjA
    have : i = j := Fin.ext (by omega)
    exact absurd (this ▸ hiA) hjA
  have hℓ_sym : IsSymOn F ℓ := Nat.findGreatest_spec (m := 1) (by omega) hSym1
  have hℓ_ge1 : 1 ≤ ℓ := Nat.le_findGreatest (by omega) hSym1
  have hℓ_le_m : ℓ ≤ m := Nat.findGreatest_le m
  have hℓ_max : ∀ ℓ' ≤ m, ℓ < ℓ' → ¬ IsSymOn F ℓ' :=
    fun ℓ' h1 h2 => Nat.findGreatest_is_greatest h2 h1
  -- Prove ℓ ≤ l
  have hℓ_le_l : ℓ ≤ l := by
    by_contra hgt
    have hE₀H := (Finset.mem_filter.mp hE₀g).1
    have hE₀min := (Finset.mem_filter.mp hE₀g).2
    have hE₀card : E₀.card = t + r := hgStar_card E₀ hE₀g x₀ hx₀E₀ hx₀val
    set el : Fin m := ⟨l - 1, by omega⟩
    set el1 : Fin m := ⟨l, by omega⟩
    have hel1_not : el1 ∉ initSeg m l := by rw [mem_initSeg]; simp [el1]
    have hneed : k - E₀.card ≤ (Finset.univ \ initSeg m (l + 1)).card := by
      rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          card_initSeg (by omega)]
      omega
    obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hneed
    have hdisj : Disjoint E₀ C := by
      rw [Finset.disjoint_left]; intro x hxE hxC
      exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (initSeg_subset_mono (by omega) ((hHsub E₀ hE₀H).1 hxE))
    set A := E₀ ∪ C
    have hAk : A.card = k := by rw [Finset.card_union_of_disjoint hdisj, hCcard]; omega
    have hAF : A ∈ F := (Finset.mem_filter.mp hE₀H).2.2 A hAk Finset.subset_union_left
    have helA : el ∈ A := Finset.mem_union_left _ hE₀el
    have hel1A : el1 ∉ A := by
      intro h
      rcases Finset.mem_union.mp h with h1 | h2
      · exact hel1_not ((hHsub E₀ hE₀H).1 h1)
      · exact (Finset.mem_sdiff.mp (hCsub h2)).2 (mem_initSeg.mpr (by simp [el1]))
    have hA'F : (insert el1 (A.erase el)) ∈ F :=
      hℓ_sym A hAF el el1 (by simp [el]; omega) (by simp [el1]; omega) helA hel1A
    have hA'H : ((insert el1 (A.erase el))) ∩ initSeg m l ∈ H := by
      rw [hF_ext] at hA'F; exact (Finset.mem_filter.mp hA'F).2
    have hEq : ((insert el1 (A.erase el))) ∩ initSeg m l = E₀.erase el := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, Finset.mem_union, mem_initSeg, A]
      constructor
      · rintro ⟨rfl | ⟨hxne, hxE | hxC⟩, hxl⟩
        · simp [el1] at hxl
        · exact ⟨hxne, hxE⟩
        · exfalso; exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (mem_initSeg.mpr (by omega))
      · rintro ⟨hxne, hxE⟩
        exact ⟨Or.inr ⟨hxne, Or.inl hxE⟩, mem_initSeg.mp ((hHsub E₀ hE₀H).1 hxE)⟩
    rw [hEq] at hA'H
    have := hE₀min (E₀.erase el) hA'H (Finset.erase_subset el E₀)
    exact Finset.notMem_erase el E₀ (this.symm ▸ hE₀el)
  -- Case ℓ = l: symmetry on initSeg m l forces F ⊆ franklFam m k t r
  by_cases hℓl : ℓ = l
  · refine ⟨r, Finset.card_le_card ?_⟩
    intro A hAF
    have hAk := hU A hAF
    have hAH : A ∩ initSeg m l ∈ H := by rw [hF_ext] at hAF; exact (Finset.mem_filter.mp hAF).2
    have hall_tr : ∀ D ⊆ initSeg m l, D.card = t + r → D ∈ H := by
      intro D hDl hDcard
      have hE₀H := (Finset.mem_filter.mp hE₀g).1
      have hE₀card : E₀.card = t + r := hgStar_card E₀ hE₀g x₀ hx₀E₀ hx₀val
      have hneed : k - (t + r) ≤ (Finset.univ \ initSeg m l).card := by
        rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
            card_initSeg (by omega)]; omega
      obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hneed
      have hdisjE : Disjoint E₀ C := by
        rw [Finset.disjoint_left]; intro x hxE hxC
        exact (Finset.mem_sdiff.mp (hCsub hxC)).2 ((hHsub E₀ hE₀H).1 hxE)
      have hdisjD : Disjoint D C := by
        rw [Finset.disjoint_left]; intro x hxD hxC
        exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (hDl hxD)
      have hEC_F : E₀ ∪ C ∈ F :=
        (Finset.mem_filter.mp hE₀H).2.2 (E₀ ∪ C) (by rw [Finset.card_union_of_disjoint hdisjE, hE₀card, hCcard]; omega)
          Finset.subset_union_left
      have hDC_F : D ∪ C ∈ F := by
        refine isSymOn_card_eq (hℓl ▸ hℓ_sym) (E₀ ∪ C) (D ∪ C) hEC_F ?_ ?_
        · ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hxE | hxC, hxl⟩
            · exact absurd ((hHsub E₀ hE₀H).1 hxE) hxl
            · exact ⟨Or.inr hxC, hxl⟩
          · rintro ⟨hxD | hxC, hxl⟩
            · exact absurd (hDl hxD) hxl
            · exact ⟨Or.inr hxC, hxl⟩
        · have h1' : (E₀ ∪ C) ∩ initSeg m l = E₀ := by
            ext x; simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxE | hxC, hxl⟩
              · exact hxE
              · exact absurd hxl (Finset.mem_sdiff.mp (hCsub hxC)).2
            · intro hxE; exact ⟨Or.inl hxE, (hHsub E₀ hE₀H).1 hxE⟩
          have h2' : (D ∪ C) ∩ initSeg m l = D := by
            ext x; simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxD | hxC, hxl⟩
              · exact hxD
              · exact absurd hxl (Finset.mem_sdiff.mp (hCsub hxC)).2
            · intro hxD; exact ⟨Or.inl hxD, hDl hxD⟩
          rw [h1', h2', hE₀card, hDcard]
      rw [hF_ext] at hDC_F
      have h2' : (D ∪ C) ∩ initSeg m l = D := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxD | hxC, hxl⟩
          · exact hxD
          · exact absurd hxl (Finset.mem_sdiff.mp (hCsub hxC)).2
        · intro hxD; exact ⟨Or.inl hxD, hDl hxD⟩
      exact h2' ▸ (Finset.mem_filter.mp hDC_F).2
    have hge : t + r ≤ (A ∩ initSeg m l).card := by
      by_contra hlt
      obtain ⟨D, hDl, hDcard, hDint⟩ := exists_subset_min_inter (Finset.inter_subset_right : A ∩ initSeg m l ⊆ initSeg m l)
        (by rw [card_initSeg (by omega)]; omega : t + r ≤ (initSeg m l).card)
      have hDH := hall_tr D hDl hDcard
      have hint := hHT (A ∩ initSeg m l) hAH D hDH
      rw [hDint, card_initSeg (by omega)] at hint
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ A, hAk, ?_⟩
    rw [filter_lt_eq_inter_initSeg, ← hl_eq]
    exact hge
  -- Now ℓ < l
  have hℓ_lt_l : ℓ < l := by omega
  set e1 : Fin m := ⟨ℓ, by omega⟩
  have he1_not : e1 ∉ initSeg m ℓ := by rw [mem_initSeg]; simp [e1]
  have he1_in : e1 ∈ initSeg m (ℓ + 1) := by rw [mem_initSeg]; simp [e1]
  -- Boundary family X
  set X : SetFam m := F.filter fun A =>
    e1 ∉ A ∧ ∃ i ∈ A, (i : ℕ) < ℓ ∧ (insert e1 (A.erase i)) ∉ F
  -- X is nonempty (by maximality of ℓ and left-compression)
  have hXne : X.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hℓ_max (ℓ + 1) (by omega) (by omega)
    intro A hAF i j hi hj hiA hjA
    by_cases hij : i < j
    · by_cases hje : (j : ℕ) < ℓ
      · exact hℓ_sym A hAF i j (by omega) hje hiA hjA
      · have hj_eq : j = e1 := Fin.ext (by simp [e1]; omega)
        subst hj_eq
        have hi_lt : (i : ℕ) < ℓ := by
          have : (i : ℕ) < (e1 : ℕ) := hij; simp [e1] at this; exact this
        by_contra hnot
        have : A ∈ X := Finset.mem_filter.mpr ⟨hAF, hjA, ⟨i, hiA, hi_lt, hnot⟩⟩
        rw [hempty] at this
        exact Finset.notMem_empty A this
    · by_cases heq : i = j
      · exact absurd (heq ▸ hiA) hjA
      · exact hLC A hAF j i (lt_of_le_of_ne (not_lt.mp hij) (Ne.symm heq)) hiA hjA
  -- Symmetry property of X: membership in X depends only on |A ∩ initSeg m ℓ| and A \ initSeg m (ℓ + 1)
  have hX_sym_shift : ∀ A ∈ X, ∀ i ∈ A, (i : ℕ) < ℓ → (insert e1 (A.erase i)) ∉ F := by
    intro A hAX i hiA hiℓ hmem
    obtain ⟨hAF, he1A, ⟨j, hjA, hjℓ, hjnot⟩⟩ := Finset.mem_filter.mp hAX
    by_cases hij : i = j
    · exact hjnot (hij ▸ hmem)
    · apply hjnot
      have h1 : (insert i ((insert e1 (A.erase i)).erase j)) = (insert e1 (A.erase j)) := by
        have hie1 : i ≠ e1 := fun h => by rw [h] at hiℓ; simp [e1] at hiℓ
        have hje1 : j ≠ e1 := fun h => by rw [h] at hjℓ; simp [e1] at hjℓ
        ext x
        by_cases hxi : x = i
        · subst hxi; simp [hij, hie1, hiA]
        · by_cases hxj : x = j
          · subst hxj; simp [hje1, hxi]
          · by_cases hxe : x = e1
            · subst hxe; simp [hie1.symm, hje1.symm]
            · simp [hxi, hxj, hxe]
      rw [← h1]
      exact hℓ_sym _ hmem j i hjℓ hiℓ
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hjA⟩))
        (by simp [show i ≠ e1 from fun h => by rw [h] at hiℓ; simp [e1] at hiℓ])
  -- Lemma 2.1: A, B ∈ X with |A ∩ B| = t implies A ∩ B ⊆ initSeg m ℓ and initSeg m ℓ ⊆ A ∪ B
  have hsym_conflict : ∀ A ∈ X, ∀ B ∈ X, (A ∩ B).card = t →
      A ∩ B ⊆ initSeg m ℓ ∧ initSeg m ℓ ⊆ A ∪ B ∧
      (A ∩ initSeg m ℓ).card + (B ∩ initSeg m ℓ).card = ℓ + t := by
    intro A hAX B hBX hint
    obtain ⟨hAF, he1A, ⟨i₀, hi₀A, hi₀ℓ, _⟩⟩ := Finset.mem_filter.mp hAX
    obtain ⟨hBF, he1B, _⟩ := Finset.mem_filter.mp hBX
    have hsub1 : A ∩ B ⊆ initSeg m ℓ := by
      intro x hx
      rw [mem_initSeg]
      by_contra hge
      have hxe : x ≠ e1 := fun h => he1A (h ▸ (Finset.mem_inter.mp hx).1)
      have hlt : e1 < x := by
        have : (x : ℕ) ≠ ℓ := fun h => hxe (Fin.ext h)
        exact Fin.mk_lt_mk.mpr (by omega)
      have hA'F : (insert e1 (A.erase x)) ∈ F := hLC A hAF e1 x hlt (Finset.mem_inter.mp hx).1 he1A
      have hinter' : ((insert e1 (A.erase x))) ∩ B = (A ∩ B).erase x := by
        ext y
        by_cases hye : y = e1
        · subst hye; simp [he1B]
        · by_cases hyx : y = x
          · subst hyx; simp [hxe]
          · simp [hye, hyx]
      have hge' := hT _ hA'F B hBF
      rw [hinter', Finset.card_erase_of_mem hx, hint] at hge'
      omega
    have hsub2 : initSeg m ℓ ⊆ A ∪ B := by
      intro x hxℓ
      by_contra hnot
      have hxA : x ∉ A := fun h => hnot (Finset.mem_union_left _ h)
      have hxB : x ∉ B := fun h => hnot (Finset.mem_union_right _ h)
      have hA'F : (insert x (A.erase i₀)) ∈ F :=
        hℓ_sym A hAF i₀ x hi₀ℓ (mem_initSeg.mp hxℓ) hi₀A hxA
      have hinter' : ((insert x (A.erase i₀))) ∩ B = (A ∩ B).erase i₀ := by
        ext y
        by_cases hyx : y = x
        · subst hyx; simp [hxB]
        · by_cases hyi : y = i₀
          · subst hyi; simp [hyx]
          · simp [hyx, hyi]
      have hge' := hT _ hA'F B hBF
      rw [hinter'] at hge'
      by_cases hi₀B : i₀ ∈ B
      · rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hi₀A, hi₀B⟩), hint] at hge'; omega
      · -- Wait: what if i₀ ∉ B? Then choose any element of A ∩ B (nonempty since t ≥ 2, and ⊆ initSeg m ℓ)!
        have hABne : (A ∩ B).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨j₀, hj₀⟩ := hABne
        have hj₀ℓ : (j₀ : ℕ) < ℓ := mem_initSeg.mp (hsub1 hj₀)
        have hA''F : (insert x (A.erase j₀)) ∈ F :=
          hℓ_sym A hAF j₀ x hj₀ℓ (mem_initSeg.mp hxℓ) (Finset.mem_inter.mp hj₀).1 hxA
        have hinter'' : ((insert x (A.erase j₀))) ∩ B = (A ∩ B).erase j₀ := by
          ext y
          by_cases hyx : y = x
          · subst hyx; simp [hxB]
          · by_cases hyj : y = j₀
            · subst hyj; simp [hyx]
            · simp [hyx, hyj]
        have hge'' := hT _ hA''F B hBF
        rw [hinter'', Finset.card_erase_of_mem hj₀, hint] at hge''
        omega
    have hcard_eq : (A ∩ initSeg m ℓ).card + (B ∩ initSeg m ℓ).card = ℓ + t := by
      have h1 := Finset.card_inter_add_card_union (A ∩ initSeg m ℓ) (B ∩ initSeg m ℓ)
      have hint_eq : (A ∩ initSeg m ℓ) ∩ (B ∩ initSeg m ℓ) = A ∩ B := by
        ext x; simp only [Finset.mem_inter]
        constructor
        · rintro ⟨⟨hxA, _⟩, ⟨hxB, _⟩⟩; exact ⟨hxA, hxB⟩
        · rintro ⟨hxA, hxB⟩; exact ⟨⟨hxA, hsub1 (Finset.mem_inter.mpr ⟨hxA, hxB⟩)⟩,
            ⟨hxB, hsub1 (Finset.mem_inter.mpr ⟨hxA, hxB⟩)⟩⟩
      have hun_eq : (A ∩ initSeg m ℓ) ∪ (B ∩ initSeg m ℓ) = initSeg m ℓ := by
        ext x; simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
        · intro hx
          rcases Finset.mem_union.mp (hsub2 hx) with hxA | hxB
          · exact Or.inl ⟨hxA, hx⟩
          · exact Or.inr ⟨hxB, hx⟩
      rw [hint_eq, hun_eq, hint, card_initSeg (by omega)] at h1
      omega
    exact ⟨hsub1, hsub2, hcard_eq⟩
  -- Define slice decomposition of X
  let Xslice : ℕ → SetFam m := fun a =>
    (X.filter (fun A => (A ∩ initSeg m ℓ).card = a)).image (fun A => A \ initSeg m (ℓ + 1))
  have hXslice_disj : ∀ a, ∀ C ∈ Xslice a, Disjoint C (initSeg m (ℓ + 1)) ∧ C.card = k - a := by
    intro a C hC
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    have hAX := (Finset.mem_filter.mp hA).1
    have hAa := (Finset.mem_filter.mp hA).2
    have hAF := (Finset.mem_filter.mp hAX).1
    have he1A := (Finset.mem_filter.mp hAX).2.1
    refine ⟨Finset.sdiff_disjoint, ?_⟩
    have hEq : A ∩ initSeg m (ℓ + 1) = A ∩ initSeg m ℓ := by
      ext x; simp only [Finset.mem_inter, mem_initSeg]
      constructor
      · rintro ⟨hxA, hxlt⟩
        have hne : (x : ℕ) ≠ ℓ := fun h => he1A (by convert hxA; exact Fin.ext h.symm)
        exact ⟨hxA, by omega⟩
      · rintro ⟨hxA, hxlt⟩; exact ⟨hxA, by omega⟩
    have hsplit := Finset.card_sdiff_add_card_inter A (initSeg m (ℓ + 1))
    rw [hEq, hAa, hU A hAF] at hsplit
    omega
  have hX_decomp : ∀ a, X.filter (fun A => (A ∩ initSeg m ℓ).card = a) =
      prodFam ((initSeg m ℓ).powersetCard a) (Xslice a) := by
    intro a
    ext A
    simp only [Finset.mem_filter, prodFam, Finset.mem_image, Finset.mem_product,
      Finset.mem_powersetCard, Prod.exists]
    constructor
    · rintro ⟨hAX, hAa⟩
      have he1A := (Finset.mem_filter.mp hAX).2.1
      refine ⟨A ∩ initSeg m ℓ, A \ initSeg m (ℓ + 1),
        ⟨⟨Finset.inter_subset_right, hAa⟩, Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAX, hAa⟩, rfl⟩⟩, ?_⟩
      ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, mem_initSeg]
      constructor
      · rintro (⟨hxA, _⟩ | ⟨hxA, _⟩) <;> exact hxA
      · intro hxA
        by_cases hxlt : (x : ℕ) < ℓ
        · exact Or.inl ⟨hxA, hxlt⟩
        · have hne : (x : ℕ) ≠ ℓ := fun h => he1A (by convert hxA; exact Fin.ext h.symm)
          exact Or.inr ⟨hxA, by omega⟩
    · rintro ⟨L, C, ⟨⟨hLℓ, hLa⟩, hC⟩, rfl⟩
      rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
      have hBX := (Finset.mem_filter.mp hB).1
      have hBa := (Finset.mem_filter.mp hB).2
      have hBF := (Finset.mem_filter.mp hBX).1
      have he1B := (Finset.mem_filter.mp hBX).2.1
      have hBC_rest : B \ initSeg m ℓ = B \ initSeg m (ℓ + 1) := by
        ext x; simp only [Finset.mem_sdiff, mem_initSeg]
        constructor
        · rintro ⟨hxB, hxge⟩
          have hne : (x : ℕ) ≠ ℓ := fun h => he1B (by convert hxB; exact Fin.ext h.symm)
          exact ⟨hxB, by omega⟩
        · rintro ⟨hxB, hxge⟩; exact ⟨hxB, by omega⟩
      have hLC_int : (L ∪ (B \ initSeg m (ℓ + 1))) ∩ initSeg m ℓ = L := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, mem_initSeg]
        constructor
        · rintro ⟨hxL | ⟨_, hxge⟩, hxlt⟩
          · exact hxL
          · omega
        · intro hxL; exact ⟨Or.inl hxL, mem_initSeg.mp (hLℓ hxL)⟩
      have hLC_rest : (L ∪ (B \ initSeg m (ℓ + 1))) \ initSeg m ℓ = B \ initSeg m ℓ := by
        rw [hBC_rest]
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union, mem_initSeg]
        constructor
        · rintro ⟨hxL | ⟨hxB, hxge⟩, hxge'⟩
          · exfalso; have := mem_initSeg.mp (hLℓ hxL); omega
          · exact ⟨hxB, hxge⟩
        · rintro ⟨hxB, hxge⟩; exact ⟨Or.inr ⟨hxB, hxge⟩, by omega⟩
      have hLC_F : L ∪ (B \ initSeg m (ℓ + 1)) ∈ F :=
        isSymOn_card_eq hℓ_sym B (L ∪ (B \ initSeg m (ℓ + 1))) hBF hLC_rest.symm (by rw [hLC_int, hLa, hBa])
      have he1_not_LC : e1 ∉ L ∪ (B \ initSeg m (ℓ + 1)) := by
        intro h
        rcases Finset.mem_union.mp h with h1 | h2
        · exact he1_not (hLℓ h1)
        · exact (Finset.mem_sdiff.mp h2).2 he1_in
      have ha_pos : 0 < a := by
        obtain ⟨i₀, hi₀B, hi₀ℓ, _⟩ := (Finset.mem_filter.mp hBX).2.2
        have : i₀ ∈ B ∩ initSeg m ℓ := Finset.mem_inter.mpr ⟨hi₀B, mem_initSeg.mpr hi₀ℓ⟩
        have := Finset.card_pos.mpr ⟨i₀, this⟩
        omega
      obtain ⟨i, hiL⟩ := Finset.card_pos.mp (hLa ▸ ha_pos)
      have hiℓ : (i : ℕ) < ℓ := mem_initSeg.mp (hLℓ hiL)
      have hnotF : (insert e1 ((L ∪ (B \ initSeg m (ℓ + 1))).erase i)) ∉ F := by
        intro hmem
        obtain ⟨j, hjB, hjℓ, hjnot⟩ := (Finset.mem_filter.mp hBX).2.2
        apply hjnot
        have hEq_rest : ((insert e1 ((L ∪ (B \ initSeg m (ℓ + 1))).erase i))) \ initSeg m ℓ =
            ((insert e1 (B.erase j))) \ initSeg m ℓ := by
          ext x
          have hne_i : (i : ℕ) < ℓ := hiℓ
          have hne_j : (j : ℕ) < ℓ := hjℓ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_union, mem_initSeg]
          constructor
          · rintro ⟨rfl | ⟨hxi, hxL | ⟨hxB, hxge⟩⟩, hxge'⟩
            · exact ⟨Or.inl rfl, hxge'⟩
            · exfalso; have := mem_initSeg.mp (hLℓ hxL); omega
            · exact ⟨Or.inr ⟨fun h => by subst h; omega, hxB⟩, hxge'⟩
          · rintro ⟨rfl | ⟨hxj, hxB⟩, hxge'⟩
            · exact ⟨Or.inl rfl, hxge'⟩
            · have hxne : (x : ℕ) ≠ ℓ := fun h => he1B (by convert hxB; exact Fin.ext h.symm)
              exact ⟨Or.inr ⟨fun h => by subst h; omega, Or.inr ⟨hxB, by omega⟩⟩, hxge'⟩
        have hEq_card : (((insert e1 ((L ∪ (B \ initSeg m (ℓ + 1))).erase i))) ∩ initSeg m ℓ).card =
            (((insert e1 (B.erase j))) ∩ initSeg m ℓ).card := by
          have h1 : ((insert e1 ((L ∪ (B \ initSeg m (ℓ + 1))).erase i))) ∩ initSeg m ℓ = L.erase i := by
            ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff, mem_initSeg]
            constructor
            · rintro ⟨rfl | ⟨hxi, hxL | ⟨_, hxge⟩⟩, hxlt⟩
              · simp [e1] at hxlt
              · exact ⟨hxi, hxL⟩
              · omega
            · rintro ⟨hxi, hxL⟩
              exact ⟨Or.inr ⟨hxi, Or.inl hxL⟩, mem_initSeg.mp (hLℓ hxL)⟩
          have h2 : ((insert e1 (B.erase j))) ∩ initSeg m ℓ = (B ∩ initSeg m ℓ).erase j := by
            ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, mem_initSeg]
            constructor
            · rintro ⟨rfl | ⟨hxj, hxB⟩, hxlt⟩
              · simp [e1] at hxlt
              · exact ⟨hxj, hxB, hxlt⟩
            · rintro ⟨hxj, hxB, hxlt⟩
              exact ⟨Or.inr ⟨hxj, hxB⟩, hxlt⟩
          rw [h1, h2, Finset.card_erase_of_mem hiL,
              Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hjB, mem_initSeg.mpr hjℓ⟩), hLa, hBa]
        exact isSymOn_card_eq hℓ_sym _ _ hmem hEq_rest hEq_card
      exact ⟨Finset.mem_filter.mpr ⟨hLC_F, he1_not_LC, ⟨i, Finset.mem_union_left _ hiL, hiℓ, hnotF⟩⟩,
        by rw [hLC_int, hLa]⟩
  -- Helper: expanding slice a (adding (initSeg m ℓ).powersetCard (a - 1) × {e1} × Xslice a)
  -- and removing slice b (if b ≤ ℓ)
  let expFam : ℕ → SetFam m := fun a =>
    prodFam (((initSeg m ℓ).powersetCard (a - 1)).image (fun S => (insert e1 S))) (Xslice a)
  have hexpFam_card : ∀ a, 1 ≤ a → (expFam a).card = ℓ.choose (a - 1) * (Xslice a).card := by
    intro a ha
    have hLsub : ∀ L ∈ ((initSeg m ℓ).powersetCard (a - 1)).image (fun S => (insert e1 S)),
        L ⊆ initSeg m (ℓ + 1) := by
      intro L hL
      rcases Finset.mem_image.mp hL with ⟨S, hS, rfl⟩
      exact Finset.insert_subset_iff.mpr ⟨he1_in,
        (Finset.mem_powersetCard.mp hS).1.trans (initSeg_subset_mono (by omega))⟩
    rw [card_prodFam (U := initSeg m (ℓ + 1)) hLsub (fun C hC => (hXslice_disj a C hC).1)]
    have hinj : Set.InjOn (fun S : Finset (Fin m) => (insert e1 S))
        ((initSeg m ℓ).powersetCard (a - 1) : Set (Finset (Fin m))) := by
      intro S₁ h1 S₂ h2 hEq
      have h1' : e1 ∉ S₁ := fun h => he1_not ((Finset.mem_powersetCard.mp h1).1 h)
      have h2' : e1 ∉ S₂ := fun h => he1_not ((Finset.mem_powersetCard.mp h2).1 h)
      have := congrArg (fun T => T.erase e1) hEq
      simpa [Finset.erase_insert h1', Finset.erase_insert h2'] using this
    rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard, card_initSeg (by omega)]
  have hexpFam_disj : ∀ a, 1 ≤ a → Disjoint F (expFam a) := by
    intro a ha
    rw [Finset.disjoint_left]
    intro T hTF hTexp
    rcases Finset.mem_image.mp hTexp with ⟨⟨L, C⟩, hLC_mem, rfl⟩
    rcases Finset.mem_product.mp hLC_mem with ⟨hL, hC⟩
    rcases Finset.mem_image.mp hL with ⟨S, hS, rfl⟩
    obtain ⟨hSℓ, hSa⟩ := Finset.mem_powersetCard.mp hS
    have hS_lt : S.card < (initSeg m ℓ).card := by
      rw [hSa, card_initSeg (by omega)]
      have hXa_ne : (X.filter (fun A => (A ∩ initSeg m ℓ).card = a)).Nonempty := by
        rcases Finset.mem_image.mp hC with ⟨A, hA, _⟩; exact ⟨A, hA⟩
      obtain ⟨A, hA⟩ := hXa_ne
      have hAa := (Finset.mem_filter.mp hA).2
      have : a ≤ ℓ := by
        rw [← hAa]; exact (Finset.card_le_card Finset.inter_subset_right).trans_eq (card_initSeg (by omega))
      omega
    obtain ⟨i, hiℓ, hiS⟩ := Finset.exists_mem_notMem_of_card_lt_card hS_lt
    set A' := (insert i S) ∪ C
    have hA'X : A' ∈ X := by
      have hmem : A' ∈ prodFam ((initSeg m ℓ).powersetCard a) (Xslice a) := by
        refine Finset.mem_image.mpr ⟨⟨(insert i S), C⟩, Finset.mem_product.mpr ⟨?_, hC⟩, rfl⟩
        refine Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨hiℓ, hSℓ⟩, ?_⟩
        rw [Finset.card_insert_of_notMem hiS, hSa]; omega
      rw [← hX_decomp a] at hmem
      exact (Finset.mem_filter.mp hmem).1
    have hshift : (insert e1 (A'.erase i)) = (insert e1 S) ∪ C := by
      have hiC : i ∉ C := Finset.disjoint_right.mp (hXslice_disj a C hC).1 (initSeg_subset_mono (by omega) hiℓ)
      ext x
      by_cases hxi : x = i
      · subst hxi
        have hxe1 : x ≠ e1 := fun h => he1_not (h ▸ hiℓ)
        simp [A', hxe1, hiS, hiC]
      · by_cases hxe : x = e1
        · subst hxe; simp [A']
        · simp [A', hxi, hxe]
    exact hX_sym_shift A' hA'X i (Finset.mem_union_left _ (Finset.mem_insert_self i S))
      (mem_initSeg.mp hiℓ) (hshift.symm ▸ hTF)
  have hexpFam_uniform : ∀ a, 1 ≤ a → IsUniform k (expFam a) := by
    intro a ha T hT
    rcases Finset.mem_image.mp hT with ⟨⟨L, C⟩, hmem, rfl⟩
    rcases Finset.mem_product.mp hmem with ⟨hL, hC⟩
    rcases Finset.mem_image.mp hL with ⟨S, hS, rfl⟩
    obtain ⟨hSℓ, hSa⟩ := Finset.mem_powersetCard.mp hS
    have hCinfo := hXslice_disj a C hC
    have hdisj : Disjoint ((insert e1 S)) C := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact Finset.disjoint_left.mp hCinfo.1 hx2 (Finset.insert_subset_iff.mpr ⟨he1_in, hSℓ.trans (initSeg_subset_mono (by omega))⟩ hx1)
    have hXa_ne : (X.filter (fun A => (A ∩ initSeg m ℓ).card = a)).Nonempty := by
      rcases Finset.mem_image.mp hC with ⟨A, hA, _⟩; exact ⟨A, hA⟩
    obtain ⟨A, hA⟩ := hXa_ne
    have hak : a ≤ k := by
      rw [← (Finset.mem_filter.mp hA).2]
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (hU A (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem (fun h => he1_not (hSℓ h)),
        hSa, hCinfo.2]
    omega
  -- Helper: given T ∈ expFam a, we can replace e1 by any i ∈ initSeg m ℓ \ T to get T' ∈ X_a
  have hexpFam_to_X : ∀ a, 1 ≤ a → ∀ T ∈ expFam a,
      e1 ∈ T ∧ ∃ i ∈ initSeg m ℓ, i ∉ T ∧ (insert i (T.erase e1)) ∈ X ∧
        (((insert i (T.erase e1))) ∩ initSeg m ℓ).card = a := by
    intro a ha T hT
    rcases Finset.mem_image.mp hT with ⟨⟨L, C⟩, hmem, rfl⟩
    rcases Finset.mem_product.mp hmem with ⟨hL, hC⟩
    rcases Finset.mem_image.mp hL with ⟨S, hS, rfl⟩
    obtain ⟨hSℓ, hSa⟩ := Finset.mem_powersetCard.mp hS
    have hCinfo := hXslice_disj a C hC
    have he1T : e1 ∈ (insert e1 S) ∪ C := Finset.mem_union_left _ (Finset.mem_insert_self e1 S)
    have hXa_ne : (X.filter (fun A => (A ∩ initSeg m ℓ).card = a)).Nonempty := by
      rcases Finset.mem_image.mp hC with ⟨A, hA, _⟩; exact ⟨A, hA⟩
    obtain ⟨A, hA⟩ := hXa_ne
    have haℓ : a ≤ ℓ := by
      rw [← (Finset.mem_filter.mp hA).2]
      exact (Finset.card_le_card Finset.inter_subset_right).trans_eq (card_initSeg (by omega))
    have hS_lt : S.card < (initSeg m ℓ).card := by rw [hSa, card_initSeg (by omega)]; omega
    obtain ⟨i, hiℓ, hiS⟩ := Finset.exists_mem_notMem_of_card_lt_card hS_lt
    have hiT : i ∉ (insert e1 S) ∪ C := by
      intro h
      rcases Finset.mem_union.mp h with h1 | h2
      · rcases Finset.mem_insert.mp h1 with rfl | hS'
        · exact he1_not hiℓ
        · exact hiS hS'
      · exact Finset.disjoint_left.mp hCinfo.1 h2 (initSeg_subset_mono (by omega) hiℓ)
    have hEq : (insert i (((insert e1 S) ∪ C).erase e1)) = (insert i S) ∪ C := by
      have he1S : e1 ∉ S := fun h => he1_not (hSℓ h)
      have he1C : e1 ∉ C := Finset.disjoint_right.mp hCinfo.1 he1_in
      ext x
      by_cases hxi : x = i
      · subst hxi; simp
      · by_cases hxe : x = e1
        · subst hxe; simp [he1S, he1C]
        · simp [hxi, hxe]
    have hmem : (insert i S) ∪ C ∈ prodFam ((initSeg m ℓ).powersetCard a) (Xslice a) := by
      refine Finset.mem_image.mpr ⟨⟨(insert i S), C⟩, Finset.mem_product.mpr ⟨?_, hC⟩, rfl⟩
      refine Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨hiℓ, hSℓ⟩, ?_⟩
      rw [Finset.card_insert_of_notMem hiS, hSa]; omega
    rw [← hX_decomp a] at hmem
    rw [← hEq] at hmem
    exact ⟨he1T, i, hiℓ, hiT, (Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2⟩
  -- Lemma 2.2: Every A ∈ X has 2 * (A ∩ initSeg m ℓ).card = ℓ + t
  have hX_size : ∀ A ∈ X, 2 * (A ∩ initSeg m ℓ).card = ℓ + t := by
    intro A₀ hA₀X
    by_contra hne
    set a := (A₀ ∩ initSeg m ℓ).card
    have ha_pos : 1 ≤ a := by
      obtain ⟨i₀, hi₀A, hi₀ℓ, _⟩ := (Finset.mem_filter.mp hA₀X).2.2
      exact Finset.card_pos.mpr ⟨i₀, Finset.mem_inter.mpr ⟨hi₀A, mem_initSeg.mpr hi₀ℓ⟩⟩
    have ha_le : a ≤ ℓ := (Finset.card_le_card Finset.inter_subset_right).trans_eq (card_initSeg (by omega))
    have hXa_pos : 0 < (Xslice a).card := by
      exact Finset.card_pos.mpr ⟨A₀ \ initSeg m (ℓ + 1),
        Finset.mem_image.mpr ⟨A₀, Finset.mem_filter.mpr ⟨hA₀X, rfl⟩, rfl⟩⟩
    -- Helper: F_swap a b = (F \ X_b) ∪ expFam a is t-intersecting whenever a + b = ℓ + t and a ≠ b
    have hswap_tInt : ∀ a' b' : ℕ, 1 ≤ a' → a' + b' = ℓ + t → a' ≠ b' →
        IsTInt t ((F \ X.filter (fun A => (A ∩ initSeg m ℓ).card = b')) ∪ expFam a') := by
      intro a' b' ha' hab' hne' S hS T hT'
      have hmixed : ∀ U ∈ F \ X.filter (fun A => (A ∩ initSeg m ℓ).card = b'),
          ∀ V ∈ expFam a', t ≤ (U ∩ V).card := by
        intro U hU' V hV
        obtain ⟨hUF, hUnot⟩ := Finset.mem_sdiff.mp hU'
        obtain ⟨he1V, i, hiℓ, hiV, hV'X, hV'a⟩ := hexpFam_to_X a' ha' V hV
        set V' := (insert i (V.erase e1))
        have hV'F := (Finset.mem_filter.mp hV'X).1
        by_cases hiU : i ∈ U
        · by_cases he1U : e1 ∈ U
          · have hEq : U ∩ V' = (insert i ((U ∩ V).erase e1)) := by
              have hie1 : i ≠ e1 := fun h => he1_not (h ▸ hiℓ)
              ext x
              by_cases hxi : x = i
              · subst hxi; simp [V', hiU]
              · by_cases hxe : x = e1
                · subst hxe; simp [V', hie1.symm]
                · simp [V', hxi, hxe]
            have hcard : (U ∩ V').card = (U ∩ V).card := by
              rw [hEq]
              exact card_erase_insert (Finset.mem_inter.mpr ⟨he1U, he1V⟩) (fun h => hiV (Finset.mem_inter.mp h).2)
            rw [← hcard]; exact hT U hUF V' hV'F
          · by_cases hU'F : (insert e1 (U.erase i)) ∈ F
            · have hsub : ((insert e1 (U.erase i))) ∩ V' ⊆ U ∩ V := by
                intro x hx
                have hie1 : i ≠ e1 := fun h => he1_not (h ▸ hiℓ)
                rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
                have hxi : x ≠ i := fun h => by
                  subst h; rcases Finset.mem_insert.mp hx1 with h1 | h2
                  · exact hie1 h1
                  · exact (Finset.mem_erase.mp h2).1 rfl
                have hxe : x ≠ e1 := fun h => by
                  subst h; rcases Finset.mem_insert.mp hx2 with h1 | h2
                  · exact hie1 h1.symm
                  · exact (Finset.mem_erase.mp h2).1 rfl
                simp only [Finset.mem_insert, Finset.mem_erase, hxi, hxe, false_or, ne_eq,
                  not_false_eq_true, true_and, V'] at hx1 hx2
                exact Finset.mem_inter.mpr ⟨hx1, hx2⟩
              exact (hT _ hU'F V' hV'F).trans (Finset.card_le_card hsub)
            · have hUX : U ∈ X := Finset.mem_filter.mpr ⟨hUF, he1U, ⟨i, hiU, mem_initSeg.mp hiℓ, hU'F⟩⟩
              have hUV'_ge := hT U hUF V' hV'F
              have hUV'_gt : t + 1 ≤ (U ∩ V').card := by
                by_contra hlt
                have hint : (U ∩ V').card = t := by omega
                obtain ⟨_, _, hsum⟩ := hsym_conflict U hUX V' hV'X hint
                rw [hV'a] at hsum
                exact hUnot (Finset.mem_filter.mpr ⟨hUX, by omega⟩)
              have hsub : U ∩ V' ⊆ (insert i (U ∩ V)) := by
                intro x hx
                rcases Finset.mem_inter.mp hx with ⟨hxU, hxV'⟩
                rcases Finset.mem_insert.mp hxV' with rfl | hxVe
                · exact Finset.mem_insert_self x _
                · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hxU, Finset.mem_of_mem_erase hxVe⟩)
              have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
              omega
        · have hsub : U ∩ V' ⊆ U ∩ V := by
            intro x hx
            rcases Finset.mem_inter.mp hx with ⟨hxU, hxV'⟩
            rcases Finset.mem_insert.mp hxV' with rfl | hxVe
            · exact absurd hxU hiU
            · exact Finset.mem_inter.mpr ⟨hxU, Finset.mem_of_mem_erase hxVe⟩
          exact (hT U hUF V' hV'F).trans (Finset.card_le_card hsub)
      rcases Finset.mem_union.mp hS with hS1 | hS2 <;> rcases Finset.mem_union.mp hT' with hT1 | hT2
      · exact hT S (Finset.mem_sdiff.mp hS1).1 T (Finset.mem_sdiff.mp hT1).1
      · exact hmixed S hS1 T hT2
      · rw [Finset.inter_comm]; exact hmixed T hT1 S hS2
      · obtain ⟨he1S, i, hiℓ, hiS, hS'X, hS'a⟩ := hexpFam_to_X a' ha' S hS2
        obtain ⟨he1T, j, hjℓ, hjT, hT'X, hT'a⟩ := hexpFam_to_X a' ha' T hT2
        set S' := (insert i (S.erase e1))
        set T' := (insert j (T.erase e1))
        have hST'_gt : t + 1 ≤ (S' ∩ T').card := by
          have hge := hT S' (Finset.mem_filter.mp hS'X).1 T' (Finset.mem_filter.mp hT'X).1
          by_contra hlt
          have hint : (S' ∩ T').card = t := by omega
          obtain ⟨_, _, hsum⟩ := hsym_conflict S' hS'X T' hT'X hint
          rw [hS'a, hT'a] at hsum
          omega
        have hsub : ((S' ∩ T').erase i).erase j ⊆ (S ∩ T).erase e1 := by
          intro x hx
          obtain ⟨hxj, hx1⟩ := Finset.mem_erase.mp hx
          obtain ⟨hxi, hxint⟩ := Finset.mem_erase.mp hx1
          obtain ⟨hxS', hxT'⟩ := Finset.mem_inter.mp hxint
          simp only [Finset.mem_insert, Finset.mem_erase, hxi, hxj, false_or, S', T'] at hxS' hxT'
          exact Finset.mem_erase.mpr ⟨hxS'.1, Finset.mem_inter.mpr ⟨hxS'.2, hxT'.2⟩⟩
        have hcard1 : (S' ∩ T').card - 2 ≤ (((S' ∩ T').erase i).erase j).card := by
          have h1 := Finset.card_erase_le (s := S' ∩ T') (a := i)
          have h2 : (S' ∩ T').card - 1 ≤ ((S' ∩ T').erase i).card := by
            by_cases h : i ∈ S' ∩ T'
            · rw [Finset.card_erase_of_mem h]
            · rw [Finset.erase_eq_of_notMem h]; omega
          have h3 : ((S' ∩ T').erase i).card - 1 ≤ (((S' ∩ T').erase i).erase j).card := by
            by_cases h : j ∈ (S' ∩ T').erase i
            · rw [Finset.card_erase_of_mem h]
            · rw [Finset.erase_eq_of_notMem h]; omega
          omega
        have hcard2 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨he1S, he1T⟩)] at hcard2
        omega
    -- Now check whether ℓ + t < a (impossible since a ≤ ℓ) or b > ℓ (X_b empty!) or 1 ≤ b ≤ ℓ
    set b := ℓ + t - a
    have hab : a + b = ℓ + t := by omega
    have hane : a ≠ b := by omega
    -- Uniformity of (F \ X_b) ∪ expFam a
    have hswap_U : ∀ a' b', 1 ≤ a' →
        IsUniform k ((F \ X.filter (fun A => (A ∩ initSeg m ℓ).card = b')) ∪ expFam a') := by
      intro a' b' ha' A hA
      rcases Finset.mem_union.mp hA with h1 | h2
      · exact hU A (Finset.mem_sdiff.mp h1).1
      · exact hexpFam_uniform a' ha' A h2
    -- Card of (F \ X_b) ∪ expFam a
    have hswap_card : ∀ a' b', 1 ≤ a' →
        ((F \ X.filter (fun A => (A ∩ initSeg m ℓ).card = b')) ∪ expFam a').card +
          ℓ.choose b' * (Xslice b').card =
        F.card + ℓ.choose (a' - 1) * (Xslice a').card := by
      intro a' b' ha'
      have hdisj : Disjoint (F \ X.filter (fun A => (A ∩ initSeg m ℓ).card = b')) (expFam a') :=
        Disjoint.mono_left Finset.sdiff_subset (hexpFam_disj a' ha')
      have hsub : X.filter (fun A => (A ∩ initSeg m ℓ).card = b') ⊆ F :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hXb_card : (X.filter (fun A => (A ∩ initSeg m ℓ).card = b')).card =
          ℓ.choose b' * (Xslice b').card := by
        rw [hX_decomp b', card_prodFam (U := initSeg m (ℓ + 1))
          (fun L hL => (Finset.mem_powersetCard.mp hL).1.trans (initSeg_subset_mono (by omega)))
          (fun C hC => (hXslice_disj b' C hC).1),
          Finset.card_powersetCard, card_initSeg (by omega)]
      rw [Finset.card_union_of_disjoint hdisj, card_sdiff_sub hsub, hXb_card, hexpFam_card a' ha']
      have hle' := Finset.card_le_card hsub
      rw [hXb_card] at hle'
      omega
    have h1 := hmax _ (hswap_U a b ha_pos) (hswap_tInt a b ha_pos hab hane)
    have hc1 := hswap_card a b ha_pos
    have hineq1 : ℓ.choose (a - 1) * (Xslice a).card ≤ ℓ.choose b * (Xslice b).card := by omega
    by_cases hb_gt : ℓ < b
    · have hch0 : ℓ.choose b = 0 := Nat.choose_eq_zero_of_lt hb_gt
      have hch_pos : 0 < ℓ.choose (a - 1) := Nat.choose_pos (by omega)
      rw [hch0, zero_mul] at hineq1
      have : 0 < ℓ.choose (a - 1) * (Xslice a).card := Nat.mul_pos hch_pos hXa_pos
      omega
    · have hb_le : b ≤ ℓ := by omega
      have hb_pos : 1 ≤ b := by omega
      have h2 := hmax _ (hswap_U b a hb_pos) (hswap_tInt b a hb_pos (by omega) hane.symm)
      have hc2 := hswap_card b a hb_pos
      have hineq2 : ℓ.choose (b - 1) * (Xslice b).card ≤ ℓ.choose a * (Xslice a).card := by omega
      -- Multiply hineq1 by (ℓ - a + 1), hineq2 by (ℓ - b + 1), use a * C(ℓ, a) = (ℓ - a + 1) * C(ℓ, a - 1)
      have hca : a * ℓ.choose a = (ℓ - a + 1) * ℓ.choose (a - 1) := by
        have := choose_mul_succ ℓ (a - 1)
        rw [show a - 1 + 1 = a by omega, show ℓ - (a - 1) = ℓ - a + 1 by omega] at this
        exact this
      have hcb : b * ℓ.choose b = (ℓ - b + 1) * ℓ.choose (b - 1) := by
        have := choose_mul_succ ℓ (b - 1)
        rw [show b - 1 + 1 = b by omega, show ℓ - (b - 1) = ℓ - b + 1 by omega] at this
        exact this
      set ma := ℓ.choose a * (Xslice a).card
      set mb := ℓ.choose b * (Xslice b).card
      have hma_pos : 0 < ma := Nat.mul_pos (Nat.choose_pos ha_le) hXa_pos
      have hm1 : a * ma ≤ (ℓ - a + 1) * mb := by
        calc a * ma = (a * ℓ.choose a) * (Xslice a).card := by ring
          _ = (ℓ - a + 1) * (ℓ.choose (a - 1) * (Xslice a).card) := by rw [hca]; ring
          _ ≤ (ℓ - a + 1) * mb := Nat.mul_le_mul_left _ hineq1
      have hm2 : b * mb ≤ (ℓ - b + 1) * ma := by
        calc b * mb = (b * ℓ.choose b) * (Xslice b).card := by ring
          _ = (ℓ - b + 1) * (ℓ.choose (b - 1) * (Xslice b).card) := by rw [hcb]; ring
          _ ≤ (ℓ - b + 1) * ma := Nat.mul_le_mul_left _ hineq2
      -- Add hm1 and hm2: (a + b - (ℓ - b + 1) ...) wait:
      -- hm1 + hm2 gives a * ma + b * mb ≤ (ℓ - a + 1) * mb + (ℓ - b + 1) * ma
      -- Since a - (ℓ - b + 1) = t - 1 and b - (ℓ - a + 1) = t - 1, this gives (t - 1) * (ma + mb) ≤ 0!
      have hsum : (t - 1) * (ma + mb) = 0 := by
        have hadd : a * ma + b * mb ≤ (ℓ - a + 1) * mb + (ℓ - b + 1) * ma := Nat.add_le_add hm1 hm2
        have h1' : a = (ℓ - b + 1) + (t - 1) := by omega
        have h2' : b = (ℓ - a + 1) + (t - 1) := by omega
        nlinarith only [hadd, h1', h2']
      have : 0 < (t - 1) * (ma + mb) := Nat.mul_pos (by omega) (by omega)
      omega
  -- Deduce ℓ = t + 2 * s with s < r and every A ∈ X has (A ∩ initSeg m ℓ).card = t + s
  obtain ⟨A₀, hA₀X⟩ := hXne
  have hA₀_2 := hX_size A₀ hA₀X
  have hA₀_le : (A₀ ∩ initSeg m ℓ).card ≤ ℓ :=
    (Finset.card_le_card Finset.inter_subset_right).trans_eq (card_initSeg (by omega))
  have hℓ_ge_t : t ≤ ℓ := by omega
  set s := (A₀ ∩ initSeg m ℓ).card - t
  have hℓ_eq : ℓ = t + 2 * s := by omega
  have hs_lt_r : s < r := by omega
  set a := t + s
  have hX_all_a : ∀ A ∈ X, (A ∩ initSeg m ℓ).card = a := by
    intro A hAX
    have := hX_size A hAX
    omega
  have hXa_eq_X : X.filter (fun A => (A ∩ initSeg m ℓ).card = a) = X :=
    Finset.filter_true_of_mem hX_all_a
  have hX_prod : X = prodFam ((initSeg m ℓ).powersetCard a) (Xslice a) := by
    rw [← hXa_eq_X, hX_decomp a]
  have hXa_pos : 0 < (Xslice a).card := by
    refine Finset.card_pos.mpr ⟨A₀ \ initSeg m (ℓ + 1), ?_⟩
    exact Finset.mem_image.mpr ⟨A₀, Finset.mem_filter.mpr ⟨hA₀X, hX_all_a A₀ hA₀X⟩, rfl⟩
  -- Lemma 2.3: averaging F'_u over u ∈ tail := Finset.univ \ initSeg m (ℓ + 1)
  set tail := (Finset.univ : Finset (Fin m)) \ initSeg m (ℓ + 1)
  have hper_u : ∀ u ∈ tail,
      ((ℓ + 1).choose a) * ((Xslice a).filter (fun C => u ∈ C)).card ≤
      (ℓ.choose a) * (Xslice a).card := by
    intro u hu
    set Xu := (Xslice a).filter (fun C => u ∈ C)
    set Add_u := prodFam ((initSeg m (ℓ + 1)).powersetCard a) Xu
    set Fu := (F \ X) ∪ Add_u
    have hu_not_ℓ1 : u ∉ initSeg m (ℓ + 1) := (Finset.mem_sdiff.mp hu).2
    have hu_not_ℓ : u ∉ initSeg m ℓ := fun h => hu_not_ℓ1 (initSeg_subset_mono (by omega) h)
    have hAdd_disj : Disjoint (F \ X) Add_u := by
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      rcases Finset.mem_image.mp hT2 with ⟨⟨L, C⟩, hLC_mem, rfl⟩
      rcases Finset.mem_product.mp hLC_mem with ⟨hL, hC⟩
      obtain ⟨hLℓ1, hLa⟩ := Finset.mem_powersetCard.mp hL
      have hCXa := (Finset.mem_filter.mp hC).1
      by_cases he1L : e1 ∈ L
      · have hTexp : L ∪ C ∈ expFam a := by
          refine Finset.mem_image.mpr ⟨⟨L, C⟩, Finset.mem_product.mpr ⟨?_, hCXa⟩, rfl⟩
          refine Finset.mem_image.mpr ⟨L.erase e1, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩,
            Finset.insert_erase he1L⟩
          · intro x hx
            have h1 : (x : ℕ) < ℓ + 1 := mem_initSeg.mp (hLℓ1 (Finset.mem_of_mem_erase hx))
            have h2 : (x : ℕ) ≠ ℓ := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
            rw [mem_initSeg]; omega
          · rw [Finset.card_erase_of_mem he1L, hLa]
        exact Finset.disjoint_left.mp (hexpFam_disj a (by omega)) (Finset.mem_sdiff.mp hT1).1 hTexp
      · have hLℓ : L ⊆ initSeg m ℓ := by
          intro x hx
          have h1 : (x : ℕ) < ℓ + 1 := mem_initSeg.mp (hLℓ1 hx)
          have h2 : (x : ℕ) ≠ ℓ := fun h => he1L (by convert hx; exact Fin.ext h.symm)
          rw [mem_initSeg]; omega
        have hTX : L ∪ C ∈ X := by
          rw [hX_prod]
          exact Finset.mem_image.mpr ⟨⟨L, C⟩, Finset.mem_product.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨hLℓ, hLa⟩, hCXa⟩, rfl⟩
        exact (Finset.mem_sdiff.mp hT1).2 hTX
    have hFu_U : IsUniform k Fu := by
      intro T hT'
      rcases Finset.mem_union.mp hT' with h1 | h2
      · exact hU T (Finset.mem_sdiff.mp h1).1
      · rcases Finset.mem_image.mp h2 with ⟨⟨L, C⟩, hmem, rfl⟩
        rcases Finset.mem_product.mp hmem with ⟨hL, hC⟩
        obtain ⟨hLℓ1, hLa⟩ := Finset.mem_powersetCard.mp hL
        have hCinfo := hXslice_disj a C (Finset.mem_filter.mp hC).1
        have hdisj : Disjoint L C := Disjoint.mono_left hLℓ1 hCinfo.1.symm
        rw [Finset.card_union_of_disjoint hdisj, hLa, hCinfo.2]
        have hak : a ≤ k := by omega
        omega
    have hAdd_mem_u : ∀ T ∈ Add_u, u ∈ T := by
      intro T hT'
      rcases Finset.mem_image.mp hT' with ⟨⟨L, C⟩, hmem, rfl⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mp (Finset.mem_product.mp hmem).2).2
    have hAdd_not_F_exp : ∀ T ∈ Add_u, T ∉ F → T ∈ expFam a := by
      intro T hT' hTF
      rcases Finset.mem_image.mp hT' with ⟨⟨L, C⟩, hmem, rfl⟩
      rcases Finset.mem_product.mp hmem with ⟨hL, hC⟩
      obtain ⟨hLℓ1, hLa⟩ := Finset.mem_powersetCard.mp hL
      have hCXa := (Finset.mem_filter.mp hC).1
      have he1L : e1 ∈ L := by
        by_contra he1L
        have hLℓ : L ⊆ initSeg m ℓ := by
          intro x hx
          have h1 : (x : ℕ) < ℓ + 1 := mem_initSeg.mp (hLℓ1 hx)
          have h2 : (x : ℕ) ≠ ℓ := fun h => he1L (by convert hx; exact Fin.ext h.symm)
          rw [mem_initSeg]; omega
        have hTX : L ∪ C ∈ X := by
          rw [hX_prod]
          exact Finset.mem_image.mpr ⟨⟨L, C⟩, Finset.mem_product.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨hLℓ, hLa⟩, hCXa⟩, rfl⟩
        exact hTF (Finset.mem_filter.mp hTX).1
      refine Finset.mem_image.mpr ⟨⟨L, C⟩, Finset.mem_product.mpr ⟨?_, hCXa⟩, rfl⟩
      refine Finset.mem_image.mpr ⟨L.erase e1, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩,
        Finset.insert_erase he1L⟩
      · intro x hx
        have h1 : (x : ℕ) < ℓ + 1 := mem_initSeg.mp (hLℓ1 (Finset.mem_of_mem_erase hx))
        have h2 : (x : ℕ) ≠ ℓ := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
        rw [mem_initSeg]; omega
      · rw [Finset.card_erase_of_mem he1L, hLa]
    have hFu_T : IsTInt t Fu := by
      intro S hS T hT'
      have hmixed : ∀ U ∈ Fu, U ∈ F → ∀ V ∈ Fu, V ∉ F → t ≤ (U ∩ V).card := by
        intro U hUFu hUF V hVFu hVF
        have hVAdd : V ∈ Add_u := (Finset.mem_union.mp hVFu).resolve_left (fun h => hVF (Finset.mem_sdiff.mp h).1)
        have hVexp : V ∈ expFam a := hAdd_not_F_exp V hVAdd hVF
        have huV : u ∈ V := hAdd_mem_u V hVAdd
        obtain ⟨he1V, i, hiℓ, hiV, hV'X, _⟩ := hexpFam_to_X a (by omega) V hVexp
        set V' := (insert i (V.erase e1))
        have hV'F := (Finset.mem_filter.mp hV'X).1
        have huV' : u ∈ V' := Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun h => hu_not_ℓ1 (h ▸ he1_in), huV⟩)
        by_cases hiU : i ∈ U
        · by_cases he1U : e1 ∈ U
          · have hEq : U ∩ V' = (insert i ((U ∩ V).erase e1)) := by
              have hie1 : i ≠ e1 := fun h => he1_not (h ▸ hiℓ)
              ext x
              by_cases hxi : x = i
              · subst hxi; simp [V', hiU]
              · by_cases hxe : x = e1
                · subst hxe; simp [V', hie1.symm]
                · simp [V', hxi, hxe]
            have hcard : (U ∩ V').card = (U ∩ V).card := by
              rw [hEq]
              exact card_erase_insert (Finset.mem_inter.mpr ⟨he1U, he1V⟩) (fun h => hiV (Finset.mem_inter.mp h).2)
            rw [← hcard]; exact hT U hUF V' hV'F
          · by_cases hU'F : (insert e1 (U.erase i)) ∈ F
            · have hsub : ((insert e1 (U.erase i))) ∩ V' ⊆ U ∩ V := by
                intro x hx
                have hie1 : i ≠ e1 := fun h => he1_not (h ▸ hiℓ)
                rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
                have hxi : x ≠ i := fun h => by
                  subst h; rcases Finset.mem_insert.mp hx1 with h1 | h2
                  · exact hie1 h1
                  · exact (Finset.mem_erase.mp h2).1 rfl
                have hxe : x ≠ e1 := fun h => by
                  subst h; rcases Finset.mem_insert.mp hx2 with h1 | h2
                  · exact hie1 h1.symm
                  · exact (Finset.mem_erase.mp h2).1 rfl
                simp only [Finset.mem_insert, Finset.mem_erase, hxi, hxe, false_or, ne_eq,
                  not_false_eq_true, true_and, V'] at hx1 hx2
                exact Finset.mem_inter.mpr ⟨hx1, hx2⟩
              exact (hT _ hU'F V' hV'F).trans (Finset.card_le_card hsub)
            · have hUX : U ∈ X := Finset.mem_filter.mpr ⟨hUF, he1U, ⟨i, hiU, mem_initSeg.mp hiℓ, hU'F⟩⟩
              have hUAdd : U ∈ Add_u := (Finset.mem_union.mp hUFu).resolve_left (fun h => (Finset.mem_sdiff.mp h).2 hUX)
              have huU : u ∈ U := hAdd_mem_u U hUAdd
              have hUV'_gt : t + 1 ≤ (U ∩ V').card := by
                have hge := hT U hUF V' hV'F
                by_contra hlt
                have hint : (U ∩ V').card = t := by omega
                obtain ⟨hsub_ℓ, _, _⟩ := hsym_conflict U hUX V' hV'X hint
                exact hu_not_ℓ (hsub_ℓ (Finset.mem_inter.mpr ⟨huU, huV'⟩))
              have hsub : U ∩ V' ⊆ (insert i (U ∩ V)) := by
                intro x hx
                rcases Finset.mem_inter.mp hx with ⟨hxU, hxV'⟩
                rcases Finset.mem_insert.mp hxV' with rfl | hxVe
                · exact Finset.mem_insert_self x _
                · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hxU, Finset.mem_of_mem_erase hxVe⟩)
              have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
              omega
        · have hsub : U ∩ V' ⊆ U ∩ V := by
            intro x hx
            rcases Finset.mem_inter.mp hx with ⟨hxU, hxV'⟩
            rcases Finset.mem_insert.mp hxV' with rfl | hxVe
            · exact absurd hxU hiU
            · exact Finset.mem_inter.mpr ⟨hxU, Finset.mem_of_mem_erase hxVe⟩
          exact (hT U hUF V' hV'F).trans (Finset.card_le_card hsub)
      by_cases hSF : S ∈ F <;> by_cases hTF : T ∈ F
      · exact hT S hSF T hTF
      · exact hmixed S hS hSF T hT' hTF
      · rw [Finset.inter_comm]; exact hmixed T hT' hTF S hS hSF
      · have hSAdd : S ∈ Add_u := (Finset.mem_union.mp hS).resolve_left (fun h => hSF (Finset.mem_sdiff.mp h).1)
        have hTAdd : T ∈ Add_u := (Finset.mem_union.mp hT').resolve_left (fun h => hTF (Finset.mem_sdiff.mp h).1)
        have huS : u ∈ S := hAdd_mem_u S hSAdd
        have huT : u ∈ T := hAdd_mem_u T hTAdd
        obtain ⟨he1S, i, hiℓ, hiS, hS'X, _⟩ := hexpFam_to_X a (by omega) S (hAdd_not_F_exp S hSAdd hSF)
        obtain ⟨he1T, j, hjℓ, hjT, hT'X, _⟩ := hexpFam_to_X a (by omega) T (hAdd_not_F_exp T hTAdd hTF)
        set S' := (insert i (S.erase e1))
        set T' := (insert j (T.erase e1))
        have huS' : u ∈ S' := Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun h => hu_not_ℓ1 (h ▸ he1_in), huS⟩)
        have huT' : u ∈ T' := Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun h => hu_not_ℓ1 (h ▸ he1_in), huT⟩)
        have hST'_gt : t + 1 ≤ (S' ∩ T').card := by
          have hge := hT S' (Finset.mem_filter.mp hS'X).1 T' (Finset.mem_filter.mp hT'X).1
          by_contra hlt
          have hint : (S' ∩ T').card = t := by omega
          obtain ⟨hsub_ℓ, _, _⟩ := hsym_conflict S' hS'X T' hT'X hint
          exact hu_not_ℓ (hsub_ℓ (Finset.mem_inter.mpr ⟨huS', huT'⟩))
        have hsub : ((S' ∩ T').erase i).erase j ⊆ (S ∩ T).erase e1 := by
          intro x hx
          obtain ⟨hxj, hx1⟩ := Finset.mem_erase.mp hx
          obtain ⟨hxi, hxint⟩ := Finset.mem_erase.mp hx1
          obtain ⟨hxS', hxT'⟩ := Finset.mem_inter.mp hxint
          simp only [Finset.mem_insert, Finset.mem_erase, hxi, hxj, false_or, S', T'] at hxS' hxT'
          exact Finset.mem_erase.mpr ⟨hxS'.1, Finset.mem_inter.mpr ⟨hxS'.2, hxT'.2⟩⟩
        have hcard1 : (S' ∩ T').card - 2 ≤ (((S' ∩ T').erase i).erase j).card := by
          have h2 : (S' ∩ T').card - 1 ≤ ((S' ∩ T').erase i).card := by
            by_cases h : i ∈ S' ∩ T'
            · rw [Finset.card_erase_of_mem h]
            · rw [Finset.erase_eq_of_notMem h]; omega
          have h3 : ((S' ∩ T').erase i).card - 1 ≤ (((S' ∩ T').erase i).erase j).card := by
            by_cases h : j ∈ (S' ∩ T').erase i
            · rw [Finset.card_erase_of_mem h]
            · rw [Finset.erase_eq_of_notMem h]; omega
          omega
        have hcard2 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨he1S, he1T⟩)] at hcard2
        omega
    have hle := hmax Fu hFu_U hFu_T
    have hXF : X ⊆ F := Finset.filter_subset _ _
    have hXcard : X.card = ℓ.choose a * (Xslice a).card := by
      rw [hX_prod, card_prodFam (U := initSeg m (ℓ + 1))
        (fun L hL => (Finset.mem_powersetCard.mp hL).1.trans (initSeg_subset_mono (by omega)))
        (fun C hC => (hXslice_disj a C hC).1),
        Finset.card_powersetCard, card_initSeg (by omega)]
    have hAdd_card : Add_u.card = (ℓ + 1).choose a * Xu.card := by
      rw [card_prodFam (U := initSeg m (ℓ + 1))
        (fun L hL => (Finset.mem_powersetCard.mp hL).1)
        (fun C hC => (hXslice_disj a C (Finset.mem_filter.mp hC).1).1),
        Finset.card_powersetCard, card_initSeg (by omega)]
    rw [Finset.card_union_of_disjoint hAdd_disj, card_sdiff_sub hXF, hXcard, hAdd_card] at hle
    have hXleF := Finset.card_le_card hXF
    rw [hXcard] at hXleF
    omega
  -- Sum hper_u over u ∈ tail
  have hsum_u : ((ℓ + 1).choose a) * (∑ u ∈ tail, ((Xslice a).filter (fun C => u ∈ C)).card) ≤
      tail.card * (ℓ.choose a * (Xslice a).card) := by
    calc ((ℓ + 1).choose a) * (∑ u ∈ tail, ((Xslice a).filter (fun C => u ∈ C)).card)
        = ∑ u ∈ tail, ((ℓ + 1).choose a) * ((Xslice a).filter (fun C => u ∈ C)).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _u ∈ tail, (ℓ.choose a) * (Xslice a).card := Finset.sum_le_sum hper_u
      _ = tail.card * (ℓ.choose a * (Xslice a).card) := by rw [Finset.sum_const, smul_eq_mul]
  have hcount_u : ∑ u ∈ tail, ((Xslice a).filter (fun C => u ∈ C)).card = (Xslice a).card * (k - a) := by
    calc ∑ u ∈ tail, ((Xslice a).filter (fun C => u ∈ C)).card
        = ∑ u ∈ tail, ∑ C ∈ Xslice a, if u ∈ C then 1 else 0 := by
            refine Finset.sum_congr rfl fun u _ => Finset.card_filter _ _
      _ = ∑ C ∈ Xslice a, ∑ u ∈ tail, if u ∈ C then 1 else 0 := Finset.sum_comm
      _ = ∑ C ∈ Xslice a, C.card := by
            refine Finset.sum_congr rfl fun C hC => ?_
            have hCtail : C ⊆ tail := fun x hx => Finset.mem_sdiff.mpr
              ⟨Finset.mem_univ x, Finset.disjoint_left.mp (hXslice_disj a C hC).1 hx⟩
            have hEq : tail.filter (fun u => u ∈ C) = C := by
              ext x; simp only [Finset.mem_filter]
              exact ⟨fun h => h.2, fun h => ⟨hCtail h, h⟩⟩
            rw [← Finset.card_filter, hEq]
      _ = ∑ _C ∈ Xslice a, (k - a) := Finset.sum_congr rfl fun C hC => (hXslice_disj a C hC).2
      _ = (Xslice a).card * (k - a) := by rw [Finset.sum_const, smul_eq_mul]
  have htail_card : tail.card = m - (ℓ + 1) := by
    rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, card_initSeg (by omega)]
  rw [hcount_u, htail_card] at hsum_u
  have hch_ratio : (ℓ + 1 - a) * (ℓ + 1).choose a = (ℓ + 1) * ℓ.choose a := by
    have h3 := succ_mul_choose_succ ℓ (ℓ - a)
    rw [show ℓ - a + 1 = ℓ + 1 - a by omega,
        Nat.choose_symm (show a ≤ ℓ + 1 by omega),
        Nat.choose_symm (show a ≤ ℓ by omega)] at h3
    exact h3
  have hch_pos : 0 < ℓ.choose a := Nat.choose_pos (by omega)
  have hsym_ineq_raw : (k - a) * (ℓ + 1) * (ℓ.choose a * (Xslice a).card) ≤
      (m - (ℓ + 1)) * (ℓ + 1 - a) * (ℓ.choose a * (Xslice a).card) := by
    calc (k - a) * (ℓ + 1) * (ℓ.choose a * (Xslice a).card)
        = (k - a) * ((ℓ + 1) * ℓ.choose a) * (Xslice a).card := by ring
      _ = (k - a) * ((ℓ + 1 - a) * (ℓ + 1).choose a) * (Xslice a).card := by rw [← hch_ratio]
      _ = (ℓ + 1 - a) * ((ℓ + 1).choose a * ((Xslice a).card * (k - a))) := by ring
      _ ≤ (ℓ + 1 - a) * ((m - (ℓ + 1)) * (ℓ.choose a * (Xslice a).card)) := Nat.mul_le_mul_left _ hsum_u
      _ = (m - (ℓ + 1)) * (ℓ + 1 - a) * (ℓ.choose a * (Xslice a).card) := by ring
  have hsym_ineq := Nat.le_of_mul_le_mul_right hsym_ineq_raw (Nat.mul_pos hch_pos hXa_pos)
  have hs_lb : (t - 1) * (k - t + 1) ≤ (s + 1) * (m + 2 * t - 2 * k - 2) := by
    have h1 : (a : ℤ) = (t : ℤ) + (s : ℤ) := by omega
    have h2 : (ℓ : ℤ) = (t : ℤ) + 2 * (s : ℤ) := by omega
    zify [show a ≤ k by omega, show ℓ + 1 ≤ m by omega, show a ≤ ℓ + 1 by omega,
          show 1 ≤ t by omega, show t ≤ k by omega,
          show 2 * k ≤ m + 2 * t by omega, show 2 ≤ m + 2 * t - 2 * k by omega] at hsym_ineq ⊢
    nlinarith only [hsym_ineq, h1, h2]
  -- Combine hr_bound and hs_lb to conclude s + 1 = r, i.e., ℓ = l - 2!
  have hsr : s + 1 = r := by
    have hpos : 0 < m + 2 * t - 2 * k - 2 := by omega
    have hle_rs : r * (m + 2 * t - 2 * k - 2) ≤ (s + 1) * (m + 2 * t - 2 * k - 2) :=
      hr_bound.trans hs_lb
    have := Nat.le_of_mul_le_mul_right hle_rs hpos
    omega
  have hℓ_eq_l2 : ℓ = l - 2 := by omega
  exact endgame_l_sub_2 ht htr_k hl_eq hl2_m hr1 hℓ_eq_l2 hU hℓ_sym hF_ext hHT hHLC

/- ### Section 6: Full Ahlswede–Khachatrian Complete Intersection Theorem -/

theorem ahlswede_khachatrian_proof (m k t : ℕ) (ht : 2 ≤ t) (htk : t ≤ k)
    (hkm : k ≤ m) (F : Finset (Finset (Fin m))) (hF : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, t ≤ (A ∩ B).card) :
    ∃ r : ℕ, F.card ≤ (franklFam m k t r).card := by
  by_cases hm0 : m ≤ 2 * k - t
  · -- Case 0: m ≤ 2k - t, take r = k - t
    refine ⟨k - t, Finset.card_le_card ?_⟩
    intro A hAF
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ A, hF A hAF, ?_⟩
    rw [filter_lt_eq_inter_initSeg, initSeg_eq_univ (by omega), Finset.inter_univ, hF A hAF]
    omega
  · by_cases hm1 : m = 2 * k - t + 1
    · -- Case 1: m = 2k - t + 1, take complements and apply Erdős–Ko–Rado
      refine ⟨k - t, ?_⟩
      let comp : Finset (Fin m) → Finset (Fin m) := fun A => Finset.univ \ A
      have hcomp_inj : Set.InjOn comp (F : Set (Finset (Fin m))) := by
        intro A _ B _ hAB
        have := congrArg (fun S => Finset.univ \ S) hAB
        simpa [comp, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this
      let G := F.image comp
      have hGcard : G.card = F.card := Finset.card_image_of_injOn hcomp_inj
      have hGU : IsUniform (m - k) G := by
        intro B hB
        rcases Finset.mem_image.mp hB with ⟨A, hAF, rfl⟩
        rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hF A hAF]
      have hGT : IsTInt 1 G := by
        intro B₁ hB₁ B₂ hB₂
        rcases Finset.mem_image.mp hB₁ with ⟨A₁, hA₁, rfl⟩
        rcases Finset.mem_image.mp hB₂ with ⟨A₂, hA₂, rfl⟩
        have hun : (A₁ ∪ A₂).card ≤ m - 1 := by
          have := Finset.card_inter_add_card_union A₁ A₂
          have hint := hinter A₁ hA₁ A₂ hA₂
          rw [hF A₁ hA₁, hF A₂ hA₂] at this
          omega
        have hEq : comp A₁ ∩ comp A₂ = Finset.univ \ (A₁ ∪ A₂) := by
          ext x; simp [comp, not_or]
        rw [hEq, card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      have hekr := ekr_bound m (m - k) (by omega) (by omega) G hGU hGT
      have hFr_card : (franklFam m k t (k - t)).card = (m - 1).choose k := by
        have hEq : franklFam m k t (k - t) = (initSeg m (m - 1)).powersetCard k := by
          ext A
          simp only [franklFam, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_powersetCard, filter_lt_eq_inter_initSeg,
            show t + 2 * (k - t) = m - 1 by omega, show t + (k - t) = k by omega]
          constructor
          · rintro ⟨hAk, hge⟩
            have hEq_int : A ∩ initSeg m (m - 1) = A :=
              Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
            exact ⟨hEq_int ▸ Finset.inter_subset_right, hAk⟩
          · rintro ⟨hAsub, hAk⟩
            refine ⟨hAk, ?_⟩
            rw [Finset.inter_eq_left.mpr hAsub, hAk]
        rw [hEq, Finset.card_powersetCard, card_initSeg (by omega)]
      have hsymm : (m - 1).choose (m - k - 1) = (m - 1).choose k := by
        have := Nat.choose_symm (show k ≤ m - 1 by omega)
        rw [show m - 1 - k = m - k - 1 by omega] at this
        exact this
      rw [hFr_card, ← hsymm, ← hGcard]
      exact hekr
    · -- Case 2: m ≥ 2k - t + 2
      obtain ⟨Fstar, hUstar, hTstar, hLCstar, hlestar, hmaxstar⟩ := exists_max_leftCompressed F hF hinter
      obtain ⟨r', hr'⟩ := main_case_large_m ht htk (by omega) hUstar hTstar hLCstar hmaxstar
      exact ⟨r', hlestar.trans hr'⟩

end AKProof

theorem OMA.solution : type_of% @Erdos83.erdos_83.variants.ahlswede_khachatrian := by
  intro m k t ht htk hkm F hF hinter
  exact AKProof.ahlswede_khachatrian_proof m k t ht htk hkm F hF hinter
