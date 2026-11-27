import FormalConjectures.ErdosProblems.«70»

/-!
# Erdős Problem 70: Erdős–Rado Theorem (`𝔠 → (ω + n, 4)³₂`)

Formal proof of Theorem 31 (equation 30) of Erdős and Rado (1956), *A partition calculus in set
theory*, Bull. Amer. Math. Soc. 62 (1956), 427–489: for every `n ≥ 2`, `RealCardinalRamsey3 (ω + n) 4`.
-/

namespace Erdos70ErdosRado

open Cardinal Ordinal Set

/- Section 1: Finite 2-color Ramsey for pairs and triples -/

private lemma ramsey2 : ∀ (a b : ℕ), ∃ N : ℕ,
    ∀ {α : Type*} [LinearOrder α] (S : Finset α) (c : α → α → Bool),
      N ≤ S.card →
      (∃ A ⊆ S, A.card = a ∧ ∀ x ∈ A, ∀ y ∈ A, x < y → c x y = false) ∨
      (∃ B ⊆ S, B.card = b ∧ ∀ x ∈ B, ∀ y ∈ B, x < y → c x y = true) := by
  intro a
  induction a with
  | zero =>
    intro b
    refine ⟨0, fun S _ _ ↦ Or.inl ⟨∅, Finset.empty_subset S, Finset.card_empty, ?_⟩⟩
    intro x hx
    exact (Finset.notMem_empty x hx).elim
  | succ a iha =>
    intro b
    induction b with
    | zero =>
      refine ⟨0, fun S _ _ ↦ Or.inr ⟨∅, Finset.empty_subset S, Finset.card_empty, ?_⟩⟩
      intro x hx
      exact (Finset.notMem_empty x hx).elim
    | succ b ihb =>
      obtain ⟨N₁, hN₁⟩ := iha (b + 1)
      obtain ⟨N₂, hN₂⟩ := ihb
      refine ⟨N₁ + N₂ + 1, fun {α} _ S c hcard ↦ ?_⟩
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      let v : α := S.min' hSne
      have hvS : v ∈ S := S.min'_mem hSne
      let S' : Finset α := S.erase v
      have hS'_card : N₁ + N₂ ≤ S'.card := by
        change N₁ + N₂ ≤ (S.erase v).card
        rw [Finset.card_erase_of_mem hvS]
        omega
      have hv_lt : ∀ x ∈ S', v < x := by
        intro x hx
        obtain ⟨hne, hxS⟩ := Finset.mem_erase.mp hx
        exact lt_of_le_of_ne (S.min'_le x hxS) hne.symm
      let L : Finset α := S'.filter (fun x ↦ c v x = false)
      let R : Finset α := S'.filter (fun x ↦ c v x = true)
      have hLR : S' ⊆ L ∪ R := by
        intro x hx
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        cases hcvx : c v x
        · exact Or.inl ⟨hx, rfl⟩
        · exact Or.inr ⟨hx, rfl⟩
      have hsum : S'.card ≤ L.card + R.card :=
        (Finset.card_le_card hLR).trans (Finset.card_union_le L R)
      rcases (by omega : N₁ ≤ L.card ∨ N₂ ≤ R.card) with hL | hR
      · rcases hN₁ L c hL with ⟨A, hAL, hAcard, hAcl⟩ | ⟨B, hBL, hBcard, hBcl⟩
        · left
          have hAS' : A ⊆ S' := hAL.trans (Finset.filter_subset _ _)
          have hvA : v ∉ A := fun hv ↦ (Finset.mem_erase.mp (hAS' hv)).1 rfl
          refine ⟨insert v A, Finset.insert_subset hvS (hAS'.trans (Finset.erase_subset _ _)),
            by rw [Finset.card_insert_of_notMem hvA, hAcard], ?_⟩
          intro x hx y hy hxy
          have hyv : y ≠ v := by
            intro rfl
            rcases Finset.mem_insert.mp hx with rfl | hxA
            · exact lt_irrefl _ hxy
            · exact lt_asymm hxy (hv_lt x (hAS' hxA))
          have hyA : y ∈ A := (Finset.mem_insert.mp hy).resolve_left hyv
          rcases Finset.mem_insert.mp hx with rfl | hxA
          · exact (Finset.mem_filter.mp (hAL hyA)).2
          · exact hAcl x hxA y hyA hxy
        · exact Or.inr ⟨B, hBL.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)),
            hBcard, hBcl⟩
      · rcases hN₂ R c hR with ⟨A, hAR, hAcard, hAcl⟩ | ⟨B, hBR, hBcard, hBcl⟩
        · exact Or.inl ⟨A, hAR.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)),
            hAcard, hAcl⟩
        · right
          have hBS' : B ⊆ S' := hBR.trans (Finset.filter_subset _ _)
          have hvB : v ∉ B := fun hv ↦ (Finset.mem_erase.mp (hBS' hv)).1 rfl
          refine ⟨insert v B, Finset.insert_subset hvS (hBS'.trans (Finset.erase_subset _ _)),
            by rw [Finset.card_insert_of_notMem hvB, hBcard], ?_⟩
          intro x hx y hy hxy
          have hyv : y ≠ v := by
            intro rfl
            rcases Finset.mem_insert.mp hx with rfl | hxB
            · exact lt_irrefl _ hxy
            · exact lt_asymm hxy (hv_lt x (hBS' hxB))
          have hyB : y ∈ B := (Finset.mem_insert.mp hy).resolve_left hyv
          rcases Finset.mem_insert.mp hx with rfl | hxB
          · exact (Finset.mem_filter.mp (hBR hyB)).2
          · exact hBcl x hxB y hyB hxy

private lemma ramsey3 : ∀ (a b : ℕ), ∃ N : ℕ,
    ∀ {α : Type*} [LinearOrder α] (S : Finset α) (c : α → α → α → Bool),
      N ≤ S.card →
      (∃ A ⊆ S, A.card = a ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x < y → y < z → c x y z = false) ∨
      (∃ B ⊆ S, B.card = b ∧ ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x < y → y < z → c x y z = true) := by
  intro a
  induction a with
  | zero =>
    intro b
    refine ⟨0, fun S _ _ ↦ Or.inl ⟨∅, Finset.empty_subset S, Finset.card_empty, ?_⟩⟩
    intro x hx
    exact (Finset.notMem_empty x hx).elim
  | succ a iha =>
    intro b
    induction b with
    | zero =>
      refine ⟨0, fun S _ _ ↦ Or.inr ⟨∅, Finset.empty_subset S, Finset.card_empty, ?_⟩⟩
      intro x hx
      exact (Finset.notMem_empty x hx).elim
    | succ b ihb =>
      obtain ⟨N₁, hN₁⟩ := iha (b + 1)
      obtain ⟨N₂, hN₂⟩ := ihb
      obtain ⟨M, hM⟩ := ramsey2 N₁ N₂
      refine ⟨M + 1, fun {α} _ S c hcard ↦ ?_⟩
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      let v : α := S.min' hSne
      have hvS : v ∈ S := S.min'_mem hSne
      let S' : Finset α := S.erase v
      have hS'_card : M ≤ S'.card := by
        change M ≤ (S.erase v).card
        rw [Finset.card_erase_of_mem hvS]
        omega
      have hv_lt : ∀ x ∈ S', v < x := by
        intro x hx
        obtain ⟨hne, hxS⟩ := Finset.mem_erase.mp hx
        exact lt_of_le_of_ne (S.min'_le x hxS) hne.symm
      rcases hM S' (fun x y ↦ c v x y) hS'_card with
          ⟨K₁, hK₁S', hK₁card, hK₁cl⟩ | ⟨K₂, hK₂S', hK₂card, hK₂cl⟩
      · rcases hN₁ K₁ c (by omega) with ⟨A, hAK₁, hAcard, hAcl⟩ | ⟨B, hBK₁, hBcard, hBcl⟩
        · left
          have hAS' : A ⊆ S' := hAK₁.trans hK₁S'
          have hvA : v ∉ A := fun hv ↦ (Finset.mem_erase.mp (hAS' hv)).1 rfl
          refine ⟨insert v A, Finset.insert_subset hvS (hAS'.trans (Finset.erase_subset _ _)),
            by rw [Finset.card_insert_of_notMem hvA, hAcard], ?_⟩
          intro x hx y hy z hz hxy hyz
          have hyv : y ≠ v := by
            intro rfl
            rcases Finset.mem_insert.mp hx with rfl | hxA
            · exact lt_irrefl _ hxy
            · exact lt_asymm hxy (hv_lt x (hAS' hxA))
          have hyA : y ∈ A := (Finset.mem_insert.mp hy).resolve_left hyv
          have hzv : z ≠ v := ne_of_gt ((hv_lt y (hAS' hyA)).trans hyz)
          have hzA : z ∈ A := (Finset.mem_insert.mp hz).resolve_left hzv
          rcases Finset.mem_insert.mp hx with rfl | hxA
          · exact hK₁cl y (hAK₁ hyA) z (hAK₁ hzA) hyz
          · exact hAcl x hxA y hyA z hzA hxy hyz
        · exact Or.inr ⟨B, hBK₁.trans (hK₁S'.trans (Finset.erase_subset _ _)), hBcard, hBcl⟩
      · rcases hN₂ K₂ c (by omega) with ⟨A, hAK₂, hAcard, hAcl⟩ | ⟨B, hBK₂, hBcard, hBcl⟩
        · exact Or.inl ⟨A, hAK₂.trans (hK₂S'.trans (Finset.erase_subset _ _)), hAcard, hAcl⟩
        · right
          have hBS' : B ⊆ S' := hBK₂.trans hK₂S'
          have hvB : v ∉ B := fun hv ↦ (Finset.mem_erase.mp (hBS' hv)).1 rfl
          refine ⟨insert v B, Finset.insert_subset hvS (hBS'.trans (Finset.erase_subset _ _)),
            by rw [Finset.card_insert_of_notMem hvB, hBcard], ?_⟩
          intro x hx y hy z hz hxy hyz
          have hyv : y ≠ v := by
            intro rfl
            rcases Finset.mem_insert.mp hx with rfl | hxB
            · exact lt_irrefl _ hxy
            · exact lt_asymm hxy (hv_lt x (hBS' hxB))
          have hyB : y ∈ B := (Finset.mem_insert.mp hy).resolve_left hyv
          have hzv : z ≠ v := ne_of_gt ((hv_lt y (hBS' hyB)).trans hyz)
          have hzB : z ∈ B := (Finset.mem_insert.mp hz).resolve_left hzv
          rcases Finset.mem_insert.mp hx with rfl | hxB
          · exact hK₂cl y (hBK₂ hyB) z (hBK₂ hzB) hyz
          · exact hBcl x hxB y hyB z hzB hxy hyz

/- Section 2: Infinite Ramsey on `ℕ` and `ω · p → (p, ω + m)²₂` -/

private lemma strictMono_of_infinite {S : Set ℕ} (hS : S.Infinite) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ k, g k ∈ S :=
  ⟨Nat.nth (· ∈ S), Nat.nth_strictMono hS, fun k ↦ Nat.nth_mem_of_infinite hS k⟩

private lemma infinite_gt_of_infinite {S : Set ℕ} (hS : S.Infinite) (x : ℕ) :
    {y ∈ S | x < y}.Infinite := by
  refine (hS.sdiff (Set.finite_le_nat x)).mono ?_
  intro y ⟨hyS, hynle⟩
  exact ⟨hyS, Nat.lt_of_not_ge hynle⟩

private lemma inf_pigeonhole_set {α : Type*} [Finite α] {S : Set ℕ} (hS : S.Infinite)
    (c : ℕ → α) : ∃ a : α, {n ∈ S | c n = a}.Infinite := by
  by_contra h
  have hfin : ∀ a : α, {n ∈ S | c n = a}.Finite := fun a ↦
    Set.not_infinite.mp (fun ha ↦ h ⟨a, ha⟩)
  exact hS ((Set.finite_iUnion hfin).subset fun n hn ↦ Set.mem_iUnion.mpr ⟨c n, hn, rfl⟩)

private lemma inf_ramsey1_finite {α : Type*} [Finite α] (c : ℕ → α) :
    ∃ (a : α) (ψ : ℕ → ℕ), StrictMono ψ ∧ ∀ i, c (ψ i) = a := by
  obtain ⟨a, ha⟩ := inf_pigeonhole_set Set.infinite_univ c
  obtain ⟨ψ, hψ_mono, hψ_mem⟩ := strictMono_of_infinite ha
  exact ⟨a, ψ, hψ_mono, fun i ↦ (hψ_mem i).2⟩

private lemma inf_ramsey2_finite {α : Type*} [Finite α] (c : ℕ → ℕ → α) :
    ∃ (a : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ i j, i < j → c (φ i) (φ j) = a := by
  let step : {S : Set ℕ // S.Infinite} → ℕ × α × {S : Set ℕ // S.Infinite} := fun S ↦
    let x := Classical.choose S.2.nonempty
    let hgt := infinite_gt_of_infinite S.2 x
    let hex := inf_pigeonhole_set hgt (c x)
    let a := Classical.choose hex
    (x, a, ⟨{y ∈ {y ∈ S.1 | x < y} | c x y = a}, Classical.choose_spec hex⟩)
  let seq : ℕ → {S : Set ℕ // S.Infinite} :=
    Nat.rec ⟨Set.univ, Set.infinite_univ⟩ (fun _ prev ↦ (step prev).2.2)
  have hsub_step : ∀ k, (seq (k + 1)).1 ⊆ (seq k).1 := by
    intro k y hy
    exact hy.1.1
  have hsub_le : ∀ {k l : ℕ}, k ≤ l → (seq l).1 ⊆ (seq k).1 := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact Subset.rfl
    | succ l _ ih => exact (hsub_step l).trans ih
  let x : ℕ → ℕ := fun k ↦ (step (seq k)).1
  let aseq : ℕ → α := fun k ↦ (step (seq k)).2.1
  have hx_mem : ∀ k, x k ∈ (seq k).1 := fun k ↦ Classical.choose_spec (seq k).2.nonempty
  have hrel : ∀ {k l : ℕ}, k < l → x k < x l ∧ c (x k) (x l) = aseq k := by
    intro k l hkl
    have hxl : x l ∈ (seq (k + 1)).1 := hsub_le (Nat.succ_le_of_lt hkl) (hx_mem l)
    exact ⟨hxl.1.2, hxl.2⟩
  obtain ⟨a, ψ, hψ_mono, hψ_eq⟩ := inf_ramsey1_finite aseq
  refine ⟨a, fun i ↦ x (ψ i), fun i j hij ↦ (hrel (hψ_mono hij)).1, ?_⟩
  intro i j hij
  exact (hrel (hψ_mono hij)).2.trans (hψ_eq i)

private lemma inf_ramsey3_bool (c : ℕ → ℕ → ℕ → Bool) :
    ∃ (b : Bool) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i j k, i < j → j < k → c (φ i) (φ j) (φ k) = b := by
  let step : {S : Set ℕ // S.Infinite} → ℕ × Bool × {S : Set ℕ // S.Infinite} := fun S ↦
    let x := Classical.choose S.2.nonempty
    let hgt := infinite_gt_of_infinite S.2 x
    let e : ℕ → ℕ := Nat.nth (· ∈ {y ∈ S.1 | x < y})
    let he_mono : StrictMono e := Nat.nth_strictMono hgt
    let hex := inf_ramsey2_finite (fun i j ↦ c x (e i) (e j))
    let b := Classical.choose hex
    let ψ := Classical.choose (Classical.choose_spec hex)
    let hψ := Classical.choose_spec (Classical.choose_spec hex)
    (x, b, ⟨Set.range (e ∘ ψ), Set.infinite_range_of_injective (he_mono.comp hψ.1).injective⟩)
  let seq : ℕ → {S : Set ℕ // S.Infinite} :=
    Nat.rec ⟨Set.univ, Set.infinite_univ⟩ (fun _ prev ↦ (step prev).2.2)
  have hsub_step : ∀ k, (seq (k + 1)).1 ⊆ (seq k).1 := by
    intro k
    rintro _ ⟨n, rfl⟩
    let S := seq k
    let x := Classical.choose S.2.nonempty
    let hgt := infinite_gt_of_infinite S.2 x
    exact (Nat.nth_mem_of_infinite hgt _).1
  have hsub_le : ∀ {k l : ℕ}, k ≤ l → (seq l).1 ⊆ (seq k).1 := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact Subset.rfl
    | succ l _ ih => exact (hsub_step l).trans ih
  let x : ℕ → ℕ := fun k ↦ (step (seq k)).1
  let bseq : ℕ → Bool := fun k ↦ (step (seq k)).2.1
  have hx_mem : ∀ k, x k ∈ (seq k).1 := fun k ↦ Classical.choose_spec (seq k).2.nonempty
  have hx_lt : ∀ {k l : ℕ}, k < l → x k < x l := by
    intro k l hkl
    have hxl : x l ∈ (seq (k + 1)).1 := hsub_le (Nat.succ_le_of_lt hkl) (hx_mem l)
    rcases hxl with ⟨n, hn⟩
    rw [← hn]
    exact (Nat.nth_mem_of_infinite (infinite_gt_of_infinite (seq k).2 (x k)) _).2
  have htri : ∀ {i j k : ℕ}, i < j → j < k → c (x i) (x j) (x k) = bseq i := by
    intro i j k hij hjk
    have hxj : x j ∈ (seq (i + 1)).1 := hsub_le (Nat.succ_le_of_lt hij) (hx_mem j)
    have hxk : x k ∈ (seq (i + 1)).1 := hsub_le (Nat.succ_le_of_lt (hij.trans hjk)) (hx_mem k)
    let S := seq i
    let hgt := infinite_gt_of_infinite S.2 (x i)
    let e : ℕ → ℕ := Nat.nth (· ∈ {y ∈ S.1 | x i < y})
    let he_mono : StrictMono e := Nat.nth_strictMono hgt
    let hex := inf_ramsey2_finite (fun u v ↦ c (x i) (e u) (e v))
    let ψ := Classical.choose (Classical.choose_spec hex)
    let hψ := Classical.choose_spec (Classical.choose_spec hex)
    rcases hxj with ⟨u, hu⟩
    rcases hxk with ⟨v, hv⟩
    change (e ∘ ψ) u = x j at hu
    change (e ∘ ψ) v = x k at hv
    have huv : u < v := (he_mono.comp hψ.1).lt_iff_lt.mp (by rw [hu, hv]; exact hx_lt hjk)
    rw [← hu, ← hv]
    exact hψ.2 u v huv
  obtain ⟨b, χ, hχ_mono, hχ_eq⟩ := inf_ramsey1_finite bseq
  refine ⟨b, fun i ↦ x (χ i), fun i j hij ↦ hx_lt (hχ_mono hij), ?_⟩
  intro i j k hij hjk
  exact (htri (hχ_mono hij) (hχ_mono hjk)).trans (hχ_eq i)

private lemma two_row_thin_aux {X₀ Y₀ : Set ℕ} (c : ℕ → ℕ → Bool) :
    ∀ (k : ℕ) {X Y : Set ℕ}, X ⊆ X₀ → Y ⊆ Y₀ → X.Infinite → Y.Infinite →
      (∃ X' ⊆ X, ∃ Y' ⊆ Y, X'.Infinite ∧ Y'.Infinite ∧
        ∀ j ∈ Y', {i ∈ X' | c i j = true}.Finite) ∨
      (∃ (X' : Set ℕ) (T : Finset ℕ), X' ⊆ X ∧ X'.Infinite ∧ (↑T : Set ℕ) ⊆ Y ∧
        T.card = k ∧ ∀ i ∈ X', ∀ j ∈ T, c i j = true) := by
  intro k
  induction k with
  | zero =>
    intro X Y _ _ hX _
    exact Or.inr ⟨X, ∅, Subset.rfl, hX, by simp, Finset.card_empty,
      fun _ _ j hj ↦ (Finset.notMem_empty j hj).elim⟩
  | succ k ih =>
    intro X Y hXX₀ hYY₀ hX hY
    let Yfin : Set ℕ := {j ∈ Y | {i ∈ X | c i j = true}.Finite}
    by_cases hYfin : Yfin.Infinite
    · exact Or.inl ⟨X, Subset.rfl, Yfin, fun _ hj ↦ hj.1, hX, hYfin, fun _ hj ↦ hj.2⟩
    · have hYfin_fin : Yfin.Finite := Set.not_infinite.mp hYfin
      obtain ⟨j₀, hj₀Y, hj₀nfin⟩ := (hY.sdiff hYfin_fin).nonempty
      let X₁ : Set ℕ := {i ∈ X | c i j₀ = true}
      have hX₁_inf : X₁.Infinite := by
        by_contra hni
        exact hj₀nfin ⟨hj₀Y, Set.not_infinite.mp hni⟩
      let Y₁ : Set ℕ := {j ∈ Y | j₀ < j}
      have hY₁_inf : Y₁.Infinite := infinite_gt_of_infinite hY j₀
      have hX₁X : X₁ ⊆ X := fun _ h ↦ h.1
      have hY₁Y : Y₁ ⊆ Y := fun _ h ↦ h.1
      rcases ih (hX₁X.trans hXX₀) (hY₁Y.trans hYY₀) hX₁_inf hY₁_inf with
          ⟨X', hX'X₁, Y', hY'Y₁, hX'inf, hY'inf, hfin⟩ |
          ⟨X', T, hX'X₁, hX'inf, hTY₁, hTcard, hTcl⟩
      · exact Or.inl ⟨X', hX'X₁.trans hX₁X, Y', hY'Y₁.trans hY₁Y, hX'inf, hY'inf, hfin⟩
      · right
        have hj₀T : j₀ ∉ T := by
          intro hj₀
          exact lt_irrefl j₀ (hTY₁ hj₀).2
        refine ⟨X', insert j₀ T, hX'X₁.trans hX₁X, hX'inf, ?_,
          by rw [Finset.card_insert_of_notMem hj₀T, hTcard], ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp (Finset.mem_coe.mp hj) with rfl | hjT
          · exact hj₀Y
          · exact (hTY₁ hjT).1
        · intro i hi j hj
          rcases Finset.mem_insert.mp hj with rfl | hjT
          · exact (hX'X₁ hi).2
          · exact hTcl i hi j hjT

private lemma omega_mul_p_ramsey (p m : ℕ) (c : (Fin p ×ₗ ℕ) → (Fin p ×ₗ ℕ) → Bool) :
    (∃ G : Finset (Fin p ×ₗ ℕ), G.card = p ∧
      ∀ x ∈ G, ∀ y ∈ G, x < y → c x y = false) ∨
    (∃ (f : ℕ → Fin p ×ₗ ℕ) (g : Fin m → Fin p ×ₗ ℕ),
      StrictMono f ∧ StrictMono g ∧ (∀ k r, f k < g r) ∧
      ∀ x ∈ Set.range f ∪ Set.range g, ∀ y ∈ Set.range f ∪ Set.range g,
        x < y → c x y = true) := by
  classical
  by_contra hNeither
  have hNoBlue : ¬ ∃ G : Finset (Fin p ×ₗ ℕ), G.card = p ∧
      ∀ x ∈ G, ∀ y ∈ G, x < y → c x y = false := fun h ↦ hNeither (Or.inl h)
  have hNoRed : ¬ ∃ (f : ℕ → Fin p ×ₗ ℕ) (g : Fin m → Fin p ×ₗ ℕ),
      StrictMono f ∧ StrictMono g ∧ (∀ k r, f k < g r) ∧
      ∀ x ∈ Set.range f ∪ Set.range g, ∀ y ∈ Set.range f ∪ Set.range g,
        x < y → c x y = true := fun h ↦ hNeither (Or.inr h)
  have hrow : ∀ a : Fin p, ∃ B : Set ℕ, B.Infinite ∧
      ∀ i ∈ B, ∀ j ∈ B, i < j → c (toLex (a, i)) (toLex (a, j)) = true := by
    intro a
    obtain ⟨b, φ, hφ_mono, hφ_eq⟩ :=
      inf_ramsey2_finite (fun i j ↦ c (toLex (a, i)) (toLex (a, j)))
    cases b with
    | false =>
      exfalso
      let emb : ℕ ↪ Fin p ×ₗ ℕ :=
        ⟨fun i ↦ toLex (a, φ i), fun i j hij ↦
          hφ_mono.injective (congrArg (fun q ↦ (ofLex q).2) hij)⟩
      let G : Finset (Fin p ×ₗ ℕ) := (Finset.range p).map emb
      refine hNoBlue ⟨G, by simp [G], ?_⟩
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨j, _, rfl⟩
      have hij : i < j := by
        rw [Prod.Lex.lt_iff] at hxy
        rcases hxy with hlt | ⟨_, hlt⟩
        · exact (lt_irrefl a hlt).elim
        · exact hφ_mono.lt_iff_lt.mp hlt
      exact hφ_eq i j hij
    | true =>
      refine ⟨Set.range φ, Set.infinite_range_of_injective hφ_mono.injective, ?_⟩
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      exact hφ_eq i j (hφ_mono.lt_iff_lt.mp hij)
  let B₀ : Fin p → Set ℕ := fun a ↦ Classical.choose (hrow a)
  have hB₀_inf : ∀ a, (B₀ a).Infinite := fun a ↦ (Classical.choose_spec (hrow a)).1
  have hB₀_cl : ∀ a, ∀ i ∈ B₀ a, ∀ j ∈ B₀ a, i < j →
      c (toLex (a, i)) (toLex (a, j)) = true := fun a ↦ (Classical.choose_spec (hrow a)).2
  have hpair : ∀ (a b : Fin p), a < b → ∀ {X Y : Set ℕ},
      X ⊆ B₀ a → Y ⊆ B₀ b → X.Infinite → Y.Infinite →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, X'.Infinite ∧ Y'.Infinite ∧
        ∀ j ∈ Y', {i ∈ X' | c (toLex (a, i)) (toLex (b, j)) = true}.Finite := by
    intro a b hab X Y hXB hYB hX hY
    rcases two_row_thin_aux (fun i j ↦ c (toLex (a, i)) (toLex (b, j))) m hXB hYB hX hY with
        hgood | ⟨X', T, hX'X, hX'inf, hTY, hTcard, hTcl⟩
    · exact hgood
    · exfalso
      obtain ⟨e, he_mono, he_mem⟩ := strictMono_of_infinite hX'inf
      let tEmb := T.orderEmbOfFin hTcard
      let f : ℕ → Fin p ×ₗ ℕ := fun k ↦ toLex (a, e k)
      let g : Fin m → Fin p ×ₗ ℕ := fun r ↦ toLex (b, tEmb r)
      have hf_mono : StrictMono f := fun k₁ k₂ hk ↦
        Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, he_mono hk⟩)
      have hg_mono : StrictMono g := fun r₁ r₂ hr ↦
        Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, tEmb.strictMono hr⟩)
      have hfg : ∀ k r, f k < g r := fun _ _ ↦ Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)
      refine hNoRed ⟨f, g, hf_mono, hg_mono, hfg, ?_⟩
      intro x hx y hy hxy
      rcases hx with ⟨k₁, rfl⟩ | ⟨r₁, rfl⟩ <;> rcases hy with ⟨k₂, rfl⟩ | ⟨r₂, rfl⟩
      · have hk : k₁ < k₂ := hf_mono.lt_iff_lt.mp hxy
        exact hB₀_cl a (e k₁) (hXB (hX'X (he_mem k₁))) (e k₂) (hXB (hX'X (he_mem k₂))) (he_mono hk)
      · exact hTcl (e k₁) (he_mem k₁) (tEmb r₂) (Finset.orderEmbOfFin_mem T hTcard r₂)
      · exact (lt_asymm hxy (hfg k₂ r₁)).elim
      · have hr : r₁ < r₂ := hg_mono.lt_iff_lt.mp hxy
        exact hB₀_cl b (tEmb r₁) (hYB (hTY (Finset.orderEmbOfFin_mem T hTcard r₁)))
          (tEmb r₂) (hYB (hTY (Finset.orderEmbOfFin_mem T hTcard r₂))) (tEmb.strictMono hr)
  have hthin_all : ∀ bound : ℕ, bound ≤ p → ∃ D : Fin p → Set ℕ,
      (∀ a, D a ⊆ B₀ a ∧ (D a).Infinite) ∧
      (∀ a b : Fin p, a < b → b.1 < bound →
        ∀ j ∈ D b, {i ∈ D a | c (toLex (a, i)) (toLex (b, j)) = true}.Finite) := by
    intro bound
    induction bound with
    | zero =>
      intro _
      exact ⟨B₀, fun a ↦ ⟨Subset.rfl, hB₀_inf a⟩, fun _ _ _ hb ↦ (Nat.not_lt_zero _ hb).elim⟩
    | succ bound ih =>
      intro hbound
      obtain ⟨D₀, hD₀_sub, hD₀_fin⟩ := ih (by omega)
      let b₀ : Fin p := ⟨bound, hbound⟩
      have hinner : ∀ sub : ℕ, sub ≤ bound → ∃ D : Fin p → Set ℕ,
          (∀ a, D a ⊆ D₀ a ∧ (D a).Infinite) ∧
          (∀ a : Fin p, a.1 < sub →
            ∀ j ∈ D b₀, {i ∈ D a | c (toLex (a, i)) (toLex (b₀, j)) = true}.Finite) := by
        intro sub
        induction sub with
        | zero =>
          intro _
          exact ⟨D₀, fun a ↦ ⟨Subset.rfl, (hD₀_sub a).2⟩,
            fun _ ha ↦ (Nat.not_lt_zero _ ha).elim⟩
        | succ sub ih_sub =>
          intro hsub
          obtain ⟨D₁, hD₁_sub, hD₁_fin⟩ := ih_sub (by omega)
          let a₀ : Fin p := ⟨sub, by omega⟩
          have ha₀b₀ : a₀ < b₀ := Fin.mk_lt_mk.mpr hsub
          obtain ⟨X', hX', Y', hY', hX'inf, hY'inf, hXYfin⟩ :=
            hpair a₀ b₀ ha₀b₀ ((hD₁_sub a₀).1.trans (hD₀_sub a₀).1)
              ((hD₁_sub b₀).1.trans (hD₀_sub b₀).1) (hD₁_sub a₀).2 (hD₁_sub b₀).2
          let D₂ : Fin p → Set ℕ := fun a ↦
            if a = a₀ then X' else if a = b₀ then Y' else D₁ a
          have hD₂_D₁ : ∀ a, D₂ a ⊆ D₁ a := by
            intro a
            dsimp only [D₂]
            split_ifs with h1 h2
            · subst h1; exact hX'
            · subst h2; exact hY'
            · exact Subset.rfl
          refine ⟨D₂, fun a ↦ ⟨(hD₂_D₁ a).trans (hD₁_sub a).1, ?_⟩, ?_⟩
          · dsimp only [D₂]
            split_ifs with h1 h2
            · exact hX'inf
            · exact hY'inf
            · exact (hD₁_sub a).2
          · intro a ha j hj
            have hjb₀ : D₂ b₀ = Y' := by
              dsimp only [D₂]
              rw [if_neg (ne_of_gt ha₀b₀), if_pos rfl]
            rw [hjb₀] at hj
            by_cases ha_eq : a = a₀
            · subst ha_eq
              have ha₀_eq : D₂ a₀ = X' := by simp [D₂]
              rw [ha₀_eq]
              exact hXYfin j hj
            · have ha_lt : a.1 < sub := by
                have : a.1 ≠ sub := fun h ↦ ha_eq (Fin.ext h)
                omega
              exact (hD₁_fin a ha_lt j (hY' hj)).subset fun i hi ↦ ⟨hD₂_D₁ a hi.1, hi.2⟩
      obtain ⟨D, hD_D₀, hD_b₀⟩ := hinner bound le_rfl
      refine ⟨D, fun a ↦ ⟨(hD_D₀ a).1.trans (hD₀_sub a).1, (hD_D₀ a).2⟩, ?_⟩
      intro a b hab hb j hj
      by_cases hbb₀ : b = b₀
      · subst hbb₀
        exact hD_b₀ a hab j hj
      · have hblt : b.1 < bound := by
          have : b.1 ≠ bound := fun h ↦ hbb₀ (Fin.ext h)
          omega
        exact (hD₀_fin a b hab hblt j ((hD_D₀ b).1 hj)).subset fun i hi ↦
          ⟨(hD_D₀ a).1 hi.1, hi.2⟩
  obtain ⟨D, hD_sub, hD_fin⟩ := hthin_all p le_rfl
  have hpick : ∀ k : ℕ, k ≤ p → ∃ G : Finset (Fin p ×ₗ ℕ),
      G.card = k ∧
      (∀ q ∈ G, p - k ≤ (ofLex q).1.1 ∧ (ofLex q).2 ∈ D (ofLex q).1) ∧
      (∀ x ∈ G, ∀ y ∈ G, x < y → c x y = false) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, Finset.card_empty, fun _ h ↦ (Finset.notMem_empty _ h).elim,
        fun _ h ↦ (Finset.notMem_empty _ h).elim⟩
    | succ k ih =>
      intro hk
      obtain ⟨G, hGcard, hGmem, hGcl⟩ := ih (by omega)
      let idx : Fin p := ⟨p - (k + 1), by omega⟩
      let bad : Set ℕ := ⋃ q ∈ G, {i ∈ D idx | c (toLex (idx, i)) q = true}
      have hbad_fin : bad.Finite := by
        refine Finset.finite_toSet G |>.biUnion fun q hq ↦ ?_
        have hlt : idx < (ofLex q).1 := by
          change p - (k + 1) < (ofLex q).1.1
          have := (hGmem q hq).1
          omega
        have hq_eq : q = toLex ((ofLex q).1, (ofLex q).2) := rfl
        rw [hq_eq]
        exact hD_fin idx (ofLex q).1 hlt (ofLex q).1.2 (ofLex q).2 (hGmem q hq).2
      obtain ⟨i₀, hi₀D, hi₀nbad⟩ := ((hD_sub idx).2.sdiff hbad_fin).nonempty
      let q₀ : Fin p ×ₗ ℕ := toLex (idx, i₀)
      have hq₀_lt : ∀ q ∈ G, q₀ < q := by
        intro q hq
        have hlt : idx < (ofLex q).1 := by
          change p - (k + 1) < (ofLex q).1.1
          have := (hGmem q hq).1
          omega
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
      have hq₀G : q₀ ∉ G := fun h ↦ lt_irrefl q₀ (hq₀_lt q₀ h)
      refine ⟨insert q₀ G, by rw [Finset.card_insert_of_notMem hq₀G, hGcard], ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqG
        · exact ⟨le_rfl, hi₀D⟩
        · exact ⟨by have := (hGmem q hqG).1; omega, (hGmem q hqG).2⟩
      · intro x hx y hy hxy
        have hyq₀ : y ≠ q₀ := by
          intro rfl
          rcases Finset.mem_insert.mp hx with rfl | hxG
          · exact lt_irrefl _ hxy
          · exact lt_asymm hxy (hq₀_lt x hxG)
        have hyG : y ∈ G := (Finset.mem_insert.mp hy).resolve_left hyq₀
        rcases Finset.mem_insert.mp hx with rfl | hxG
        · cases hcy : c q₀ y with
          | false => rfl
          | true =>
            exfalso
            exact hi₀nbad (Set.mem_iUnion₂.mpr ⟨y, hyG, hi₀D, hcy⟩)
        · exact hGcl x hxG y hyG hxy
  obtain ⟨G, hGcard, _, hGcl⟩ := hpick p le_rfl
  exact hNoBlue ⟨G, hGcard, hGcl⟩

/- Section 3: Uncountable real partition lemma `A → (ω, ω + m)²₂` -/

private lemma iio_zero_not_countable : ¬ (Set.Iio (0 : ℝ)).Countable := by
  intro h
  apply Set.not_countable_univ (α := ℝ)
  have huniv : (Set.univ : Set ℝ) ⊆ Set.Iio 0 ∪ {0} ∪ ((fun x : ℝ ↦ -x) '' Set.Iio 0) := by
    intro x _
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · exact Or.inl (Or.inl hlt)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨-x, neg_lt_zero.mpr hgt, neg_neg x⟩
  exact ((h.union (Set.countable_singleton 0)).union (h.image _)).mono huniv

private lemma uncountable_diff_countable {α : Type*} {A B : Set α}
    (hA : ¬ A.Countable) (hB : B.Countable) : ¬ (A \ B).Countable := by
  intro h
  apply hA
  exact (h.union hB).mono fun x hx ↦ by
    by_cases hxB : x ∈ B
    · exact Or.inr hxB
    · exact Or.inl ⟨hx, hxB⟩

private lemma nonempty_of_not_countable {α : Type*} {A : Set α} (hA : ¬ A.Countable) :
    A.Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun he ↦ hA (he ▸ Set.countable_empty)

private lemma countable_left_thin (A : Set ℝ) :
    {x ∈ A | (A ∩ Set.Iio x).Countable}.Countable := by
  classical
  let S : Set ℝ := {x ∈ A | (A ∩ Set.Iio x).Countable}
  let T : ℚ → Set ℝ := fun q ↦
    if h : ∃ x ∈ S, (q : ℝ) < x then A ∩ Set.Iio h.choose else ∅
  have hT : ∀ q : ℚ, (T q).Countable := by
    intro q
    dsimp only [T]
    split_ifs with h
    · exact h.choose_spec.1.2
    · exact Set.countable_empty
  let U : Set ℝ := ⋃ q : ℚ, T q
  have hU : U.Countable := Set.countable_iUnion hT
  have hsub : (S \ U).Subsingleton := by
    intro x₁ hx₁ x₂ hx₂
    by_contra hne
    have hwlog : ∀ {u v : ℝ}, u ∈ S \ U → v ∈ S \ U → u < v → False := by
      intro u v hu hv huv
      obtain ⟨q, hqu, hqv⟩ := exists_rat_btwn huv
      have hex : ∃ x ∈ S, (q : ℝ) < x := ⟨v, hv.1, hqv⟩
      have huT : u ∈ T q := by
        dsimp only [T]
        rw [dif_pos hex]
        exact ⟨hu.1.1, hqu.trans hex.choose_spec.2⟩
      exact hu.2 (Set.mem_iUnion.mpr ⟨q, huT⟩)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hwlog hx₁ hx₂ hlt
    · exact hwlog hx₂ hx₁ hgt
  exact ((hsub.countable).union hU).mono fun x hx ↦ by
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · exact Or.inl ⟨hx, hxU⟩

private lemma countable_right_thin (A : Set ℝ) :
    {x ∈ A | (A ∩ Set.Ioi x).Countable}.Countable := by
  classical
  let S : Set ℝ := {x ∈ A | (A ∩ Set.Ioi x).Countable}
  let T : ℚ → Set ℝ := fun q ↦
    if h : ∃ x ∈ S, x < (q : ℝ) then A ∩ Set.Ioi h.choose else ∅
  have hT : ∀ q : ℚ, (T q).Countable := by
    intro q
    dsimp only [T]
    split_ifs with h
    · exact h.choose_spec.1.2
    · exact Set.countable_empty
  let U : Set ℝ := ⋃ q : ℚ, T q
  have hU : U.Countable := Set.countable_iUnion hT
  have hsub : (S \ U).Subsingleton := by
    intro x₁ hx₁ x₂ hx₂
    by_contra hne
    have hwlog : ∀ {u v : ℝ}, u ∈ S \ U → v ∈ S \ U → u < v → False := by
      intro u v hu hv huv
      obtain ⟨q, hqu, hqv⟩ := exists_rat_btwn huv
      have hex : ∃ x ∈ S, x < (q : ℝ) := ⟨u, hu.1, hqu⟩
      have hvT : v ∈ T q := by
        dsimp only [T]
        rw [dif_pos hex]
        exact ⟨hv.1.1, hex.choose_spec.2.trans hqv⟩
      exact hv.2 (Set.mem_iUnion.mpr ⟨q, hvT⟩)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hwlog hx₁ hx₂ hlt
    · exact hwlog hx₂ hx₁ hgt
  exact ((hsub.countable).union hU).mono fun x hx ↦ by
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · exact Or.inl ⟨hx, hxU⟩

private lemma uncountable_split {A : Set ℝ} (hA : ¬ A.Countable) :
    ∃ L R : Set ℝ, L ⊆ A ∧ R ⊆ A ∧ ¬ L.Countable ∧ ¬ R.Countable ∧
      ∀ x ∈ L, ∀ y ∈ R, x < y := by
  have hbad : ({x ∈ A | (A ∩ Set.Iio x).Countable} ∪
      {x ∈ A | (A ∩ Set.Ioi x).Countable}).Countable :=
    (countable_left_thin A).union (countable_right_thin A)
  obtain ⟨z, hzA, hznbad⟩ := nonempty_of_not_countable (uncountable_diff_countable hA hbad)
  refine ⟨A ∩ Set.Iio z, A ∩ Set.Ioi z, Set.inter_subset_left, Set.inter_subset_left,
    fun hL ↦ hznbad (Or.inl ⟨hzA, hL⟩), fun hR ↦ hznbad (Or.inr ⟨hzA, hR⟩), ?_⟩
  intro x hx y hy
  exact hx.2.trans hy.2

private lemma uncountable_omega_blocks {A : Set ℝ} (hA : ¬ A.Countable) :
    ∃ B : ℕ → Set ℝ, (∀ k, B k ⊆ A ∧ ¬ (B k).Countable) ∧
      ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y := by
  let Unc := {S : Set ℝ // S ⊆ A ∧ ¬ S.Countable}
  let splitL : Unc → Unc := fun S ↦
    let hex := uncountable_split S.2.2
    let L := Classical.choose hex
    let hspec := Classical.choose_spec hex
    let hR := Classical.choose_spec hspec
    ⟨L, hR.1.trans S.2.1, hR.2.2.1⟩
  let splitR : Unc → Unc := fun S ↦
    let hex := uncountable_split S.2.2
    let hspec := Classical.choose_spec hex
    let R := Classical.choose hspec
    let hR := Classical.choose_spec hspec
    ⟨R, hR.2.1.trans S.2.1, hR.2.2.2.1⟩
  have hLR_sub : ∀ S : Unc, (splitL S).1 ⊆ S.1 ∧ (splitR S).1 ⊆ S.1 ∧
      ∀ x ∈ (splitL S).1, ∀ y ∈ (splitR S).1, x < y := by
    intro S
    let hex := uncountable_split S.2.2
    let hspec := Classical.choose_spec hex
    let hR := Classical.choose_spec hspec
    exact ⟨hR.1, hR.2.1, hR.2.2.2.2⟩
  let rem : ℕ → Unc := Nat.rec ⟨A, Subset.rfl, hA⟩ (fun _ prev ↦ splitR prev)
  have hrem_le : ∀ {i j : ℕ}, i ≤ j → (rem j).1 ⊆ (rem i).1 := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact Subset.rfl
    | succ j _ ih => exact (hLR_sub (rem j)).2.1.trans ih
  refine ⟨fun k ↦ (splitL (rem k)).1, fun k ↦ (splitL (rem k)).2, ?_⟩
  intro i j hij x hx y hy
  have hy_rem : y ∈ (rem (i + 1)).1 :=
    hrem_le (Nat.succ_le_of_lt hij) ((hLR_sub (rem j)).1 hy)
  exact (hLR_sub (rem i)).2.2 x hx y hy_rem

private lemma pick_from_blocks (B : ℕ → Set ℝ) (hB : ∀ k, ¬ (B k).Countable)
    (bad : ℝ → Set ℝ) (hbad : ∀ k, ∀ x ∈ B k, (bad x).Countable)
    (S₀ : Set ℝ) (hS₀ : S₀.Countable) :
    ∃ u : ℕ → ℝ, (∀ k, u k ∈ B k) ∧ (∀ k, u k ∉ S₀) ∧
      ∀ i j, i < j → u j ∉ bad (u i) := by
  let Cnt := {S : Set ℝ // S.Countable}
  let choosePt : ∀ (k : ℕ) (S : Cnt), ℝ := fun k S ↦
    Classical.choose (nonempty_of_not_countable (uncountable_diff_countable (hB k) S.2))
  have choosePt_spec : ∀ (k : ℕ) (S : Cnt), choosePt k S ∈ B k ∧ choosePt k S ∉ S.1 := fun k S ↦
    Classical.choose_spec (nonempty_of_not_countable (uncountable_diff_countable (hB k) S.2))
  let acc : ℕ → Cnt := Nat.rec ⟨S₀, hS₀⟩ fun k prev ↦
    ⟨prev.1 ∪ bad (choosePt k prev), prev.2.union (hbad k _ (choosePt_spec k prev).1)⟩
  have hacc_step : ∀ k, (acc k).1 ⊆ (acc (k + 1)).1 := fun _ ↦ Set.subset_union_left
  have hacc_le : ∀ {i j : ℕ}, i ≤ j → (acc i).1 ⊆ (acc j).1 := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact Subset.rfl
    | succ j _ ih => exact ih.trans (hacc_step j)
  let u : ℕ → ℝ := fun k ↦ choosePt k (acc k)
  refine ⟨u, fun k ↦ (choosePt_spec k (acc k)).1,
    fun k hk ↦ (choosePt_spec k (acc k)).2 (hacc_le (Nat.zero_le k) hk), ?_⟩
  intro i j hij hbad_ij
  have hmem : u j ∈ (acc (i + 1)).1 := Or.inr hbad_ij
  exact (choosePt_spec j (acc j)).2 (hacc_le (Nat.succ_le_of_lt hij) hmem)

private lemma uncountable_real_ramsey (m : ℕ) {A : Set ℝ} (hA : ¬ A.Countable)
    (c : ℝ → ℝ → Bool) :
    (∃ P : ℕ → ℝ, StrictMono P ∧ (∀ k, P k ∈ A) ∧ ∀ i j, i < j → c (P i) (P j) = false) ∨
    (∃ (Q : ℕ → ℝ) (T : Fin m → ℝ), StrictMono Q ∧ StrictMono T ∧
      (∀ k r, Q k < T r) ∧ (∀ k, Q k ∈ A) ∧ (∀ r, T r ∈ A) ∧
      ∀ x ∈ Set.range Q ∪ Set.range T, ∀ y ∈ Set.range Q ∪ Set.range T,
        x < y → c x y = true) := by
  rcases Classical.em (∃ X : Set ℝ, X ⊆ A ∧ ¬ X.Countable ∧
      ∀ x ∈ X, {y ∈ X | x < y ∧ c x y = false}.Countable) with
      ⟨X, hXA, hXunc, hXcnt⟩ | hnoX
  · right
    obtain ⟨XL, XR, hXLX, hXRX, hXLunc, hXRunc, hLRlt⟩ := uncountable_split hXunc
    obtain ⟨B, hB, hBlt⟩ := uncountable_omega_blocks hXLunc
    obtain ⟨TB, hTB, hTBlt⟩ := uncountable_omega_blocks hXRunc
    let bad : ℝ → Set ℝ := fun x ↦ {y ∈ X | x < y ∧ c x y = false}
    have hbadB : ∀ k, ∀ x ∈ B k, (bad x).Countable := fun k x hx ↦
      hXcnt x (hXLX ((hB k).1 hx))
    have hbadTB : ∀ k, ∀ x ∈ TB k, (bad x).Countable := fun k x hx ↦
      hXcnt x (hXRX ((hTB k).1 hx))
    obtain ⟨Q, hQB, _, hQbad⟩ :=
      pick_from_blocks B (fun k ↦ (hB k).2) bad hbadB ∅ Set.countable_empty
    let Sall : Set ℝ := ⋃ k : ℕ, bad (Q k)
    have hSall : Sall.Countable := Set.countable_iUnion fun k ↦ hbadB k (Q k) (hQB k)
    obtain ⟨V, hVTB, hVnS, hVbad⟩ :=
      pick_from_blocks TB (fun k ↦ (hTB k).2) bad hbadTB Sall hSall
    let T : Fin m → ℝ := fun r ↦ V r.1
    have hQ_mono : StrictMono Q := fun i j hij ↦ hBlt i j hij (Q i) (hQB i) (Q j) (hQB j)
    have hT_mono : StrictMono T := fun r s hrs ↦
      hTBlt r.1 s.1 hrs (V r.1) (hVTB r.1) (V s.1) (hVTB s.1)
    have hQT : ∀ k r, Q k < T r := fun k r ↦
      hLRlt (Q k) ((hB k).1 (hQB k)) (V r.1) ((hTB r.1).1 (hVTB r.1))
    have hQX : ∀ k, Q k ∈ X := fun k ↦ hXLX ((hB k).1 (hQB k))
    have hTX : ∀ r, T r ∈ X := fun r ↦ hXRX ((hTB r.1).1 (hVTB r.1))
    refine ⟨Q, T, hQ_mono, hT_mono, hQT, fun k ↦ hXA (hQX k), fun r ↦ hXA (hTX r), ?_⟩
    intro x hx y hy hxy
    rcases hx with ⟨i, rfl⟩ | ⟨r, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨s, rfl⟩
    · have hij : i < j := hQ_mono.lt_iff_lt.mp hxy
      cases hc : c (Q i) (Q j) with
      | true => rfl
      | false => exact (hQbad i j hij ⟨hQX j, hxy, hc⟩).elim
    · cases hc : c (Q i) (T s) with
      | true => rfl
      | false => exact (hVnS s.1 (Set.mem_iUnion.mpr ⟨i, hTX s, hxy, hc⟩)).elim
    · exact (lt_asymm hxy (hQT j r)).elim
    · have hrs : r < s := hT_mono.lt_iff_lt.mp hxy
      cases hc : c (T r) (T s) with
      | true => rfl
      | false => exact (hVbad r.1 s.1 hrs ⟨hTX s, hxy, hc⟩).elim
  · left
    have hall : ∀ X : Set ℝ, X ⊆ A → ¬ X.Countable →
        ∃ x ∈ X, ¬ {y ∈ X | x < y ∧ c x y = false}.Countable := by
      intro X hXA hXunc
      by_contra h
      exact hnoX ⟨X, hXA, hXunc, fun x hx ↦
        Classical.not_not.mp fun hnc ↦ h ⟨x, hx, hnc⟩⟩
    let Unc := {X : Set ℝ // X ⊆ A ∧ ¬ X.Countable}
    let pt : Unc → ℝ := fun S ↦ Classical.choose (hall S.1 S.2.1 S.2.2)
    have hpt : ∀ S : Unc, pt S ∈ S.1 ∧
        ¬ {y ∈ S.1 | pt S < y ∧ c (pt S) y = false}.Countable := fun S ↦
      Classical.choose_spec (hall S.1 S.2.1 S.2.2)
    let next : Unc → Unc := fun S ↦
      have hsub : {y ∈ S.1 | pt S < y ∧ c (pt S) y = false} ⊆ S.1 := fun _ h ↦ h.1
      ⟨{y ∈ S.1 | pt S < y ∧ c (pt S) y = false}, hsub.trans S.2.1, (hpt S).2⟩
    let seq : ℕ → Unc := Nat.rec ⟨A, Subset.rfl, hA⟩ (fun _ prev ↦ next prev)
    have hseq_step : ∀ k, (seq (k + 1)).1 ⊆ (seq k).1 := fun _ _ h ↦ h.1
    have hseq_le : ∀ {i j : ℕ}, i ≤ j → (seq j).1 ⊆ (seq i).1 := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => exact Subset.rfl
      | succ j _ ih => exact (hseq_step j).trans ih
    let P : ℕ → ℝ := fun k ↦ pt (seq k)
    have hrel : ∀ {i j : ℕ}, i < j → P i < P j ∧ c (P i) (P j) = false := by
      intro i j hij
      have hPj : P j ∈ (seq (i + 1)).1 := hseq_le (Nat.succ_le_of_lt hij) (hpt (seq j)).1
      exact hPj.2
    exact ⟨P, fun i j hij ↦ (hrel hij).1, fun k ↦ (seq k).2.1 (hpt (seq k)).1,
      fun i j hij ↦ (hrel hij).2⟩

/- Section 4: Main ordered proof of Erdős–Rado Theorem 31 (equation 30) -/

private lemma erdos_rado_ordered (m : ℕ) (isRed : ℝ → ℝ → ℝ → Prop) :
    (∃ (f : ℕ → ℝ) (g : Fin m → ℝ),
      StrictMono f ∧ StrictMono g ∧ (∀ k r, f k < g r) ∧
      ∀ x ∈ Set.range f ∪ Set.range g, ∀ y ∈ Set.range f ∪ Set.range g,
        ∀ z ∈ Set.range f ∪ Set.range g, x < y → y < z → isRed x y z) ∨
    (∃ x₀ x₁ x₂ x₃ : ℝ, x₀ < x₁ ∧ x₁ < x₂ ∧ x₂ < x₃ ∧
      ¬ isRed x₀ x₁ x₂ ∧ ¬ isRed x₀ x₁ x₃ ∧ ¬ isRed x₀ x₂ x₃ ∧ ¬ isRed x₁ x₂ x₃) := by
  classical
  by_contra hNeither
  have hNoRed : ¬ ∃ (f : ℕ → ℝ) (g : Fin m → ℝ),
      StrictMono f ∧ StrictMono g ∧ (∀ k r, f k < g r) ∧
      ∀ x ∈ Set.range f ∪ Set.range g, ∀ y ∈ Set.range f ∪ Set.range g,
        ∀ z ∈ Set.range f ∪ Set.range g, x < y → y < z → isRed x y z :=
    fun h ↦ hNeither (Or.inl h)
  have hNoBlue4 : ¬ ∃ x₀ x₁ x₂ x₃ : ℝ, x₀ < x₁ ∧ x₁ < x₂ ∧ x₂ < x₃ ∧
      ¬ isRed x₀ x₁ x₂ ∧ ¬ isRed x₀ x₁ x₃ ∧ ¬ isRed x₀ x₂ x₃ ∧ ¬ isRed x₁ x₂ x₃ :=
    fun h ↦ hNeither (Or.inr h)
  have hex_blue_triple : ∀ (f : ℕ → ℝ) (g : Fin m → ℝ),
      StrictMono f → StrictMono g → (∀ k r, f k < g r) →
      ∃ y₀ ∈ Set.range f ∪ Set.range g, ∃ y₁ ∈ Set.range f ∪ Set.range g,
        ∃ y₂ ∈ Set.range f ∪ Set.range g, y₀ < y₁ ∧ y₁ < y₂ ∧ ¬ isRed y₀ y₁ y₂ := by
    intro f g hf hg hfg
    by_contra hAll
    refine hNoRed ⟨f, g, hf, hg, hfg, ?_⟩
    intro x hx y hy z hz hxy hyz
    by_contra hnr
    exact hAll ⟨x, hx, y, hy, z, hz, hxy, hyz, hnr⟩
  obtain ⟨N₀, hN₀⟩ := ramsey3 4 m
  let N : ℕ := max N₀ 1
  have hN_ge : N₀ ≤ N := le_max_left N₀ 1
  have hN_pos : 1 ≤ N := le_max_right N₀ 1
  let p : ℕ := (N - 1) * (1 + m + m * m) + 1
  let cEmb : (Fin p ×ₗ ℕ) → ℝ := fun q ↦
    (((ofLex q).1.1 : ℝ) + 1) - 1 / (((ofLex q).2 : ℝ) + 2)
  have hcEmb_bounds : ∀ q : Fin p ×ₗ ℕ,
      ((ofLex q).1.1 : ℝ) + 1 / 2 ≤ cEmb q ∧ cEmb q < ((ofLex q).1.1 : ℝ) + 1 := by
    intro q
    let d : ℝ := ((ofLex q).2 : ℝ) + 2
    have hd_ge : (2 : ℝ) ≤ d := by
      dsimp only [d]
      have : (0 : ℝ) ≤ ((ofLex q).2 : ℝ) := Nat.cast_nonneg _
      linarith
    have hd_pos : (0 : ℝ) < d := by linarith
    have hdiv_le : 1 / d ≤ (1 : ℝ) / 2 :=
      one_div_le_one_div_of_le (by norm_num) hd_ge
    have hdiv_pos : (0 : ℝ) < 1 / d := one_div_pos.mpr hd_pos
    dsimp only [cEmb]
    change _ ≤ _ - 1 / d ∧ _ - 1 / d < _
    constructor <;> linarith
  have hcEmb_pos : ∀ q : Fin p ×ₗ ℕ, 0 < cEmb q := by
    intro q
    have h0 : (0 : ℝ) ≤ ((ofLex q).1.1 : ℝ) := Nat.cast_nonneg _
    have h1 := (hcEmb_bounds q).1
    linarith
  have hcEmb_mono : StrictMono cEmb := by
    intro q₁ q₂ hq
    rw [Prod.Lex.lt_iff] at hq
    rcases hq with ha | ⟨ha_eq, hk⟩
    · have ha' : ((ofLex q₁).1.1 : ℝ) + 1 ≤ ((ofLex q₂).1.1 : ℝ) := by
        have : (ofLex q₁).1.1 + 1 ≤ (ofLex q₂).1.1 := ha
        exact_mod_cast this
      have hb₁ := (hcEmb_bounds q₁).2
      have hb₂ := (hcEmb_bounds q₂).1
      linarith
    · have hk' : (((ofLex q₁).2 : ℝ) + 2) < (((ofLex q₂).2 : ℝ) + 2) := by
        have : (ofLex q₁).2 + 2 < (ofLex q₂).2 + 2 := Nat.add_lt_add_right hk 2
        exact_mod_cast this
      have hd₁ : (0 : ℝ) < ((ofLex q₁).2 : ℝ) + 2 := by positivity
      have hdiv : 1 / (((ofLex q₂).2 : ℝ) + 2) < 1 / (((ofLex q₁).2 : ℝ) + 2) :=
        one_div_lt_one_div_of_lt hd₁ hk'
      dsimp only [cEmb]
      rw [ha_eq]
      linarith
  -- Step 1: Find `D` of size `p` and uncountable `A ⊆ (-∞, 0)` with all `A × [cEmb '' D]²` red
  let PSub := {D : Finset (Fin p ×ₗ ℕ) // D.card = p}
  have : Countable (Fin p ×ₗ ℕ) := Function.Injective.countable ofLex.injective
  have : Countable PSub := by
    refine Function.Injective.countable (f := fun D : PSub ↦ fun i : Fin p ↦ D.1.orderEmbOfFin D.2 i) ?_
    intro D₁ D₂ heq
    apply Subtype.ext
    apply Finset.coe_inj.mp
    rw [← Finset.range_orderEmbOfFin D₁.1 D₁.2, ← Finset.range_orderEmbOfFin D₂.1 D₂.2]
    exact congrArg Set.range (funext fun i ↦ congrFun heq i)
  let AD : PSub → Set ℝ := fun D ↦
    {x₀ ∈ Set.Iio (0 : ℝ) | ∀ q₁ ∈ D.1, ∀ q₂ ∈ D.1, q₁ < q₂ → isRed x₀ (cEmb q₁) (cEmb q₂)}
  have hex_AD : ∃ D : PSub, ¬ (AD D).Countable := by
    by_contra hall_cnt
    have hcnt : ∀ D : PSub, (AD D).Countable := fun D ↦
      Classical.not_not.mp fun hnc ↦ hall_cnt ⟨D, hnc⟩
    have hunion_cnt : (⋃ D : PSub, AD D).Countable := Set.countable_iUnion hcnt
    obtain ⟨z₁, hz₁_lt, hz₁_nmem⟩ :=
      nonempty_of_not_countable (uncountable_diff_countable iio_zero_not_countable hunion_cnt)
    have hz₁_prop : ∀ (G : Finset (Fin p ×ₗ ℕ)), G.card = p →
        ∃ q₁ ∈ G, ∃ q₂ ∈ G, q₁ < q₂ ∧ ¬ isRed z₁ (cEmb q₁) (cEmb q₂) := by
      intro G hGcard
      by_contra hG_all
      refine hz₁_nmem (Set.mem_iUnion.mpr ⟨⟨G, hGcard⟩, hz₁_lt, ?_⟩)
      intro q₁ hq₁ q₂ hq₂ hq₁₂
      by_contra hnr
      exact hG_all ⟨q₁, hq₁, q₂, hq₂, hq₁₂, hnr⟩
    rcases omega_mul_p_ramsey p m (fun q₁ q₂ ↦ decide (¬ isRed z₁ (cEmb q₁) (cEmb q₂))) with
        ⟨G, hGcard, hGcl⟩ | ⟨f₀, g₀, hf₀, hg₀, hfg₀, hcl⟩
    · obtain ⟨q₁, hq₁, q₂, hq₂, hq₁₂, hnr⟩ := hz₁_prop G hGcard
      have := hGcl q₁ hq₁ q₂ hq₂ hq₁₂
      simp [hnr] at this
    · let f : ℕ → ℝ := cEmb ∘ f₀
      let g : Fin m → ℝ := cEmb ∘ g₀
      have hf : StrictMono f := hcEmb_mono.comp hf₀
      have hg : StrictMono g := hcEmb_mono.comp hg₀
      have hfg : ∀ k r, f k < g r := fun k r ↦ hcEmb_mono (hfg₀ k r)
      obtain ⟨y₀, hy₀, y₁, hy₁, y₂, hy₂, hy₀₁, hy₁₂, hblue_y⟩ := hex_blue_triple f g hf hg hfg
      have hmem_map : ∀ {y : ℝ}, y ∈ Set.range f ∪ Set.range g →
          ∃ q ∈ Set.range f₀ ∪ Set.range g₀, cEmb q = y := by
        rintro y (⟨k, rfl⟩ | ⟨r, rfl⟩)
        · exact ⟨f₀ k, Or.inl ⟨k, rfl⟩, rfl⟩
        · exact ⟨g₀ r, Or.inr ⟨r, rfl⟩, rfl⟩
      obtain ⟨q₀, hq₀, rfl⟩ := hmem_map hy₀
      obtain ⟨q₁, hq₁, rfl⟩ := hmem_map hy₁
      obtain ⟨q₂, hq₂, rfl⟩ := hmem_map hy₂
      have hq₀₁ : q₀ < q₁ := hcEmb_mono.lt_iff_lt.mp hy₀₁
      have hq₁₂ : q₁ < q₂ := hcEmb_mono.lt_iff_lt.mp hy₁₂
      have hq₀₂ : q₀ < q₂ := hq₀₁.trans hq₁₂
      have hb₀₁ : ¬ isRed z₁ (cEmb q₀) (cEmb q₁) := of_decide_eq_true (hcl q₀ hq₀ q₁ hq₁ hq₀₁)
      have hb₀₂ : ¬ isRed z₁ (cEmb q₀) (cEmb q₂) := of_decide_eq_true (hcl q₀ hq₀ q₂ hq₂ hq₀₂)
      have hb₁₂ : ¬ isRed z₁ (cEmb q₁) (cEmb q₂) := of_decide_eq_true (hcl q₁ hq₁ q₂ hq₂ hq₁₂)
      have hz₁q₀ : z₁ < cEmb q₀ := hz₁_lt.trans (hcEmb_pos q₀)
      exact hNoBlue4 ⟨z₁, cEmb q₀, cEmb q₁, cEmb q₂, hz₁q₀, hy₀₁, hy₁₂,
        hb₀₁, hb₀₂, hb₁₂, hblue_y⟩
  obtain ⟨D₀, hA_unc⟩ := hex_AD
  let A : Set ℝ := AD D₀
  let H : Finset ℝ := D₀.1.map ⟨cEmb, hcEmb_mono.injective⟩
  have hH_card : H.card = p := by simp [H, D₀.2]
  have hH_pos : ∀ x ∈ H, 0 < x := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨q, _, rfl⟩
    exact hcEmb_pos q
  have hA_neg : ∀ x ∈ A, x < 0 := fun _ hx ↦ hx.1
  have hAH_red : ∀ x₀ ∈ A, ∀ x₁ ∈ H, ∀ x₂ ∈ H, x₁ < x₂ → isRed x₀ x₁ x₂ := by
    intro x₀ hx₀ x₁ hx₁ x₂ hx₂ hx₁₂
    rcases Finset.mem_map.mp hx₁ with ⟨q₁, hq₁, rfl⟩
    rcases Finset.mem_map.mp hx₂ with ⟨q₂, hq₂, rfl⟩
    exact hx₀.2 q₁ hq₁ q₂ hq₂ (hcEmb_mono.lt_iff_lt.mp hx₁₂)
  -- Step 2: Partition pairs of `A` by whether `|V(x₀, x₁)| ≥ N` or `< N`
  let V : ℝ → ℝ → Finset ℝ := fun x₀ x₁ ↦ H.filter (fun x₂ ↦ isRed x₀ x₁ x₂)
  rcases uncountable_real_ramsey m hA_unc (fun x₀ x₁ ↦ decide ((V x₀ x₁).card < N)) with
      ⟨P, hP_mono, hPA, hP_large⟩ | ⟨Q₁, T, hQ₁_mono, hT_mono, hQ₁T, hQ₁A, hTA, hQT_small⟩
  · -- Case 1: Infinite clique `P` in `A` with `|V(P i, P j)| ≥ N`
    let PowH := {W : Finset ℝ // W ∈ H.powerset}
    let colV : ℕ → ℕ → PowH := fun i j ↦
      ⟨V (P i) (P j), Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
    obtain ⟨Jsub, φ₁, hφ₁_mono, hφ₁_eq⟩ := inf_ramsey2_finite colV
    let J : Finset ℝ := Jsub.1
    have hJH : J ⊆ H := Finset.mem_powerset.mp Jsub.2
    let P' : ℕ → ℝ := P ∘ φ₁
    have hP'_mono : StrictMono P' := hP_mono.comp hφ₁_mono
    have hP'A : ∀ k, P' k ∈ A := fun k ↦ hPA (φ₁ k)
    have hP'_V : ∀ i j, i < j → V (P' i) (P' j) = J :=
      fun i j hij ↦ congrArg Subtype.val (hφ₁_eq i j hij)
    have hJ_card : N ≤ J.card := by
      have hlt01 : φ₁ 0 < φ₁ 1 := hφ₁_mono (by omega)
      have hge : ¬ (V (P (φ₁ 0)) (P (φ₁ 1))).card < N :=
        of_decide_eq_false (hP_large (φ₁ 0) (φ₁ 1) hlt01)
      have heq : V (P' 0) (P' 1) = J := hP'_V 0 1 (by omega)
      change V (P (φ₁ 0)) (P (φ₁ 1)) = J at heq
      rw [← heq]
      exact Nat.le_of_not_lt hge
    obtain ⟨bQ, φ₂, hφ₂_mono, hφ₂_eq⟩ :=
      inf_ramsey3_bool (fun i j k ↦ decide (isRed (P' i) (P' j) (P' k)))
    let Q : ℕ → ℝ := P' ∘ φ₂
    have hQ_mono : StrictMono Q := hP'_mono.comp hφ₂_mono
    cases bQ with
    | false =>
      have hb012 : ¬ isRed (Q 0) (Q 1) (Q 2) := of_decide_eq_false (hφ₂_eq 0 1 2 (by omega) (by omega))
      have hb013 : ¬ isRed (Q 0) (Q 1) (Q 3) := of_decide_eq_false (hφ₂_eq 0 1 3 (by omega) (by omega))
      have hb023 : ¬ isRed (Q 0) (Q 2) (Q 3) := of_decide_eq_false (hφ₂_eq 0 2 3 (by omega) (by omega))
      have hb123 : ¬ isRed (Q 1) (Q 2) (Q 3) := of_decide_eq_false (hφ₂_eq 1 2 3 (by omega) (by omega))
      exact hNoBlue4 ⟨Q 0, Q 1, Q 2, Q 3, hQ_mono (by omega), hQ_mono (by omega),
        hQ_mono (by omega), hb012, hb013, hb023, hb123⟩
    | true =>
      rcases hN₀ J (fun x y z ↦ decide (isRed x y z)) (hN_ge.trans hJ_card) with
          ⟨A₄, _, hA₄card, hA₄cl⟩ | ⟨M, hMJ, hMcard, hMcl⟩
      · let emb4 := A₄.orderEmbOfFin hA₄card
        have hm4 : ∀ i : Fin 4, emb4 i ∈ A₄ := Finset.orderEmbOfFin_mem A₄ hA₄card
        have hlt4 : ∀ {i j : Fin 4}, i < j → emb4 i < emb4 j := fun h ↦ emb4.strictMono h
        exact hNoBlue4 ⟨emb4 0, emb4 1, emb4 2, emb4 3,
          hlt4 (by decide), hlt4 (by decide), hlt4 (by decide),
          of_decide_eq_false (hA₄cl _ (hm4 0) _ (hm4 1) _ (hm4 2) (hlt4 (by decide)) (hlt4 (by decide))),
          of_decide_eq_false (hA₄cl _ (hm4 0) _ (hm4 1) _ (hm4 3) (hlt4 (by decide)) (hlt4 (by decide))),
          of_decide_eq_false (hA₄cl _ (hm4 0) _ (hm4 2) _ (hm4 3) (hlt4 (by decide)) (hlt4 (by decide))),
          of_decide_eq_false (hA₄cl _ (hm4 1) _ (hm4 2) _ (hm4 3) (hlt4 (by decide)) (hlt4 (by decide)))⟩
      · let gEmb := M.orderEmbOfFin hMcard
        let g : Fin m → ℝ := fun r ↦ gEmb r
        have hg_mono : StrictMono g := gEmb.strictMono
        have hgM : ∀ r, g r ∈ M := Finset.orderEmbOfFin_mem M hMcard
        have hQg : ∀ k r, Q k < g r := fun k r ↦
          (hA_neg (Q k) (hP'A (φ₂ k))).trans (hH_pos (g r) (hJH (hMJ (hgM r))))
        refine hNoRed ⟨Q, g, hQ_mono, hg_mono, hQg, ?_⟩
        intro x hx y hy z hz hxy hyz
        rcases hx with ⟨i, rfl⟩ | ⟨r₁, rfl⟩ <;>
          rcases hy with ⟨j, rfl⟩ | ⟨r₂, rfl⟩ <;>
          rcases hz with ⟨k, rfl⟩ | ⟨r₃, rfl⟩
        · exact of_decide_eq_true (hφ₂_eq i j k
            (hQ_mono.lt_iff_lt.mp hxy) (hQ_mono.lt_iff_lt.mp hyz))
        · have hij : i < j := hQ_mono.lt_iff_lt.mp hxy
          have hmemV : g r₃ ∈ V (P' (φ₂ i)) (P' (φ₂ j)) := by
            rw [hP'_V (φ₂ i) (φ₂ j) (hφ₂_mono hij)]
            exact hMJ (hgM r₃)
          exact (Finset.mem_filter.mp hmemV).2
        · exact (lt_asymm hyz (hQg k r₂)).elim
        · exact hAH_red (Q i) (hP'A (φ₂ i)) (g r₂) (hJH (hMJ (hgM r₂)))
            (g r₃) (hJH (hMJ (hgM r₃))) hyz
        · exact (lt_asymm hxy (hQg j r₁)).elim
        · exact (lt_asymm hxy (hQg j r₁)).elim
        · exact (lt_asymm (hxy.trans hyz) (hQg k r₁)).elim
        · exact of_decide_eq_true (hMcl (g r₁) (hgM r₁) (g r₂) (hgM r₂)
            (g r₃) (hgM r₃) hxy hyz)
  · -- Case 2: Copy `Q₁ + T` of `ω + m` in `A` with `|V(u, v)| < N`
    let col₁ : ℕ → ℕ → (↥H → Bool) := fun i j x₂ ↦ decide (isRed (Q₁ i) (Q₁ j) x₂.1)
    obtain ⟨ρ, ψ₁, hψ₁_mono, hψ₁_eq⟩ := inf_ramsey2_finite col₁
    let Q₂ : ℕ → ℝ := Q₁ ∘ ψ₁
    have hQ₂_mono : StrictMono Q₂ := hQ₁_mono.comp hψ₁_mono
    let col₂ : ℕ → (Fin m → ↥H → Bool) := fun i r x₂ ↦ decide (isRed (Q₂ i) (T r) x₂.1)
    obtain ⟨σ, ψ₂, hψ₂_mono, hψ₂_eq⟩ := inf_ramsey1_finite col₂
    let Q₃ : ℕ → ℝ := Q₂ ∘ ψ₂
    have hQ₃_mono : StrictMono Q₃ := hQ₂_mono.comp hψ₂_mono
    have hQ₃T : ∀ k r, Q₃ k < T r := fun k r ↦ hQ₁T (ψ₁ (ψ₂ k)) r
    have hQ₃_sub : Set.range Q₃ ⊆ Set.range Q₁ := by
      rintro _ ⟨k, rfl⟩
      exact ⟨ψ₁ (ψ₂ k), rfl⟩
    have hV_le : ∀ x ∈ Set.range Q₁ ∪ Set.range T, ∀ y ∈ Set.range Q₁ ∪ Set.range T,
        x < y → (V x y).card ≤ N - 1 := by
      intro x hx y hy hxy
      have hlt : (V x y).card < N := of_decide_eq_true (hQT_small x hx y hy hxy)
      omega
    let x₀'' : ℝ := Q₃ 0
    let x₁'' : ℝ := Q₃ 1
    let pairsT : Finset (Fin m × Fin m) := Finset.univ.filter (fun q ↦ q.1 < q.2)
    let Bbad : Finset ℝ :=
      V x₀'' x₁'' ∪ Finset.univ.biUnion (fun r : Fin m ↦ V x₀'' (T r)) ∪
        pairsT.biUnion (fun q ↦ V (T q.1) (T q.2))
    have hBbad_cover : ∀ x₂ ∈ H,
        ∀ u ∈ Set.range Q₃ ∪ Set.range T, ∀ v ∈ Set.range Q₃ ∪ Set.range T,
          u < v → isRed u v x₂ → x₂ ∈ Bbad := by
      intro x₂ hx₂ u hu v hv huv hred
      rcases hu with ⟨i, rfl⟩ | ⟨r, rfl⟩ <;> rcases hv with ⟨j, rfl⟩ | ⟨s, rfl⟩
      · have hij : i < j := hQ₃_mono.lt_iff_lt.mp huv
        have hρ_ij : col₁ (ψ₁ (ψ₂ i)) (ψ₁ (ψ₂ j)) ⟨x₂, hx₂⟩ = ρ ⟨x₂, hx₂⟩ :=
          congrFun (hψ₁_eq (ψ₂ i) (ψ₂ j) (hψ₂_mono hij)) ⟨x₂, hx₂⟩
        have hρ_01 : col₁ (ψ₁ (ψ₂ 0)) (ψ₁ (ψ₂ 1)) ⟨x₂, hx₂⟩ = ρ ⟨x₂, hx₂⟩ :=
          congrFun (hψ₁_eq (ψ₂ 0) (ψ₂ 1) (hψ₂_mono (by omega))) ⟨x₂, hx₂⟩
        have hred01 : isRed x₀'' x₁'' x₂ := by
          have htrue : col₁ (ψ₁ (ψ₂ i)) (ψ₁ (ψ₂ j)) ⟨x₂, hx₂⟩ = true := decide_eq_true hred
          exact of_decide_eq_true (hρ_01.trans (hρ_ij.symm.trans htrue))
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hx₂, hred01⟩))
      · have hσ_i : col₂ (ψ₂ i) s ⟨x₂, hx₂⟩ = σ s ⟨x₂, hx₂⟩ :=
          congrFun (congrFun (hψ₂_eq i) s) ⟨x₂, hx₂⟩
        have hσ_0 : col₂ (ψ₂ 0) s ⟨x₂, hx₂⟩ = σ s ⟨x₂, hx₂⟩ :=
          congrFun (congrFun (hψ₂_eq 0) s) ⟨x₂, hx₂⟩
        have hred0 : isRed x₀'' (T s) x₂ := by
          have htrue : col₂ (ψ₂ i) s ⟨x₂, hx₂⟩ = true := decide_eq_true hred
          exact of_decide_eq_true (hσ_0.trans (hσ_i.symm.trans htrue))
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, Finset.mem_filter.mpr ⟨hx₂, hred0⟩⟩))
      · exact (lt_asymm huv (hQ₃T j r)).elim
      · have hrs : r < s := hT_mono.lt_iff_lt.mp huv
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨(r, s), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs⟩,
            Finset.mem_filter.mpr ⟨hx₂, hred⟩⟩)
    have hcard1 : (V x₀'' x₁'').card ≤ N - 1 :=
      hV_le x₀'' (Or.inl (hQ₃_sub ⟨0, rfl⟩)) x₁'' (Or.inl (hQ₃_sub ⟨1, rfl⟩)) (hQ₃_mono (by omega))
    have hcard2 : (Finset.univ.biUnion (fun r : Fin m ↦ V x₀'' (T r))).card ≤ m * (N - 1) := by
      calc (Finset.univ.biUnion (fun r : Fin m ↦ V x₀'' (T r))).card
          ≤ ∑ r : Fin m, (V x₀'' (T r)).card := Finset.card_biUnion_le
        _ ≤ ∑ _r : Fin m, (N - 1) := Finset.sum_le_sum fun r _ ↦
            hV_le x₀'' (Or.inl (hQ₃_sub ⟨0, rfl⟩)) (T r) (Or.inr ⟨r, rfl⟩) (hQ₃T 0 r)
        _ = m * (N - 1) := by simp
    have hcard3 : (pairsT.biUnion (fun q ↦ V (T q.1) (T q.2))).card ≤ (m * m) * (N - 1) := by
      calc (pairsT.biUnion (fun q ↦ V (T q.1) (T q.2))).card
          ≤ ∑ q ∈ pairsT, (V (T q.1) (T q.2)).card := Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ pairsT, (N - 1) := Finset.sum_le_sum fun q hq ↦
            hV_le (T q.1) (Or.inr ⟨q.1, rfl⟩) (T q.2) (Or.inr ⟨q.2, rfl⟩)
              (hT_mono (Finset.mem_filter.mp hq).2)
        _ = pairsT.card * (N - 1) := by simp
        _ ≤ (Finset.univ : Finset (Fin m × Fin m)).card * (N - 1) :=
            Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
        _ = (m * m) * (N - 1) := by simp
    have hBbad_lt : Bbad.card < H.card := by
      have hle : Bbad.card ≤ (N - 1) + m * (N - 1) + (m * m) * (N - 1) := by
        calc Bbad.card
            ≤ (V x₀'' x₁'' ∪ Finset.univ.biUnion (fun r : Fin m ↦ V x₀'' (T r))).card +
                (pairsT.biUnion (fun q ↦ V (T q.1) (T q.2))).card := Finset.card_union_le _ _
          _ ≤ (V x₀'' x₁'').card +
                (Finset.univ.biUnion (fun r : Fin m ↦ V x₀'' (T r))).card +
                (pairsT.biUnion (fun q ↦ V (T q.1) (T q.2))).card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ ≤ (N - 1) + m * (N - 1) + (m * m) * (N - 1) := by omega
      have hmul : (N - 1) + m * (N - 1) + (m * m) * (N - 1) = (N - 1) * (1 + m + m * m) := by
        ring
      rw [hH_card]
      dsimp only [p]
      omega
    have hH_sdiff : (H \ Bbad).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
      exact not_lt_of_ge (Finset.card_le_card hemp) hBbad_lt
    obtain ⟨x₂'', hx₂''⟩ := hH_sdiff
    obtain ⟨hx₂''H, hx₂''nbad⟩ := Finset.mem_sdiff.mp hx₂''
    obtain ⟨y₀, hy₀, y₁, hy₁, y₂, hy₂, hy₀₁, hy₁₂, hblue_y⟩ :=
      hex_blue_triple Q₃ T hQ₃_mono hT_mono hQ₃T
    have hy₂_neg : y₂ < 0 := by
      rcases hy₂ with ⟨k, rfl⟩ | ⟨r, rfl⟩
      · exact hA_neg _ (hQ₁A (ψ₁ (ψ₂ k)))
      · exact hA_neg _ (hTA r)
    have hy₂x₂ : y₂ < x₂'' := hy₂_neg.trans (hH_pos x₂'' hx₂''H)
    exact hNoBlue4 ⟨y₀, y₁, y₂, x₂'', hy₀₁, hy₁₂, hy₂x₂, hblue_y,
      fun hr ↦ hx₂''nbad (hBbad_cover x₂'' hx₂''H y₀ hy₀ y₁ hy₁ hy₀₁ hr),
      fun hr ↦ hx₂''nbad (hBbad_cover x₂'' hx₂''H y₀ hy₀ y₂ hy₂ (hy₀₁.trans hy₁₂) hr),
      fun hr ↦ hx₂''nbad (hBbad_cover x₂'' hx₂''H y₁ hy₁ y₂ hy₂ hy₁₂ hr)⟩

/- Section 5: Symmetry, Ordinal/Cardinal bridge, and main theorem -/

private lemma triplewise_of_lt {P : ℝ → ℝ → ℝ → Prop}
    (hSym : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (P x y z ↔ P y x z) ∧ (P x y z ↔ P x z y))
    {S : Set ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → P x y z) :
    S.Triplewise P := by
  have hall6 : ∀ {a b c : ℝ}, a ∈ S → b ∈ S → c ∈ S → a < b → b < c →
      P a b c ∧ P a c b ∧ P b a c ∧ P b c a ∧ P c a b ∧ P c b a := by
    intro a b c ha hb hc hab hbc
    have hac : a < c := hab.trans hbc
    have nab : a ≠ b := ne_of_lt hab
    have nbc : b ≠ c := ne_of_lt hbc
    have nac : a ≠ c := ne_of_lt hac
    have h_abc : P a b c := hS a ha b hb c hc hab hbc
    have h_bac : P b a c := (hSym a b c nab nbc nac).1.mp h_abc
    have h_acb : P a c b := (hSym a b c nab nbc nac).2.mp h_abc
    have h_bca : P b c a := (hSym b a c nab.symm nac nbc).2.mp h_bac
    have h_cab : P c a b := (hSym a c b nac nbc.symm nab).1.mp h_acb
    have h_cba : P c b a := (hSym c a b nac.symm nab nbc.symm).2.mp h_cab
    exact ⟨h_abc, h_acb, h_bac, h_bca, h_cab, h_cba⟩
  intro x hx y hy z hz hxy hyz hxz
  rcases lt_or_gt_of_ne hxy with hxy' | hyx'
  · rcases lt_or_gt_of_ne hyz with hyz' | hzy'
    · exact (hall6 hx hy hz hxy' hyz').1
    · rcases lt_or_gt_of_ne hxz with hxz' | hzx'
      · exact (hall6 hx hz hy hxz' hzy').2.1
      · exact (hall6 hz hx hy hzx' hxy').2.2.2.1
  · rcases lt_or_gt_of_ne hxz with hxz' | hzx'
    · exact (hall6 hy hx hz hyx' hxz').2.2.1
    · rcases lt_or_gt_of_ne hyz with hyz' | hzy'
      · exact (hall6 hy hz hx hyz' hzx').2.2.2.2.1
      · exact (hall6 hz hy hx hzy' hyx').2.2.2.2.2

theorem main_thm (n : ℕ) (_hn : 2 ≤ n) :
    Erdos70.RealCardinalRamsey3 (ω + n) 4 := by
  intro isRed hSym
  rcases erdos_rado_ordered n isRed with
      ⟨f, g, hf_mono, hg_mono, hfg, hred_lt⟩ |
      ⟨x₀, x₁, x₂, x₃, hx₀₁, hx₁₂, hx₂₃, hb012, hb013, hb023, hb123⟩
  · left
    have htype : Ordinal.type
        (Sum.Lex ((· < ·) : ℕ → ℕ → Prop) ((· < ·) : Fin n → Fin n → Prop)) =
        ω + (n : Ordinal.{0}) := by
      rw [Ordinal.type_sum_lex, ← Ordinal.type_nat_lt, ← Ordinal.type_fin]
    obtain ⟨iso⟩ :=
      Ordinal.type_eq.mp ((Ordinal.type_toType (ω + (n : Ordinal.{0}))).trans htype.symm)
    have hsum_mono : ∀ {s₁ s₂ : ℕ ⊕ Fin n},
        Sum.Lex (· < ·) (· < ·) s₁ s₂ → Sum.elim f g s₁ < Sum.elim f g s₂ := by
      intro s₁ s₂ hs
      cases hs with
      | inl h => exact hf_mono h
      | inr h => exact hg_mono h
      | sep k r => exact hfg k r
    let e : (ω + (n : Ordinal.{0})).ToType ↪o ℝ :=
      OrderEmbedding.ofStrictMono (fun a ↦ Sum.elim f g (iso a))
        (fun a b hab ↦ hsum_mono (iso.map_rel_iff.mpr hab))
    have he_apply : ∀ a, e a = Sum.elim f g (iso a) := fun _ ↦ rfl
    have hrange : Set.range e = Set.range f ∪ Set.range g := by
      ext x
      simp only [Set.mem_range, Set.mem_union]
      constructor
      · rintro ⟨a, rfl⟩
        rw [he_apply]
        exact Sum.casesOn (iso a) (fun k ↦ Or.inl ⟨k, rfl⟩) (fun r ↦ Or.inr ⟨r, rfl⟩)
      · rintro (⟨k, rfl⟩ | ⟨r, rfl⟩)
        · refine ⟨iso.symm (Sum.inl k), ?_⟩
          rw [he_apply, iso.apply_symm_apply]
          rfl
        · refine ⟨iso.symm (Sum.inr r), ?_⟩
          rw [he_apply, iso.apply_symm_apply]
          rfl
    refine ⟨e, ?_⟩
    rw [hrange]
    exact triplewise_of_lt hSym hred_lt
  · right
    classical
    let F : Finset ℝ := {x₀, x₁, x₂, x₃}
    have hx₀₂ : x₀ < x₂ := hx₀₁.trans hx₁₂
    have hx₀₃ : x₀ < x₃ := hx₀₂.trans hx₂₃
    have hx₁₃ : x₁ < x₃ := hx₁₂.trans hx₂₃
    have hFcard : F.card = 4 := by
      dsimp only [F]
      rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hx₀₁, ne_of_lt hx₀₂, ne_of_lt hx₀₃]),
        Finset.card_insert_of_notMem (by simp [ne_of_lt hx₁₂, ne_of_lt hx₁₃]),
        Finset.card_insert_of_notMem (by simp [ne_of_lt hx₂₃]),
        Finset.card_singleton]
    refine ⟨(F : Set ℝ), ?_, ?_⟩
    · simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset, hFcard]
      norm_num
    · refine triplewise_of_lt (fun x y z hxy hyz hxz ↦
        ⟨not_iff_not.mpr (hSym x y z hxy hyz hxz).1,
         not_iff_not.mpr (hSym x y z hxy hyz hxz).2⟩) ?_
      intro x hx y hy z hz hxy hyz
      simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy hz
      rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;>
        rcases hz with rfl | rfl | rfl | rfl <;>
        first
        | exact hb012
        | exact hb013
        | exact hb023
        | exact hb123
        | linarith

end Erdos70ErdosRado

theorem OMA.solution : type_of% @Erdos70.erdos_70.variants.erdos_rado :=
  Erdos70ErdosRado.main_thm

