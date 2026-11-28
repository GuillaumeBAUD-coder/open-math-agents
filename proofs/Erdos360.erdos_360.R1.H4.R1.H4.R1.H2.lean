import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1_H4_R1
import Mathlib
-- Credit: @LordMike
-- Route: Hamidoune isoperimetric (atom) method, giving Olson's bound
-- |B + S| >= min(|G|, |B| + |S|/2) for S in no coset of a proper subgroup.

namespace OMA.E360H2

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- `X` is a candidate for `S`: nonempty, and `X + S` is not the whole group. -/
def IsCand (S X : Finset G) : Prop := X.Nonempty ∧ X + S ≠ Finset.univ

/-- `X` is a fragment: a candidate of minimal boundary `|X + S| - |X|` (stated without subtraction). -/
def IsFrag (S X : Finset G) : Prop :=
  IsCand S X ∧ ∀ Y : Finset G, IsCand S Y → (X + S).card + Y.card ≤ (Y + S).card + X.card

/-- `X` is an atom: a fragment of minimal cardinality. -/
def IsAtom (S X : Finset G) : Prop :=
  IsFrag S X ∧ ∀ Y : Finset G, IsFrag S Y → X.card ≤ Y.card

/-- The `k`-fold sumset, in the exact form used by the hypothesis H2. -/
def kSum (A : Finset G) (k : ℕ) : Finset G :=
  (Fintype.piFinset (fun _ : Fin k => A)).image (fun f => ∑ i : Fin k, f i)

/-- L1: if a candidate exists, an atom exists. -/
theorem exists_atom {S B : Finset G} (hB : IsCand S B) : ∃ X, IsAtom S X := by
  classical
  obtain ⟨X₀, hX₀C, hX₀min⟩ := Finset.exists_min_image (Finset.univ.filter (IsCand S))
    (fun X : Finset G => ((X + S).card : ℤ) - X.card) ⟨B, by simpa using hB⟩
  have hX₀ : IsFrag S X₀ := by
    refine ⟨by simpa using hX₀C, fun Y hY => ?_⟩
    have := hX₀min Y (by simpa using hY)
    omega
  obtain ⟨X, hXF, hXmin⟩ := Finset.exists_min_image (Finset.univ.filter (IsFrag S))
    (fun X : Finset G => X.card) ⟨X₀, by simpa using hX₀⟩
  exact ⟨X, by simpa using hXF, fun Y hY => hXmin Y (by simpa using hY)⟩

theorem isAtom_vadd_aux1 (S X : Finset G) (g : G) : (g +ᵥ X) + S = g +ᵥ (X + S) := by
  ext z
  simp only [Finset.mem_add, Finset.mem_vadd_finset, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, s, hs, rfl⟩
    exact ⟨x + s, ⟨x, hx, s, hs, rfl⟩, by abel⟩
  · rintro ⟨_, ⟨x, hx, s, hs, rfl⟩, rfl⟩
    exact ⟨g + x, ⟨x, hx, rfl⟩, s, hs, by abel⟩

theorem isAtom_vadd_aux2 (S X : Finset G) (g : G) : IsCand S (g +ᵥ X) ↔ IsCand S X := by
  unfold IsCand
  rw [isAtom_vadd_aux1, Finset.vadd_finset_nonempty]
  have : g +ᵥ (X + S) = Finset.univ ↔ X + S = Finset.univ := by
    constructor
    · intro h
      have := congrArg (fun T => (-g) +ᵥ T) h
      simpa [neg_vadd_vadd] using this
    · intro h
      rw [h, Finset.vadd_finset_univ]
  simp only [ne_eq, this]

/-- L2: translates of atoms are atoms. -/
theorem isAtom_vadd {S X : Finset G} (hX : IsAtom S X) (g : G) : IsAtom S (g +ᵥ X) := by
  obtain ⟨⟨hc, hf⟩, hm⟩ := hX
  have hcard : ∀ T : Finset G, (g +ᵥ T).card = T.card := fun T => Finset.card_vadd_finset g T
  refine ⟨⟨(isAtom_vadd_aux2 S X g).2 hc, fun Y hY => ?_⟩, fun Y hY => ?_⟩
  · rw [isAtom_vadd_aux1, hcard, hcard]
    exact hf Y hY
  · rw [hcard]
    exact hm Y hY

/-- L3: an atom is no larger than the complement of its sumset. -/
theorem atom_card_add_le {S X : Finset G} (hX : IsAtom S X) :
    X.card + (X + S).card ≤ Fintype.card G := by
  classical
  obtain ⟨⟨hXne, hXS⟩, hXfrag⟩ := hX.1
  set W : Finset G := Finset.univ \ (X + S) with hW
  have hWcard : W.card + (X + S).card = Fintype.card G := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (X + S))
    rw [Finset.card_univ] at this
    exact this
  have hWne : W.Nonempty := by
    rw [hW, Finset.sdiff_nonempty]
    intro h
    exact hXS (Finset.eq_univ_of_forall (fun g => h (Finset.mem_univ g)))
  have hYcard : (-W).card = W.card := Finset.card_neg W
  have hsub : (-W) + S ⊆ Finset.univ \ (-X) := by
    intro z hz
    obtain ⟨y, hy, s, hs, rfl⟩ := Finset.mem_add.mp hz
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    rw [Finset.mem_neg'] at hmem hy
    have hwW : -y ∈ W := hy
    rw [hW, Finset.mem_sdiff] at hwW
    apply hwW.2
    have : -y = -(y + s) + s := by abel
    rw [this]
    exact Finset.mem_add.mpr ⟨_, hmem, s, hs, rfl⟩
  have hXcard : (Finset.univ \ (-X)).card + X.card = Fintype.card G := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (-X))
    rw [Finset.card_univ, Finset.card_neg] at this
    exact this
  have hYS : ((-W) + S).card + X.card ≤ Fintype.card G := by
    have := Finset.card_le_card hsub
    omega
  have hXpos : 0 < X.card := Finset.card_pos.mpr hXne
  have hYcand : IsCand S (-W) := by
    refine ⟨hWne.neg, ?_⟩
    intro h
    rw [h, Finset.card_univ] at hYS
    omega
  have hYfrag : IsFrag S (-W) := by
    refine ⟨hYcand, ?_⟩
    intro Z hZ
    have := hXfrag Z hZ
    omega
  have := hX.2 _ hYfrag
  omega

/-- L4: intersection of two fragments is a fragment, under a size condition. -/
theorem isFrag_inter {S X Y : Finset G} (hX : IsFrag S X) (hY : IsFrag S Y)
    (hXY : (X ∩ Y).Nonempty) (hsize : X.card + (Y + S).card ≤ Fintype.card G) :
    IsFrag S (X ∩ Y) := by
  classical
  obtain ⟨⟨hXne, hXS⟩, hXmin⟩ := hX
  obtain ⟨⟨hYne, hYS⟩, hYmin⟩ := hY
  have hsub : (X ∩ Y) + S ⊆ (X + S) ∩ (Y + S) :=
    Finset.subset_inter (Finset.add_subset_add_right Finset.inter_subset_left)
      (Finset.add_subset_add_right Finset.inter_subset_right)
  have hcand : IsCand S (X ∩ Y) := by
    refine ⟨hXY, fun h => hXS ?_⟩
    apply Finset.eq_univ_of_card
    apply le_antisymm (Finset.card_le_univ _)
    have := Finset.card_le_card (Finset.add_subset_add_right (t := S) (Finset.inter_subset_left (s₁ := X) (s₂ := Y)))
    rw [h, Finset.card_univ] at this
    exact this
  have h1 := hXmin Y ⟨hYne, hYS⟩
  have h2 := hYmin X ⟨hXne, hXS⟩
  have hunion : (X ∪ Y) + S = (X + S) ∪ (Y + S) := Finset.union_add
  have hkey : (X ∪ Y).card + (X + S).card ≤ ((X ∪ Y) + S).card + X.card := by
    by_cases h : (X ∪ Y) + S = Finset.univ
    · have hc : ((X ∪ Y) + S).card = Fintype.card G := by rw [h, Finset.card_univ]
      have := Finset.card_union_le X Y
      omega
    · have := hXmin (X ∪ Y) ⟨hXne.mono Finset.subset_union_left, h⟩
      omega
  have c1 := Finset.card_union_add_card_inter (X + S) (Y + S)
  have c2 := Finset.card_union_add_card_inter X Y
  have c3 := Finset.card_le_card hsub
  rw [← hunion] at c1
  refine ⟨hcand, fun Z hZ => ?_⟩
  have := hXmin Z hZ
  omega

/-- L5: an atom meeting its translate equals it. -/
theorem atom_vadd_eq {S X : Finset G} (hX : IsAtom S X) (g : G)
    (hg : (X ∩ (g +ᵥ X)).Nonempty) : g +ᵥ X = X := by
  have hY := isAtom_vadd hX g
  have hYS : ((g +ᵥ X) + S) = g +ᵥ (X + S) := by
    ext z
    simp only [Finset.mem_add, Finset.mem_vadd_finset]
    constructor
    · rintro ⟨a, ⟨x, hx, rfl⟩, s, hs, rfl⟩
      exact ⟨x + s, ⟨x, hx, s, hs, rfl⟩, by simp [vadd_eq_add, add_assoc]⟩
    · rintro ⟨w, ⟨x, hx, s, hs, rfl⟩, rfl⟩
      exact ⟨g + x, ⟨x, hx, rfl⟩, s, hs, by simp [vadd_eq_add, add_assoc]⟩
  have hcard : ((g +ᵥ X) + S).card = (X + S).card := by
    rw [hYS, Finset.card_vadd_finset]
  have h3 := atom_card_add_le hX
  have hF := isFrag_inter hX.1 hY.1 hg (by omega)
  have h1 : X.card ≤ (X ∩ (g +ᵥ X)).card := hX.2 _ hF
  have h2 : X ∩ (g +ᵥ X) = X :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left h1
  have hsub : X ⊆ g +ᵥ X := by
    intro x hx
    exact (Finset.mem_inter.1 (h2 ▸ hx)).2
  symm
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_vadd_finset])

/-- L6: the boundary of an atom is at least |S|/2 when S lies in no coset of a proper subgroup. -/
theorem atom_bound {S X : Finset G} (hX : IsAtom S X) (hS0 : S.Nonempty)
    (hS : ∀ H : AddSubgroup G, H ≠ ⊤ → ¬ ∃ x : G, ∀ a ∈ S, a - x ∈ H) :
    S.card + 2 * X.card ≤ 2 * (X + S).card := by
  classical
  have hXc : IsCand S X := hX.1.1
  obtain ⟨x₀, hx₀⟩ := hXc.1
  obtain ⟨s₂, hs₂⟩ := hS0
  let H : AddSubgroup G :=
    { carrier := {g | g +ᵥ X = X}
      zero_mem' := by simp
      add_mem' := by
        intro g h hg hh
        change (g + h) +ᵥ X = X
        change g +ᵥ X = X at hg
        change h +ᵥ X = X at hh
        rw [add_vadd, hh, hg]
      neg_mem' := by
        intro g hg
        change (-g) +ᵥ X = X
        change g +ᵥ X = X at hg
        calc (-g) +ᵥ X = (-g) +ᵥ (g +ᵥ X) := by rw [hg]
          _ = X := by rw [vadd_vadd, neg_add_cancel, zero_vadd] }
  have hmemH : ∀ g, g ∈ H ↔ g +ᵥ X = X := fun g => Iff.rfl
  have hne : H ≠ ⊤ := by
    intro hT
    apply hXc.2
    have hXu : X = Finset.univ := by
      ext y
      simp only [Finset.mem_univ, iff_true]
      have h1 : (y - x₀) +ᵥ X = X := (hmemH _).1 (by rw [hT]; trivial)
      rw [← h1]
      exact Finset.mem_vadd_finset.2 ⟨x₀, hx₀, by simp⟩
    ext y
    simp only [Finset.mem_univ, iff_true]
    exact Finset.mem_add.2 ⟨y - s₂, by rw [hXu]; exact Finset.mem_univ _, s₂, hs₂, by simp⟩
  have h2 := hS H hne
  push Not at h2
  obtain ⟨s₁, hs₁, hs₁H⟩ := h2 s₂
  have hdisj : Disjoint (s₁ +ᵥ X) (s₂ +ᵥ X) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_vadd_finset.1 ha
    obtain ⟨x', hx', hxx⟩ := Finset.mem_vadd_finset.1 hb
    apply hs₁H
    rw [hmemH]
    apply atom_vadd_eq hX
    refine ⟨x', Finset.mem_inter.2 ⟨hx', Finset.mem_vadd_finset.2 ⟨x, hx, ?_⟩⟩⟩
    simp only [vadd_eq_add] at hxx ⊢
    have h3 : s₂ + x' = s₁ + x := hxx
    calc s₁ - s₂ + x = (s₁ + x) - s₂ := by abel
      _ = (s₂ + x') - s₂ := by rw [h3]
      _ = x' := by abel
  have hsub : (s₁ +ᵥ X) ∪ (s₂ +ᵥ X) ⊆ X + S := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_vadd_finset.1 h
      exact Finset.mem_add.2 ⟨x, hx, s₁, hs₁, by simp [add_comm]⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_vadd_finset.1 h
      exact Finset.mem_add.2 ⟨x, hx, s₂, hs₂, by simp [add_comm]⟩
  have hc1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_vadd_finset, Finset.card_vadd_finset] at hc1
  have hsub2 : x₀ +ᵥ S ⊆ X + S := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_vadd_finset.1 ha
    exact Finset.mem_add.2 ⟨x₀, hx₀, s, hs, rfl⟩
  have hc2 := Finset.card_le_card hsub2
  rw [Finset.card_vadd_finset] at hc2
  omega

/-- L7: Olson's increment bound. -/
theorem increment {S B : Finset G} (hB : B.Nonempty) (hS0 : S.Nonempty)
    (hS : ∀ H : AddSubgroup G, H ≠ ⊤ → ¬ ∃ x : G, ∀ a ∈ S, a - x ∈ H) :
    Fintype.card G ≤ (B + S).card ∨ 2 * B.card + S.card ≤ 2 * (B + S).card := by
  by_cases h : B + S = Finset.univ
  · left
    rw [h, Finset.card_univ]
  · right
    obtain ⟨X, hX⟩ := exists_atom (S := S) (B := B) (And.intro hB h)
    have h1 := hX.1.2 B (And.intro hB h)
    have h2 := atom_bound hX hS0 hS
    omega

/-- L8a: the 1-fold sumset is the set itself. -/
theorem kSum_one (A : Finset G) : kSum A 1 = A := by
  ext x
  simp only [kSum, Finset.mem_image, Fintype.mem_piFinset, Fin.sum_univ_one]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf 0
  · intro hx
    exact ⟨fun _ => x, fun _ => hx, rfl⟩

/-- L8b: the (k+1)-fold sumset is the k-fold sumset plus A. -/
theorem kSum_succ (A : Finset G) (k : ℕ) : kSum A (k + 1) = kSum A k + A := by
  ext x
  simp only [kSum, Finset.mem_image, Finset.mem_add, Fintype.mem_piFinset]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨∑ i : Fin k, f i.castSucc, ⟨fun i => f i.castSucc, fun i => hf _, rfl⟩,
      f (Fin.last k), hf _, ?_⟩
    rw [Fin.sum_univ_castSucc]
  · rintro ⟨_, ⟨g, hg, rfl⟩, a, ha, rfl⟩
    refine ⟨Fin.snoc (α := fun _ => G) g a, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using ha
      · simpa using hg j
    · rw [Fin.sum_univ_castSucc]
      simp

theorem kSum_bound_aux1 (A : Finset G) (hA : A.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    (kSum A k).Nonempty := by
  induction k, hk using Nat.le_induction with
  | base => rw [kSum_one]; exact hA
  | succ j hj ih2 => rw [kSum_succ]; exact ih2.add hA

/-- L9: the k-fold bound, by induction from L7 and L8. -/
theorem kSum_bound (A : Finset G) (k : ℕ) (hk : 1 ≤ k)
    (hS : ∀ H : AddSubgroup G, H ≠ ⊤ → ¬ ∃ x : G, ∀ a ∈ A, a - x ∈ H) :
    min (Fintype.card G : ℝ) (((k + 1 : ℕ) : ℝ) * (A.card : ℝ) / 2) ≤ ((kSum A k).card : ℝ) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
    exact (min_le_right _ _).trans (Nat.cast_nonneg _)
  induction k, hk using Nat.le_induction with
  | base =>
    rw [kSum_one]
    exact min_le_of_right_le (by push_cast; nlinarith [(Nat.cast_nonneg A.card : (0:ℝ) ≤ A.card)])
  | succ k hk ih =>
    have hne : (kSum A k).Nonempty := kSum_bound_aux1 A hA k hk
    rw [kSum_succ]
    set B := kSum A k with hB
    have hle : B.card ≤ (B + A).card := by
      obtain ⟨a, ha⟩ := hA
      calc B.card = (B + {a}).card := by simp
        _ ≤ (B + A).card := Finset.card_le_card (Finset.add_subset_add_left (by simpa using ha))
    rcases increment hne hA hS with h | h
    · exact min_le_of_left_le (by exact_mod_cast h)
    · have h' : (2 * B.card + A.card : ℝ) ≤ 2 * (B + A).card := by exact_mod_cast h
      rcases le_total (Fintype.card G : ℝ) (B.card : ℝ) with h1 | h1
      · exact min_le_of_left_le (h1.trans (by exact_mod_cast hle))
      · have ih' := ih
        rcases min_le_iff.mp ih' with h2 | h2
        · exact min_le_of_left_le (by
            have : Fintype.card G ≤ (B + A).card := by
              have : Fintype.card G ≤ B.card := by exact_mod_cast h2
              omega
            exact_mod_cast this)
        · apply min_le_of_right_le
          push_cast at h2 ⊢
          linarith

end OMA.E360H2

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1_H4_R1_H4_R1.H2 := by
  intro m _ A k hk hS
  have h := OMA.E360H2.kSum_bound (G := ZMod m) A k hk hS
  rw [ZMod.card] at h
  exact h
