import OMAStatements.S_erdos_531
import Mathlib

namespace OMA.P531
open OMA.S_erdos_531 Hindman

lemma step (j : ℕ) (hj : 1 ≤ j) : ∀ a : Stream' ℕ+, ∃ x : ℕ+, j ≤ (x : ℕ) ∧ x ∈ FS a ∧
    ∀ y ∈ FS (a.drop j), x + y ∈ FS a := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro a
    refine ⟨a.head, a.head.pos, FS.head a, ?_⟩
    intro y hy
    exact FS.cons a y hy
  | succ j hj ih =>
    intro a
    obtain ⟨x, hx1, hx2, hx3⟩ := ih a.tail
    refine ⟨a.head + x, ?_, FS.cons a x hx2, ?_⟩
    · have := a.head.pos
      simp only [PNat.add_coe]
      omega
    · intro y hy
      rw [Stream'.drop_succ] at hy
      rw [add_assoc]
      exact FS.cons a _ (hx3 y hy)

lemma key (k : ℕ) : ∀ (a : Stream' ℕ+) (M : ℕ), ∃ A : Finset ℕ, A.card = k ∧ (∀ x ∈ A, M < x) ∧
    ∀ S ⊆ A, S.Nonempty → ∃ y ∈ FS a, (y : ℕ) = S.sum id := by
  induction k with
  | zero =>
    intro a M
    refine ⟨∅, rfl, by simp, ?_⟩
    intro S hS hne
    rw [Finset.subset_empty] at hS
    subst hS
    simp at hne
  | succ k ih =>
    intro a M
    obtain ⟨x, hx1, hx2, hx3⟩ := step (M + 1) (by omega) a
    obtain ⟨A, hA1, hA2, hA3⟩ := ih (a.drop (M + 1)) x
    have hxA : (x : ℕ) ∉ A := fun h => lt_irrefl _ (hA2 _ h)
    refine ⟨insert (x : ℕ) A, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hxA, hA1]
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · omega
      · have := hA2 z hz; omega
    · intro S hS hne
      by_cases hxS : (x : ℕ) ∈ S
      · rcases (S.erase (x : ℕ)).eq_empty_or_nonempty with he | he
        · refine ⟨x, hx2, ?_⟩
          have : S = {(x : ℕ)} := by
            ext z; constructor
            · intro hz
              by_contra hzx
              have : z ∈ S.erase (x : ℕ) := Finset.mem_erase.mpr ⟨by simpa using hzx, hz⟩
              rw [he] at this; simp at this
            · intro hz; rw [Finset.mem_singleton] at hz; rw [hz]; exact hxS
          rw [this]; simp
        · have hsub : S.erase (x : ℕ) ⊆ A := by
            intro z hz
            have h1 := Finset.mem_erase.mp hz
            have h2 := hS h1.2
            rw [Finset.mem_insert] at h2
            rcases h2 with h2 | h2
            · exact absurd h2 h1.1
            · exact h2
          obtain ⟨y, hy1, hy2⟩ := hA3 _ hsub he
          refine ⟨x + y, hx3 y hy1, ?_⟩
          rw [← Finset.add_sum_erase S id hxS, PNat.add_coe, hy2]
          rfl
      · have hsub : S ⊆ A := by
          intro z hz
          have h2 := hS hz
          rw [Finset.mem_insert] at h2
          rcases h2 with h2 | h2
          · rw [h2] at hz; exact absurd hz hxS
          · exact h2
        obtain ⟨y, hy1, hy2⟩ := hA3 _ hsub hne
        exact ⟨y, FS_iter_tail_sub_FS a (M + 1) hy1, hy2⟩

/-- The red part of a colouring on the interval. -/
def redOf (N : ℕ) (col : ℕ → Bool) : Finset ℕ := (Finset.Icc 1 N).filter (fun i => col i = true)

/-- A colouring is bad for N. -/
def Bad (k N : ℕ) (col : ℕ → Bool) : Prop :=
  ¬ ∃ A ∈ (Finset.Icc 1 N).powersetCard k,
    subsetSums A ⊆ redOf N col ∨ subsetSums A ⊆ Finset.Icc 1 N \ redOf N col

lemma bad_mono (k N : ℕ) (col : ℕ → Bool) (h : Bad k (N + 1) col) : Bad k N col := by
  rintro ⟨A, hA, h1 | h1⟩
  · apply h
    refine ⟨A, ?_, Or.inl ?_⟩
    · rw [Finset.mem_powersetCard] at hA ⊢
      exact ⟨hA.1.trans (Finset.Icc_subset_Icc le_rfl (by omega)), hA.2⟩
    · intro z hz
      have := h1 hz
      simp only [redOf, Finset.mem_filter, Finset.mem_Icc] at this ⊢
      exact ⟨⟨this.1.1, by omega⟩, this.2⟩
  · apply h
    refine ⟨A, ?_, Or.inr ?_⟩
    · rw [Finset.mem_powersetCard] at hA ⊢
      exact ⟨hA.1.trans (Finset.Icc_subset_Icc le_rfl (by omega)), hA.2⟩
    · intro z hz
      have := h1 hz
      simp only [redOf, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at this ⊢
      refine ⟨⟨this.1.1, by omega⟩, ?_⟩
      intro h2
      exact this.2 ⟨this.1, h2.2⟩

lemma bad_closed (k N : ℕ) : IsClosed {col : ℕ → Bool | Bad k N col} := by
  let r : (ℕ → Bool) → (Fin (N + 1) → Bool) := fun col i => col i
  have hr : Continuous r := continuous_pi fun i => continuous_apply _
  have : {col : ℕ → Bool | Bad k N col} = r ⁻¹' (r '' {col | Bad k N col}) := by
    ext col
    constructor
    · intro h; exact ⟨col, h, rfl⟩
    · rintro ⟨col', h', he⟩
      have hred : redOf N col = redOf N col' := by
        ext i
        simp only [redOf, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hi, hc⟩
          refine ⟨hi, ?_⟩
          have := congrFun he ⟨i, by omega⟩
          simp only [r] at this
          rw [this]; exact hc
        · rintro ⟨hi, hc⟩
          refine ⟨hi, ?_⟩
          have := congrFun he ⟨i, by omega⟩
          simp only [r] at this
          rw [← this]; exact hc
      show Bad k N col
      unfold Bad; rw [hred]; exact h'
  rw [this]
  exact (isClosed_discrete _).preimage hr

lemma forces_mono (k N N' : ℕ) (h : ForcesMonoSums k N) (hN : N ≤ N') : ForcesMonoSums k N' := by
  intro red hred
  obtain ⟨A, hA, h1⟩ := h (red ∩ Finset.Icc 1 N) (by
    rw [Finset.mem_powerset]; exact Finset.inter_subset_right)
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 N' := Finset.Icc_subset_Icc le_rfl hN
  refine ⟨A, ?_, ?_⟩
  · rw [Finset.mem_powersetCard] at hA ⊢
    exact ⟨hA.1.trans hsub, hA.2⟩
  · rcases h1 with h1 | h1
    · left; exact h1.trans Finset.inter_subset_left
    · right
      intro z hz
      have := h1 hz
      simp only [Finset.mem_sdiff, Finset.mem_inter] at this ⊢
      exact ⟨hsub this.1, fun h2 => this.2 ⟨h2, this.1⟩⟩

lemma exists_forces (k : ℕ) : ∃ N, ForcesMonoSums k N := by
  by_contra hno
  push Not at hno
  have hne : ∀ N, ({col : ℕ → Bool | Bad k N col}).Nonempty := by
    intro N
    have h := hno N
    simp only [ForcesMonoSums, not_forall, not_exists] at h
    obtain ⟨red, hred, hA⟩ := h
    refine ⟨fun i => decide (i ∈ red), ?_⟩
    have hr : redOf N (fun i => decide (i ∈ red)) = red := by
      ext i
      simp only [redOf, Finset.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨Finset.mem_powerset.mp hred h, h⟩
    show Bad k N _
    unfold Bad
    rw [hr]
    rintro ⟨A, hA1, hA2⟩
    exact hA A ⟨hA1, hA2⟩
  obtain ⟨col, hcol⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun N => {col : ℕ → Bool | Bad k N col}) (fun N col h => bad_mono k N col h) hne
    (bad_closed k 0).isCompact (fun N => bad_closed k N)
  rw [Set.mem_iInter] at hcol
  obtain ⟨c, hc, a, hac⟩ := exists_FS_of_finite_cover
    ({{x : ℕ+ | col x = true}, {x : ℕ+ | col x = false}} : Set (Set ℕ+))
    (Set.toFinite _) (by
      intro x _
      by_cases hx : col x = true
      · exact ⟨_, Set.mem_insert _ _, hx⟩
      · exact ⟨_, Set.mem_insert_of_mem _ rfl, by simpa using hx⟩)
  obtain ⟨A, hA1, hA2, hA3⟩ := key k a 0
  apply hcol (A.sum id)
  have hsumle : ∀ S ⊆ A, S.sum id ≤ A.sum id := fun S hS =>
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have hss : ∀ z ∈ subsetSums A, z ∈ Finset.Icc 1 (A.sum id) ∧ ∃ y ∈ FS a, (y : ℕ) = z := by
    intro z hz
    simp only [subsetSums, Finset.mem_image, Finset.mem_erase, Finset.mem_powerset] at hz
    obtain ⟨S, ⟨hS0, hS⟩, rfl⟩ := hz
    obtain ⟨y, hy, hyz⟩ := hA3 S hS (Finset.nonempty_iff_ne_empty.mpr hS0)
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hsumle S hS⟩, y, hy, hyz⟩
    rw [← hyz]; exact y.pos
  refine ⟨A, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, hA1⟩
    intro x hx
    rw [Finset.mem_Icc]
    refine ⟨hA2 x hx, ?_⟩
    have := hsumle {x} (Finset.singleton_subset_iff.mpr hx)
    simpa using this
  · rcases hc with rfl | hc
    · left
      intro z hz
      obtain ⟨hz1, y, hy, hyz⟩ := hss z hz
      have := hac hy
      simp only [Set.mem_ofPred_eq] at this
      simp only [redOf, Finset.mem_filter]
      rw [← hyz]
      exact ⟨by rw [hyz]; exact hz1, this⟩
    · rw [Set.mem_singleton_iff] at hc
      subst hc
      right
      intro z hz
      obtain ⟨hz1, y, hy, hyz⟩ := hss z hz
      have := hac hy
      simp only [Set.mem_ofPred_eq] at this
      simp only [redOf, Finset.mem_sdiff, Finset.mem_filter, not_and]
      refine ⟨hz1, fun _ => ?_⟩
      rw [← hyz, this]
      simp

lemma isLeast (k : ℕ) : IsLeast {N : ℕ | ForcesMonoSums k N} (folkmanNumber k) :=
  ⟨Nat.sInf_mem (exists_forces k), fun _ h => Nat.sInf_le h⟩

end OMA.P531

theorem OMA.solution : type_of% @OMA.S_erdos_531.main := by
  refine ⟨fun k _ => OMA.P531.isLeast k, ?_⟩
  intro k₀ lower upper _
  have hF : ∀ k N, OMA.S_erdos_531.folkmanNumber k ≤ N ↔ OMA.S_erdos_531.ForcesMonoSums k N := by
    intro k N
    constructor
    · intro h
      exact OMA.P531.forces_mono k _ N (OMA.P531.isLeast k).1 h
    · intro h
      exact (OMA.P531.isLeast k).2 h
  unfold OMA.S_erdos_531.BoundsFrom
  constructor
  · intro h k hk
    obtain ⟨h1, h2⟩ := h k hk
    refine ⟨fun hc => ?_, (hF k _).mp h2⟩
    have := (hF k _).mpr hc
    omega
  · intro h k hk
    obtain ⟨h1, h2⟩ := h k hk
    refine ⟨?_, (hF k _).mpr h2⟩
    by_contra hc
    exact h1 ((hF k _).mp (by omega))
