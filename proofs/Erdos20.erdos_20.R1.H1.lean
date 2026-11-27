import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib

-- Step Erdos20.erdos_20.R1.H1: hypothesis H1 of reduction Erdos20.erdos_20.R1
-- Credit: @ivillar
--
-- Proof (color coding by double counting). Let U be the union of the family F. For a coloring
-- k : U -> Fin n, call A in F rainbow if k is injective on A. For each A in F, exactly
-- n! * n^(|U| - n) of the n^|U| colorings make A rainbow. Summing over colorings, the average
-- number of rainbow sets is |F| * n! / n^n, so some coloring reaches it. Extend that coloring
-- to all of the type by a constant, and take G to be its rainbow sets (injective = bijective,
-- as |A| = n).

namespace OMA.Erdos20H1

theorem count_inj {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (n : ℕ)
    (hs : s.card = n) :
    (Finset.univ.filter (fun κ : ι → Fin n => Set.InjOn κ ↑s)).card * n ^ n =
      n.factorial * n ^ Fintype.card ι := by
  classical
  let e : {κ : ι → Fin n // Set.InjOn κ ↑s} ≃ (↥s ↪ Fin n) × ({i // i ∉ s} → Fin n) :=
    { toFun := fun κ => (⟨fun i => κ.1 i, fun a b h => Subtype.ext (κ.2 a.2 b.2 h)⟩,
        fun i => κ.1 i)
      invFun := fun p => ⟨fun i => if h : i ∈ s then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩, by
        intro a ha b hb hab
        simp only [Finset.mem_coe] at ha hb
        simp only [dif_pos ha, dif_pos hb] at hab
        exact congrArg Subtype.val (p.1.injective hab)⟩
      left_inv := fun κ => by
        apply Subtype.ext
        funext i
        by_cases h : i ∈ s
        · simp only [dif_pos h]; rfl
        · simp only [dif_neg h]
      right_inv := fun p => by
        rcases p with ⟨e', ψ⟩
        refine Prod.ext ?_ ?_
        · ext i
          simp [i.2]
        · funext i
          simp [i.2] }
  have h1 : Fintype.card {κ : ι → Fin n // Set.InjOn κ ↑s} =
      n.factorial * n ^ (Fintype.card ι - n) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fun]
    simp [hs, Fintype.card_subtype_compl, Nat.descFactorial_self]
  have hle : n ≤ Fintype.card ι := hs ▸ Finset.card_le_univ s
  rw [← Fintype.card_subtype, h1, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end OMA.Erdos20H1

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  unfold OMA.R_Erdos20_erdos_20_R1.H1
  intro α n hn F hF
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set U : Finset α := F.biUnion id with hU
  have hAU : ∀ A ∈ F, ∀ x ∈ A, x ∈ U := fun A hA x hx => Finset.mem_biUnion.2 ⟨A, hA, hx⟩
  let c : (↥U → Fin n) → α → Fin n := fun κ x => if h : x ∈ U then κ ⟨x, h⟩ else ⟨0, hn⟩
  let P : (↥U → Fin n) → Finset α → Prop := fun κ A => Function.Injective (fun x : A => c κ x)
  have key : ∀ A ∈ F, ∀ κ, P κ A ↔ Set.InjOn κ ↑(A.subtype (· ∈ U)) := by
    intro A hA κ
    constructor
    · intro h y1 hy1 y2 hy2 heq
      rw [Finset.mem_coe, Finset.mem_subtype] at hy1 hy2
      have h' := @h ⟨y1.1, hy1⟩ ⟨y2.1, hy2⟩ (by
        simp only [c, dif_pos y1.2, dif_pos y2.2]
        exact heq)
      exact Subtype.ext (Subtype.mk.inj h')
    · intro h x1 x2 heq
      have h1 := hAU A hA x1.1 x1.2
      have h2 := hAU A hA x2.1 x2.2
      simp only [c, dif_pos h1, dif_pos h2] at heq
      have h' := h (by rw [Finset.mem_coe, Finset.mem_subtype]; exact x1.2)
        (by rw [Finset.mem_coe, Finset.mem_subtype]; exact x2.2) heq
      exact Subtype.ext (Subtype.mk.inj h')
  have hcount : ∀ A ∈ F, (Finset.univ.filter (fun κ => P κ A)).card * n ^ n =
      n.factorial * n ^ U.card := by
    intro A hA
    have hs : (A.subtype (· ∈ U)).card = n := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem (hAU A hA), hF A hA]
    have h0 := OMA.Erdos20H1.count_inj (A.subtype (· ∈ U)) n hs
    rw [Fintype.card_coe] at h0
    rw [Finset.filter_congr (fun κ _ => key A hA κ)]
    exact h0
  have hsum : ∑ κ : ↥U → Fin n, (F.filter (fun A => P κ A)).card * n ^ n =
      F.card * (n.factorial * n ^ U.card) := by
    rw [← Finset.sum_mul]
    have hc : ∑ κ : ↥U → Fin n, (F.filter (fun A => P κ A)).card =
        ∑ A ∈ F, (Finset.univ.filter (fun κ => P κ A)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hc, Finset.sum_mul, Finset.sum_congr rfl hcount, Finset.sum_const, smul_eq_mul]
  have hle : ∑ _κ : ↥U → Fin n, F.card * n.factorial ≤
      ∑ κ : ↥U → Fin n, (F.filter (fun A => P κ A)).card * n ^ n := by
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
      Fintype.card_fin, smul_eq_mul]
    exact le_of_eq (by ring)
  obtain ⟨κ, -, hκ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  refine ⟨c κ, F.filter (fun A => P κ A), Finset.filter_subset _ _, ?_, hκ⟩
  intro A hA
  rw [Finset.mem_filter] at hA
  exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hA.2, by simp [hF A hA.1]⟩
