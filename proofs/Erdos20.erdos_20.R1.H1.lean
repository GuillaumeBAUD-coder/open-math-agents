import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib.Data.Fintype.CardEmbedding

-- Step Erdos20.erdos_20.R1.H1: hypothesis H1 of reduction Erdos20.erdos_20.R1
-- Credit: @JamesSlash
-- H1 := ∀ (α : Type) (n : ℕ), 0 < n →     ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →       ∃ (c : α → Fin n) (G : Finset (Finset α)),         G ⊆ F ∧         (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧         F.card * n.factorial ≤ G.card * n ^ n
--
-- Proof (colour coding by averaging): let U be the union of the family. Each n-set A in F is
-- rainbow (injectively coloured) under exactly n! * n^(|U| - n) of the n^|U| colourings U -> Fin n
-- (split a colouring into its restriction to A, which must be a bijection, and its values off A).
-- Summing over A, the colourings make F.card * n! * n^(|U| - n) rainbow incidences in total, so
-- some colouring c has at least F.card * n! / n^n rainbow members. Take G to be those members.

namespace OMA.Erdos20H1Claude


open Finset

/-- Number of colourings `β → Fin n` that are injective on a fixed `n`-set `s`. -/
theorem card_injOn {β : Type} [Fintype β] [DecidableEq β] (n : ℕ) (s : Finset β)
    (hs : s.card = n) :
    (univ.filter (fun f : β → Fin n => Set.InjOn f (s : Set β))).card
      = n.factorial * n ^ (Fintype.card β - n) := by
  classical
  have h1 : (univ.filter (fun f : β → Fin n => Set.InjOn f (s : Set β))).card
      = Fintype.card {f : β → Fin n // Set.InjOn f (s : Set β)} := by
    rw [Fintype.card_subtype]
  rw [h1]
  let e2 : {f : β → Fin n // Set.InjOn f (s : Set β)} ≃
      {g : {x // x ∈ s} → Fin n // Function.Injective g} × ({x // x ∉ s} → Fin n) :=
    { toFun := fun f => (⟨fun x => f.1 x, fun a b h => Subtype.ext (f.2 a.2 b.2 h)⟩,
        fun x => f.1 x)
      invFun := fun p => ⟨fun x => if h : x ∈ s then p.1.1 ⟨x, h⟩ else p.2 ⟨x, h⟩, by
        intro a ha b hb hab
        simp only [Finset.mem_coe] at ha hb
        simp only [ha, hb, dif_pos] at hab
        exact congrArg Subtype.val (p.1.2 hab)⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext x
        by_cases h : x ∈ s <;> simp [h]
      right_inv := by
        intro p
        rcases p with ⟨⟨g, hg⟩, k⟩
        simp only [Prod.mk.injEq]
        constructor
        · apply Subtype.ext
          funext x
          simp [x.2]
        · funext x
          simp [x.2] }
  rw [Fintype.card_congr e2, Fintype.card_prod,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fun]
  simp [Fintype.card_subtype_compl, hs, Nat.descFactorial_self]

theorem main : ∀ (α : Type) (n : ℕ), 0 < n →
    ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →
      ∃ (c : α → Fin n) (G : Finset (Finset α)),
        G ⊆ F ∧
        (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
        F.card * n.factorial ≤ G.card * n ^ n := by
  intro α n hn F hF
  classical
  rcases F.eq_empty_or_nonempty with hFe | ⟨A0, hA0⟩
  · exact ⟨fun _ => ⟨0, hn⟩, ∅, by simp, by simp, by simp [hFe]⟩
  set U : Finset α := F.biUnion id with hU
  have hsub : ∀ A ∈ F, A ⊆ U := fun A hA x hx => by
    rw [hU, Finset.mem_biUnion]; exact ⟨A, hA, hx⟩
  let ext : ({x // x ∈ U} → Fin n) → α → Fin n :=
    fun f x => if h : x ∈ U then f ⟨x, h⟩ else ⟨0, hn⟩
  let good : ({x // x ∈ U} → Fin n) → Finset (Finset α) :=
    fun f => F.filter (fun A => Set.InjOn (ext f) (A : Set α))
  -- pull an `n`-set back to `U`
  let pb : Finset α → Finset {x // x ∈ U} := fun A => A.subtype (· ∈ U)
  have hpb_card : ∀ A ∈ F, (pb A).card = n := by
    intro A hA
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hsub A hA hx), hF A hA]
  have hinj_iff : ∀ A ∈ F, ∀ f : {x // x ∈ U} → Fin n,
      Set.InjOn (ext f) (A : Set α) ↔ Set.InjOn f (pb A : Set {x // x ∈ U}) := by
    intro A hA f
    constructor
    · intro h a ha b hb hab
      simp only [pb, Finset.mem_coe, Finset.mem_subtype] at ha hb
      apply Subtype.ext
      apply h ha hb
      simp only [ext, a.2, b.2, dif_pos]
      simpa using hab
    · intro h a ha b hb hab
      have ha' : a ∈ U := hsub A hA ha
      have hb' : b ∈ U := hsub A hA hb
      simp only [ext, ha', hb', dif_pos] at hab
      have := h (x₁ := ⟨a, ha'⟩) (x₂ := ⟨b, hb'⟩)
        (by simpa [pb] using ha) (by simpa [pb] using hb) hab
      exact congrArg Subtype.val this
  have hcount : ∀ A ∈ F,
      (univ.filter (fun f : {x // x ∈ U} → Fin n => Set.InjOn (ext f) (A : Set α))).card
        = n.factorial * n ^ (U.card - n) := by
    intro A hA
    have := card_injOn n (pb A) (hpb_card A hA)
    rw [Fintype.card_coe] at this
    rw [← this]
    congr 1
    ext f
    simp [hinj_iff A hA f]
  -- total count
  have htotal : ∑ f : {x // x ∈ U} → Fin n, (good f).card
      = F.card * (n.factorial * n ^ (U.card - n)) := by
    simp only [good, Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (g := fun _ => n.factorial * n ^ (U.card - n)) (fun A hA => by
      rw [← Finset.card_filter]; exact hcount A hA)]
    simp
  have hnU : n ≤ U.card := by
    rw [← hF A0 hA0]; exact Finset.card_le_card (hsub A0 hA0)
  -- averaging
  have hne : (univ : Finset ({x // x ∈ U} → Fin n)).Nonempty := by
    exact ⟨fun _ => ⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨f, -, hf⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => F.card * (n.factorial * n ^ (U.card - n)))
    (g := fun f => (good f).card * n ^ U.card) (by
      rw [Finset.sum_const, ← Finset.sum_mul, htotal, Finset.card_univ, Fintype.card_fun,
        Fintype.card_coe, Fintype.card_fin, smul_eq_mul]
      exact le_of_eq (by ring))
  refine ⟨ext f, good f, Finset.filter_subset _ _, ?_, ?_⟩
  · intro A hA
    simp only [good, Finset.mem_filter] at hA
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [hF A hA.1]⟩
    intro a b hab
    exact Subtype.ext (hA.2 a.2 b.2 hab)
  · have hpow : n ^ U.card = n ^ n * n ^ (U.card - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hnU]
    have hpos : 0 < n ^ (U.card - n) := pow_pos hn _
    rw [hpow] at hf
    have : F.card * n.factorial * n ^ (U.card - n)
        ≤ (good f).card * n ^ n * n ^ (U.card - n) := by
      simpa [mul_assoc] using hf
    exact Nat.le_of_mul_le_mul_right this hpos

end OMA.Erdos20H1Claude

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 :=
  OMA.Erdos20H1Claude.main
