import OMAReductions.R_Erdos427_erdos_427_variants_shiu_R1

-- Step Erdos427.erdos_427.variants.shiu.R1.H2: hypothesis H2 of reduction Erdos427.erdos_427.variants.shiu.R1
-- Credit: @ivillar
-- H2 := ∀ (good : ℕ → Bool) (l r k : ℕ), 1 ≤ k →     (k - 1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <         ((Finset.Ico l r).filter (fun i => good i = true)).card →     ∃ m : ℕ, l ≤ m ∧ m + k ≤ r ∧ ∀ i ∈ Finset.Ico m (m + k), good i = true

namespace OMA.E427ShiuH2

open Finset

lemma split_card (p : ℕ → Prop) [DecidablePred p] {l m r : ℕ} (h1 : l ≤ m) (h2 : m ≤ r) :
    ((Ico l r).filter p).card = ((Ico l m).filter p).card + ((Ico m r).filter p).card := by
  rw [← Finset.Ico_union_Ico_eq_Ico h1 h2, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive l m r)

lemma filter_card_le (p : ℕ → Prop) [DecidablePred p] (l r : ℕ) :
    ((Ico l r).filter p).card ≤ r - l := by
  calc ((Ico l r).filter p).card ≤ (Ico l r).card := card_filter_le _ _
    _ = r - l := Nat.card_Ico l r

/-- Without a run of `k` consecutive good indices in `[l, r)`, the good indices number at most
`(k - 1)` times one more than the bad ones: the bad indices cut `[l, r)` into at most
`bad + 1` blocks, each holding fewer than `k` good indices. -/
lemma key (good : ℕ → Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∀ n l r, r - l = n → l ≤ r →
    (∀ m, l ≤ m → m + k ≤ r → ∃ i ∈ Ico m (m + k), good i = false) →
    ((Ico l r).filter (fun i => good i = true)).card ≤
      (k - 1) * (((Ico l r).filter (fun i => good i = false)).card + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l r hn hlr hno
  by_cases hsmall : r < l + k
  · calc ((Ico l r).filter (fun i => good i = true)).card ≤ r - l := filter_card_le _ l r
      _ ≤ k - 1 := by omega
      _ ≤ (k - 1) * (((Ico l r).filter (fun i => good i = false)).card + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
  · push_neg at hsmall
    obtain ⟨i, hi, hbad⟩ := hno l le_rfl hsmall
    rw [mem_Ico] at hi
    have hir : i + 1 ≤ r := by omega
    have ih' := ih (r - (i + 1)) (by omega) (i + 1) r rfl hir
      (fun m hm hmr => hno m (by omega) hmr)
    have eT := split_card (fun j => good j = true) (show l ≤ i by omega) (show i ≤ r by omega)
    have eT2 := split_card (fun j => good j = true) (show i ≤ i + 1 by omega) hir
    have eF := split_card (fun j => good j = false) (show l ≤ i by omega) (show i ≤ r by omega)
    have eF2 := split_card (fun j => good j = false) (show i ≤ i + 1 by omega) hir
    have sT : ((Ico i (i + 1)).filter (fun j => good j = true)).card = 0 := by
      rw [Nat.Ico_succ_singleton, filter_singleton]; simp [hbad]
    have sF : ((Ico i (i + 1)).filter (fun j => good j = false)).card = 1 := by
      rw [Nat.Ico_succ_singleton, filter_singleton]; simp [hbad]
    have hLi : ((Ico l i).filter (fun j => good j = true)).card ≤ k - 1 :=
      (filter_card_le _ l i).trans (by omega)
    rw [eT, eT2, eF, eF2, sT, sF]
    generalize ((Ico l i).filter (fun j => good j = true)).card = a at *
    generalize ((Ico (i + 1) r).filter (fun j => good j = true)).card = g at *
    generalize ((Ico l i).filter (fun j => good j = false)).card = b at *
    generalize ((Ico (i + 1) r).filter (fun j => good j = false)).card = b' at *
    generalize k - 1 = K at *
    nlinarith

end OMA.E427ShiuH2

open OMA.E427ShiuH2 in
theorem OMA.solution : OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2 := by
  unfold OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2
  intro good l r k hk h
  by_contra hcon
  push_neg at hcon
  by_cases hlr : l ≤ r
  · have hno : ∀ m, l ≤ m → m + k ≤ r → ∃ i ∈ Finset.Ico m (m + k), good i = false := by
      intro m hm hmr
      obtain ⟨i, hi, hne⟩ := hcon m hm hmr
      exact ⟨i, hi, by simpa using hne⟩
    have := key good k hk (r - l) l r rfl hlr hno
    omega
  · have hE : Finset.Ico l r = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hE] at h
    simp at h
