import OMAReductions.R_Erdos19_erdos_19_R1_H1_R1_H2_R1
import Mathlib

-- Step Erdos19.erdos_19.R1.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos19.erdos_19.R1.H1.R1.H2.R1
-- Credit: @ivillar. Each new line is a pair {p, q} with p in P and q outside b; it gets the fresh
-- color n - t + (index p + index q) mod t, a Latin square on P x (univ minus b).

/-! Latin-square extension of a coloring to a batch of ordinary points. -/

open Finset
open scoped Classical

namespace P7E19H2

/-- A line outside `K` is a pair `{p, q}` with `p ∈ P` and `q ∉ b`. -/
lemma new_line {n : ℕ} {L : Finset (Finset (Fin n))} {b P a : Finset (Fin n)}
    (hb : b ∈ L) (hPb : P ⊆ b)
    (hlin : ∀ a ∈ L, ∀ d ∈ L, a ≠ d → (a ∩ d).card ≤ 1)
    (hP : ∀ p ∈ P, ∀ a ∈ L, a ≠ b → p ∈ a → a.card = 2)
    (ha : a ∈ L) (hab : a ≠ b) (hdis : ¬ Disjoint a P) :
    ∃ p q, p ∈ P ∧ q ∉ b ∧ p ≠ q ∧ a = {p, q} := by
  obtain ⟨p, hpa, hpP⟩ := Finset.not_disjoint_iff.mp hdis
  have h2 := hP p hpP a ha hab hpa
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
  have hpb := hPb hpP
  have hl := hlin _ ha b hb hab
  rcases Finset.mem_insert.mp hpa with rfl | hp
  · refine ⟨p, y, hpP, ?_, hxy, rfl⟩
    intro hyb
    have : ({p, y} : Finset (Fin n)) ⊆ {p, y} ∩ b := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_inter.mpr ⟨hz, hpb⟩
      · rw [Finset.mem_singleton.mp hz]
        exact Finset.mem_inter.mpr ⟨by simp, hyb⟩
    have := Finset.card_le_card this
    rw [Finset.card_pair hxy] at this
    omega
  · rw [Finset.mem_singleton.mp hp] at hpP hpb
    refine ⟨y, x, hpP, ?_, hxy.symm, Finset.pair_comm x y⟩
    intro hxb
    have : ({x, y} : Finset (Fin n)) ⊆ {x, y} ∩ b := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_inter.mpr ⟨by simp, hxb⟩
      · rw [Finset.mem_singleton.mp hz]
        exact Finset.mem_inter.mpr ⟨by simp, hpb⟩
    have := Finset.card_le_card this
    rw [Finset.card_pair hxy] at this
    omega

lemma mod_ne {t i j j' : ℕ} (hj : j < t) (hj' : j' < t) (hne : j ≠ j') :
    (i + j) % t ≠ (i + j') % t := by
  intro h
  have := Nat.ModEq.add_left_cancel' i h
  rw [Nat.ModEq, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at this
  exact hne this

end P7E19H2

open P7E19H2

theorem OMA.solution : OMA.R_Erdos19_erdos_19_R1_H1_R1_H2_R1.H2 := by
  unfold OMA.R_Erdos19_erdos_19_R1_H1_R1_H2_R1.H2
  intro n t L b P ht hb hPb hPc hQc hlin hP K hK
  obtain ⟨c, hc⟩ := hK
  let eP := P.equivFinOfCardEq hPc
  let eQ := (univ \ b).equivFinOfCardEq hQc
  let iP : Fin n → ℕ := fun x => if h : x ∈ P then (eP ⟨x, h⟩).val else 0
  let iQ : Fin n → ℕ := fun x => if h : x ∈ univ \ b then (eQ ⟨x, h⟩).val else 0
  have htn : t ≤ n := by
    have := Finset.card_le_univ (univ \ b)
    simp only [Fintype.card_fin] at this
    omega
  have hiP : ∀ x ∈ P, ∀ y ∈ P, iP x = iP y → x = y := by
    intro x hx y hy h
    simp only [iP, dif_pos hx, dif_pos hy] at h
    have := eP.injective (Fin.ext h)
    exact congrArg Subtype.val this
  have hiQ : ∀ x, x ∉ b → ∀ y, y ∉ b → iQ x = iQ y → x = y := by
    intro x hx y hy h
    have hx' : x ∈ univ \ b := by simp [hx]
    have hy' : y ∈ univ \ b := by simp [hy]
    simp only [iQ, dif_pos hx', dif_pos hy'] at h
    have := eQ.injective (Fin.ext h)
    exact congrArg Subtype.val this
  have hiPlt : ∀ x, iP x < t := by
    intro x
    simp only [iP]
    split_ifs
    · exact (eP _).isLt
    · exact ht
  have hiQlt : ∀ x, iQ x < t := by
    intro x
    simp only [iQ]
    split_ifs
    · exact (eQ _).isLt
    · exact ht
  have hsum : ∀ p q, p ∈ P → q ∉ b → p ≠ q →
      ∑ x ∈ ({p, q} : Finset (Fin n)), (iP x + iQ x) = iP p + iQ q := by
    intro p q hp hq hpq
    rw [Finset.sum_pair hpq]
    have h1 : iQ p = 0 := by
      simp only [iQ]
      rw [dif_neg]
      simp [hPb hp]
    have h2 : iP q = 0 := by
      simp only [iP]
      rw [dif_neg]
      exact fun h => hq (hPb h)
    omega
  let col : L → Fin n := fun a =>
    if h : a.val ∈ K then Fin.castLE (Nat.sub_le n t) (c ⟨a.val, h⟩)
    else ⟨n - t + (∑ x ∈ a.val, (iP x + iQ x)) % t, by
      have := Nat.mod_lt (∑ x ∈ a.val, (iP x + iQ x)) ht
      omega⟩
  refine ⟨col, ?_⟩
  intro a d had hint
  have hnotK : ∀ e : L, e.val ∉ K → e.val ≠ b ∧ ¬ Disjoint e.val P := by
    intro e he
    simp only [K, Finset.mem_filter, not_and, not_or] at he
    exact he e.prop
  by_cases ha : a.val ∈ K <;> by_cases hd : d.val ∈ K
  · simp only [col, dif_pos ha, dif_pos hd]
    intro h
    apply hc ⟨a.val, ha⟩ ⟨d.val, hd⟩ _ hint (Fin.castLE_injective _ h)
    intro h'
    have h'' := congrArg (fun x : K => (x : Finset (Fin n))) h'
    exact had (Subtype.ext h'')
  · simp only [col, dif_pos ha, dif_neg hd]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    have := (c ⟨a.val, ha⟩).isLt
    omega
  · simp only [col, dif_neg ha, dif_pos hd]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    have := (c ⟨d.val, hd⟩).isLt
    omega
  · obtain ⟨hab, hadis⟩ := hnotK a ha
    obtain ⟨hdb, hddis⟩ := hnotK d hd
    obtain ⟨p, q, hp, hq, hpq, hae⟩ := new_line hb hPb hlin hP a.prop hab hadis
    obtain ⟨p', q', hp', hq', hpq', hde⟩ := new_line hb hPb hlin hP d.prop hdb hddis
    simp only [col, dif_neg ha, dif_neg hd]
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    rw [hae, hde, hsum p q hp hq hpq, hsum p' q' hp' hq' hpq'] at hv
    have hmod : (iP p + iQ q) % t = (iP p' + iQ q') % t := by omega
    obtain ⟨x, hx⟩ := hint
    rw [hae, hde, Finset.mem_inter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    have hne : ({p, q} : Finset (Fin n)) ≠ {p', q'} := by
      intro h'
      apply had
      apply Subtype.ext
      rw [hae, hde, h']
    rcases hx1 with rfl | rfl <;> rcases hx2 with h2 | h2
    · -- x = p = p'
      subst h2
      have hqq : q ≠ q' := fun h' => hne (by rw [h'])
      exact mod_ne (hiQlt q) (hiQlt q') (fun h' => hqq (hiQ q hq q' hq' h')) hmod
    · subst h2
      exact hq' (hPb hp)
    · subst h2
      exact hq (hPb hp')
    · subst h2
      have hpp : p ≠ p' := fun h' => hne (by rw [h'])
      rw [add_comm (iP p), add_comm (iP p')] at hmod
      exact mod_ne (hiPlt p) (hiPlt p') (fun h' => hpp (hiP p hp p' hp' h')) hmod

