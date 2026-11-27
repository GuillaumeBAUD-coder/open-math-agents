import OMAReductions.R_Erdos20_erdos_20_R1

-- Step Erdos20.erdos_20.R1.H1: hypothesis H1 of reduction Erdos20.erdos_20.R1
-- Credit: @marcusbuffett
-- H1 := ∀ (α : Type) (n : ℕ), 0 < n →     ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →       ∃ (c : α → Fin n) (G : Finset (Finset α)),         G ⊆ F ∧         (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧         F.card * n.factorial ≤ G.card * n ^ n

open Finset Function
open scoped Classical

private lemma count_bijections {V : Type} [Fintype V] (p : V → Prop) [DecidablePred p]
    {n : ℕ} (hn : Fintype.card {x // p x} = n) :
    (univ.filter fun c : V → Fin n => @Bijective {x // p x} (Fin n) (fun x => c x)).card =
      n.factorial * n ^ (Fintype.card V - n) := by
  classical
  let E := Equiv.piEquivPiSubtypeProd p (fun _ => Fin n)
  let e : {c : V → Fin n // Bijective (fun x : {x // p x} => c x)} ≃
      (({x // p x} ≃ Fin n) × ({x // ¬ p x} → Fin n)) := {
    toFun := fun c => (Equiv.ofBijective (E c.1).1 c.2, (E c.1).2)
    invFun := fun ⟨b,d⟩ => ⟨E.symm (b,d), by
      change Bijective (E (E.symm (⇑b,d))).1
      rw [Equiv.apply_symm_apply]
      exact b.bijective⟩
    left_inv := fun c => Subtype.ext (E.symm_apply_apply c.1)
    right_inv := by
      rintro ⟨b,d⟩
      apply Prod.ext
      · apply Equiv.ext
        intro x
        change (E (E.symm (⇑b,d))).1 x = b x
        rw [Equiv.apply_symm_apply]
      · change (E (E.symm (⇑b,d))).2 = d
        rw [Equiv.apply_symm_apply] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_prod,
    Fintype.card_equiv (Fintype.equivFinOfCardEq hn), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_fin, hn]

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  intro α n hn F hF
  classical
  let U := F.biUnion id
  let extend (c : U → Fin n) (x : α) := if h : x ∈ U then c ⟨x,h⟩ else ⟨0,hn⟩
  let good (A : Finset α) (c : U → Fin n) := Bijective (fun x : A => extend c x)
  by_cases hf : F.Nonempty
  swap
  · exact ⟨fun _ => ⟨0,hn⟩, ∅, empty_subset _, by simp, by simp [not_nonempty_iff_eq_empty.mp hf]⟩
  have sub (A : Finset α) (ha : A ∈ F) : A ⊆ U := fun _ hx => mem_biUnion.mpr ⟨A,ha,hx⟩
  have hnU : n ≤ U.card := by
    obtain ⟨A,ha⟩ := hf
    simpa [hF A ha] using card_le_card (sub A ha)
  have countGood (A : Finset α) (ha : A ∈ F) :
      (univ.filter (good A)).card = n.factorial * n ^ (U.card - n) := by
    let p (x : U) := x.1 ∈ A
    let e : A ≃ {x // p x} := {
      toFun := fun a => ⟨⟨a,sub A ha a.2⟩,a.2⟩
      invFun := fun a => ⟨a.1.1,a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hcard : Fintype.card {x // p x} = n := by
      rw [← Fintype.card_congr e, Fintype.card_coe, hF A ha]
    have H := count_bijections p hcard
    rw [Fintype.card_coe] at H
    rw [← H]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← e.bijective_comp]
    change Bijective (fun x : A => extend c x) ↔ Bijective (fun x : A => c ⟨x,sub A ha x.2⟩)
    have he (x : A) : extend c x = c ⟨x,sub A ha x.2⟩ := dif_pos (sub A ha x.2)
    simp_rw [he]
  let score (c : U → Fin n) := (F.filter (fun A => good A c)).card
  have htotal : ∑ c : U → Fin n, score c = F.card * (n.factorial * n ^ (U.card - n)) := by
    simp only [score, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _A ∈ F, n.factorial * n ^ (U.card - n) := by
        apply Finset.sum_congr rfl
        intro A ha
        rw [← countGood A ha, Finset.card_filter]
      _ = _ := by simp
  letI : Nonempty (U → Fin n) := ⟨fun _ => ⟨0,hn⟩⟩
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image (univ : Finset (U → Fin n)) score univ_nonempty
  refine ⟨extend c, F.filter (fun A => good A c), filter_subset _ _, fun _ ha => (mem_filter.mp ha).2, ?_⟩
  have hbound := Finset.sum_le_sum hc
  change _ ≤ score c * n ^ n
  have hsum : ∑ _d : U → Fin n, score c = n ^ U.card * score c := by simp
  rw [htotal,hsum] at hbound
  have he : n ^ U.card = n ^ n * n ^ (U.card - n) := by
    rw [← pow_add, Nat.add_sub_of_le hnU]
  rw [he] at hbound
  exact Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound)
    (pow_pos hn (U.card - n))
