/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import OMAReductions.R_Erdos19_erdos_19_R1_H1_R1

/-!
Credit: Hanan Beer (@hananzlt).
Parent completed-space reduction: Elia Yousf (@eliayousf), PR2910.
Ancestor linear-family reduction: @zarnab222-dev, PR1479.

A line missing at most six points has at most fifteen exceptional points.
Removing one batch of ordinary points gives a smaller completed space.
The finite base of at most 26 points remains a hypothesis. The Latin-square
extension is a separate, independently provable input. No finite computations
or unverified coloring certificates are used in the reduction proof.
-/
open Finset
open scoped Classical

namespace OMA.R_Erdos19_erdos_19_R1_H1_R1_H2_R1

/-- The finite base: completed linear spaces on at most 26 points with at most
six points outside some line. This hypothesis still requires finite certificates. -/
def H1 : Prop := ∀ (n : ℕ), n ≤ 26 → ∀ L : Finset (Finset (Fin n)),
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ d ∈ L, a ≠ d → (a ∩ d).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ a ∈ L, i ∈ a ∧ j ∈ a) →
    (∃ b ∈ L, n ≤ b.card + 6) →
    ∃ c : L → Fin n, ∀ a d : L,
      a ≠ d → (a.val ∩ d.val).Nonempty → c a ≠ c d

/-- Restore a batch of ordinary points on a distinguished line. The batch and
the outside set have the same size; a Latin square supplies fresh colors. -/
def H2 : Prop := ∀ (n t : ℕ) (L : Finset (Finset (Fin n))) (b P : Finset (Fin n)),
    0 < t → b ∈ L → P ⊆ b → P.card = t → (univ \ b).card = t →
    (∀ a ∈ L, ∀ d ∈ L, a ≠ d → (a ∩ d).card ≤ 1) →
    (∀ p ∈ P, ∀ a ∈ L, a ≠ b → p ∈ a → a.card = 2) →
    let K := L.filter fun a => a = b ∨ Disjoint a P
    (∃ c : K → Fin (n-t), ∀ a d : K,
      a ≠ d → (a.val ∩ d.val).Nonempty → c a ≠ c d) →
    ∃ c : L → Fin n, ∀ a d : L,
      a ≠ d → (a.val ∩ d.val).Nonempty → c a ≠ c d


theorem exceptional_points_bound {n : ℕ} (L : Finset (Finset (Fin n)))
    (b : Finset (Fin n)) (hb : b ∈ L)
    (linear : ∀ a ∈ L, ∀ c ∈ L, a ≠ c → (a ∩ c).card ≤ 1) :
    (b.filter fun p => ∃ e ∈ L, e ≠ b ∧ 3 ≤ e.card ∧ p ∈ e).card ≤
      (n - b.card).choose 2 := by
  classical
  let E := b.filter fun p => ∃ e ∈ L, e ≠ b ∧ 3 ≤ e.card ∧ p ∈ e
  have witness (p : E) : ∃ e ∈ L, e ≠ b ∧ 3 ≤ e.card ∧ p.val ∈ e :=
    (mem_filter.mp p.property).2
  choose e heL heb hes hep using witness
  have pairs (p : E) : ∃ Q : Finset (Fin n), Q ⊆ e p \ b ∧ Q.card = 2 := by
    have hi := linear (e p) (heL p) b hb (heb p)
    have hc := card_sdiff_add_card_inter (e p) b
    have hs := hes p
    apply exists_subset_card_eq
    omega
  choose Q hQsub hQcard using pairs
  let f : E → ((univ \ b).powersetCard 2 : Finset (Finset (Fin n))) :=
    fun p => ⟨Q p, mem_powersetCard.mpr ⟨by
      intro x hx
      exact mem_sdiff.mpr ⟨mem_univ x, (mem_sdiff.mp (hQsub p hx)).2⟩, hQcard p⟩⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hQ : Q p = Q q := congrArg Subtype.val hpq
    have he : e p = e q := by
      by_contra hne
      have hlin := linear (e p) (heL p) (e q) (heL q) hne
      have hsub : Q p ⊆ e p ∩ e q := by
        intro x hx
        exact mem_inter.mpr ⟨(mem_sdiff.mp (hQsub p hx)).1,
          (mem_sdiff.mp (hQsub q (hQ ▸ hx))).1⟩
      have hcard := card_le_card hsub
      rw [hQcard] at hcard
      omega
    apply Subtype.ext
    apply card_le_one.mp (linear (e p) (heL p) b hb (heb p))
    · exact mem_inter.mpr ⟨hep p, (mem_filter.mp p.property).1⟩
    · exact mem_inter.mpr ⟨he ▸ hep q, (mem_filter.mp q.property).1⟩
  have bound := card_le_card_of_injective hf
  change E.card ≤ (n - b.card).choose 2
  simpa only [card_powersetCard, card_sdiff_of_subset (subset_univ b), card_univ,
    Fintype.card_fin] using bound


theorem exists_ordinary_batch {n : ℕ} (L : Finset (Finset (Fin n)))
    (b : Finset (Fin n)) (hb : b ∈ L)
    (size : ∀ a ∈ L, 2 ≤ a.card)
    (linear : ∀ a ∈ L, ∀ c ∈ L, a ≠ c → (a ∩ c).card ≤ 1)
    (hn : 26 < n) (hlarge : n ≤ b.card + 6) :
    ∃ P ⊆ b, P.card = n - b.card ∧ 2 ≤ (b \ P).card ∧
      ∀ p ∈ P, ∀ a ∈ L, a ≠ b → p ∈ a → a.card = 2 := by
  classical
  let E := b.filter fun p => ∃ e ∈ L, e ≠ b ∧ 3 ≤ e.card ∧ p ∈ e
  have hE : E.card ≤ 15 := by
    have h := exceptional_points_bound L b hb linear
    have ht : n - b.card ≤ 6 := by omega
    have hc := Nat.choose_le_choose 2 ht
    exact h.trans hc
  have hbn : b.card ≤ n := by simpa using card_le_card (subset_univ b)
  have ht : n - b.card ≤ 6 := by omega
  have hc : n - b.card ≤ (b \ E).card := by
    have h := card_sdiff_add_card_eq_card (filter_subset (fun p =>
      ∃ e ∈ L, e ≠ b ∧ 3 ≤ e.card ∧ p ∈ e) b)
    change (b \ E).card + E.card = b.card at h
    omega
  obtain ⟨P,hPsub,hPcard⟩ := exists_subset_card_eq hc
  have hPb : P ⊆ b := hPsub.trans sdiff_subset
  refine ⟨P,hPb,hPcard,?_,?_⟩
  · rw [card_sdiff_of_subset hPb, hPcard]
    omega
  · intro p hp a ha hne hpa
    have hpE := (mem_sdiff.mp (hPsub hp)).2
    have hs := size a ha
    have hnlarge : ¬ 3 ≤ a.card := by
      intro h
      exact hpE (mem_filter.mpr ⟨hPb hp,a,ha,hne,h,hpa⟩)
    omega

theorem exists_reduced_family {n t : ℕ}
    (L : Finset (Finset (Fin n))) (b P : Finset (Fin n))
    (hb : b ∈ L) (hPb : P ⊆ b) (hP : P.card = t) (hbp : 2 ≤ (b \ P).card)
    (hlarge : n ≤ b.card + 6)
    (size : ∀ a ∈ L, 2 ≤ a.card)
    (linear : ∀ a ∈ L, ∀ d ∈ L, a ≠ d → (a ∩ d).card ≤ 1)
    (covers : ∀ i j : Fin n, i ≠ j → ∃ a ∈ L, i ∈ a ∧ j ∈ a)
    (ordinary : ∀ p ∈ P, ∀ a ∈ L, a ≠ b → p ∈ a → a.card = 2) :
    let K := L.filter fun a => a = b ∨ Disjoint a P
    ∃ J : Finset (Finset (Fin (n - t))),
      (∀ a ∈ J, 2 ≤ a.card) ∧
      (∀ a ∈ J, ∀ d ∈ J, a ≠ d → (a ∩ d).card ≤ 1) ∧
      (∀ i j : Fin (n-t), i ≠ j → ∃ a ∈ J, i ∈ a ∧ j ∈ a) ∧
      (∃ a ∈ J, n-t ≤ a.card + 6) ∧
      ((∃ c : J → Fin (n-t), ∀ a d : J,
          a ≠ d → (a.val ∩ d.val).Nonempty → c a ≠ c d) →
        ∃ c : K → Fin (n-t), ∀ a d : K,
          a ≠ d → (a.val ∩ d.val).Nonempty → c a ≠ c d) := by
  classical
  let K := L.filter fun a => a = b ∨ Disjoint a P
  let A : Finset (Fin n) := univ \ P
  have hAc : A.card = n-t := by
    simp only [A, card_sdiff_of_subset (subset_univ P), card_univ, Fintype.card_fin, hP]
  let ep : A ≃ Fin (n-t) := Finset.equivFinOfCardEq hAc
  let e : Fin (n-t) ↪ Fin n := ep.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have eavoid (i : Fin (n-t)) : e i ∉ P :=
    (mem_sdiff.mp (ep.symm i).property).2
  have erange (x : Fin n) : (∃ i, e i = x) ↔ x ∉ P := by
    constructor
    · rintro ⟨i,rfl⟩
      exact eavoid i
    · intro hx
      refine ⟨ep ⟨x,mem_sdiff.mpr ⟨mem_univ _,hx⟩⟩,?_⟩
      simp [e]
  let f (a : Finset (Fin n)) := a.preimage e e.injective.injOn
  have fmem {a : Finset (Fin n)} {i : Fin (n-t)} : i ∈ f a ↔ e i ∈ a :=
    mem_preimage
  have fcard (a : Finset (Fin n)) : (f a).card = (a \ P).card := by
    rw [Finset.card_preimage]
    congr 1
    ext x
    simp only [mem_filter, Set.mem_range, erange, mem_sdiff]
  have Ksub : K ⊆ L := filter_subset _ _
  have bk : b ∈ K := mem_filter.mpr ⟨hb,Or.inl rfl⟩
  have fsize (a : Finset (Fin n)) (ha : a ∈ K) : 2 ≤ (f a).card := by
    rw [fcard]
    rcases (mem_filter.mp ha).2 with rfl | hd
    · exact hbp
    · rw [sdiff_eq_left.mpr hd]
      exact size a (Ksub ha)
  have flinear {a d : Finset (Fin n)} (ha : a ∈ K) (hd : d ∈ K) (had : a ≠ d) :
      (f a ∩ f d).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    apply e.injective
    exact card_le_one.mp (linear a (Ksub ha) d (Ksub hd) had)
      _ (mem_inter.mpr ⟨fmem.mp (mem_inter.mp hi).1, fmem.mp (mem_inter.mp hi).2⟩)
      _ (mem_inter.mpr ⟨fmem.mp (mem_inter.mp hj).1, fmem.mp (mem_inter.mp hj).2⟩)
  have finj : Set.InjOn f K := by
    intro a ha d hd h
    by_contra hne
    have hl := flinear ha hd hne
    rw [h, inter_self] at hl
    have hs := fsize d hd
    omega
  let J := K.image f
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨d,hd,rfl⟩ := mem_image.mp ha
    exact fsize d hd
  · intro a ha d hd had
    obtain ⟨aa,haa,rfl⟩ := mem_image.mp ha
    obtain ⟨dd,hdd,rfl⟩ := mem_image.mp hd
    exact flinear haa hdd (fun heq => had (congrArg f heq))
  · intro i j hij
    obtain ⟨a,ha,hi,hj⟩ := covers (e i) (e j) (fun h => hij (e.injective h))
    have hak : a ∈ K := by
      refine mem_filter.mpr ⟨ha, ?_⟩
      by_cases hab : a = b
      · exact Or.inl hab
      · right
        apply disjoint_left.mpr
        intro p hp hpP
        have hs := ordinary p hpP a ha hab hp
        have hpairs : {e i,e j} ⊆ a := insert_subset_iff.mpr ⟨hi,singleton_subset_iff.mpr hj⟩
        have heq : {e i,e j} = a := eq_of_subset_of_card_le hpairs (by
          rw [hs,card_pair (fun h => hij (e.injective h))])
        rw [← heq] at hp
        simp only [mem_insert,mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact eavoid i hpP
        · exact eavoid j hpP
    exact ⟨f a,mem_image_of_mem f hak,fmem.mpr hi,fmem.mpr hj⟩
  · refine ⟨f b,mem_image_of_mem f bk,?_⟩
    rw [fcard,card_sdiff_of_subset hPb,hP]
    omega
  · rintro ⟨c,hc⟩
    let lift : K → J := fun a => ⟨f a.val,mem_image_of_mem f a.property⟩
    refine ⟨fun a => c (lift a),?_⟩
    intro a d had hmeet
    apply hc (lift a) (lift d)
    · intro h
      exact had (Subtype.ext (finj a.property d.property (congrArg Subtype.val h)))
    · obtain ⟨x,hx⟩ := hmeet
      obtain ⟨hxa,hxd⟩ := mem_inter.mp hx
      have hxP : x ∉ P := by
        rcases (mem_filter.mp a.property).2 with hab | haP
        · rcases (mem_filter.mp d.property).2 with hdb | hdP
          · exact (had (Subtype.ext (hab.trans hdb.symm))).elim
          · exact fun hp => disjoint_left.mp hdP hxd hp
        · exact fun hp => disjoint_left.mp haP hxa hp
      obtain ⟨i,hi⟩ := (erange x).mpr hxP
      exact ⟨i,mem_inter.mpr ⟨fmem.mpr (hi ▸ hxa),fmem.mpr (hi ▸ hxd)⟩⟩

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_R1_H1_R1.H2 := by
  intro base extend
  have general : ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
      (∀ a ∈ L, 2 ≤ a.card) →
      (∀ a ∈ L, ∀ d ∈ L, a ≠ d → (a ∩ d).card ≤ 1) →
      (∀ i j : Fin n, i ≠ j → ∃ a ∈ L, i ∈ a ∧ j ∈ a) →
      (∃ b ∈ L, n ≤ b.card + 6) →
      ∃ c : L → Fin n, ∀ a d : L,
        a ≠ d → (a.val ∩ d.val).Nonempty → c a ≠ c d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L size linear covers giant
      by_cases hn : n ≤ 26
      · exact base n hn L size linear covers giant
      obtain ⟨b,hb,hlarge⟩ := giant
      have hbn : b.card ≤ n := by simpa using card_le_card (subset_univ b)
      by_cases hfull : b.card = n
      · have hbU : b = univ := eq_of_subset_of_card_le (subset_univ b) (by simp [hfull])
        have all_eq (a : Finset (Fin n)) (ha : a ∈ L) : a = b := by
          by_contra hab
          have hl := linear a ha b hb hab
          rw [hbU,inter_univ] at hl
          have hs := size a ha
          omega
        refine ⟨fun _ => ⟨0,by omega⟩,?_⟩
        intro a d had _
        exact (had (Subtype.ext ((all_eq a.val a.property).trans (all_eq d.val d.property).symm))).elim
      have ht : 0 < n - b.card := by omega
      obtain ⟨P,hPb,hP,hbp,hordinary⟩ := exists_ordinary_batch L b hb size linear (by omega) hlarge
      have hT : (univ \ b).card = n - b.card := by
        simp only [card_sdiff_of_subset (subset_univ b),card_univ,Fintype.card_fin]
      obtain ⟨J,hsize,hlinear,hcovers,hgiant,hlift⟩ :=
        exists_reduced_family L b P hb hPb hP hbp hlarge size linear covers hordinary
      have hsmaller : n - (n - b.card) < n := by omega
      have hcolor := ih (n - (n - b.card)) hsmaller J hsize hlinear hcovers hgiant
      exact extend n (n - b.card) L b P ht hb hPb hP hT linear hordinary (hlift hcolor)
  intro n L size linear covers _core giant
  exact general n L size linear covers giant

end OMA.R_Erdos19_erdos_19_R1_H1_R1_H2_R1
