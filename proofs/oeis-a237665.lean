import OMAStatements.S_oeis_a237665

/-!
The argument formalizes the bijection underlying Shane Chern, On a conjecture of
George Beck II, The Mathematics Student 88 (2019), Theorem 3.2.
https://cpb-us-e1.wpmucdn.com/sites.psu.edu/dist/9/62616/files/2018/07/On-a-conjecture-of-George-Beck-II-2dpatgk.pdf
-/

namespace BeckPartition
open Finset

-- Column heights in the Ferrers diagram.
private def height (p : Multiset ℕ) (j : ℕ) : ℕ := p.countP (j ≤ ·)

private theorem height_mono (p : Multiset ℕ) {i j : ℕ} (h : i ≤ j) :
    height p j ≤ height p i := by
  simp only [height, Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun _ hb => h.trans hb)

private theorem height_step (p : Multiset ℕ) (i : ℕ) :
    height p i = p.count i + height p (i+1) := by
  induction p using Multiset.induction_on with
  | empty => simp [height]
  | cons a p ih =>
    simp only [height, Multiset.countP_cons, Multiset.count_cons] at ih ⊢
    by_cases h : a = i
    · subst a
      simp at *
      omega
    · by_cases h' : i < a
      · have hne : i ≠ a := Ne.symm h
        simp only [Nat.le_of_lt h', Nat.succ_le_of_lt h', if_true, hne, if_false] 
        omega
      · have hi : ¬ i ≤ a := by omega
        have hs : ¬ i+1 ≤ a := by omega
        have hne : i ≠ a := Ne.symm h
        simp only [hi, hs, hne, if_false]
        omega

private theorem height_pos_of_mem {p : Multiset ℕ} {i j : ℕ} (h : j ∈ p) (hij : i ≤ j) :
    0 < height p i := Multiset.countP_pos.mpr ⟨j,h,hij⟩

private def conjugateParts (p : Multiset ℕ) (n : ℕ) : Multiset ℕ :=
  ((Icc 1 n).val.map (height p)).filter (· ≠ 0)

private theorem height_conjugateParts (p : Multiset ℕ) (n : ℕ) {j : ℕ} (hj : 0 < j) :
    height (conjugateParts p n) j = ((Icc 1 n).filter fun i => j ≤ height p i).card := by
  simp only [height, conjugateParts, Multiset.countP_filter,
    Multiset.countP_map, card]
  congr 1
  apply Multiset.filter_congr
  intro x hx
  exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩

private theorem sum_height (p : Multiset ℕ) (n : ℕ) (hp : ∀ i ∈ p, i ≤ n) :
    ∑ j ∈ Icc 1 n, height p j = p.sum := by
  induction p using Multiset.induction_on with
  | empty => simp [height]
  | cons a p ih =>
    have ha : a ≤ n := hp a (Multiset.mem_cons_self _ _)
    have hb : ∀ i ∈ p, i ≤ n := fun i hi => hp i (Multiset.mem_cons_of_mem hi)
    simp only [height, Multiset.countP_cons]
    rw [Finset.sum_add_distrib]
    change ((∑ j ∈ Icc 1 n, height p j) + _) = _
    rw [ih hb, Finset.sum_ite]
    have he : (Icc 1 n).filter (· ≤ a) = Icc 1 a := by
      ext j; simp; omega
    simp [he, Nat.card_Icc, Multiset.sum_cons, add_comm]

private theorem sum_conjugateParts (p : Multiset ℕ) (n : ℕ) (hp : ∀ i ∈ p, i ≤ n) :
    (conjugateParts p n).sum = p.sum := by
  unfold conjugateParts
  have hz : (((Icc 1 n).val.map (height p)).filter (· = 0)).sum = 0 := by
    simp [Multiset.sum_eq_zero_iff]
  have h := sum_height p n hp
  change ((Icc 1 n).val.map (height p)).sum = p.sum at h
  rw [← Multiset.filter_add_not (· ≠ 0) ((Icc 1 n).val.map (height p)), Multiset.sum_add] at h
  simpa [hz] using h

private def conjugate {n : ℕ} (p : Nat.Partition n) : Nat.Partition n where
  parts := conjugateParts p.parts n
  parts_pos := fun h => Nat.pos_of_ne_zero (Multiset.mem_filter.mp h).2
  parts_sum := (sum_conjugateParts p.parts n fun _ hi => p.le_of_mem_parts hi).trans p.parts_sum

private theorem conjugate_symm {n : ℕ} (p : Nat.Partition n) {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) :
    i ≤ height (conjugate p).parts j ↔ j ≤ height p.parts i := by
  rw [conjugate, height_conjugateParts _ _ hj]
  constructor
  · intro h
    by_contra! h'
    have hs : (Icc 1 n).filter (fun x => j ≤ height p.parts x) ⊆ Icc 1 (i-1) := by
      intro x hx
      simp only [mem_filter, mem_Icc] at hx ⊢
      refine ⟨hx.1.1, ?_⟩
      by_contra! hb
      exact (not_le_of_gt h') (hx.2.trans (height_mono _ (by omega)))
    have hc := card_le_card hs
    rw [Nat.card_Icc] at hc
    omega
  · intro h
    have hip : i ≤ n := by
      have hpos : 0 < height p.parts i := hj.trans_le h
      obtain ⟨x, hx, hix⟩ := (Multiset.countP_pos).mp hpos
      exact hix.trans (p.le_of_mem_parts hx)
    have hs : Icc 1 i ⊆ (Icc 1 n).filter (fun x => j ≤ height p.parts x) := by
      intro x hx
      simp only [mem_filter, mem_Icc] at hx ⊢
      exact ⟨⟨hx.1, hx.2.trans hip⟩, h.trans (height_mono _ hx.2)⟩
    simpa [Nat.card_Icc] using card_le_card hs

private theorem conjugate_involutive {n : ℕ} (p : Nat.Partition n) :
    conjugate (conjugate p) = p := by
  have he (i : ℕ) (hi : 0 < i) : height (conjugate (conjugate p)).parts i = height p.parts i := by
    apply Nat.le_antisymm
    · by_contra! h
      let j := height p.parts i + 1
      have hj : 0 < j := by omega
      have h' := (conjugate_symm (conjugate p) hj hi).mp (show j ≤ _ by omega)
      have h'' := (conjugate_symm p hi hj).mp h'
      omega
    · by_contra! h
      let j := height (conjugate (conjugate p)).parts i + 1
      have hj : 0 < j := by omega
      have h' := (conjugate_symm p hi hj).mpr (show j ≤ _ by omega)
      have h'' := (conjugate_symm (conjugate p) hj hi).mpr h'
      omega
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    rw [Multiset.count_eq_zero_of_notMem (fun h => Nat.lt_irrefl 0 ((conjugate (conjugate p)).parts_pos h)),
      Multiset.count_eq_zero_of_notMem (fun h => Nat.lt_irrefl 0 (p.parts_pos h))]
  · have hp : 0 < i := Nat.pos_of_ne_zero hi
    have h1 := height_step (conjugate (conjugate p)).parts i
    have h2 := height_step p.parts i
    rw [he i hp, he (i+1) (by omega)] at h1
    omega

private theorem count_conjugate {n : ℕ} (p : Nat.Partition n) {j : ℕ} (hj : 0 < j) :
    (conjugate p).parts.count j = ((Icc 1 n).filter fun i => height p.parts i = j).card := by
  unfold conjugate conjugateParts
  rw [Multiset.count]
  simp only [Multiset.countP_filter, Multiset.countP_map, card]
  congr 1
  apply Multiset.filter_congr
  intro x hx
  exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, by omega⟩⟩

private theorem height_le_card (p : Multiset ℕ) (i : ℕ) :
    height p i ≤ p.card := Multiset.countP_le_card _ _

private theorem height_eq_card_iff (p : Multiset ℕ) (i : ℕ) :
    height p i = p.card ↔ ∀ x ∈ p, i ≤ x := Multiset.countP_eq_card

private theorem height_pos_iff (p : Multiset ℕ) (i : ℕ) :
    0 < height p i ↔ ∃ x ∈ p, i ≤ x := Multiset.countP_pos

private def Nontrivial {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∃ a ∈ p.parts, ∃ b ∈ p.parts, a < b

private def TopRepeated {n : ℕ} (p : Nat.Partition n) : Prop :=
  Nontrivial p ∧ ∀ x : ℕ, (∃ y ∈ p.parts, x < y) → p.parts.count x ≤ 1

private theorem height_mem_conjugate {n : ℕ} (p : Nat.Partition n) {i : ℕ}
    (hi : 0 < i) (hpos : 0 < height p.parts i) :
    height p.parts i ∈ (conjugate p).parts := by
  apply Multiset.count_pos.mp
  rw [count_conjugate _ hpos]
  apply Finset.card_pos.mpr
  use i
  simp only [mem_filter, mem_Icc, and_true]
  obtain ⟨x, hx, hix⟩ := (height_pos_iff _ _).mp hpos
  exact ⟨hi, hix.trans (p.le_of_mem_parts hx)⟩

private theorem mem_conjugate_height {n : ℕ} {p : Nat.Partition n} {h : ℕ}
    (hm : h ∈ (conjugate p).parts) : ∃ i ∈ Icc 1 n, height p.parts i = h := by
  have hp := (conjugate p).parts_pos hm
  have hs := Multiset.count_pos.mpr hm
  rw [count_conjugate p hp] at hs
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hs
  exact ⟨i,(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩

private theorem nontrivial_conjugate {n : ℕ} (p : Nat.Partition n) :
    Nontrivial (conjugate p) ↔ Nontrivial p := by
  have forward {q : Nat.Partition n} : Nontrivial q → Nontrivial (conjugate q) := by
    rintro ⟨a,ha,b,hb,hab⟩
    have hpa := q.parts_pos ha
    have hlo := height_pos_of_mem hb (show a+1 ≤ b by omega)
    have hhi := height_pos_of_mem ha (show 1 ≤ a by omega)
    refine ⟨_, height_mem_conjugate q (i := a+1) (by omega) hlo,
      _, height_mem_conjugate q (i := 1) (by omega) hhi, ?_⟩
    have hstep := height_step q.parts a
    have hc := Multiset.count_pos.mpr ha
    have hmono := height_mono q.parts (show 1 ≤ a by omega)
    omega
  exact ⟨fun h => (conjugate_involutive p) ▸ forward h, forward⟩

-- An omitted part gives equal adjacent column heights below the maximum.
private theorem topRepeated_conjugate {n : ℕ} (p : Nat.Partition n) :
    TopRepeated (conjugate p) ↔
      ∃ a b : ℕ, a < b ∧ p.parts.toFinset = Icc a b := by
  constructor
  · rintro ⟨hn,hr⟩
    have hn' := (nontrivial_conjugate p).mp hn
    obtain ⟨x,hx,y,hy,hxy⟩ := hn'
    have hs : p.parts.toFinset.Nonempty := ⟨x,Multiset.mem_toFinset.mpr hx⟩
    let a := p.parts.toFinset.min' hs
    let b := p.parts.toFinset.max' hs
    have ha : a ∈ p.parts := Multiset.mem_toFinset.mp (Finset.min'_mem _ _)
    have hb : b ∈ p.parts := Multiset.mem_toFinset.mp (Finset.max'_mem _ _)
    have ah {u} (hu : u ∈ p.parts) : a ≤ u := Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hu)
    have bh {u} (hu : u ∈ p.parts) : u ≤ b := Finset.le_max' _ _ (Multiset.mem_toFinset.mpr hu)
    have hab := (ah hx).trans_lt (hxy.trans_le (bh hy))
    refine ⟨a,b,hab,?_⟩
    ext i
    simp only [Multiset.mem_toFinset,mem_Icc]
    refine ⟨fun h => ⟨ah h,bh h⟩,?_⟩
    rintro ⟨hai,hib⟩
    by_contra hf
    have hai' : a < i := by contrapose! hf; simpa [le_antisymm hai hf] using ha
    have hib' : i < b := by contrapose! hf; simpa [le_antisymm hib hf] using hb
    have hpi := height_pos_of_mem hb (show i ≤ b from hib)
    have hc := height_step p.parts i
    rw [Multiset.count_eq_zero_of_notMem hf, zero_add] at hc
    have hi1 : 0 < i := lt_trans (p.parts_pos ha) hai'
    have hiN := p.le_of_mem_parts hb
    have hicard : height p.parts i < p.parts.card := by
      refine lt_of_le_of_ne (height_le_card _ _) ?_
      intro h
      exact (Nat.not_le_of_lt hai') ((height_eq_card_iff _ _).mp h a ha)
    have hcard : height p.parts 1 = p.parts.card :=
      (height_eq_card_iff _ _).mpr fun _ h => p.parts_pos h
    have hbig : height p.parts 1 ∈ (conjugate p).parts := by
      apply height_mem_conjugate p (by omega : 0 < 1)
      omega
    have hmax := hr (height p.parts i) ⟨height p.parts 1,hbig,by omega⟩
    rw [count_conjugate p hpi] at hmax
    have hsubset : {i,i+1} ⊆ (Icc 1 n).filter (fun u => height p.parts u = height p.parts i) := by
      intro u hu
      simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl <;> simp [mem_Icc, ← hc] <;> omega
    have hh := card_le_card hsubset
    simp at hh
    omega
  · rintro ⟨a,b,hab,hs⟩
    have he (i : ℕ) : i ∈ p.parts ↔ a ≤ i ∧ i ≤ b := by
      rw [← Multiset.mem_toFinset, hs, mem_Icc]
    have ha := (he a).mpr ⟨le_rfl,hab.le⟩
    have hb := (he b).mpr ⟨hab.le,le_rfl⟩
    refine ⟨(nontrivial_conjugate p).mpr ⟨a,ha,b,hb,hab⟩,?_⟩
    intro x hx
    by_cases hp : x = 0
    · subst x
      rw [Multiset.count_eq_zero_of_notMem (fun h => Nat.lt_irrefl _ ((conjugate p).parts_pos h))]
      omega
    have hxpos := Nat.pos_of_ne_zero hp
    obtain ⟨y,hy,hxy⟩ := hx
    obtain ⟨j,hj,hjy⟩ := mem_conjugate_height hy
    have hsmall : x < p.parts.card := hxy.trans_le (hjy ▸ height_le_card p.parts j)
    rw [count_conjugate p hxpos]
    apply Finset.card_le_one.mpr
    intro i hi k hk
    simp only [mem_filter,mem_Icc] at hi hk
    have hi_gt : a < i := by
      by_contra! hd
      have hcard := (height_eq_card_iff p.parts i).mpr fun m hm => hd.trans ((he m).mp hm).1
      omega
    have hk_gt : a < k := by
      by_contra! hd
      have hcard := (height_eq_card_iff p.parts k).mpr fun m hm => hd.trans ((he m).mp hm).1
      omega
    have hi_le : i ≤ b := by
      obtain ⟨m,hm,him⟩ := (height_pos_iff _ i).mp (show 0 < height p.parts i by omega)
      exact him.trans ((he m).mp hm).2
    have hk_le : k ≤ b := by
      obtain ⟨m,hm,hkm⟩ := (height_pos_iff _ k).mp (show 0 < height p.parts k by omega)
      exact hkm.trans ((he m).mp hm).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hh | hh
    · have hc := Multiset.count_pos.mpr ((he i).mpr ⟨hi_gt.le,hi_le⟩)
      have hst := height_step p.parts i
      have hm := height_mono p.parts (show i+1 ≤ k by omega)
      omega
    · have hc := Multiset.count_pos.mpr ((he k).mpr ⟨hk_gt.le,hk_le⟩)
      have hst := height_step p.parts k
      have hm := height_mono p.parts (show k+1 ≤ i by omega)
      omega

end BeckPartition

namespace BeckPartition
open Finset

private def Short (t : ℕ) (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, b < a+t

private def residues (t : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (· % t)

private def quotSum (t : ℕ) (S : Finset ℕ) : ℕ := ∑ a ∈ S, a / t

private theorem residues_inj {t : ℕ} {S : Finset ℕ} (h : Short t S) :
    Set.InjOn (· % t) (S : Set ℕ) := by
  intro x hx y hy he
  exact (show x ≡ y [MOD t] from he).eq_of_abs_lt (by
    rw [abs_lt]
    have hxy := h.2 x hx y hy
    have hyx := h.2 y hy x hx
    omega)

private theorem residues_card {t : ℕ} {S : Finset ℕ} (h : Short t S) :
    (residues t S).card = S.card := card_image_of_injOn (residues_inj h)

private theorem sum_residues {t : ℕ} {S : Finset ℕ} (h : Short t S) :
    ∑ a ∈ S, a = t * quotSum t S + ∑ b ∈ residues t S, b := by
  unfold residues quotSum
  rw [Finset.mul_sum, Finset.sum_image (residues_inj h)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => (Nat.div_add_mod a t).symm

-- Raising the least element by one period preserves the width bound and the residues.
private def up (t : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if h : S.Nonempty then insert (S.min' h + t) (S.erase (S.min' h)) else S

private def down (t : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if h : S.Nonempty then insert (S.max' h - t) (S.erase (S.max' h)) else S

private theorem short_up {t : ℕ} {S : Finset ℕ} (h : Short t S) :
    Short t (up t S) ∧ 0 ∉ up t S ∧
      residues t (up t S) = residues t S ∧ quotSum t (up t S) = quotSum t S + 1 := by
  have ht : 0 < t := by
    obtain ⟨x,hx⟩ := h.1
    have hxx := h.2 x hx x hx
    omega
  let m := S.min' h.1
  have hm : m ∈ S := min'_mem _ _
  have hmin {x} (hx : x ∈ S) : m ≤ x := min'_le _ _ hx
  have hbelow {x} (hx : x ∈ S) : x < m+t := h.2 m hm x hx
  have hnot : m+t ∉ S.erase m := by
    intro hx
    exact (Nat.lt_irrefl _) (hbelow (mem_of_mem_erase hx))
  have hU : up t S = insert (m+t) (S.erase m) := by simp [up,h.1,m]
  rw [hU]
  refine ⟨⟨mem_insert_self _ _ |> fun hh => ⟨_,hh⟩,?_⟩,?_,?_,?_⟩
  · intro a ha b hb
    rcases mem_insert.mp ha with rfl | ha
    · rcases mem_insert.mp hb with rfl | hb
      · omega
      · have := hbelow (mem_of_mem_erase hb)
        omega
    · rcases mem_insert.mp hb with rfl | hb
      · have hl := hmin (mem_of_mem_erase ha)
        have hn := (mem_erase.mp ha).1
        omega
      · exact h.2 _ (mem_of_mem_erase ha) _ (mem_of_mem_erase hb)
  · intro hz
    rcases mem_insert.mp hz with he | hz
    · omega
    · have hl := hmin (mem_of_mem_erase hz)
      have hn := (mem_erase.mp hz).1
      omega
  · unfold residues
    rw [image_insert]
    rw [show (m+t)%t = m%t by simp]
    rw [← image_insert (f := fun x : ℕ => x % t) (s := S.erase m) (a := m), insert_erase hm]
  · rw [quotSum, sum_insert hnot, Nat.add_div_right _ ht]
    have hs := sum_erase_add S (fun x => x/t) hm
    unfold quotSum
    omega

private theorem short_down {t : ℕ} {S : Finset ℕ} (h : Short t S) (hs : 0 < quotSum t S) :
    Short t (down t S) ∧ up t (down t S) = S ∧
      residues t (down t S) = residues t S ∧ quotSum t (down t S) + 1 = quotSum t S := by
  let m := S.max' h.1
  have hm : m ∈ S := max'_mem _ _
  have hmax {x} (hx : x ∈ S) : x ≤ m := le_max' _ _ hx
  have ht : 0 < t := by have hc := h.2 m hm m hm; omega
  have htm : t ≤ m := by
    by_contra! hlt
    have hz : quotSum t S = 0 :=
      Finset.sum_eq_zero fun x hx => Nat.div_eq_of_lt ((hmax hx).trans_lt hlt)
    omega
  have hbelow {x} (hx : x ∈ S) : m-t < x := by
    have hh := h.2 x hx m hm
    omega
  have hnot : m-t ∉ S.erase m := by
    intro hx
    exact (Nat.lt_irrefl _) (hbelow (mem_of_mem_erase hx))
  have hD : down t S = insert (m-t) (S.erase m) := by simp [down,h.1,m]
  rw [hD]
  have hN : (insert (m-t) (S.erase m)).Nonempty := ⟨_,mem_insert_self _ _⟩
  have hsub : m - t + t = m := Nat.sub_add_cancel htm
  refine ⟨⟨hN,?_⟩,?_,?_,?_⟩
  · intro a ha b hb
    rcases mem_insert.mp ha with rfl | ha
    · rcases mem_insert.mp hb with rfl | hb
      · omega
      · have hl := hmax (mem_of_mem_erase hb)
        have hn := (mem_erase.mp hb).1
        omega
    · rcases mem_insert.mp hb with rfl | hb
      · have hl := hbelow (mem_of_mem_erase ha)
        omega
      · exact h.2 _ (mem_of_mem_erase ha) _ (mem_of_mem_erase hb)
  · have hmin : (insert (m-t) (S.erase m)).min' hN = m-t := by
      apply le_antisymm (Finset.min'_le _ _ (mem_insert_self _ _))
      apply Finset.le_min'
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hbelow (mem_of_mem_erase hx)).le
    rw [up, dif_pos hN, hmin, hsub, erase_insert hnot, insert_erase hm]
  · unfold residues
    rw [image_insert]
    have he : (m-t)%t = m%t := by
      nth_rw 2 [← hsub]
      simp
    rw [he, ← image_insert (f := fun x : ℕ => x % t) (s := S.erase m) (a := m), insert_erase hm]
  · rw [quotSum, sum_insert hnot]
    have he : (m-t)/t + 1 = m/t := by
      nth_rw 2 [← hsub]
      rw [Nat.add_div_right _ ht]
    have hs' := sum_erase_add S (fun x => x/t) hm
    unfold quotSum
    omega

-- The sum of quotients counts the number of period shifts from the least residues.
private theorem lift_unique (t : ℕ) (ht : 0 < t) (R : Finset ℕ)
    (hR : R.Nonempty) (hbound : ∀ a ∈ R, a < t) (r : ℕ) :
    ∃! S : Finset ℕ, Short t S ∧ residues t S = R ∧ quotSum t S = r := by
  induction r with
  | zero =>
    have hshort : Short t R := ⟨hR, fun a ha b hb => (hbound b hb).trans_le (by omega)⟩
    have he : residues t R = R := image_congr (fun a ha => Nat.mod_eq_of_lt (hbound a ha))
      |>.trans Finset.image_id
    have hz : quotSum t R = 0 := sum_eq_zero fun a ha => Nat.div_eq_of_lt (hbound a ha)
    refine ⟨R,⟨hshort,he,hz⟩,?_⟩
    rintro S ⟨_,he',hz'⟩
    have hlt : ∀ a ∈ S, a < t := by
      intro a ha
      have hp := single_le_sum (f := fun a : ℕ => a/t) (fun _ _ => Nat.zero_le _) ha
      change a / t ≤ quotSum t S at hp
      rw [hz'] at hp
      exact Nat.lt_of_div_eq_zero ht (Nat.eq_zero_of_le_zero hp)
    have hs : residues t S = S :=
      (image_congr (fun a ha => Nat.mod_eq_of_lt (hlt a ha))).trans Finset.image_id
    exact hs.symm.trans he'
  | succ r ih =>
    obtain ⟨T,⟨hts,htr,htq⟩, hu⟩ := ih
    obtain ⟨hs,_,hr,hq⟩ := short_up hts
    refine ⟨up t T,⟨hs,hr.trans htr,hq.trans (by omega)⟩,?_⟩
    rintro S ⟨hSs,hSr,hSq⟩
    obtain ⟨hDs,hU,hDr,hDq⟩ := short_down hSs (by omega)
    have he : down t S = T := hu _ ⟨hDs,hDr.trans hSr,by omega⟩
    rw [← he,hU]

end BeckPartition

namespace BeckPartition
open Finset

-- A repeated largest part t, its multiplicity r, and the distinct smaller parts.
private structure Data (n : ℕ) where
  t : ℕ
  r : ℕ
  R : Finset ℕ
  r_pos : 0 < r
  nonempty : R.Nonempty
  residues_pos : ∀ a ∈ R, 0 < a ∧ a < t
  weight : n = t * r + ∑ a ∈ R, a

private def Data.parts {n : ℕ} (d : Data n) : Multiset ℕ :=
  Multiset.replicate d.r d.t + d.R.val

private theorem Data.t_pos {n : ℕ} (d : Data n) : 0 < d.t := by
  obtain ⟨a,ha⟩ := d.nonempty
  exact Nat.zero_lt_of_lt (d.residues_pos a ha).2

private theorem Data.t_mem {n : ℕ} (d : Data n) : d.t ∈ d.parts := by
  apply Multiset.mem_add.mpr
  left
  exact Multiset.mem_replicate.mpr ⟨d.r_pos.ne',rfl⟩

private theorem Data.parts_pos {n : ℕ} (d : Data n) {a : ℕ} (ha : a ∈ d.parts) : 0 < a := by
  rcases Multiset.mem_add.mp ha with ha | ha
  · simp only [Multiset.mem_replicate] at ha
    exact ha.2 ▸ d.t_pos
  · exact (d.residues_pos a ha).1

private theorem Data.max_part {n : ℕ} (d : Data n) {a : ℕ} (ha : a ∈ d.parts) : a ≤ d.t := by
  rcases Multiset.mem_add.mp ha with ha | ha
  · simp only [Multiset.mem_replicate] at ha
    exact ha.2.le
  · exact (d.residues_pos a ha).2.le

private theorem Data.not_mem_t {n : ℕ} (d : Data n) : d.t ∉ d.R :=
  fun h => (Nat.lt_irrefl _) (d.residues_pos _ h).2

private theorem Data.count_top {n : ℕ} (d : Data n) : d.parts.count d.t = d.r := by
  simp [Data.parts, Multiset.count_eq_zero_of_notMem d.not_mem_t]

private theorem Data.erase_top {n : ℕ} (d : Data n) : d.parts.toFinset.erase d.t = d.R := by
  ext a
  simp only [mem_erase, Multiset.mem_toFinset, Data.parts, Multiset.mem_add]
  constructor
  · rintro ⟨hne,ha | ha⟩
    · simp only [Multiset.mem_replicate] at ha
      exact False.elim (hne ha.2)
    · exact ha
  · intro ha
    exact ⟨(d.residues_pos _ ha).2.ne, Or.inr ha⟩

private def Data.partition {n : ℕ} (d : Data n) : Nat.Partition n where
  parts := d.parts
  parts_pos := d.parts_pos
  parts_sum := by simpa [Data.parts, Multiset.sum_replicate, mul_comm] using d.weight.symm

private theorem Data.unique {n : ℕ} {d e : Data n} (h : d.parts = e.parts) : d = e := by
  have ht1 := e.max_part (show d.t ∈ e.parts from h ▸ d.t_mem)
  have ht2 := d.max_part (show e.t ∈ d.parts from h.symm ▸ e.t_mem)
  have ht := ht1.antisymm ht2
  have hr := d.count_top
  rw [h,ht,e.count_top] at hr
  have hR := d.erase_top
  rw [h,ht,e.erase_top] at hR
  cases d
  cases e
  congr
  · exact hr.symm
  · exact hR.symm

end BeckPartition
namespace BeckPartition
open Finset
open OMA.S_oeis_a237665

private theorem Data.topRepeated {n : ℕ} (d : Data n) : TopRepeated d.partition := by
  obtain ⟨a,ha⟩ := d.nonempty
  have ham : a ∈ d.partition.parts := Multiset.mem_add.mpr (Or.inr ha)
  refine ⟨⟨a,ham,d.t,d.t_mem,(d.residues_pos a ha).2⟩,?_⟩
  rintro x ⟨y,hy,hxy⟩
  have hx := hxy.trans_le (d.max_part hy)
  change (Multiset.replicate d.r d.t + d.R.val).count x ≤ 1
  simp only [Multiset.count_add, Multiset.count_replicate, if_neg hx.ne.symm, zero_add]
  exact (Multiset.nodup_iff_count_le_one.mp d.R.nodup) x

private theorem exists_data_of_topRepeated {n : ℕ} {p : Nat.Partition n}
    (h : TopRepeated p) : ∃ d : Data n, d.partition = p := by
  obtain ⟨⟨a,ha,b,hb,hab⟩,hrep⟩ := h
  let S := p.parts.toFinset
  have hS : S.Nonempty := ⟨a,Multiset.mem_toFinset.mpr ha⟩
  let t := S.max' hS
  have htS : t ∈ S := max'_mem _ _
  have ht : t ∈ p.parts := Multiset.mem_toFinset.mp htS
  have hmax {x : ℕ} (hx : x ∈ p.parts) : x ≤ t :=
    le_max' _ _ (Multiset.mem_toFinset.mpr hx)
  let R := S.erase t
  have hR : R.Nonempty := ⟨a,mem_erase.mpr ⟨(hab.trans_le (hmax hb)).ne,Multiset.mem_toFinset.mpr ha⟩⟩
  have hr : 0 < p.parts.count t := Multiset.count_pos.mpr ht
  have hRp : ∀ x ∈ R, 0 < x ∧ x < t := by
    intro x hx
    obtain ⟨hne,hx⟩ := mem_erase.mp hx
    have hxp := Multiset.mem_toFinset.mp hx
    exact ⟨p.parts_pos hxp, lt_of_le_of_ne (hmax hxp) hne⟩
  have he : Multiset.replicate (p.parts.count t) t + R.val = p.parts := by
    apply Multiset.ext.mpr
    intro x
    rw [Multiset.count_add]
    by_cases hx : x = t
    · subst x
      have hnot : t ∉ R := by simp [R]
      simp [Multiset.count_eq_zero_of_notMem hnot]
    · by_cases hxp : x ∈ p.parts
      · have hxR : x ∈ R := mem_erase.mpr ⟨hx,Multiset.mem_toFinset.mpr hxp⟩
        have hs := (Multiset.nodup_iff_count_eq_one.mp R.nodup) x hxR
        have hp1 := hrep x ⟨t,ht,lt_of_le_of_ne (hmax hxp) hx⟩
        have hp2 := Multiset.count_pos.mpr hxp
        simp only [Multiset.count_replicate, if_neg (Ne.symm hx), zero_add, hs]
        omega
      · have hnot : x ∉ R := fun hx => hxp (Multiset.mem_toFinset.mp (mem_of_mem_erase hx))
        simp only [Multiset.count_replicate, if_neg (Ne.symm hx), zero_add,
          Multiset.count_eq_zero_of_notMem hnot, Multiset.count_eq_zero_of_notMem hxp]
  have hw : n = t * p.parts.count t + ∑ x ∈ R, x := by
    have hn := congrArg Multiset.sum he
    simpa [Multiset.sum_replicate,p.parts_sum,mul_comm] using hn.symm
  exact ⟨⟨t, p.parts.count t, R, hr, hR, hRp, hw⟩, Nat.Partition.ext he⟩

private abbrev EvenDistinct (n : ℕ) :=
  {p : Nat.Partition n // p.parts.Nodup ∧ p.parts ≠ 0 ∧ Even p.parts.card}

private abbrev Marked (n : ℕ) := Sigma fun p : EvenDistinct n => Fin (smallestPart p.1)

private def addZero (R : Finset ℕ) : Finset ℕ := if Even R.card then R else insert 0 R

private theorem addZero_props {t : ℕ} {R : Finset ℕ} (hR : R.Nonempty)
    (h : ∀ a ∈ R, 0 < a ∧ a < t) :
    (addZero R).Nonempty ∧ (∀ a ∈ addZero R, a < t) ∧ Even (addZero R).card ∧
      (addZero R).erase 0 = R ∧ (∑ a ∈ addZero R, a) = ∑ a ∈ R, a := by
  have hno : 0 ∉ R := fun hb => Nat.lt_irrefl _ (h 0 hb).1
  have ht : 0 < t := by
    obtain ⟨a,ha⟩ := hR
    exact (h a ha).1.trans (h a ha).2
  by_cases he : Even R.card
  · simp only [addZero, if_pos he]
    exact ⟨hR,fun a ha => (h a ha).2,he,erase_eq_of_notMem hno,True.intro⟩
  · simp only [addZero, if_neg he]
    refine ⟨⟨0,mem_insert_self _ _⟩,?_,?_,erase_insert hno,by rw [sum_insert hno,zero_add]⟩
    · intro a ha
      rcases mem_insert.mp ha with rfl | hb
      · exact ht
      · exact (h a hb).2
    · rw [card_insert_of_notMem hno]
      exact (Nat.not_even_iff_odd.mp he).add_odd (by decide : Odd 1)

private theorem addZero_erase {R : Finset ℕ} (he : Even R.card) : addZero (R.erase 0) = R := by
  by_cases h : 0 ∈ R
  · have hc := card_erase_add_one h
    have ho : ¬ Even (R.erase 0).card := by
      obtain ⟨k,hk⟩ := he
      intro hh
      obtain ⟨j,hj⟩ := hh
      omega
    simp [addZero, ho, insert_erase h]
  · simp [addZero, erase_eq_of_notMem h, he]

private theorem quotSum_pos {t : ℕ} {S : Finset ℕ} (ht : 0 < t) (hS : S.Nonempty) :
    0 < quotSum t S ↔ t ≤ S.max' hS := by
  constructor
  · intro h
    by_contra! hm
    have hz : quotSum t S = 0 :=
      sum_eq_zero fun x hx => Nat.div_eq_of_lt ((le_max' _ _ hx).trans_lt hm)
    omega
  · intro h
    have hm := Finset.single_le_sum (f := fun a : ℕ => a/t)
      (fun _ _ => Nat.zero_le _) (max'_mem S hS)
    have hp := Nat.div_pos h ht
    exact hp.trans_le hm

private theorem exists_marked_of_data {n : ℕ} (d : Data n) :
    ∃ p : Marked n, ∃ hS : p.1.1.parts.toFinset.Nonempty,
      p.1.1.parts.toFinset.max' hS = d.t + p.2.val ∧
      residues d.t p.1.1.parts.toFinset = addZero d.R ∧
      quotSum d.t p.1.1.parts.toFinset = d.r := by
  obtain ⟨hR,hRt,hRe,_,hRs⟩ := addZero_props d.nonempty d.residues_pos
  obtain ⟨S,⟨hs,hr,hq⟩,hu⟩ := lift_unique d.t d.t_pos (addZero d.R) hR hRt d.r
  have hS0 : 0 ∉ S := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero d.r_pos.ne'
    obtain ⟨T,⟨hts,htr,htq⟩,_⟩ := lift_unique d.t d.t_pos (addZero d.R) hR hRt k
    obtain ⟨hU,hU0,hUr,hUq⟩ := short_up hts
    have he := hu (up d.t T) ⟨hU,hUr.trans htr, by omega⟩
    rwa [he] at hU0
  have hweight : ∑ a ∈ S, a = n := by
    rw [sum_residues hs, hq, hr, hRs, ← d.weight]
  let p : Nat.Partition n :=
    ⟨S.val, fun ha => Nat.pos_of_ne_zero (fun he => hS0 (he ▸ ha)), by
      rw [Finset.sum_eq_multiset_sum, Multiset.map_id'] at hweight
      exact hweight⟩
  have hSp : p.parts.toFinset = S := by simp [p]
  have he : Even p.parts.card := by
    change Even S.card
    rwa [← residues_card hs,hr]
  have hNE : p.parts ≠ 0 := by
    obtain ⟨a,ha⟩ := hs.1
    intro he
    have : a ∈ p.parts := ha
    simp [he] at this
  let hp : EvenDistinct n := ⟨p,S.nodup,hNE,he⟩
  have htmax := (quotSum_pos d.t_pos hs.1).mp (hq.symm ▸ d.r_pos)
  let k := S.max' hs.1 - d.t
  have hk : k < smallestPart p := by
    unfold smallestPart
    rw [hSp, dif_pos hs.1]
    have hh := hs.2 (S.min' hs.1) (min'_mem _ _) (S.max' hs.1) (max'_mem _ _)
    dsimp only [k]
    omega
  let out : Marked n := ⟨hp,⟨k,hk⟩⟩
  have hf : p.parts.toFinset.Nonempty := by
    rw [hSp]
    exact hs.1
  refine ⟨out,hf,?_,?_,?_⟩
  · change p.parts.toFinset.max' hf = d.t + k
    have hm : p.parts.toFinset.max' hf = S.max' hs.1 := by
      apply le_antisymm
      · exact le_max' _ _ (hSp ▸ max'_mem _ _)
      · exact le_max' _ _ (hSp.symm ▸ max'_mem _ _)
    rw [hm]
    dsimp only [k]
    omega
  · change residues d.t p.parts.toFinset = _
    rwa [hSp]
  · change quotSum d.t p.parts.toFinset = _
    rwa [hSp]

private theorem marked_nonempty {n : ℕ} (p : Marked n) :
    p.1.1.parts.toFinset.Nonempty := by
  obtain ⟨a,ha⟩ := Multiset.exists_mem_of_ne_zero p.1.2.2.1
  exact ⟨a,Multiset.mem_toFinset.mpr ha⟩

private theorem exists_data_of_marked {n : ℕ} (p : Marked n) :
    ∃ d : Data n, ∃ hS : p.1.1.parts.toFinset.Nonempty,
      p.1.1.parts.toFinset.max' hS = d.t + p.2.val ∧
      residues d.t p.1.1.parts.toFinset = addZero d.R ∧
      quotSum d.t p.1.1.parts.toFinset = d.r := by
  let S := p.1.1.parts.toFinset
  let hS : S.Nonempty := marked_nonempty p
  let M := S.max' hS
  let t := M - p.2.val
  have hpmin : smallestPart p.1.1 = S.min' hS := dif_pos hS
  have hmark : p.2.val < S.min' hS := hpmin ▸ p.2.isLt
  have hM : M ∈ S := max'_mem _ _
  have hminmax := Finset.min'_le _ _ hM
  have ht : 0 < t := by dsimp only [t]; omega
  have hshort : Short t S := by
    refine ⟨hS,?_⟩
    intro a ha b hb
    have ham := min'_le _ _ ha
    have hbm : b ≤ M := le_max' _ _ hb
    dsimp only [t]
    omega
  let U := residues t S
  let R := U.erase 0
  have hSc : S.card = p.1.1.parts.card := Multiset.toFinset_card_of_nodup p.1.2.1
  have hEven : Even U.card := by
    change Even (residues t S).card
    rw [residues_card hshort,hSc]
    exact p.1.2.2.2
  have hUlarge : 2 ≤ U.card := by
    have hUpos := Finset.card_pos.mpr (Finset.Nonempty.image hS (· % t))
    obtain ⟨j,hj⟩ := hEven
    have hPos : 0 < U.card := hUpos
    omega
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    by_cases h0 : 0 ∈ U
    · have hcard : R.card + 1 = U.card := card_erase_add_one h0
      omega
    · simpa [R,erase_eq_of_notMem h0] using (show 0 < U.card by omega)
  have hRp : ∀ a ∈ R, 0 < a ∧ a < t := by
    intro a ha
    obtain ⟨hne,ha⟩ := mem_erase.mp ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    exact ⟨Nat.pos_of_ne_zero hne,Nat.mod_lt _ ht⟩
  have hUp : addZero R = U := addZero_erase hEven
  have hq : 0 < quotSum t S := (quotSum_pos ht hS).mpr (by dsimp only [t]; omega)
  have hweight : ∑ a ∈ S, a = n := by
    rw [Finset.sum_eq_multiset_sum]
    have he : S.val = p.1.1.parts :=
      (Multiset.toFinset_val _).trans (Multiset.dedup_eq_self.mpr p.1.2.1)
    simpa [he] using p.1.1.parts_sum
  have hsum := sum_residues hshort
  have hs : ∑ a ∈ U, a = ∑ a ∈ R, a := by
    rw [← hUp]
    exact (addZero_props hR hRp).2.2.2.2
  rw [hweight,hs] at hsum
  refine ⟨⟨t,quotSum t S,R,hq,hR,hRp,hsum⟩,hS,?_,hUp.symm,rfl⟩
  change M = t + p.2.val
  dsimp only [t]
  omega


private def packetRel {n : ℕ} (d : Data n) (p : Marked n) : Prop :=
  ∃ hS : p.1.1.parts.toFinset.Nonempty,
    p.1.1.parts.toFinset.max' hS = d.t + p.2.val ∧
    residues d.t p.1.1.parts.toFinset = addZero d.R ∧
    quotSum d.t p.1.1.parts.toFinset = d.r

private theorem relation_leftUnique {n : ℕ} {d e : Data n} {p : Marked n}
    (hd : packetRel d p) (he : packetRel e p) : d = e := by
  obtain ⟨hSd,htd,hRd,hrd⟩ := hd
  obtain ⟨hSe,hte,hRe,hre⟩ := he
  have ht : d.t = e.t := by omega
  have hr : d.r = e.r := by rw [ht,hre] at hrd; exact hrd.symm
  have hR : d.R = e.R := by
    rw [ht,hRe] at hRd
    have hde := congrArg (fun s : Finset ℕ => s.erase 0) hRd
    rw [(addZero_props e.nonempty e.residues_pos).2.2.2.1,
      (addZero_props d.nonempty d.residues_pos).2.2.2.1] at hde
    exact hde.symm
  apply Data.unique
  simp [Data.parts,ht,hr,hR]

private theorem relation_short {n : ℕ} {d : Data n} {p : Marked n} (hr : packetRel d p) :
    Short d.t p.1.1.parts.toFinset := by
  obtain ⟨hS,ht,hR,hq⟩ := hr
  refine ⟨hS,?_⟩
  intro a ha b hb
  have hm := min'_le _ _ ha
  have hx := le_max' _ _ hb
  have hmin : smallestPart p.1.1 = p.1.1.parts.toFinset.min' hS := dif_pos hS
  have hk : p.2.val < p.1.1.parts.toFinset.min' hS := hmin ▸ p.2.isLt
  omega

private theorem relation_rightUnique {n : ℕ} {d : Data n} {p q : Marked n}
    (hp : packetRel d p) (hq : packetRel d q) : p = q := by
  have hps := relation_short hp
  have hqs := relation_short hq
  obtain ⟨hSp,htp,hRp,hrp⟩ := hp
  obtain ⟨hSq,htq,hRq,hrq⟩ := hq
  obtain ⟨hR,hRt,hRe,_,hRs⟩ := addZero_props d.nonempty d.residues_pos
  obtain ⟨S,_,hu⟩ := lift_unique d.t d.t_pos (addZero d.R) hR hRt d.r
  have hS : p.1.1.parts.toFinset = q.1.1.parts.toFinset :=
    (hu _ ⟨hps,hRp,hrp⟩).trans (hu _ ⟨hqs,hRq,hrq⟩).symm
  have hMaxEq : p.1.1.parts.toFinset.max' hSp = q.1.1.parts.toFinset.max' hSq := by
    apply le_antisymm
    · exact le_max' _ _ (hS ▸ max'_mem _ _)
    · exact le_max' _ _ (hS.symm ▸ max'_mem _ _)
  have hK : p.2.val = q.2.val := by omega
  have he : p.1 = q.1 := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact Multiset.Nodup.toFinset_inj p.1.2.1 q.1.2.1 hS
  rcases p with ⟨p,k⟩
  rcases q with ⟨q,l⟩
  change p = q at he
  subst q
  have hl : k = l := Fin.ext hK
  subst l
  rfl

private noncomputable def dataMarkedEquiv (n : ℕ) : Data n ≃ Marked n :=
  Equiv.ofBijective (fun d => (exists_marked_of_data d).choose) <| by
    constructor
    · intro d e he
      have hd : packetRel d (exists_marked_of_data d).choose :=
        (exists_marked_of_data d).choose_spec
      have hE : packetRel e (exists_marked_of_data e).choose :=
        (exists_marked_of_data e).choose_spec
      change (exists_marked_of_data d).choose = (exists_marked_of_data e).choose at he
      rw [← he] at hE
      exact relation_leftUnique hd hE
    · intro p
      obtain ⟨d,hd⟩ := exists_data_of_marked p
      exact ⟨d,relation_rightUnique (exists_marked_of_data d).choose_spec hd⟩

private noncomputable def dataTopEquiv (n : ℕ) :
    Data n ≃ {p : Nat.Partition n // TopRepeated p} :=
  Equiv.ofBijective (fun d => ⟨d.partition,d.topRepeated⟩) <| by
    constructor
    · intro d e he
      exact Data.unique (congrArg (fun p : {p : Nat.Partition n // TopRepeated p} =>
        p.val.parts) he)
    · intro p
      obtain ⟨d,hd⟩ := exists_data_of_topRepeated p.2
      exact ⟨d,Subtype.ext hd⟩

private theorem topRepeated_conjugate_iff {n : ℕ} (p : Nat.Partition n) :
    TopRepeated (conjugate p) ↔ ConsecutiveDistinctParts p := by
  rw [topRepeated_conjugate,ConsecutiveDistinctParts]
  constructor
  · rintro ⟨a,b,hab,h⟩
    exact ⟨a,b-a,by omega,by convert h using 2; omega⟩
  · rintro ⟨a,r,hr,h⟩
    exact ⟨a,a+r,by omega,h⟩

private def consecutiveEquiv (n : ℕ) :
    {p : Nat.Partition n // ConsecutiveDistinctParts p} ≃ {p : Nat.Partition n // TopRepeated p} where
  toFun p := ⟨conjugate p.1,(topRepeated_conjugate_iff p.1).mpr p.2⟩
  invFun p := ⟨conjugate p.1,(topRepeated_conjugate_iff _).mp (by simpa [conjugate_involutive] using p.2)⟩
  left_inv p := Subtype.ext (conjugate_involutive p.1)
  right_inv p := Subtype.ext (conjugate_involutive p.1)

private theorem count_left (n : ℕ) :
    Nat.card {p : Nat.Partition n // ConsecutiveDistinctParts p} = a n := by
  classical
  let S := (Finset.univ : Finset (Nat.Partition n)).filter ConsecutiveDistinctParts
  let e : {p : Nat.Partition n // ConsecutiveDistinctParts p} ≃ S :=
    Equiv.subtypeEquivProp (funext fun _ => propext (by simp [S]))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

private theorem count_right (n : ℕ) : Nat.card (Marked n) = sumSmallestEvenDistinct n := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Sigma fun p : EvenDistinct n => Fin (smallestPart p.1)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  symm
  unfold sumSmallestEvenDistinct
  exact Finset.sum_subtype _ (by simp) (fun p => smallestPart p)

protected theorem result (n : ℕ) : a n = sumSmallestEvenDistinct n := by
  rw [← count_left, ← count_right]
  exact Nat.card_congr ((consecutiveEquiv n).trans ((dataTopEquiv n).symm.trans (dataMarkedEquiv n)))

end BeckPartition

theorem OMA.solution : type_of% @OMA.S_oeis_a237665.main :=
  BeckPartition.result
