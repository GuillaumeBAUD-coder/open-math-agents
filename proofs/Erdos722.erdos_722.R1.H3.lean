import OMAReductions.R_Erdos722_erdos_722_R1

-- Step Erdos722.erdos_722.R1.H3: hypothesis H3 of reduction Erdos722.erdos_722.R1
-- Credit: @Williamnowak
-- A shorter proof of the step (same route as the first proof: induction on the ground set, with the
-- square case solved by inclusion-exclusion).

/-!
Integral designs (Wilson 1973, Graver–Jurkat 1973): every integer vector on the `r`-subsets of a
finite set `s` satisfying the divisibility conditions is an integer combination of the columns of
the `r`-subsets versus `k`-subsets inclusion matrix, as soon as `k + r ≤ #s`.

Induction on `s`, splitting on one point. The square case `#s = k + r` is solved explicitly by
inclusion–exclusion over the subsets of the complement of a block.
-/

namespace OMA.W

open Finset

variable {α : Type*} [DecidableEq α]

/-- Sum of `f` over the `j`-subsets of `s` that contain `I`. -/
def cs (s : Finset α) (j : ℕ) (I : Finset α) (f : Finset α → ℤ) : ℤ :=
  ∑ A ∈ (s.powersetCard j).filter (I ⊆ ·), f A

lemma cs_congr {s : Finset α} {j : ℕ} {I : Finset α} {f g : Finset α → ℤ}
    (h : ∀ A ∈ s.powersetCard j, f A = g A) : cs s j I f = cs s j I g :=
  sum_congr rfl fun A hA => h A (mem_filter.1 hA).1

lemma card_sup (B I : Finset α) (j : ℕ) (hI : I ⊆ B) (hj : #I ≤ j) :
    #((B.powersetCard j).filter (I ⊆ ·)) = (#B - #I).choose (j - #I) := by
  rw [← card_sdiff_of_subset hI, ← card_powersetCard]
  refine card_bij' (fun A _ => A \ I) (fun C _ => C ∪ I) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hA, hIA⟩ := mem_filter.1 hA
    obtain ⟨hAB, hAc⟩ := mem_powersetCard.1 hA
    exact mem_powersetCard.2 ⟨sdiff_subset_sdiff hAB le_rfl, by rw [card_sdiff_of_subset hIA, hAc]⟩
  · intro C hC
    obtain ⟨hCB, hCc⟩ := mem_powersetCard.1 hC
    obtain ⟨hC1, hC2⟩ := subset_sdiff.1 hCB
    exact mem_filter.2 ⟨mem_powersetCard.2 ⟨union_subset hC1 hI,
      by rw [card_union_of_disjoint hC2, hCc]; omega⟩, subset_union_right⟩
  · intro A hA
    exact sdiff_union_of_subset (mem_filter.1 hA).2
  · intro C hC
    exact union_sdiff_cancel_right (subset_sdiff.1 (mem_powersetCard.1 hC).1).2

lemma cs_cs (s I : Finset α) (j m : ℕ) (f : Finset α → ℤ) (hj : #I ≤ j) :
    cs s j I (fun A => cs s m A f) = (m - #I).choose (j - #I) * cs s m I f := by
  simp only [cs]
  rw [sum_comm' (s' := fun B => (B.powersetCard j).filter (I ⊆ ·))
    (t' := (s.powersetCard m).filter (I ⊆ ·)), mul_sum]
  · refine sum_congr rfl fun B hB => ?_
    obtain ⟨hB, hIB⟩ := mem_filter.1 hB
    rw [sum_const, card_sup _ _ _ hIB hj, (mem_powersetCard.1 hB).2, nsmul_eq_mul]
  · intro A B
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨⟨_, hAc⟩, hIA⟩, hB, hAB⟩
      exact ⟨⟨⟨hAB, hAc⟩, hIA⟩, hB, hIA.trans hAB⟩
    · rintro ⟨⟨⟨hAB, hAc⟩, hIA⟩, hB, _⟩
      exact ⟨⟨⟨hAB.trans hB.1, hAc⟩, hIA⟩, hB, hAB⟩

lemma cs_insert {s : Finset α} {p : α} (hp : p ∉ s) (m : ℕ) (A : Finset α) (g : Finset α → ℤ) :
    cs (insert p s) (m + 1) A g = cs s (m + 1) A g +
      ∑ B ∈ (s.powersetCard m).filter (fun B => A ⊆ insert p B), g (insert p B) := by
  have hn : ∀ B ∈ s.powersetCard m, p ∉ B := fun B hB h => hp ((mem_powersetCard.1 hB).1 h)
  rw [cs, powersetCard_succ_insert hp, filter_union, sum_union, filter_image, sum_image]
  · rfl
  · intro B hB C hC h
    rw [← erase_insert (hn B (mem_filter.1 hB).1), h, erase_insert (hn C (mem_filter.1 hC).1)]
  · refine disjoint_left.2 fun B hB hB' => ?_
    obtain ⟨C, _, rfl⟩ := mem_image.1 (mem_filter.1 hB').1
    exact hp ((mem_powersetCard.1 (mem_filter.1 hB).1).1 (mem_insert_self p C))

lemma cs_insert0 {s : Finset α} {p : α} (hp : p ∉ s) (m : ℕ) {A : Finset α} (hA : p ∉ A)
    (g : Finset α → ℤ) :
    cs (insert p s) (m + 1) A g = cs s (m + 1) A g + cs s m A fun B => g (insert p B) := by
  rw [cs_insert hp]
  congr 1
  exact sum_congr (filter_congr fun B _ => subset_insert_iff_of_notMem hA) fun _ _ => rfl

lemma cs_insert1 {s : Finset α} {p : α} (hp : p ∉ s) (m : ℕ) {A : Finset α} (hA : p ∉ A)
    (g : Finset α → ℤ) :
    cs (insert p s) (m + 1) (insert p A) g = cs s m A fun B => g (insert p B) := by
  rw [cs_insert hp, cs, filter_false_of_mem, sum_empty, zero_add]
  · exact sum_congr (filter_congr fun B _ => insert_subset_insert_iff hA) fun _ _ => rfl
  · intro B hB h
    exact hp ((mem_powersetCard.1 hB).1 (h (mem_insert_self _ _)))

/-- The square case `#s = k + r`, by inclusion–exclusion. -/
lemma base (s : Finset α) (k r : ℕ) (hrk : r ≤ k) (hs : #s = k + r) (y : Finset α → ℤ)
    (hD : ∀ I ⊆ s, #I ≤ r → ((k - #I).choose (r - #I) : ℤ) ∣ cs s r I y) :
    ∃ x : Finset α → ℤ, ∀ A ∈ s.powersetCard r, cs s k A x = y A := by
  refine ⟨fun B => ∑ I ∈ (s \ B).powerset,
    (-1) ^ #I * (cs s r I y / (k - #I).choose (r - #I)), fun A hA => ?_⟩
  obtain ⟨hAs, hAc⟩ := mem_powersetCard.1 hA
  rw [cs, sum_comm' (s' := fun I => ((s \ I).powersetCard k).filter (A ⊆ ·))
    (t' := (s \ A).powerset)]
  · trans ∑ I ∈ (s \ A).powerset, (-1) ^ #I * cs s r I y
    · refine sum_congr rfl fun I hI => ?_
      obtain ⟨hIs, hIA⟩ := subset_sdiff.1 (mem_powerset.1 hI)
      have hik : #I ≤ k := by
        have := card_le_card (mem_powerset.1 hI)
        rw [card_sdiff_of_subset hAs, hs, hAc] at this
        omega
      rw [sum_const, card_sup _ _ _ (subset_sdiff.2 ⟨hAs, hIA.symm⟩) (hAc ▸ hrk),
        card_sdiff_of_subset hIs, hs, hAc, nsmul_eq_mul]
      rcases le_or_gt #I r with h | h
      · obtain ⟨d, hd⟩ := hD I hIs h
        rw [hd, show k + r - #I - r = k - #I by omega,
          Nat.choose_symm_of_eq_add (show k - #I = k - r + (r - #I) by omega),
          Int.mul_ediv_cancel_left _ (by exact_mod_cast (Nat.choose_pos (by omega)).ne')]
        ring
      · have h0 : cs s r I y = 0 := by
          rw [cs, filter_false_of_mem, sum_empty]
          intro C hC hIC
          have := card_le_card hIC
          rw [(mem_powersetCard.1 hC).2] at this
          omega
        rw [h0, Nat.choose_eq_zero_of_lt (by omega)]
        simp
    · simp_rw [cs, mul_sum]
      rw [sum_comm' (s' := fun C => (C \ A).powerset) (t' := s.powersetCard r)]
      · simp_rw [← sum_mul, sum_powerset_neg_one_pow_card]
        rw [sum_eq_single A]
        · simp
        · intro C hC hne
          rw [if_neg, zero_mul]
          intro h0
          exact hne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.1 h0)
            (by rw [hAc, (mem_powersetCard.1 hC).2]))
        · exact fun h => (h hA).elim
      · intro I C
        simp only [mem_powerset, mem_filter, mem_powersetCard, subset_sdiff]
        constructor
        · rintro ⟨⟨_, hIA⟩, hC, hIC⟩
          exact ⟨⟨hIC, hIA⟩, hC⟩
        · rintro ⟨⟨hIC, hIA⟩, hC⟩
          exact ⟨⟨hIC.trans hC.1, hIA⟩, hC, hIC⟩
  · intro B I
    simp only [mem_powerset, mem_filter, mem_powersetCard, subset_sdiff]
    constructor
    · rintro ⟨⟨⟨hBs, hBc⟩, hAB⟩, hIs, hIB⟩
      exact ⟨⟨⟨⟨hBs, hIB.symm⟩, hBc⟩, hAB⟩, hIs, hIB.mono_right hAB⟩
    · rintro ⟨⟨⟨⟨hBs, hBI⟩, hBc⟩, hAB⟩, hIs, _⟩
      exact ⟨⟨⟨hBs, hBc⟩, hAB⟩, hIs, hBI.symm⟩

theorem wilson (s : Finset α) : ∀ (k r : ℕ) (y : Finset α → ℤ), r ≤ k → k + r ≤ #s →
    (∀ I ⊆ s, #I ≤ r → ((k - #I).choose (r - #I) : ℤ) ∣ cs s r I y) →
    ∃ x : Finset α → ℤ, ∀ A ∈ s.powersetCard r, cs s k A x = y A := by
  induction s using Finset.induction_on with
  | empty =>
    intro k r y hrk hs hD
    exact base ∅ k r hrk (by simp at hs ⊢; omega) y hD
  | insert p s hp ih =>
    intro k r y hrk hs hD
    rcases eq_or_lt_of_le hs with h | h
    · exact base _ k r hrk h.symm y hD
    rw [card_insert_of_notMem hp] at h
    have hps : ∀ B ∈ s.powersetCard k, p ∉ B := fun B hB h' => hp ((mem_powersetCard.1 hB).1 h')
    rcases r with _ | r
    · obtain ⟨B, hB⟩ := powersetCard_nonempty.2 (show k ≤ #(insert p s) by omega)
      refine ⟨fun C => if C = B then y ∅ else 0, fun A hA => ?_⟩
      obtain rfl := card_eq_zero.1 (mem_powersetCard.1 hA).2
      simp [cs, mem_powersetCard.1 hB]
    obtain _ | k := k
    · omega
    have hps : ∀ B ∈ s.powersetCard k, p ∉ B := fun B hB h' => hp ((mem_powersetCard.1 hB).1 h')
    obtain ⟨x1, h1⟩ := ih k r (fun A => y (insert p A)) (by omega) (by omega) fun I hI hc => by
      have hpI : p ∉ I := fun h' => hp (hI h')
      have := hD (insert p I) (insert_subset_insert p hI) (by rw [card_insert_of_notMem hpI]; omega)
      rwa [card_insert_of_notMem hpI, Nat.add_sub_add_right, Nat.add_sub_add_right,
        cs_insert1 hp _ hpI] at this
    obtain ⟨x0, h0⟩ := ih (k + 1) (r + 1) (fun A => y A - cs s k A x1) hrk (by omega)
      fun I hI hc => by
        have hpI : p ∉ I := fun h' => hp (hI h')
        rcases hc.eq_or_lt with e | hc'
        · simp [e]
        have hT := hD I (hI.trans (subset_insert _ _)) hc
        have e1 : cs s r I (fun A => y (insert p A)) = (k - #I).choose (r - #I) * cs s k I x1 := by
          rw [← cs_cs s I r k x1 (by omega)]
          exact cs_congr fun A hA => (h1 A hA).symm
        have e3 : cs s (r + 1) I (fun A => y A - cs s k A x1) =
            cs s (r + 1) I y - cs s (r + 1) I fun A => cs s k A x1 := by
          simp only [cs, sum_sub_distrib]
        rw [cs_insert0 hp _ hpI, e1, show k + 1 - #I = k - #I + 1 by omega,
          show r + 1 - #I = r - #I + 1 by omega, Nat.choose_succ_succ] at hT
        rw [e3, cs_cs s I (r + 1) k x1 hc, show k + 1 - #I = k - #I + 1 by omega,
          show r + 1 - #I = r - #I + 1 by omega, Nat.choose_succ_succ]
        push_cast at hT ⊢
        obtain ⟨d, hd⟩ := hT
        exact ⟨d - cs s k I x1, by linear_combination hd⟩
    refine ⟨fun B => if p ∈ B then x1 (B.erase p) else x0 B, fun A hA => ?_⟩
    obtain ⟨hAs, hAc⟩ := mem_powersetCard.1 hA
    have e2 : ∀ C, cs s k C (fun B => if p ∈ insert p B then x1 ((insert p B).erase p)
        else x0 (insert p B)) = cs s k C x1 := fun C => cs_congr fun B hB => by
      rw [if_pos (mem_insert_self _ _), erase_insert (hps B hB)]
    by_cases hpA : p ∈ A
    · rw [← insert_erase hpA, cs_insert1 hp _ (notMem_erase p A), e2]
      exact h1 _ (mem_powersetCard.2 ⟨fun a ha => (mem_insert.1 (hAs (mem_of_mem_erase ha))).resolve_left
        (ne_of_mem_erase ha), by rw [card_erase_of_mem hpA, hAc]; rfl⟩)
    · rw [cs_insert0 hp _ hpA, e2, cs_congr (g := x0) fun B hB => if_neg fun h' =>
        hp ((mem_powersetCard.1 hB).1 h'),
        h0 A (mem_powersetCard.2 ⟨(subset_insert_iff_of_notMem hpA).1 hAs, hAc⟩)]
      ring

end OMA.W

theorem OMA.solution : OMA.R_Erdos722_erdos_722_R1.H3 := by
  intro n k r hrk hn hdiv U
  obtain ⟨x, hx⟩ := OMA.W.wilson (Finset.univ : Finset (Fin n)) k r (fun _ => 1) hrk
    (by simpa using hn) fun I _ hI => by
      rw [OMA.W.cs, Finset.sum_const, OMA.W.card_sup _ _ _ (Finset.subset_univ _) hI,
        Finset.card_univ, Fintype.card_fin]
      rcases hI.eq_or_lt with e | h
      · simp [e]
      · simpa using Int.natCast_dvd_natCast.2 (hdiv _ h)
  refine ⟨x, fun A hA => ?_⟩
  rw [if_pos hA, ← Finset.sum_filter]
  exact hx A hA
