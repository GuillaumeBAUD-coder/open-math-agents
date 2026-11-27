import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2
import Mathlib.Data.Nat.Choose.Sum

/-!
For Pedro Bessa's Johnson-graph reduction (#2739), center the indicator of a
color class so that its sum vanishes on every star of a codimension-one
face. Counting extensions shows that it vanishes on the star of every
smaller face too. Inclusion-exclusion on one block then determines the
number of blocks of the same color disjoint from it. The bijection on a
codimension-one star also appears in Ian Qvist's extend_colors in PR #3012.
-/

open Finset

namespace OMA.JohnsonDisjoint

variable {V : Type*} [DecidableEq V]

private def starSum (blocks : Finset (Finset V)) (w : Finset V → ℤ) (S : Finset V) : ℤ :=
  ∑ B ∈ blocks, if S ⊆ B then w B else 0

private lemma disjoint_sum (blocks : Finset (Finset V)) (w : Finset V → ℤ) (A : Finset V) :
    (∑ B ∈ blocks, if Disjoint A B then w B else 0) =
      ∑ S ∈ A.powerset, (-1 : ℤ)^S.card * starSum blocks w S := by
  classical
  simp only [starSum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro B _
  have hel (S : Finset V) : (-1 : ℤ)^S.card * (if S ⊆ B then w B else 0) =
      (if S ⊆ B then (-1 : ℤ)^S.card else 0) * w B := by split_ifs <;> simp
  simp_rw [hel]
  rw [← sum_mul, ← sum_filter]
  have he : A.powerset.filter (· ⊆ B) = (A ∩ B).powerset := by
    ext S
    simp only [mem_filter, mem_powerset, subset_inter_iff]
  rw [he, sum_powerset_neg_one_pow_card]
  by_cases hd : Disjoint A B <;> simp [hd, ← disjoint_iff_inter_eq_empty]

variable [Fintype V]

private lemma extension_sum (blocks : Finset (Finset V)) (w : Finset V → ℤ)
    (k : ℕ) (hk : ∀ B ∈ blocks, B.card = k) (S : Finset V) :
    ∑ x ∈ Sᶜ, starSum blocks w (insert x S) =
      ((k - S.card : ℕ) : ℤ) * starSum blocks w S := by
  classical
  unfold starSum
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro B hB
  by_cases hs : S ⊆ B
  · simp only [insert_subset_iff, hs, and_true, if_true, ← sum_filter]
    have he : Sᶜ.filter (· ∈ B) = B \ S := by ext x; simp [and_comm]
    rw [he, sum_const, nsmul_eq_mul, card_sdiff_of_subset hs, hk B hB]
  · simp [insert_subset_iff, hs]

private lemma smaller_stars (blocks : Finset (Finset V)) (w : Finset V → ℤ)
    (k : ℕ) (hk : ∀ B ∈ blocks, B.card = k)
    (top : ∀ T : Finset V, T.card + 1 = k → starSum blocks w T = 0)
    (S : Finset V) (hs : S.card < k) : starSum blocks w S = 0 := by
  induction h : k - S.card using Nat.strong_induction_on generalizing S with
  | h d ih =>
    by_cases htop : S.card + 1 = k
    · exact top S htop
    have he := extension_sum blocks w k hk S
    have hz : (∑ x ∈ Sᶜ, starSum blocks w (insert x S)) = 0 := by
      apply sum_eq_zero
      intro x hx
      have hc := card_insert_of_notMem (mem_compl.mp hx)
      exact ih (k - (insert x S).card) (by omega) _ (by omega) rfl
    rw [hz] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (by exact_mod_cast Nat.ne_of_gt (by omega : 0 < k - S.card))

private lemma facet_sum {p k : ℕ} (hp : k+2=p) (hV : Fintype.card V = 2*k+1)
    (c : Finset V → Fin p) (a : Fin p)
    (proper : ∀ A B : Finset V, A.card = k → B.card = k → (A ∩ B).card+1 = k → c A ≠ c B)
    (T : Finset V) (ht : T.card+1=k) :
    starSum (univ.powersetCard k) (fun B => (if c B = a then (p : ℤ) else 0) - 1) T = 0 := by
  classical
  let F := (univ.powersetCard k).filter (T ⊆ ·)
  have hc : F.card = p := by
    dsimp [F]
    rw [card_filter_powersetCard_subset T univ k (subset_univ _) (by omega), card_univ, hV,
      show k-T.card = 1 by omega, Nat.choose_one_right]
    omega
  have hi : Set.InjOn c (F : Set (Finset V)) := by
    intro A hA B hB he
    obtain ⟨ha, hta⟩ := mem_filter.mp hA
    obtain ⟨hb, htb⟩ := mem_filter.mp hB
    have hka := (mem_powersetCard.mp ha).2
    have hkb := (mem_powersetCard.mp hb).2
    by_contra hne
    have hsmall : (A ∩ B).card < k := by
      rw [← hka]
      apply card_lt_card
      refine ssubset_of_subset_of_ne inter_subset_left ?_
      intro hh
      exact hne (eq_of_subset_of_card_le (inter_eq_left.mp hh) (by omega))
    have hlarge := card_le_card (subset_inter hta htb)
    exact proper A B hka hkb (by omega) he
  have him : F.image c = univ := eq_univ_of_card _ (by rw [card_image_of_injOn hi, hc, Fintype.card_fin])
  unfold starSum
  rw [← sum_filter]
  change (∑ B ∈ F, ((if c B = a then (p : ℤ) else 0) - 1)) = _
  calc
    _ = ∑ g ∈ F.image c, ((if g = a then (p : ℤ) else 0) - 1) := (sum_image hi).symm
    _ = 0 := by rw [him, sum_sub_distrib]; simp

private theorem separated {p k : ℕ} (hp : k+2=p) (hV : Fintype.card V = 2*k+1)
    (ho : Odd k) (c : Finset V → Fin p)
    (proper : ∀ A B : Finset V, A.card = k → B.card = k → (A ∩ B).card+1 = k → c A ≠ c B)
    (A B : Finset V) (hA : A.card = k) (hB : B.card = k) (hd : Disjoint A B) :
    c A ≠ c B := by
  classical
  let blocks := (univ : Finset V).powersetCard k
  let w (U : Finset V) : ℤ := (if c U = c A then (p : ℤ) else 0) - 1
  have hc (U : Finset V) (h : U ∈ blocks) : U.card = k := (mem_powersetCard.mp h).2
  have ha : A ∈ blocks := mem_powersetCard.mpr ⟨subset_univ _, hA⟩
  have htop : starSum blocks w A = w A := by
    unfold starSum
    rw [sum_eq_single A]
    · simp
    · intro U hU hne
      exact if_neg (fun hs => hne (eq_of_subset_of_card_le hs (by rw [hc U hU, hA])).symm)
    · exact fun h => (h ha).elim
  have hdisj := disjoint_sum blocks w A
  rw [sum_eq_single (s := A.powerset) A] at hdisj
  · rw [htop, hA, ho.neg_one_pow] at hdisj
    let avoid := Aᶜ.powersetCard k
    have he : blocks.filter (Disjoint A) = avoid := by
      ext U
      simp only [blocks, avoid, mem_filter, mem_powersetCard, subset_univ, true_and,
        subset_compl_iff_disjoint_left, and_comm]
    have hcount : avoid.card = k+1 := by
      rw [show avoid = Aᶜ.powersetCard k from rfl, card_powersetCard, card_compl, hA, hV,
        show 2*k+1-k=k+1 by omega, Nat.choose_succ_self_right]
    rw [← sum_filter, he] at hdisj
    dsimp only [w] at hdisj
    rw [sum_sub_distrib, ← sum_filter, sum_const, sum_const, nsmul_eq_mul,
      nsmul_eq_mul, hcount, if_pos rfl] at hdisj
    intro hcolor
    have hbmem : B ∈ avoid.filter (fun U => c U = c A) :=
      mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_compl_iff_disjoint_left.mpr hd, hB⟩,
        hcolor.symm⟩
    have hpos : 0 < (avoid.filter fun U => c U = c A).card := card_pos.mpr ⟨B, hbmem⟩
    have hmul : (0 : ℤ) < ((avoid.filter fun U => c U = c A).card : ℤ) * (p : ℤ) :=
      mul_pos (by exact_mod_cast hpos) (by exact_mod_cast (show 0 < p by omega))
    push_cast at hdisj
    omega
  · intro S hs hne
    have hlt : S.card < k := hA ▸ card_lt_card (ssubset_of_subset_of_ne (mem_powerset.mp hs) hne)
    rw [smaller_stars blocks w k hc (facet_sum hp hV c (c A) proper) S hlt, mul_zero]
  · simp

end OMA.JohnsonDisjoint

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H3 := by
  intro p hp h5 c h A B hA hB hd
  have hodd := hp.odd_of_ne_two (by omega)
  have hk : Odd (p-2) := by
    obtain ⟨i, hi⟩ := hodd
    exact ⟨i-1, by omega⟩
  apply OMA.JohnsonDisjoint.separated (k := p-2) (by omega) (by simp; omega) hk c _ A B hA hB hd
  intro U W hu hw he
  exact h U W hu hw (by omega)
