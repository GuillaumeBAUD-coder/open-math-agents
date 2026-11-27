import FormalConjectures.ErdosProblems.«805»

-- Problem: Erdős Problem 805 — alon sudakov
-- Credit: @senamakel
-- Proof: the argument of Alon and Sudakov (J. Graph Theory 2007, Theorem 2.2 and the Claim of
-- Section 4): in a graph where every s-set holds an independent t-set, iteratively pick an
-- independent h-set with a large common non-neighbourhood; t - 1 disjoint such independent sets
-- give an s-set with no t-clique.
open Finset SimpleGraph

namespace OMA805

lemma choose_ratio : ∀ (j m s : ℕ), j ≤ s → s ≤ m →
    (m : ℝ) ^ j * ((m - j).choose (s - j) : ℕ) ≤ (s : ℝ) ^ j * (m.choose s : ℕ) := by
  intro j
  induction j with
  | zero => intro m s _ _; simp
  | succ j ih =>
    intro m s hjs hsm
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hid := Nat.add_one_mul_choose_eq m' s'
    have hih := ih m' s' (by omega) (by omega)
    have e1 : m' + 1 - (j + 1) = m' - j := by omega
    have e2 : s' + 1 - (j + 1) = s' - j := by omega
    rw [e1, e2]
    have hidR : ((m' + 1 : ℕ) : ℝ) * (m'.choose s' : ℕ) = ((m' + 1).choose (s' + 1) : ℕ) * ((s' + 1 : ℕ) : ℝ) := by
      exact_mod_cast hid
    push_cast at hidR ⊢
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp at hih ⊢; nlinarith
    have hm' : (0 : ℝ) < m' := by have : 0 < m' := by omega
                                  exact_mod_cast this
    have hcmp : ((s' : ℝ) * (m' + 1)) ^ j ≤ ((s' + 1 : ℝ) * m') ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      have : (s' : ℝ) ≤ m' := by exact_mod_cast (show s' ≤ m' by omega)
      nlinarith
    have hC0 : (0 : ℝ) ≤ ((m' - j).choose (s' - j) : ℕ) := Nat.cast_nonneg _
    have hC1 : (0 : ℝ) ≤ (m'.choose s' : ℕ) := Nat.cast_nonneg _
    have key : ((m' : ℝ) + 1) ^ j * ((m' - j).choose (s' - j) : ℕ) ≤ ((s' : ℝ) + 1) ^ j * (m'.choose s' : ℕ) := by
      have h1 : ((m' : ℝ) + 1) ^ j * (m' : ℝ) ^ j * ((m' - j).choose (s' - j) : ℕ) ≤
          ((m' : ℝ) + 1) ^ j * (s' : ℝ) ^ j * (m'.choose s' : ℕ) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left hih (by positivity)
      have h2 : ((m' : ℝ) + 1) ^ j * (s' : ℝ) ^ j * (m'.choose s' : ℕ) ≤
          ((s' : ℝ) + 1) ^ j * (m' : ℝ) ^ j * (m'.choose s' : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ hC1
        rw [← mul_pow, ← mul_pow, mul_comm ((m' : ℝ) + 1)]; exact hcmp
      have h3 := h1.trans h2
      have hp : (0 : ℝ) < (m' : ℝ) ^ j := by positivity
      nlinarith
    calc ((m' : ℝ) + 1) ^ (j + 1) * ((m' - j).choose (s' - j) : ℕ)
        = ((m' : ℝ) + 1) * (((m' : ℝ) + 1) ^ j * ((m' - j).choose (s' - j) : ℕ)) := by ring
      _ ≤ ((m' : ℝ) + 1) * (((s' : ℝ) + 1) ^ j * (m'.choose s' : ℕ)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = ((s' : ℝ) + 1) ^ j * (((m' : ℝ) + 1) * (m'.choose s' : ℕ)) := by ring
      _ = ((s' : ℝ) + 1) ^ (j + 1) * ((m' + 1).choose (s' + 1) : ℕ) := by rw [hidR]; ring

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma step (s h : ℕ) (hh : 1 ≤ h) (hs : 2 * h ≤ s)
    (hprop : ∀ S : Finset V, #S = s → ∃ I ⊆ S, #I = 2 * h ∧ G.IsIndepSet (I : Set V))
    (W : Finset V) (hW : s ≤ #W) :
    ∃ X ⊆ W, #X = h ∧ G.IsIndepSet (X : Set V) ∧ ∃ W' ⊆ W \ X,
      (∀ x ∈ X, ∀ w ∈ W', ¬ G.Adj x w) ∧ (#W : ℝ) ≤ (s : ℝ) ^ 2 * #W' := by
  classical
  set m := #W with hm
  let 𝓘 : Finset (Finset V) := (W.powersetCard (2 * h)).filter (fun I : Finset V => G.IsIndepSet (↑I : Set V))
  -- (a)
  have ha : m.choose s ≤ #𝓘 * (m - 2 * h).choose (s - 2 * h) := by
    have h1 : ∀ S ∈ W.powersetCard s, 1 ≤ #(𝓘.filter (fun I => I ⊆ S)) := by
      intro S hS
      rw [mem_powersetCard] at hS
      obtain ⟨I, hIS, hI, hind⟩ := hprop S hS.2
      apply card_pos.2
      refine ⟨I, ?_⟩
      simp only [𝓘, mem_filter, mem_powersetCard]
      exact ⟨⟨⟨hIS.trans hS.1, hI⟩, hind⟩, hIS⟩
    have h2 := card_nsmul_le_sum _ _ 1 h1
    rw [card_powersetCard, smul_eq_mul, mul_one] at h2
    have h3 : ∑ S ∈ W.powersetCard s, #(𝓘.filter (fun I => I ⊆ S)) =
        ∑ I ∈ 𝓘, #((W.powersetCard s).filter (fun S => I ⊆ S)) := by
      simp only [card_eq_sum_ones, sum_filter]
      exact sum_comm
    have h4 : ∀ I ∈ 𝓘, #((W.powersetCard s).filter (fun S => I ⊆ S)) =
        (m - 2 * h).choose (s - 2 * h) := by
      intro I hI
      simp only [𝓘, mem_filter, mem_powersetCard] at hI
      rw [card_filter_powersetCard_subset I W s hI.1.1 (by omega), hI.1.2]
    rw [h3, sum_congr rfl h4, sum_const, smul_eq_mul] at h2
    exact h2
  -- (b)
  have hIpos : 0 < #𝓘 := by
    have : 0 < m.choose s := Nat.choose_pos hW
    rcases Nat.eq_zero_or_pos #𝓘 with h0 | h0
    · rw [h0] at ha; omega
    · exact h0
  have hb : ∃ X ∈ W.powersetCard h, #𝓘 ≤ #(𝓘.filter (fun I => X ⊆ I)) * m.choose h := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ X ∈ W.powersetCard h, #(𝓘.filter (fun I => X ⊆ I)) =
        ∑ I ∈ 𝓘, #((W.powersetCard h).filter (fun X => X ⊆ I)) := by
      simp only [card_eq_sum_ones, sum_filter]
      exact sum_comm
    have h2 : ∀ I ∈ 𝓘, #((W.powersetCard h).filter (fun X => X ⊆ I)) = (2 * h).choose h := by
      intro I hI
      simp only [𝓘, mem_filter, mem_powersetCard] at hI
      have : (W.powersetCard h).filter (fun X => X ⊆ I) = I.powersetCard h := by
        ext X; simp only [mem_filter, mem_powersetCard]
        constructor
        · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1.trans hI.1.1, h2⟩, h1⟩
      rw [this, card_powersetCard, hI.1.2]
    rw [sum_congr rfl h2, sum_const, smul_eq_mul] at h1
    have h3 : ∑ X ∈ W.powersetCard h, #(𝓘.filter (fun I => X ⊆ I)) * m.choose h <
        ∑ X ∈ W.powersetCard h, #𝓘 := by
      apply sum_lt_sum_of_nonempty
      · exact powersetCard_nonempty.2 (by omega)
      · exact hcon
    rw [← sum_mul, h1, sum_const, card_powersetCard, smul_eq_mul] at h3
    have h4 : 1 ≤ (2 * h).choose h := Nat.choose_pos (by omega)
    rw [← hm] at h3
    have : #𝓘 * m.choose h ≤ #𝓘 * (2 * h).choose h * m.choose h := by
      apply Nat.mul_le_mul_right; exact Nat.le_mul_of_pos_right _ h4
    rw [mul_comm (m.choose h)] at h3
    omega
  obtain ⟨X, hXW, hXcount⟩ := hb
  rw [mem_powersetCard] at hXW
  let W' := (W \ X).filter (fun w => ∀ x ∈ X, ¬ G.Adj x w)
  have hc : #(𝓘.filter (fun I => X ⊆ I)) ≤ (#W').choose h := by
    rw [← card_powersetCard]
    apply card_le_card_of_injOn (fun I => I \ X)
    · intro I hI
      rw [mem_coe] at hI ⊢
      simp only [𝓘, mem_filter, mem_powersetCard] at hI
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro w hw
        rw [mem_sdiff] at hw
        simp only [W', mem_filter, mem_sdiff]
        refine ⟨⟨hI.1.1.1 hw.1, hw.2⟩, fun x hx hadj => ?_⟩
        exact hI.1.2 (hI.2 hx) hw.1 (fun h => hw.2 (h ▸ hx)) hadj
      · rw [card_sdiff_of_subset hI.2, hI.1.1.2, hXW.2]; omega
    · intro I1 hI1 I2 hI2 heq
      rw [mem_coe, mem_filter] at hI1 hI2
      have e1 : I1 = X ∪ (I1 \ X) := (union_sdiff_of_subset hI1.2).symm
      have e2 : I2 = X ∪ (I2 \ X) := (union_sdiff_of_subset hI2.2).symm
      rw [e1, e2]; simp only at heq; rw [heq]
  have hXind : G.IsIndepSet (X : Set V) := by
    have : 0 < #(𝓘.filter (fun I => X ⊆ I)) := by
      rcases Nat.eq_zero_or_pos #(𝓘.filter (fun I => X ⊆ I)) with h0 | h0
      · rw [h0] at hXcount; omega
      · exact h0
    obtain ⟨I, hI⟩ := card_pos.1 this
    simp only [𝓘, mem_filter] at hI
    exact hI.1.2.mono (by exact_mod_cast hI.2)
  refine ⟨X, hXW.1, hXW.2, hXind, W', filter_subset _ _, fun x hx w hw => ?_, ?_⟩
  · exact (mem_filter.1 hw).2 x hx
  -- (d)
  have hd : (m.choose s : ℝ) ≤ (m : ℝ) ^ h * (#W' : ℝ) ^ h * ((m - 2 * h).choose (s - 2 * h) : ℕ) := by
    have e1 : (m.choose s : ℝ) ≤ (#𝓘 : ℝ) * ((m - 2 * h).choose (s - 2 * h) : ℕ) := by exact_mod_cast ha
    have e2 : (#𝓘 : ℝ) ≤ ((#W').choose h : ℕ) * (m.choose h : ℕ) := by
      have := hXcount.trans (Nat.mul_le_mul_right _ hc)
      exact_mod_cast this
    have e3 : (((#W').choose h : ℕ) : ℝ) ≤ (#W' : ℝ) ^ h := by exact_mod_cast Nat.choose_le_pow _ _
    have e4 : ((m.choose h : ℕ) : ℝ) ≤ (m : ℝ) ^ h := by exact_mod_cast Nat.choose_le_pow _ _
    have hC : (0 : ℝ) ≤ ((m - 2 * h).choose (s - 2 * h) : ℕ) := Nat.cast_nonneg _
    calc (m.choose s : ℝ) ≤ (#𝓘 : ℝ) * ((m - 2 * h).choose (s - 2 * h) : ℕ) := e1
      _ ≤ (((#W').choose h : ℕ) * (m.choose h : ℕ)) * ((m - 2 * h).choose (s - 2 * h) : ℕ) :=
          mul_le_mul_of_nonneg_right e2 hC
      _ ≤ ((#W' : ℝ) ^ h * (m : ℝ) ^ h) * ((m - 2 * h).choose (s - 2 * h) : ℕ) := by
          apply mul_le_mul_of_nonneg_right _ hC
          exact mul_le_mul e3 e4 (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hr := choose_ratio (2 * h) m s hs hW
  have hCpos : (0 : ℝ) < ((m - 2 * h).choose (s - 2 * h) : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h5 : (m : ℝ) ^ (2 * h) ≤ (s : ℝ) ^ (2 * h) * ((m : ℝ) ^ h * (#W' : ℝ) ^ h) := by
    have := hr.trans (mul_le_mul_of_nonneg_left hd (by positivity))
    have h6 : (m : ℝ) ^ (2 * h) * ((m - 2 * h).choose (s - 2 * h) : ℕ) ≤
        ((s : ℝ) ^ (2 * h) * ((m : ℝ) ^ h * (#W' : ℝ) ^ h)) * ((m - 2 * h).choose (s - 2 * h) : ℕ) := by
      linarith [this]
    exact le_of_mul_le_mul_right h6 hCpos
  have h7 : (m : ℝ) ^ h ≤ ((s : ℝ) ^ 2 * #W') ^ h := by
    have hmh : (0 : ℝ) < (m : ℝ) ^ h := by positivity
    rw [mul_pow, ← pow_mul]
    have : (m : ℝ) ^ (2 * h) = (m : ℝ) ^ h * (m : ℝ) ^ h := by rw [two_mul, pow_add]
    rw [this] at h5
    nlinarith
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by omega)).1 h7

lemma iter (s h : ℕ) (hh : 1 ≤ h) (hs : 2 * h ≤ s)
    (hprop : ∀ S : Finset V, #S = s → ∃ I ⊆ S, #I = 2 * h ∧ G.IsIndepSet (I : Set V)) :
    ∀ r : ℕ, ∀ W : Finset V, (s : ℝ) * ((s : ℝ) ^ 2) ^ r ≤ #W →
      ∃ I ⊆ W, r * h ≤ #I ∧ G.IsIndepSet (I : Set V) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  intro r
  induction r with
  | zero => intro W _; exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ r ih =>
    intro W hW
    have hpow : (1 : ℝ) ≤ ((s : ℝ) ^ 2) ^ (r + 1) := one_le_pow₀ (by nlinarith)
    have hWs : s ≤ #W := by
      have : (s : ℝ) ≤ #W := by nlinarith
      exact_mod_cast this
    obtain ⟨X, hXW, hXc, hXind, W', hW'sub, hcross, hWW'⟩ := step G s h hh hs hprop W hWs
    have hW' : (s : ℝ) * ((s : ℝ) ^ 2) ^ r ≤ #W' := by
      have hs2 : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
      have : (s : ℝ) ^ 2 * ((s : ℝ) * ((s : ℝ) ^ 2) ^ r) ≤ (s : ℝ) ^ 2 * #W' := by
        have e : (s : ℝ) ^ 2 * ((s : ℝ) * ((s : ℝ) ^ 2) ^ r) = (s : ℝ) * ((s : ℝ) ^ 2) ^ (r + 1) := by
          rw [pow_succ]; ring
        rw [e]; exact hW.trans hWW'
      exact le_of_mul_le_mul_left this hs2
    obtain ⟨I', hI'W', hI'c, hI'ind⟩ := ih W' hW'
    have hdisj : Disjoint X I' := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have := hW'sub (hI'W' hx')
      exact (mem_sdiff.1 this).2 hx
    refine ⟨X ∪ I', union_subset hXW (hI'W'.trans (hW'sub.trans sdiff_subset)), ?_, ?_⟩
    · rw [card_union_of_disjoint hdisj, hXc]; nlinarith
    · rw [coe_union, SimpleGraph.IsIndepSet, Set.pairwise_union]
      refine ⟨hXind, hI'ind, fun a ha b hb _ => ?_⟩
      have hab := hcross a ha b (hI'W' hb)
      exact ⟨hab, fun h => hab h.symm⟩

lemma comb (s t h r : ℕ) (hh : 1 ≤ h) (hs : 2 * h ≤ s) (ht : 2 * h ≤ t)
    (hcl : ∀ S : Finset V, #S = s → ∃ C ⊆ S, t ≤ #C ∧ G.IsClique (C : Set V))
    (hind : ∀ S : Finset V, #S = s → ∃ I ⊆ S, t ≤ #I ∧ G.IsIndepSet (I : Set V))
    (h1 : s ≤ (t - 1) * (r * h))
    (h2 : (s : ℝ) * ((s : ℝ) ^ 2) ^ r + (((t - 1) * (r * h) : ℕ) : ℝ) ≤ Fintype.card V) : False := by
  classical
  have hprop : ∀ S : Finset V, #S = s → ∃ I ⊆ S, #I = 2 * h ∧ G.IsIndepSet (I : Set V) := by
    intro S hS
    obtain ⟨I, hIS, hIc, hIind⟩ := hind S hS
    obtain ⟨I0, hI0, hI0c⟩ := exists_subset_card_eq (show 2 * h ≤ #I by omega)
    exact ⟨I0, hI0.trans hIS, hI0c, hIind.mono (by exact_mod_cast hI0)⟩
  set f := r * h
  have P : ∀ j, j ≤ t - 1 → ∃ U : Finset V, #U = j * f ∧
      ∀ C ⊆ U, G.IsClique (C : Set V) → #C ≤ j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨∅, by simp, fun C hC _ => ?_⟩
      rw [subset_empty.1 hC]; simp
    | succ j ih =>
      intro hj
      obtain ⟨U, hUc, hUcl⟩ := ih (by omega)
      have hW : (s : ℝ) * ((s : ℝ) ^ 2) ^ r ≤ #Uᶜ := by
        rw [card_compl, Nat.cast_sub (card_le_univ U), hUc]
        have : ((j * f : ℕ) : ℝ) ≤ (((t - 1) * f : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_right _ (by omega)
        linarith
      obtain ⟨I, hIW, hIc, hIind⟩ := iter G s h hh hs hprop r Uᶜ hW
      obtain ⟨I0, hI0, hI0c⟩ := exists_subset_card_eq hIc
      have hdisj : Disjoint U I0 := by
        rw [Finset.disjoint_left]; intro x hx hx'
        exact (mem_compl.1 (hIW (hI0 hx'))) hx
      refine ⟨U ∪ I0, by rw [card_union_of_disjoint hdisj, hUc, hI0c]; ring, ?_⟩
      intro C hC hCcl
      have hA : #(C \ I0) ≤ j := by
        apply hUcl
        · intro x hx
          rw [mem_sdiff] at hx
          rcases mem_union.1 (hC hx.1) with h | h
          · exact h
          · exact absurd h hx.2
        · exact hCcl.subset (by exact_mod_cast sdiff_subset)
      have hB : #(C ∩ I0) ≤ 1 := by
        rw [card_le_one]
        intro a ha b hb
        by_contra hab
        rw [mem_inter] at ha hb
        have h1 := hCcl ha.1 hb.1 hab
        have h2 := (hIind.mono (by exact_mod_cast hI0)) ha.2 hb.2 hab
        exact h2 h1
      have := card_sdiff_add_card_inter C I0
      omega
  obtain ⟨U, hUc, hUcl⟩ := P (t - 1) le_rfl
  obtain ⟨S, hSU, hSc⟩ := exists_subset_card_eq (show s ≤ #U by rw [hUc]; exact h1)
  obtain ⟨C, hCS, hCc, hCcl⟩ := hcl S hSc
  have := hUcl C (hCS.trans hSU) hCcl
  omega

lemma loglog_bounds (L : ℝ) (hL : 1024 ≤ L) : 1 ≤ Real.log L ∧ Real.log L ≤ L / 16 := by
  have hL0 : 0 < L := by linarith
  constructor
  · rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  · have hsq : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
    have h1 : Real.log L = 2 * Real.log (Real.sqrt L) := by
      rw [← Real.log_rpow hsq, Real.rpow_two, Real.sq_sqrt hL0.le]
    have h2 := Real.log_le_sub_one_of_pos hsq
    have h3 : (32 : ℝ) ≤ Real.sqrt L := by
      rw [show (32 : ℝ) = Real.sqrt 1024 by
        rw [show (1024 : ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hL
    have h4 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
    nlinarith

theorem main_asym (n : ℕ) (hn : 1024 ≤ Real.log n) :
    ¬ ∃ G : SimpleGraph (Fin n), ∀ S : Finset (Fin n),
      S.card = ⌊(1 / 64 : ℝ) * Real.log n ^ 3 / Real.log (Real.log n)⌋₊ →
      (∃ C ⊆ S, ⌈Real.log n⌉₊ ≤ C.card ∧ G.IsClique (C : Set (Fin n))) ∧
      (∃ I ⊆ S, ⌈Real.log n⌉₊ ≤ I.card ∧ G.IsIndepSet (I : Set (Fin n))) := by
  classical
  rintro ⟨G, hG⟩
  set L := Real.log n with hLdef
  set ℓ := Real.log L with hℓdef
  obtain ⟨hℓ1, hℓL⟩ := loglog_bounds L hn
  rw [← hℓdef] at hℓ1 hℓL
  have hℓ0 : 0 < ℓ := by linarith
  have h8ℓ : 0 < 8 * ℓ := by linarith
  have hL0 : 0 < L := by linarith
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [hLdef, h] at hn; simp at hn; linarith
    · exact_mod_cast h
  have hnexp : (n : ℝ) = Real.exp L := (Real.exp_log hnpos).symm
  set t := ⌈L⌉₊ with htdef
  set s := ⌊(1 / 64 : ℝ) * L ^ 3 / ℓ⌋₊ with hsdef
  set r := ⌊L / (8 * ℓ)⌋₊ with hrdef
  set h := t / 2 with hhdef
  have ht1 : L ≤ t := Nat.le_ceil L
  have ht2 : (t : ℝ) < L + 1 := Nat.ceil_lt_add_one hL0.le
  have hsA : (1 / 64 : ℝ) * L ^ 3 / ℓ - 1 < s := by
    have := Nat.lt_floor_add_one ((1 / 64 : ℝ) * L ^ 3 / ℓ); rw [← hsdef] at this; linarith
  have hsB : (s : ℝ) ≤ (1 / 64 : ℝ) * L ^ 3 / ℓ := Nat.floor_le (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hL0.le 3)) hℓ0.le)
  have hrA : L / (8 * ℓ) - 1 < r := by
    have := Nat.lt_floor_add_one (L / (8 * ℓ)); rw [← hrdef] at this; linarith
  have hrB : (r : ℝ) ≤ L / (8 * ℓ) := Nat.floor_le (div_nonneg hL0.le h8ℓ.le)
  clear_value h r s t ℓ L
  have hh2 : t ≤ 2 * h + 1 := by omega
  have hh3 : 2 * h ≤ t := by omega
  have hh2R : (t : ℝ) ≤ 2 * h + 1 := by exact_mod_cast hh2
  have hh3R : (2 * h : ℝ) ≤ t := by exact_mod_cast hh3
  have hLℓ : L / (8 * ℓ) ≥ 2 := by
    rw [ge_iff_le, le_div_iff₀ h8ℓ]; linarith
  have hL3 : (1 / 64 : ℝ) * L ^ 3 / ℓ ≥ L ^ 2 / 4 := by
    rw [ge_iff_le, le_div_iff₀ hℓ0]
    have : L ^ 2 / 4 * ℓ ≤ L ^ 2 / 4 * (L / 16) := by
      apply mul_le_mul_of_nonneg_left hℓL; positivity
    nlinarith
  -- conditions
  have hh1 : 1 ≤ h := by
    have : (2 : ℝ) ≤ t := by linarith
    have : 2 ≤ t := by exact_mod_cast this
    omega
  have hs2h : 2 * h ≤ s := by
    have : (2 * h : ℝ) ≤ s := by nlinarith
    exact_mod_cast this
  have ht1' : 1 ≤ t := by omega
  have hcond1 : s ≤ (t - 1) * (r * h) := by
    have hcast : (((t - 1) * (r * h) : ℕ) : ℝ) = ((t : ℝ) - 1) * (r * h) := by
      rw [Nat.cast_mul, Nat.cast_sub ht1', Nat.cast_mul]; simp
    have hhR : ((t : ℝ) - 1) / 2 ≤ h := by linarith
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hA : (L - 1) ^ 2 / 2 ≤ ((t : ℝ) - 1) * h := by
      have : L - 1 ≤ (t : ℝ) - 1 := by linarith
      have h0 : 0 ≤ L - 1 := by linarith
      have hsq : (L - 1) ^ 2 ≤ ((t : ℝ) - 1) ^ 2 := pow_le_pow_left₀ h0 this 2
      have : ((t : ℝ) - 1) * (((t : ℝ) - 1) / 2) ≤ ((t : ℝ) - 1) * h :=
        mul_le_mul_of_nonneg_left hhR (by linarith)
      have e : ((t : ℝ) - 1) ^ 2 / 2 = ((t : ℝ) - 1) * (((t : ℝ) - 1) / 2) := by ring
      linarith
    have hB : (L - 1) ^ 2 / 2 * (L / (8 * ℓ) - 1) ≤ ((t : ℝ) - 1) * h * r := by
      apply mul_le_mul hA hrA.le (by linarith)
      exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have hC : (1 / 64 : ℝ) * L ^ 3 / ℓ ≤ (L - 1) ^ 2 / 2 * (L / (8 * ℓ) - 1) := by
      have e1 : (L - 1) ^ 2 / 2 ≥ L ^ 2 / 4 := by nlinarith [mul_le_mul hn hn (by norm_num) hL0.le]
      have e2 : (L - 1) ^ 2 / 2 * (L / (8 * ℓ) - 1) ≥ L ^ 2 / 4 * (L / (8 * ℓ) - 1) :=
        mul_le_mul_of_nonneg_right e1 (by linarith)
      have e3 : L ^ 2 / 4 * (L / (8 * ℓ) - 1) = 2 * ((1 / 64 : ℝ) * L ^ 3 / ℓ) - L ^ 2 / 4 := by
        field_simp; ring
      linarith
    have : (s : ℝ) ≤ (((t - 1) * (r * h) : ℕ) : ℝ) := by
      rw [hcast]
      have : ((t : ℝ) - 1) * h * r = ((t : ℝ) - 1) * (r * h) := by ring
      linarith
    exact_mod_cast this
  have hcond2 : (s : ℝ) * ((s : ℝ) ^ 2) ^ r + (((t - 1) * (r * h) : ℕ) : ℝ) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, hnexp]
    have hsL : (s : ℝ) ≤ L ^ 3 := by
      have : (1 / 64 : ℝ) * L ^ 3 / ℓ ≤ L ^ 3 := by
        rw [div_le_iff₀ hℓ0]
        have h3 := pow_nonneg hL0.le 3
        have : L ^ 3 * 1 ≤ L ^ 3 * ℓ := mul_le_mul_of_nonneg_left hℓ1 h3
        linarith
      linarith
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have hL3exp : L ^ 3 = Real.exp (3 * ℓ) := by
      rw [show (3 : ℝ) * ℓ = ((3 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hℓdef, Real.exp_log hL0]
    have hpowle : (s : ℝ) * ((s : ℝ) ^ 2) ^ r ≤ Real.exp (((2 * r + 1 : ℕ) : ℝ) * (3 * ℓ)) := by
      rw [Real.exp_nat_mul, ← hL3exp]
      have : (s : ℝ) * ((s : ℝ) ^ 2) ^ r = (s : ℝ) ^ (2 * r + 1) := by ring
      rw [this]
      exact pow_le_pow_left₀ hs0 hsL _
    have hexp1 : ((2 * r + 1 : ℕ) : ℝ) * (3 * ℓ) ≤ 3 * L / 4 + 3 * ℓ := by
      push_cast
      have h8 : (r : ℝ) * (8 * ℓ) ≤ L := (le_div_iff₀ h8ℓ).1 hrB
      have : (2 * (r : ℝ) + 1) * (3 * ℓ) = 6 * ((r : ℝ) * ℓ) + 3 * ℓ := by ring
      rw [this]
      have : (r : ℝ) * (8 * ℓ) = 8 * ((r : ℝ) * ℓ) := by ring
      linarith
    have hprod : (((t - 1) * (r * h) : ℕ) : ℝ) ≤ Real.exp (3 * ℓ) := by
      rw [← hL3exp]
      have hcast : (((t - 1) * (r * h) : ℕ) : ℝ) = ((t : ℝ) - 1) * (r * h) := by
        rw [Nat.cast_mul, Nat.cast_sub ht1', Nat.cast_mul]; simp
      rw [hcast]
      have e1 : (t : ℝ) - 1 ≤ L := by linarith
      have e2 : (r : ℝ) ≤ L := by
        have : L / (8 * ℓ) ≤ L := by
          rw [div_le_iff₀ h8ℓ]; nlinarith
        linarith
      have e3 : (h : ℝ) ≤ L := by linarith
      have : (0:ℝ) ≤ (t : ℝ) - 1 := by linarith
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      calc ((t : ℝ) - 1) * (r * h) ≤ L * (L * L) :=
            mul_le_mul e1 (mul_le_mul e2 e3 hh0 hL0.le) (by positivity) hL0.le
        _ = L ^ 3 := by ring
    have hsum : Real.exp (((2 * r + 1 : ℕ) : ℝ) * (3 * ℓ)) + Real.exp (3 * ℓ) ≤
        2 * Real.exp (3 * L / 4 + 3 * ℓ) := by
      have a1 := Real.exp_le_exp.2 hexp1
      have a2 : Real.exp (3 * ℓ) ≤ Real.exp (3 * L / 4 + 3 * ℓ) := Real.exp_le_exp.2 (by linarith)
      linarith
    have h2e : 2 * Real.exp (3 * L / 4 + 3 * ℓ) ≤ Real.exp L := by
      have : 3 * L / 4 + 3 * ℓ + 1 ≤ L := by linarith
      calc 2 * Real.exp (3 * L / 4 + 3 * ℓ) ≤ Real.exp 1 * Real.exp (3 * L / 4 + 3 * ℓ) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            have := Real.add_one_le_exp 1; linarith
        _ = Real.exp (3 * L / 4 + 3 * ℓ + 1) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp L := Real.exp_le_exp.2 this
    linarith
  exact comb G s t h r hh1 hs2h hh3
    (fun S hS => (hG S hS).1) (fun S hS => (hG S hS).2) hcond1 hcond2

theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ¬ ∃ G : SimpleGraph (Fin n),
    Erdos805.IsLocallyRamsey G ⌊c * Real.log n ^ 3 / Real.log (Real.log n)⌋₊ ⌈Real.log n⌉₊ := by
  refine ⟨1 / 64, by norm_num, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1024 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1024
  filter_upwards [hev] with n hn
  rintro ⟨G, hG⟩
  exact main_asym n hn ⟨G, fun S hS => hG S hS⟩

end OMA805

theorem OMA.solution : type_of% @Erdos805.erdos_805.variants.alon_sudakov := OMA805.solution

