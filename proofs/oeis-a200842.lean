import OMAStatements.S_oeis_a200842

namespace OMA.Solution_oeis_a200842

open OMA.S_oeis_a200842 Finset PowerSeries

private def dpTriple : ℕ → ℕ → (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ)
  | 0, n => (fun v => v, fun _ => 1, fun v => n - v)
  | m + 1, n =>
    let t := dpTriple m n
    (fun v => ∑ u ∈ Finset.range v, (t.2.1 u + t.2.2 u),
     fun v => t.1 v + t.2.1 v + t.2.2 v,
     fun v => ∑ u ∈ Finset.Ico (v + 1) (n + 1), (t.1 u + t.2.1 u))

private def dpUp (m n v : ℕ) : ℕ := (dpTriple m n).1 v
private def dpEq (m n v : ℕ) : ℕ := (dpTriple m n).2.1 v
private def dpDn (m n v : ℕ) : ℕ := (dpTriple m n).2.2 v

private lemma dpUp_zero (n v : ℕ) : dpUp 0 n v = v := rfl
private lemma dpEq_zero (n v : ℕ) : dpEq 0 n v = 1 := rfl
private lemma dpDn_zero (n v : ℕ) : dpDn 0 n v = n - v := rfl

private lemma dpUp_succ (m n v : ℕ) :
    dpUp (m + 1) n v = ∑ u ∈ Finset.range v, (dpEq m n u + dpDn m n u) := rfl

private lemma dpEq_succ (m n v : ℕ) :
    dpEq (m + 1) n v = dpUp m n v + dpEq m n v + dpDn m n v := rfl

private lemma dpDn_succ (m n v : ℕ) :
    dpDn (m + 1) n v = ∑ u ∈ Finset.Ico (v + 1) (n + 1), (dpUp m n u + dpEq m n u) := rfl

private lemma dp_symm (m n : ℕ) :
    ∀ v, v ≤ n → dpDn m n v = dpUp m n (n - v) ∧ dpEq m n v = dpEq m n (n - v) := by
  induction m with
  | zero =>
    intro v _
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro v hv
    have hdn : dpDn (m + 1) n v = dpUp (m + 1) n (n - v) := by
      rw [dpDn_succ, dpUp_succ]
      refine Finset.sum_bij (fun u _ => n - u) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_Ico, Finset.mem_range] at hu ⊢
        omega
      · intro u₁ hu₁ u₂ hu₂ heq
        simp only [Finset.mem_Ico] at hu₁ hu₂
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        refine ⟨n - j, ?_, ?_⟩
        · simp only [Finset.mem_Ico]
          omega
        · omega
      · intro u hu
        simp only [Finset.mem_Ico] at hu
        have h1 := ih (n - u) (by omega)
        have hsub : n - (n - u) = u := by omega
        rw [hsub] at h1
        rw [h1.1, h1.2, add_comm]
    have heq : dpEq (m + 1) n v = dpEq (m + 1) n (n - v) := by
      rw [dpEq_succ, dpEq_succ]
      have h1 := ih v hv
      have h2 := ih (n - v) (by omega)
      have hsub : n - (n - v) = v := by omega
      rw [hsub] at h2
      omega
    exact ⟨hdn, heq⟩

private lemma dpDn_symm (m n v : ℕ) (hv : v ≤ n) : dpDn m n v = dpUp m n (n - v) :=
  (dp_symm m n v hv).1

private def S_up (m n : ℕ) (v : Fin (n + 1)) : Finset (Fin (m + 2) → Fin (n + 1)) :=
  univ.filter fun x => good x ∧ x ⟨m + 1, by omega⟩ = v ∧ x ⟨m, by omega⟩ < v

private def S_eq (m n : ℕ) (v : Fin (n + 1)) : Finset (Fin (m + 2) → Fin (n + 1)) :=
  univ.filter fun x => good x ∧ x ⟨m + 1, by omega⟩ = v ∧ x ⟨m, by omega⟩ = v

private def S_dn (m n : ℕ) (v : Fin (n + 1)) : Finset (Fin (m + 2) → Fin (n + 1)) :=
  univ.filter fun x => good x ∧ x ⟨m + 1, by omega⟩ = v ∧ v < x ⟨m, by omega⟩

private def extend {m n : ℕ} (y : Fin (m + 2) → Fin (n + 1)) (v : Fin (n + 1)) :
    Fin (m + 3) → Fin (n + 1) :=
  fun i => if h : i.val < m + 2 then y ⟨i.val, h⟩ else v

private lemma extend_init_last {m n : ℕ} (x : Fin (m + 3) → Fin (n + 1)) :
    extend (fun i : Fin (m + 2) => x ⟨i.val, by omega⟩) (x ⟨m + 2, by omega⟩) = x := by
  funext i
  simp only [extend]
  split_ifs with h
  · rfl
  · congr 1
    ext
    have hi := i.isLt
    dsimp only
    omega

private lemma good_extend_iff {m n : ℕ} (y : Fin (m + 2) → Fin (n + 1)) (v : Fin (n + 1)) :
    good (extend y v) ↔
      good y ∧
      ¬ (y ⟨m, by omega⟩ < y ⟨m + 1, by omega⟩ ∧ y ⟨m + 1, by omega⟩ < v) ∧
      ¬ (y ⟨m, by omega⟩ > y ⟨m + 1, by omega⟩ ∧ y ⟨m + 1, by omega⟩ > v) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j k hj hk
      have h' := h ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ ⟨k.val, by omega⟩ hj hk
      simpa [extend, i.isLt, j.isLt, k.isLt] using h'
    · have h' := h ⟨m, by omega⟩ ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ rfl rfl
      simpa [extend] using h'.1
    · have h' := h ⟨m, by omega⟩ ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ rfl rfl
      simpa [extend] using h'.2
  · rintro ⟨hy, h1, h2⟩ i j k hj hk
    by_cases hklt : k.val < m + 2
    · have hilt : i.val < m + 2 := by omega
      have hjlt : j.val < m + 2 := by omega
      have h' := hy ⟨i.val, hilt⟩ ⟨j.val, hjlt⟩ ⟨k.val, hklt⟩ hj hk
      simpa [extend, hilt, hjlt, hklt] using h'
    · have hkval : k.val = m + 2 := by omega
      have hjval : j.val = m + 1 := by omega
      have hival : i.val = m := by omega
      have hi : extend y v i = y ⟨m, by omega⟩ := by
        simp only [extend, show i.val < m + 2 by omega, ↓reduceDIte]
        congr 1; ext; exact hival
      have hj' : extend y v j = y ⟨m + 1, by omega⟩ := by
        simp only [extend, show j.val < m + 2 by omega, ↓reduceDIte]
        congr 1; ext; exact hjval
      have hk' : extend y v k = v := by
        simp only [extend, hklt, ↓reduceDIte]
      rw [hi, hj', hk']
      exact ⟨h1, h2⟩

private lemma good_two {n : ℕ} (x : Fin 2 → Fin (n + 1)) : good x := by
  intro i j k hj hk
  omega

private lemma dp_card (m n : ℕ) :
    ∀ v : Fin (n + 1),
      (S_up m n v).card = dpUp m n v.val ∧
      (S_eq m n v).card = dpEq m n v.val ∧
      (S_dn m n v).card = dpDn m n v.val := by
  induction m with
  | zero =>
    intro v
    refine ⟨?_, ?_, ?_⟩
    · rw [dpUp_zero, ← Finset.card_range v.val]
      refine Finset.card_bij (fun x _ => (x ⟨0, by omega⟩).val) ?_ ?_ ?_
      · intro x hx
        simp only [S_up, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hx ⊢
        exact hx.2.2
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [S_up, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext i
        fin_cases i
        · exact Fin.ext heq
        · exact hx₁.2.1.trans hx₂.2.1.symm
      · intro u hu
        simp only [Finset.mem_range] at hu
        refine ⟨fun i => if i.val = 0 then ⟨u, by omega⟩ else v, ?_, ?_⟩
        · simp only [S_up, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨good_two _, rfl, hu⟩
        · rfl
    · rw [dpEq_zero]
      have hcard : S_eq 0 n v = {fun _ => v} := by
        ext x
        simp only [S_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h1, h0⟩
          funext i
          fin_cases i
          · exact h0
          · exact h1
        · rintro rfl
          exact ⟨good_two _, rfl, rfl⟩
      rw [hcard, Finset.card_singleton]
    · rw [dpDn_zero]
      have hico : (Finset.Ico (v.val + 1) (n + 1)).card = n - v.val := by
        rw [Nat.card_Ico]
        omega
      rw [← hico]
      refine Finset.card_bij (fun x _ => (x ⟨0, by omega⟩).val) ?_ ?_ ?_
      · intro x hx
        simp only [S_dn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hx ⊢
        exact ⟨Nat.succ_le_of_lt hx.2.2, (x ⟨0, by omega⟩).isLt⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext i
        fin_cases i
        · exact Fin.ext heq
        · exact hx₁.2.1.trans hx₂.2.1.symm
      · intro u hu
        simp only [Finset.mem_Ico] at hu
        refine ⟨fun i => if i.val = 0 then ⟨u, hu.2⟩ else v, ?_, ?_⟩
        · simp only [S_dn, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨good_two _, rfl, by change v.val < u; omega⟩
        · rfl
  | succ m ih =>
    intro v
    have hdisj_eq_dn : ∀ u : Fin (n + 1), Disjoint (S_eq m n u) (S_dn m n u) := by
      intro u
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      simp only [S_eq, S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      exact (ne_of_gt hy2.2.2) hy1.2.2
    have hdisj_up_eq : ∀ u : Fin (n + 1), Disjoint (S_up m n u) (S_eq m n u) := by
      intro u
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      simp only [S_up, S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      exact (ne_of_lt hy1.2.2) hy2.2.2
    have hdisj_up_dn : ∀ u : Fin (n + 1), Disjoint (S_up m n u) (S_dn m n u) := by
      intro u
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      simp only [S_up, S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      exact lt_asymm hy1.2.2 hy2.2.2
    refine ⟨?_, ?_, ?_⟩
    · -- S_up (m + 1) n v
      let T := (univ.filter fun u : Fin (n + 1) => u < v).biUnion fun u => S_eq m n u ∪ S_dn m n u
      have hcard_eq : (S_up (m + 1) n v).card = T.card := by
        refine Finset.card_bij (fun x _ => fun i : Fin (m + 2) => x ⟨i.val, by omega⟩) ?_ ?_ ?_
        · intro x hx
          simp only [S_up, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          set y : Fin (m + 2) → Fin (n + 1) := fun i => x ⟨i.val, by omega⟩
          have hxext : extend y v = x := by
            simpa [y, hx.2.1] using extend_init_last x
          have hgood : good (extend y v) := hxext.symm ▸ hx.1
          rw [good_extend_iff] at hgood
          simp only [T, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, S_eq, S_dn]
          refine ⟨y ⟨m + 1, by omega⟩, hx.2.2, ?_⟩
          rcases lt_trichotomy (y ⟨m, by omega⟩) (y ⟨m + 1, by omega⟩) with hlt | heq | hgt
          · exfalso
            exact hgood.2.1 ⟨hlt, hx.2.2⟩
          · exact Or.inl ⟨hgood.1, rfl, heq⟩
          · exact Or.inr ⟨hgood.1, rfl, hgt⟩
        · intro x₁ hx₁ x₂ hx₂ heq
          simp only [S_up, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
          have h1 := extend_init_last x₁
          have h2 := extend_init_last x₂
          rw [hx₁.2.1] at h1
          rw [hx₂.2.1] at h2
          rw [← h1, ← h2, heq]
        · intro y hy
          simp only [T, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, S_eq, S_dn] at hy
          rcases hy with ⟨u, huv, hyu⟩
          refine ⟨extend y v, ?_, ?_⟩
          · simp only [S_up, Finset.mem_filter, Finset.mem_univ, true_and]
            have hlast : extend y v ⟨m + 2, by omega⟩ = v := by simp [extend]
            have hprev : extend y v ⟨m + 1, by omega⟩ = y ⟨m + 1, by omega⟩ := by simp [extend]
            rw [hlast, hprev]
            rcases hyu with ⟨hgy, hyu1, hyu2⟩ | ⟨hgy, hyu1, hyu2⟩
            · refine ⟨(good_extend_iff y v).2 ⟨hgy, ?_, ?_⟩, rfl, hyu1.symm ▸ huv⟩
              · rintro ⟨hlt, _⟩; exact (ne_of_lt hlt) (hyu2.trans hyu1.symm)
              · rintro ⟨_, hgt⟩; exact lt_asymm (hyu1.symm ▸ huv) hgt
            · refine ⟨(good_extend_iff y v).2 ⟨hgy, ?_, ?_⟩, rfl, hyu1.symm ▸ huv⟩
              · rintro ⟨hlt, _⟩; exact lt_asymm hlt (hyu1.symm ▸ hyu2)
              · rintro ⟨_, hgt⟩; exact lt_asymm (hyu1.symm ▸ huv) hgt
          · funext i
            simp [extend, i.isLt]
      rw [hcard_eq]
      have hpw : Set.PairwiseDisjoint (↑(univ.filter fun u : Fin (n + 1) => u < v))
          (fun u => S_eq m n u ∪ S_dn m n u) := by
        intro u₁ _ u₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro y hy1 hy2
        simp only [Finset.mem_union, S_eq, S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
        have h1 : y ⟨m + 1, by omega⟩ = u₁ := by rcases hy1 with h | h <;> exact h.2.1
        have h2 : y ⟨m + 1, by omega⟩ = u₂ := by rcases hy2 with h | h <;> exact h.2.1
        exact hne (h1.symm.trans h2)
      rw [Finset.card_biUnion hpw, dpUp_succ]
      refine Finset.sum_bij (fun u _ => u.val) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hu ⊢
        exact hu
      · intro u₁ _ u₂ _ heq
        exact Fin.ext heq
      · intro u hu
        simp only [Finset.mem_range] at hu
        refine ⟨⟨u, by omega⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu
      · intro u _
        rw [Finset.card_union_of_disjoint (hdisj_eq_dn u), (ih u).2.1, (ih u).2.2]
    · -- S_eq (m + 1) n v
      let T := S_up m n v ∪ S_eq m n v ∪ S_dn m n v
      have hcard_eq : (S_eq (m + 1) n v).card = T.card := by
        refine Finset.card_bij (fun x _ => fun i : Fin (m + 2) => x ⟨i.val, by omega⟩) ?_ ?_ ?_
        · intro x hx
          simp only [S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          set y : Fin (m + 2) → Fin (n + 1) := fun i => x ⟨i.val, by omega⟩
          have hxext : extend y v = x := by
            simpa [y, hx.2.1] using extend_init_last x
          have hgood : good (extend y v) := hxext.symm ▸ hx.1
          rw [good_extend_iff] at hgood
          simp only [T, Finset.mem_union, S_up, S_eq, S_dn, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases lt_trichotomy (y ⟨m, by omega⟩) v with hlt | heq | hgt
          · exact Or.inl (Or.inl ⟨hgood.1, hx.2.2, hlt⟩)
          · exact Or.inl (Or.inr ⟨hgood.1, hx.2.2, heq⟩)
          · exact Or.inr ⟨hgood.1, hx.2.2, hgt⟩
        · intro x₁ hx₁ x₂ hx₂ heq
          simp only [S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
          have h1 := extend_init_last x₁
          have h2 := extend_init_last x₂
          rw [hx₁.2.1] at h1
          rw [hx₂.2.1] at h2
          rw [← h1, ← h2, heq]
        · intro y hy
          simp only [T, Finset.mem_union, S_up, S_eq, S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hgy : good y := by rcases hy with (h | h) | h <;> exact h.1
          have hy1 : y ⟨m + 1, by omega⟩ = v := by rcases hy with (h | h) | h <;> exact h.2.1
          refine ⟨extend y v, ?_, ?_⟩
          · simp only [S_eq, Finset.mem_filter, Finset.mem_univ, true_and]
            have hlast : extend y v ⟨m + 2, by omega⟩ = v := by simp [extend]
            have hprev : extend y v ⟨m + 1, by omega⟩ = y ⟨m + 1, by omega⟩ := by simp [extend]
            rw [hlast, hprev, hy1]
            refine ⟨(good_extend_iff y v).2 ⟨hgy, ?_, ?_⟩, rfl, rfl⟩
            · rintro ⟨_, hlt⟩; rw [hy1] at hlt; exact lt_irrefl _ hlt
            · rintro ⟨_, hgt⟩; rw [hy1] at hgt; exact lt_irrefl _ hgt
          · funext i
            simp [extend, i.isLt]
      rw [hcard_eq]
      have hd1 : Disjoint (S_up m n v ∪ S_eq m n v) (S_dn m n v) :=
        Finset.disjoint_union_left.2 ⟨hdisj_up_dn v, hdisj_eq_dn v⟩
      rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint (hdisj_up_eq v),
        dpEq_succ, (ih v).1, (ih v).2.1, (ih v).2.2]
    · -- S_dn (m + 1) n v
      let T := (univ.filter fun u : Fin (n + 1) => v < u).biUnion fun u => S_up m n u ∪ S_eq m n u
      have hcard_eq : (S_dn (m + 1) n v).card = T.card := by
        refine Finset.card_bij (fun x _ => fun i : Fin (m + 2) => x ⟨i.val, by omega⟩) ?_ ?_ ?_
        · intro x hx
          simp only [S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          set y : Fin (m + 2) → Fin (n + 1) := fun i => x ⟨i.val, by omega⟩
          have hxext : extend y v = x := by
            simpa [y, hx.2.1] using extend_init_last x
          have hgood : good (extend y v) := hxext.symm ▸ hx.1
          rw [good_extend_iff] at hgood
          simp only [T, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, S_up, S_eq]
          refine ⟨y ⟨m + 1, by omega⟩, hx.2.2, ?_⟩
          rcases lt_trichotomy (y ⟨m, by omega⟩) (y ⟨m + 1, by omega⟩) with hlt | heq | hgt
          · exact Or.inl ⟨hgood.1, rfl, hlt⟩
          · exact Or.inr ⟨hgood.1, rfl, heq⟩
          · exfalso
            exact hgood.2.2 ⟨hgt, hx.2.2⟩
        · intro x₁ hx₁ x₂ hx₂ heq
          simp only [S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
          have h1 := extend_init_last x₁
          have h2 := extend_init_last x₂
          rw [hx₁.2.1] at h1
          rw [hx₂.2.1] at h2
          rw [← h1, ← h2, heq]
        · intro y hy
          simp only [T, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, S_up, S_eq] at hy
          rcases hy with ⟨u, hvu, hyu⟩
          refine ⟨extend y v, ?_, ?_⟩
          · simp only [S_dn, Finset.mem_filter, Finset.mem_univ, true_and]
            have hlast : extend y v ⟨m + 2, by omega⟩ = v := by simp [extend]
            have hprev : extend y v ⟨m + 1, by omega⟩ = y ⟨m + 1, by omega⟩ := by simp [extend]
            rw [hlast, hprev]
            rcases hyu with ⟨hgy, hyu1, hyu2⟩ | ⟨hgy, hyu1, hyu2⟩
            · refine ⟨(good_extend_iff y v).2 ⟨hgy, ?_, ?_⟩, rfl, hyu1.symm ▸ hvu⟩
              · rintro ⟨_, hlt⟩; exact lt_asymm (hyu1.symm ▸ hvu) hlt
              · rintro ⟨hgt, _⟩; exact lt_asymm (hyu1.symm ▸ hyu2) hgt
            · refine ⟨(good_extend_iff y v).2 ⟨hgy, ?_, ?_⟩, rfl, hyu1.symm ▸ hvu⟩
              · rintro ⟨_, hlt⟩; exact lt_asymm (hyu1.symm ▸ hvu) hlt
              · rintro ⟨hgt, _⟩; exact (ne_of_gt hgt) (hyu2.trans hyu1.symm)
          · funext i
            simp [extend, i.isLt]
      rw [hcard_eq]
      have hpw : Set.PairwiseDisjoint (↑(univ.filter fun u : Fin (n + 1) => v < u))
          (fun u => S_up m n u ∪ S_eq m n u) := by
        intro u₁ _ u₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro y hy1 hy2
        simp only [Finset.mem_union, S_up, S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
        have h1 : y ⟨m + 1, by omega⟩ = u₁ := by rcases hy1 with h | h <;> exact h.2.1
        have h2 : y ⟨m + 1, by omega⟩ = u₂ := by rcases hy2 with h | h <;> exact h.2.1
        exact hne (h1.symm.trans h2)
      rw [Finset.card_biUnion hpw, dpDn_succ]
      refine Finset.sum_bij (fun u _ => u.val) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hu ⊢
        exact ⟨Nat.succ_le_of_lt hu, u.isLt⟩
      · intro u₁ _ u₂ _ heq
        exact Fin.ext heq
      · intro u hu
        simp only [Finset.mem_Ico] at hu
        refine ⟨⟨u, hu.2⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Nat.lt_of_succ_le hu.1
      · intro u _
        rw [Finset.card_union_of_disjoint (hdisj_up_eq u), (ih u).1, (ih u).2.1]

private lemma a_eq_sum_dp (n : ℕ) :
    a n = ∑ v ∈ Finset.range (n + 1), (dpUp 5 n v + dpEq 5 n v + dpDn 5 n v) := by
  unfold a
  have hunion : (univ : Finset (Fin 7 → Fin (n + 1))).filter good =
      (univ : Finset (Fin (n + 1))).biUnion fun v => S_up 5 n v ∪ S_eq 5 n v ∪ S_dn 5 n v := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_union,
      S_up, S_eq, S_dn]
    constructor
    · intro hx
      refine ⟨x ⟨6, by omega⟩, ?_⟩
      rcases lt_trichotomy (x ⟨5, by omega⟩) (x ⟨6, by omega⟩) with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨hx, rfl, hlt⟩)
      · exact Or.inl (Or.inr ⟨hx, rfl, heq⟩)
      · exact Or.inr ⟨hx, rfl, hgt⟩
    · rintro ⟨v, (h | h) | h⟩ <;> exact h.1
  rw [hunion]
  have hpw : Set.PairwiseDisjoint (↑(univ : Finset (Fin (n + 1))))
      (fun v => S_up 5 n v ∪ S_eq 5 n v ∪ S_dn 5 n v) := by
    intro v₁ _ v₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_union, S_up, S_eq, S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    have h1 : x ⟨6, by omega⟩ = v₁ := by rcases hx1 with (h | h) | h <;> exact h.2.1
    have h2 : x ⟨6, by omega⟩ = v₂ := by rcases hx2 with (h | h) | h <;> exact h.2.1
    exact hne (h1.symm.trans h2)
  rw [Finset.card_biUnion hpw]
  refine Finset.sum_bij (fun v _ => v.val) ?_ ?_ ?_ ?_
  · intro v _
    exact Finset.mem_range.2 v.isLt
  · intro v₁ _ v₂ _ heq
    exact Fin.ext heq
  · intro v hv
    exact ⟨⟨v, Finset.mem_range.1 hv⟩, Finset.mem_univ _, rfl⟩
  · intro v _
    have h1 : Disjoint (S_up 5 n v) (S_eq 5 n v) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [S_up, S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      exact (ne_of_lt hx1.2.2) hx2.2.2
    have h2 : Disjoint (S_up 5 n v ∪ S_eq 5 n v) (S_dn 5 n v) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_union, S_up, S_eq, S_dn, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      rcases hx1 with h | h
      · exact lt_asymm h.2.2 hx2.2.2
      · exact (ne_of_gt hx2.2.2) h.2.2
    rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1,
      (dp_card 5 n v).1, (dp_card 5 n v).2.1, (dp_card 5 n v).2.2]

private lemma dpUp_0 (n v : ℕ) (_hv : v ≤ n) :
    (dpUp 0 n v : ℚ) = (v : ℚ) := by
  rw [dpUp_zero]

private lemma dpEq_0 (n v : ℕ) (_hv : v ≤ n) :
    (dpEq 0 n v : ℚ) = 1 := by
  rw [dpEq_zero]; norm_num

private lemma dpUp_1 (n v : ℕ) (hv : v ≤ n) :
    (dpUp 1 n v : ℚ) =
      (1 : ℚ) * (n : ℚ) * (v : ℚ) + (-1 / 2 : ℚ) * (v : ℚ) ^ 2 + (3 / 2 : ℚ) * (v : ℚ) := by
  induction v with
  | zero => rw [dpUp_succ]; simp
  | succ v ih =>
    rw [dpUp_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_add]
    have hprev := ih (by omega)
    rw [dpUp_succ] at hprev
    rw [hprev, dpEq_0 n v (by omega), dpDn_symm 0 n v (by omega), dpUp_0 n (n - v) (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring

private lemma dpEq_1 (n v : ℕ) (hv : v ≤ n) :
    (dpEq 1 n v : ℚ) = (1 : ℚ) * (n : ℚ) + (1 : ℚ) := by
  rw [dpEq_succ, Nat.cast_add, Nat.cast_add]
  rw [dpUp_0 n v hv, dpEq_0 n v hv, dpDn_symm 0 n v hv, dpUp_0 n (n - v) (by omega),
    Nat.cast_sub hv]
  ring

private lemma dpUp_2 (n v : ℕ) (hv : v ≤ n) :
    (dpUp 2 n v : ℚ) =
      (1 / 2 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) + (-1 / 6 : ℚ) * (v : ℚ) ^ 3 +
      (5 / 2 : ℚ) * (n : ℚ) * (v : ℚ) + (-1 / 2 : ℚ) * (v : ℚ) ^ 2 + (5 / 3 : ℚ) * (v : ℚ) := by
  induction v with
  | zero => rw [dpUp_succ]; simp
  | succ v ih =>
    rw [dpUp_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_add]
    have hprev := ih (by omega)
    rw [dpUp_succ] at hprev
    rw [hprev, dpEq_1 n v (by omega), dpDn_symm 1 n v (by omega), dpUp_1 n (n - v) (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring

private lemma dpEq_2 (n v : ℕ) (hv : v ≤ n) :
    (dpEq 2 n v : ℚ) =
      (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) * (v : ℚ) + (-1 : ℚ) * (v : ℚ) ^ 2 +
      (5 / 2 : ℚ) * (n : ℚ) + (1 : ℚ) := by
  rw [dpEq_succ, Nat.cast_add, Nat.cast_add]
  rw [dpUp_1 n v hv, dpEq_1 n v hv, dpDn_symm 1 n v hv, dpUp_1 n (n - v) (by omega),
    Nat.cast_sub hv]
  ring

private lemma dpUp_3 (n v : ℕ) (hv : v ≤ n) :
    (dpUp 3 n v : ℚ) =
      (1 / 3 : ℚ) * (n : ℚ) ^ 3 * (v : ℚ) + (-1 / 6 : ℚ) * (n : ℚ) * (v : ℚ) ^ 3 +
      (1 / 24 : ℚ) * (v : ℚ) ^ 4 + (5 / 2 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) +
      (-7 / 12 : ℚ) * (v : ℚ) ^ 3 + (13 / 3 : ℚ) * (n : ℚ) * (v : ℚ) +
      (-1 / 24 : ℚ) * (v : ℚ) ^ 2 + (19 / 12 : ℚ) * (v : ℚ) := by
  induction v with
  | zero => rw [dpUp_succ]; simp
  | succ v ih =>
    rw [dpUp_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_add]
    have hprev := ih (by omega)
    rw [dpUp_succ] at hprev
    rw [hprev, dpEq_2 n v (by omega), dpDn_symm 2 n v (by omega), dpUp_2 n (n - v) (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring

private lemma dpEq_3 (n v : ℕ) (hv : v ≤ n) :
    (dpEq 3 n v : ℚ) =
      (1 / 3 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) +
      (-1 / 2 : ℚ) * (n : ℚ) * (v : ℚ) ^ 2 + (5 / 2 : ℚ) * (n : ℚ) ^ 2 +
      (2 : ℚ) * (n : ℚ) * (v : ℚ) + (-2 : ℚ) * (v : ℚ) ^ 2 +
      (25 / 6 : ℚ) * (n : ℚ) + (1 : ℚ) := by
  rw [dpEq_succ, Nat.cast_add, Nat.cast_add]
  rw [dpUp_2 n v hv, dpEq_2 n v hv, dpDn_symm 2 n v hv, dpUp_2 n (n - v) (by omega),
    Nat.cast_sub hv]
  ring

private lemma dpUp_4 (n v : ℕ) (hv : v ≤ n) :
    (dpUp 4 n v : ℚ) =
      (5 / 24 : ℚ) * (n : ℚ) ^ 4 * (v : ℚ) + (-1 / 12 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) ^ 3 +
      (1 / 120 : ℚ) * (v : ℚ) ^ 5 + (9 / 4 : ℚ) * (n : ℚ) ^ 3 * (v : ℚ) +
      (-3 / 4 : ℚ) * (n : ℚ) * (v : ℚ) ^ 3 + (1 / 8 : ℚ) * (v : ℚ) ^ 4 +
      (55 / 8 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) + (-23 / 24 : ℚ) * (v : ℚ) ^ 3 +
      (13 / 2 : ℚ) * (n : ℚ) * (v : ℚ) + (3 / 8 : ℚ) * (v : ℚ) ^ 2 +
      (29 / 20 : ℚ) * (v : ℚ) := by
  induction v with
  | zero => rw [dpUp_succ]; simp
  | succ v ih =>
    rw [dpUp_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_add]
    have hprev := ih (by omega)
    rw [dpUp_succ] at hprev
    rw [hprev, dpEq_3 n v (by omega), dpDn_symm 3 n v (by omega), dpUp_3 n (n - v) (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring

private lemma dpEq_4 (n v : ℕ) (hv : v ≤ n) :
    (dpEq 4 n v : ℚ) =
      (5 / 24 : ℚ) * (n : ℚ) ^ 4 + (1 / 3 : ℚ) * (n : ℚ) ^ 3 * (v : ℚ) +
      (-1 / 4 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) ^ 2 + (-1 / 6 : ℚ) * (n : ℚ) * (v : ℚ) ^ 3 +
      (1 / 12 : ℚ) * (v : ℚ) ^ 4 + (9 / 4 : ℚ) * (n : ℚ) ^ 3 +
      (9 / 4 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) + (-9 / 4 : ℚ) * (n : ℚ) * (v : ℚ) ^ 2 +
      (163 / 24 : ℚ) * (n : ℚ) ^ 2 + (25 / 12 : ℚ) * (n : ℚ) * (v : ℚ) +
      (-25 / 12 : ℚ) * (v : ℚ) ^ 2 + (23 / 4 : ℚ) * (n : ℚ) + (1 : ℚ) := by
  rw [dpEq_succ, Nat.cast_add, Nat.cast_add]
  rw [dpUp_3 n v hv, dpEq_3 n v hv, dpDn_symm 3 n v hv, dpUp_3 n (n - v) (by omega),
    Nat.cast_sub hv]
  ring

private lemma dpUp_5 (n v : ℕ) (hv : v ≤ n) :
    (dpUp 5 n v : ℚ) =
      (2 / 15 : ℚ) * (n : ℚ) ^ 5 * (v : ℚ) + (-1 / 18 : ℚ) * (n : ℚ) ^ 3 * (v : ℚ) ^ 3 +
      (1 / 120 : ℚ) * (n : ℚ) * (v : ℚ) ^ 5 + (-1 / 720 : ℚ) * (v : ℚ) ^ 6 +
      (11 / 6 : ℚ) * (n : ℚ) ^ 4 * (v : ℚ) + (-7 / 12 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) ^ 3 +
      (11 / 240 : ℚ) * (v : ℚ) ^ 5 + (74 / 9 : ℚ) * (n : ℚ) ^ 3 * (v : ℚ) +
      (-125 / 72 : ℚ) * (n : ℚ) * (v : ℚ) ^ 3 + (19 / 144 : ℚ) * (v : ℚ) ^ 4 +
      (57 / 4 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) + (-47 / 48 : ℚ) * (v : ℚ) ^ 3 +
      (1607 / 180 : ℚ) * (n : ℚ) * (v : ℚ) + (133 / 360 : ℚ) * (v : ℚ) ^ 2 +
      (43 / 30 : ℚ) * (v : ℚ) := by
  induction v with
  | zero => rw [dpUp_succ]; simp
  | succ v ih =>
    rw [dpUp_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_add]
    have hprev := ih (by omega)
    rw [dpUp_succ] at hprev
    rw [hprev, dpEq_4 n v (by omega), dpDn_symm 4 n v (by omega), dpUp_4 n (n - v) (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring

private lemma dpEq_5 (n v : ℕ) (hv : v ≤ n) :
    (dpEq 5 n v : ℚ) =
      (2 / 15 : ℚ) * (n : ℚ) ^ 5 + (5 / 24 : ℚ) * (n : ℚ) ^ 4 * (v : ℚ) +
      (-1 / 6 : ℚ) * (n : ℚ) ^ 3 * (v : ℚ) ^ 2 + (-1 / 12 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) ^ 3 +
      (1 / 24 : ℚ) * (n : ℚ) * (v : ℚ) ^ 4 + (11 / 6 : ℚ) * (n : ℚ) ^ 4 +
      (25 / 12 : ℚ) * (n : ℚ) ^ 3 * (v : ℚ) + (-7 / 4 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) ^ 2 +
      (-2 / 3 : ℚ) * (n : ℚ) * (v : ℚ) ^ 3 + (1 / 3 : ℚ) * (v : ℚ) ^ 4 +
      (49 / 6 : ℚ) * (n : ℚ) ^ 3 + (41 / 8 : ℚ) * (n : ℚ) ^ 2 * (v : ℚ) +
      (-41 / 8 : ℚ) * (n : ℚ) * (v : ℚ) ^ 2 + (41 / 3 : ℚ) * (n : ℚ) ^ 2 +
      (4 / 3 : ℚ) * (n : ℚ) * (v : ℚ) + (-4 / 3 : ℚ) * (v : ℚ) ^ 2 +
      (36 / 5 : ℚ) * (n : ℚ) + (1 : ℚ) := by
  rw [dpEq_succ, Nat.cast_add, Nat.cast_add]
  rw [dpUp_4 n v hv, dpEq_4 n v hv, dpDn_symm 4 n v hv, dpUp_4 n (n - v) (by omega),
    Nat.cast_sub hv]
  ring

private lemma sum_dp5_partial (n k : ℕ) (hk : k ≤ n + 1) :
    ∑ v ∈ Finset.range k, ((dpUp 5 n v : ℚ) + (dpEq 5 n v : ℚ) + (dpDn 5 n v : ℚ)) =
      (61 / 720 : ℚ) * (n : ℚ) ^ 6 * (k : ℚ) + (1 / 15 : ℚ) * (n : ℚ) ^ 5 * (k : ℚ) ^ 2 +
      (-5 / 144 : ℚ) * (n : ℚ) ^ 4 * (k : ℚ) ^ 3 + (-1 / 72 : ℚ) * (n : ℚ) ^ 3 * (k : ℚ) ^ 4 +
      (1 / 240 : ℚ) * (n : ℚ) ^ 2 * (k : ℚ) ^ 5 + (1 / 720 : ℚ) * (n : ℚ) * (k : ℚ) ^ 6 +
      (-1 / 2520 : ℚ) * (k : ℚ) ^ 7 + (109 / 80 : ℚ) * (n : ℚ) ^ 5 * (k : ℚ) +
      (11 / 12 : ℚ) * (n : ℚ) ^ 4 * (k : ℚ) ^ 2 + (-11 / 24 : ℚ) * (n : ℚ) ^ 3 * (k : ℚ) ^ 3 +
      (-7 / 48 : ℚ) * (n : ℚ) ^ 2 * (k : ℚ) ^ 4 + (1 / 20 : ℚ) * (n : ℚ) * (k : ℚ) ^ 5 +
      (1 / 720 : ℚ) * (k : ℚ) ^ 6 + (545 / 72 : ℚ) * (n : ℚ) ^ 4 * (k : ℚ) +
      (295 / 72 : ℚ) * (n : ℚ) ^ 3 * (k : ℚ) ^ 2 + (-16 / 9 : ℚ) * (n : ℚ) ^ 2 * (k : ℚ) ^ 3 +
      (-31 / 72 : ℚ) * (n : ℚ) * (k : ℚ) ^ 4 + (17 / 144 : ℚ) * (k : ℚ) ^ 5 +
      (285 / 16 : ℚ) * (n : ℚ) ^ 3 * (k : ℚ) + (335 / 48 : ℚ) * (n : ℚ) ^ 2 * (k : ℚ) ^ 2 +
      (-2 : ℚ) * (n : ℚ) * (k : ℚ) ^ 3 + (-43 / 144 : ℚ) * (k : ℚ) ^ 4 +
      (4297 / 240 : ℚ) * (n : ℚ) ^ 2 * (k : ℚ) + (967 / 240 : ℚ) * (n : ℚ) * (k : ℚ) ^ 2 +
      (1 / 720 : ℚ) * (k : ℚ) ^ 3 + (419 / 60 : ℚ) * (n : ℚ) * (k : ℚ) +
      (107 / 360 : ℚ) * (k : ℚ) ^ 2 + (37 / 42 : ℚ) * (k : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega), dpUp_5 n k (by omega), dpEq_5 n k (by omega),
      dpDn_symm 5 n k (by omega), dpUp_5 n (n - k) (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring

private lemma a_formula (n : ℕ) :
    (a n : ℚ) =
      (34 / 315 : ℚ) * (n : ℚ) ^ 7 + (163 / 90 : ℚ) * (n : ℚ) ^ 6 +
      (1981 / 180 : ℚ) * (n : ℚ) ^ 5 + (557 / 18 : ℚ) * (n : ℚ) ^ 4 +
      (7807 / 180 : ℚ) * (n : ℚ) ^ 3 + (1361 / 45 : ℚ) * (n : ℚ) ^ 2 +
      (333 / 35 : ℚ) * (n : ℚ) + 1 := by
  rw [a_eq_sum_dp]
  push_cast
  rw [sum_dp5_partial n (n + 1) le_rfl]
  push_cast
  ring

private lemma a_recurrence_rat (n : ℕ) (hn : 8 < n) :
    (a n : ℚ) =
      8 * (a (n - 1) : ℚ) - 28 * (a (n - 2) : ℚ) + 56 * (a (n - 3) : ℚ) -
      70 * (a (n - 4) : ℚ) + 56 * (a (n - 5) : ℚ) - 28 * (a (n - 6) : ℚ) +
      8 * (a (n - 7) : ℚ) - (a (n - 8) : ℚ) := by
  rw [a_formula n, a_formula (n - 1), a_formula (n - 2), a_formula (n - 3),
    a_formula (n - 4), a_formula (n - 5), a_formula (n - 6), a_formula (n - 7),
    a_formula (n - 8)]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
    Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
    Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

private lemma a_recurrence_int (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) =
      8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  have h := a_recurrence_rat n hn
  exact_mod_cast h

private lemma a_gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (128 + 441 * X + 74 * X ^ 2 - 151 * X ^ 3 + 74 * X ^ 4 - 29 * X ^ 5 + 8 * X ^ 6 - X ^ 7) := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hlhs : A * (1 - X) ^ 8 =
      A - 8 • (X ^ 1 * A) + 28 • (X ^ 2 * A) - 56 • (X ^ 3 * A) + 70 • (X ^ 4 * A) -
      56 • (X ^ 5 * A) + 28 • (X ^ 6 * A) - 8 • (X ^ 7 * A) + X ^ 8 * A := by
    simp only [nsmul_eq_mul]
    ring
  have hrhs :
      (X * (128 + 441 * X + 74 * X ^ 2 - 151 * X ^ 3 + 74 * X ^ 4 - 29 * X ^ 5 + 8 * X ^ 6 - X ^ 7) : PowerSeries ℚ) =
      128 • (X : PowerSeries ℚ) ^ 1 + 441 • X ^ 2 + 74 • X ^ 3 - 151 • X ^ 4 +
      74 • X ^ 5 - 29 • X ^ 6 + 8 • X ^ 7 - X ^ 8 := by
    simp only [nsmul_eq_mul]
    ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow_mul', coeff_X_pow]
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else (a k : ℚ) := fun k => coeff_mk k _
  simp only [nsmul_eq_mul, hc]
  match n with
  | 0 => simp
  | 1 => simp [a_formula]; norm_num
  | 2 => simp [a_formula]; norm_num
  | 3 => simp [a_formula]; norm_num
  | 4 => simp [a_formula]; norm_num
  | 5 => simp [a_formula]; norm_num
  | 6 => simp [a_formula]; norm_num
  | 7 => simp [a_formula]; norm_num
  | 8 => simp [a_formula]; norm_num
  | m + 9 =>
    have hrec := a_recurrence_rat (m + 9) (by omega)
    simp only [show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega, show 3 ≤ m + 9 by omega,
      show 4 ≤ m + 9 by omega, show 5 ≤ m + 9 by omega, show 6 ≤ m + 9 by omega,
      show 7 ≤ m + 9 by omega, show 8 ≤ m + 9 by omega, ↓reduceIte,
      show m + 9 ≠ 0 by omega, show m + 9 ≠ 1 by omega, show m + 9 ≠ 2 by omega,
      show m + 9 ≠ 3 by omega, show m + 9 ≠ 4 by omega, show m + 9 ≠ 5 by omega,
      show m + 9 ≠ 6 by omega, show m + 9 ≠ 7 by omega, show m + 9 ≠ 8 by omega]
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
      show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega,
      show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega,
      show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega] at hrec ⊢
    simp only [show m + 8 ≠ 0 by omega, show m + 7 ≠ 0 by omega, show m + 6 ≠ 0 by omega,
      show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
      show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, ↓reduceIte]
    push_cast
    linarith

end OMA.Solution_oeis_a200842

theorem OMA.solution : type_of% @OMA.S_oeis_a200842.main :=
  ⟨OMA.Solution_oeis_a200842.a_gf, OMA.Solution_oeis_a200842.a_recurrence_int⟩
