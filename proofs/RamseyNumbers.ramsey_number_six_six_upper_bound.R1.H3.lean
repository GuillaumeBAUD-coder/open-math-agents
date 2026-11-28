import OMAReductions.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1

/-! Proof of Mackey's nonexistence of SRG(165, 82, 40, 41) for R(6,6) R1.H3. -/

open Finset SimpleGraph Matrix

section Helpers

private lemma sum_ne_distinct_triples (n : ℕ) :
    (∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
      if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0) =
      n * (n - 1) * (n - 2) := by
  have h1 : ∀ u : Fin n, (∑ v : Fin n, ∑ w : Fin n,
      if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0) = (n - 1) * (n - 2) := by
    intro u
    have h2 : ∀ v : Fin n, (∑ w : Fin n,
        if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0) =
        if u = v then 0 else n - 2 := by
      intro v
      by_cases huv : u = v
      · subst huv; simp
      · have : (∑ w : Fin n, if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0) =
            ((Finset.univ.erase u).erase v).card := by
          rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
          congr 1; ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
          tauto
        rw [if_neg huv, this, Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩),
          Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
        omega
    simp_rw [h2]
    have hs : (∑ v : Fin n, if u = v then (0 : ℕ) else n - 2) =
        ∑ v : Fin n, (if v ∈ Finset.univ.erase u then 1 else 0) * (n - 2) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : u = v <;> simp [h, Finset.mem_erase, ne_comm]
    rw [hs, ← Finset.sum_mul, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ, Fintype.card_fin]
  simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← mul_assoc]

private lemma srg_params (G : SimpleGraph (Fin 165)) [DecidableRel G.Adj]
    (hdeg : ∀ v, 80 ≤ G.degree v ∧ G.degree v ≤ 84)
    (hred : ∀ u v, G.Adj u v → (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 40)
    (hblue : ∀ u v, Gᶜ.Adj u v → (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card ≤ 40) :
    (∀ u, G.degree u = 82) ∧
    (∀ u v, G.Adj u v → (G.neighborFinset u ∩ G.neighborFinset v).card = 40) ∧
    (∀ u v, Gᶜ.Adj u v → (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card = 40) := by
  let dmono : Fin 165 → Fin 165 → Fin 165 → ℕ := fun u v w =>
    if u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      ((G.Adj u v ∧ G.Adj u w ∧ G.Adj v w) ∨ (¬G.Adj u v ∧ ¬G.Adj u w ∧ ¬G.Adj v w))
    then 1 else 0
  let dmix : Fin 165 → Fin 165 → Fin 165 → ℕ := fun u v w =>
    if u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ ((G.Adj u v ∧ ¬G.Adj u w) ∨ (¬G.Adj u v ∧ G.Adj u w))
    then 1 else 0
  have hpt : ∀ u v w : Fin 165,
      2 * ((if u ≠ v ∧ u ≠ w ∧ v ≠ w then 1 else 0) - dmono u v w) =
      dmix u v w + dmix v w u + dmix w u v := by
    intro u v w
    dsimp [dmono, dmix]
    by_cases h1 : u = v <;> by_cases h2 : u = w <;> by_cases h3 : v = w
    all_goals try (simp [h1, h2, h3]; done)
    have c1 : G.Adj v u ↔ G.Adj u v := G.adj_comm v u
    have c2 : G.Adj w u ↔ G.Adj u w := G.adj_comm w u
    have c3 : G.Adj w v ↔ G.Adj v w := G.adj_comm w v
    by_cases a1 : G.Adj u v <;> by_cases a2 : G.Adj u w <;> by_cases a3 : G.Adj v w <;>
      simp [h1, h2, h3, c1, c2, c3, a1, a2, a3, ne_comm]
  have hmix_sum : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmix u v w) =
      2 * ∑ u : Fin 165, G.degree u * (164 - G.degree u) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hsep : ∀ v w : Fin 165, dmix u v w =
        (if v ≠ u ∧ G.Adj u v ∧ w ≠ u ∧ ¬G.Adj u w ∧ v ≠ w then 1 else 0) +
        (if v ≠ u ∧ ¬G.Adj u v ∧ w ≠ u ∧ G.Adj u w ∧ v ≠ w then 1 else 0) := by
      intro v w; dsimp [dmix]
      by_cases h1 : u = v <;> by_cases h2 : u = w <;> by_cases h3 : v = w <;>
        by_cases a1 : G.Adj u v <;> by_cases a2 : G.Adj u w <;>
        simp [h1, h2, h3, a1, a2, ne_comm]
    simp_rw [hsep, Finset.sum_add_distrib]
    have hs1 : (∑ v : Fin 165, ∑ w : Fin 165,
        if v ≠ u ∧ G.Adj u v ∧ w ≠ u ∧ ¬G.Adj u w ∧ v ≠ w then (1 : ℕ) else 0) =
        G.degree u * (164 - G.degree u) := by
      have hsub : ∀ v w : Fin 165,
          (if v ≠ u ∧ G.Adj u v ∧ w ≠ u ∧ ¬G.Adj u w ∧ v ≠ w then (1 : ℕ) else 0) =
          (if G.Adj u v then 1 else 0) * (if w ≠ u ∧ ¬G.Adj u w then 1 else 0) := by
        intro v w
        by_cases av : G.Adj u v
        · have hvu : v ≠ u := (G.ne_of_adj av).symm
          by_cases hwu : w = u
          · simp [hwu]
          · by_cases aw : G.Adj u w
            · simp [aw]
            · have hvw : v ≠ w := fun h => aw (h ▸ av)
              simp [hvu, av, hwu, aw, hvw]
        · simp [av]
      simp_rw [hsub, ← Finset.mul_sum, ← Finset.sum_mul]
      have hd : (∑ v : Fin 165, if G.Adj u v then (1 : ℕ) else 0) = G.degree u := by
        rw [← G.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1; ext v; simp [mem_neighborFinset]
      have hcd : (∑ w : Fin 165, if w ≠ u ∧ ¬G.Adj u w then (1 : ℕ) else 0) = 164 - G.degree u := by
        have hdc : G.degree u + (Finset.univ.filter fun w : Fin 165 => w ≠ u ∧ ¬G.Adj u w).card = 164 := by
          rw [← G.card_neighborFinset_eq_degree]
          have hdisj : Disjoint (G.neighborFinset u) (Finset.univ.filter fun w : Fin 165 => w ≠ u ∧ ¬G.Adj u w) := by
            rw [Finset.disjoint_left]; intro w h1 h2; simp_all [mem_neighborFinset]
          have hun : G.neighborFinset u ∪ (Finset.univ.filter fun w : Fin 165 => w ≠ u ∧ ¬G.Adj u w) =
              Finset.univ.erase u := by
            ext w; simp only [Finset.mem_union, mem_neighborFinset, Finset.mem_filter, Finset.mem_univ,
              true_and, and_true, Finset.mem_erase, ne_eq]
            constructor
            · rintro (ha | ⟨hne, _⟩)
              · exact (G.ne_of_adj ha).symm
              · exact hne
            · intro hne
              by_cases ha : G.Adj u w
              · exact Or.inl ha
              · exact Or.inr ⟨hne, ha⟩
          rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_erase_of_mem (Finset.mem_univ u),
            Finset.card_univ, Fintype.card_fin]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter] at hdc
        omega
      rw [hd, hcd]
    have hs2 : (∑ v : Fin 165, ∑ w : Fin 165,
        if v ≠ u ∧ ¬G.Adj u v ∧ w ≠ u ∧ G.Adj u w ∧ v ≠ w then (1 : ℕ) else 0) =
        G.degree u * (164 - G.degree u) := by
      rw [Finset.sum_comm]
      have hswap : ∀ w v : Fin 165,
          (if v ≠ u ∧ ¬G.Adj u v ∧ w ≠ u ∧ G.Adj u w ∧ v ≠ w then (1 : ℕ) else 0) =
          (if w ≠ u ∧ G.Adj u w ∧ v ≠ u ∧ ¬G.Adj u v ∧ w ≠ v then (1 : ℕ) else 0) := by
        intro w v
        refine if_congr ?_ rfl rfl
        exact ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h3, h4, h1, h2, h5.symm⟩,
               fun ⟨h3, h4, h1, h2, h5⟩ => ⟨h1, h2, h3, h4, h5.symm⟩⟩
      simp_rw [hswap]
      exact hs1
    rw [hs1, hs2]; omega
  have hmono_sum : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmono u v w) =
      ∑ u : Fin 165, ∑ v ∈ Finset.univ.erase u,
        if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v).card
        else (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card := by
    refine Finset.sum_congr rfl fun u _ => ?_
    have hsep_sum : ∀ v : Fin 165, (∑ w : Fin 165, dmono u v w) =
        if v ∈ Finset.univ.erase u then
          (if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v).card
           else (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card)
        else 0 := by
      intro v
      by_cases huv : u = v
      · subst huv; simp [dmono]
      · have hve : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩
        rw [if_pos hve]
        by_cases av : G.Adj u v
        · have hS : (G.neighborFinset u ∩ G.neighborFinset v).card =
              ∑ w : Fin 165, if w ∈ G.neighborFinset u ∩ G.neighborFinset v then 1 else 0 := by
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_eq_sum_ones]
          rw [if_pos av, hS]
          refine Finset.sum_congr rfl fun w _ => ?_
          dsimp [dmono]
          refine if_congr ?_ rfl rfl
          simp only [Finset.mem_inter, mem_neighborFinset]
          exact ⟨fun ⟨_, huw, hvw, h⟩ => by rcases h with ⟨_, a2, a3⟩ | ⟨n1, _⟩; exact ⟨a2, a3⟩; exact absurd av n1,
                 fun ⟨a2, a3⟩ => ⟨huv, G.ne_of_adj a2, G.ne_of_adj a3, Or.inl ⟨av, a2, a3⟩⟩⟩
        · have hS : (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card =
              ∑ w : Fin 165, if w ∈ Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v then 1 else 0 := by
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_eq_sum_ones]
          rw [if_neg av, hS]
          refine Finset.sum_congr rfl fun w _ => ?_
          dsimp [dmono]
          refine if_congr ?_ rfl rfl
          simp only [Finset.mem_inter, mem_neighborFinset, compl_adj]
          exact ⟨fun ⟨_, huw, hvw, h⟩ => by
                   rcases h with ⟨a1, _⟩ | ⟨_, n2, n3⟩
                   · exact absurd a1 av
                   · exact ⟨⟨huw, n2⟩, ⟨hvw, n3⟩⟩,
                 fun ⟨⟨huw, n2⟩, ⟨hvw, n3⟩⟩ => ⟨huv, huw, hvw, Or.inr ⟨av, n2, n3⟩⟩⟩
    simp_rw [hsep_sum]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have htot : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165,
      (if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0)) = 165 * 164 * 163 := by
    simpa using sum_ne_distinct_triples 165
  have hmono_le : ∀ u v w : Fin 165, dmono u v w ≤ if u ≠ v ∧ u ≠ w ∧ v ≠ w then 1 else 0 := by
    intro u v w; dsimp [dmono]; split_ifs <;> omega
  have hsum_pt : 2 * (165 * 164 * 163 - ∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmono u v w) =
      3 * (2 * ∑ u : Fin 165, G.degree u * (164 - G.degree u)) := by
    have hs := Finset.sum_congr rfl fun u (_ : u ∈ (Finset.univ : Finset (Fin 165))) =>
      Finset.sum_congr rfl fun v (_ : v ∈ (Finset.univ : Finset (Fin 165))) =>
      Finset.sum_congr rfl fun w (_ : w ∈ (Finset.univ : Finset (Fin 165))) => hpt u v w
    simp_rw [← Finset.mul_sum] at hs
    have hdiff : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165,
        ((if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0) - dmono u v w)) =
        165 * 164 * 163 - ∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmono u v w := by
      have hadd : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165,
          ((if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0) - dmono u v w)) +
          (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmono u v w) = 165 * 164 * 163 := by
        simp_rw [← Finset.sum_add_distrib]
        have hpt_add : ∀ u v w : Fin 165,
            ((if u ≠ v ∧ u ≠ w ∧ v ≠ w then (1 : ℕ) else 0) - dmono u v w) + dmono u v w =
            if u ≠ v ∧ u ≠ w ∧ v ≠ w then 1 else 0 := fun u v w => Nat.sub_add_cancel (hmono_le u v w)
        simp_rw [hpt_add, htot]
      omega
    rw [hdiff] at hs
    simp_rw [Finset.sum_add_distrib] at hs
    have hc1 : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmix v w u) =
        ∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmix u v w := by
      conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    have hc2 : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmix w u v) =
        ∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmix u v w := by
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext w; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
    rw [hc1, hc2, hmix_sum] at hs
    omega
  have hf_le : ∀ u : Fin 165, G.degree u * (164 - G.degree u) ≤ 6724 := by
    intro u; have ⟨h1, h2⟩ := hdeg u; interval_cases G.degree u <;> norm_num
  have hb_le : ∀ u : Fin 165, ∀ v ∈ Finset.univ.erase u,
      (if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v).card
        else (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card) ≤ 40 := by
    intro u v hv
    have huv : u ≠ v := (Finset.mem_erase.mp hv).1.symm
    by_cases av : G.Adj u v
    · simp only [av, ↓reduceIte]; exact hred u v av
    · simp only [av, ↓reduceIte]; exact hblue u v ⟨huv, av⟩
  have hM_le : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmono u v w) ≤ 1082400 := by
    rw [hmono_sum]
    calc (∑ u : Fin 165, ∑ v ∈ Finset.univ.erase u,
          if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v).card
          else (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card)
      _ ≤ ∑ _u : Fin 165, ∑ _v ∈ Finset.univ.erase _u, 40 :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v hv => hb_le u v hv
      _ = 1082400 := by
          simp [Finset.card_erase_of_mem (Finset.mem_univ _)]
  have hf_sum_le : (∑ u : Fin 165, G.degree u * (164 - G.degree u)) ≤ 165 * 6724 := by
    calc (∑ u : Fin 165, G.degree u * (164 - G.degree u))
      _ ≤ ∑ _u : Fin 165, 6724 := Finset.sum_le_sum fun u _ => hf_le u
      _ = 165 * 6724 := by simp
  have hf_sum_eq : (∑ u : Fin 165, G.degree u * (164 - G.degree u)) = 165 * 6724 := by omega
  have hM_eq : (∑ u : Fin 165, ∑ v : Fin 165, ∑ w : Fin 165, dmono u v w) = 1082400 := by omega
  have hf_all : ∀ u ∈ (Finset.univ : Finset (Fin 165)),
      G.degree u * (164 - G.degree u) = 6724 :=
    (Finset.sum_eq_sum_iff_of_le (fun u _ => hf_le u)).mp (by simpa using hf_sum_eq)
  have hb_all : ∀ u ∈ (Finset.univ : Finset (Fin 165)),
      (∑ v ∈ Finset.univ.erase u,
        if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v).card
        else (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card) = ∑ _v ∈ Finset.univ.erase u, 40 :=
    (Finset.sum_eq_sum_iff_of_le (fun u _ =>
      Finset.sum_le_sum fun v hv => hb_le u v hv)).mp (by
        rw [← hmono_sum, hM_eq]; simp [Finset.card_erase_of_mem (Finset.mem_univ _)])
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have heq := hf_all u (Finset.mem_univ u)
    have hd := hdeg u
    have hle : G.degree u ≤ 164 := by omega
    have hsq : (G.degree u : ℤ) * (164 - (G.degree u : ℤ)) = 6724 := by
      have hcz : ((G.degree u * (164 - G.degree u) : ℕ) : ℤ) = (6724 : ℤ) := by exact_mod_cast heq
      push_cast [Nat.cast_sub hle] at hcz
      exact hcz
    nlinarith
  · intro u v huv
    have hb := (Finset.sum_eq_sum_iff_of_le (fun w hw => hb_le u w hw)).mp
      (hb_all u (Finset.mem_univ u)) v (Finset.mem_erase.mpr ⟨(G.ne_of_adj huv).symm, Finset.mem_univ v⟩)
    simpa [huv] using hb
  · intro u v huv
    have hb := (Finset.sum_eq_sum_iff_of_le (fun w hw => hb_le u w hw)).mp
      (hb_all u (Finset.mem_univ u)) v (Finset.mem_erase.mpr ⟨huv.1.symm, Finset.mem_univ v⟩)
    have nav : ¬ G.Adj u v := huv.2
    simpa [nav] using hb

private def confMat (G : SimpleGraph (Fin 165)) [DecidableRel G.Adj] :
    Matrix (Option (Fin 165)) (Option (Fin 165)) ℤ
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some u, some v => if u = v then 0 else if G.Adj u v then 1 else -1

private lemma confMat_transpose (G : SimpleGraph (Fin 165)) [DecidableRel G.Adj] :
    (confMat G)ᵀ = confMat G := by
  ext i j
  cases i <;> cases j <;> simp [confMat, SimpleGraph.adj_comm, eq_comm]

private lemma confMat_mul_self (G : SimpleGraph (Fin 165)) [DecidableRel G.Adj]
    (hdeg : ∀ u, G.degree u = 82)
    (hred : ∀ u v, G.Adj u v → (G.neighborFinset u ∩ G.neighborFinset v).card = 40)
    (hblue : ∀ u v, Gᶜ.Adj u v → (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card = 40) :
    confMat G * confMat G = (165 : ℤ) • (1 : Matrix (Option (Fin 165)) (Option (Fin 165)) ℤ) := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_option, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have sum_edge_sgn : ∀ u : Fin 165,
      (∑ w : Fin 165, (if u = w then (0 : ℤ) else if G.Adj u w then 1 else -1)) = 0 := by
    intro u
    have hpt : ∀ w : Fin 165,
        (if u = w then (0 : ℤ) else if G.Adj u w then 1 else -1) =
        2 * (if G.Adj u w then (1 : ℤ) else 0) - if w = u then 0 else 1 := by
      intro w
      by_cases h : u = w
      · subst h; simp
      · have h' : w ≠ u := Ne.symm h
        by_cases a : G.Adj u w <;> simp [h, h', a]
    simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hd : (∑ w : Fin 165, if G.Adj u w then (1 : ℤ) else 0) = 82 := by
      have hnat : (∑ w : Fin 165, if G.Adj u w then (1 : ℕ) else 0) = 82 := by
        rw [← hdeg u, ← G.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1; ext w; simp [mem_neighborFinset]
      exact_mod_cast hnat
    have h1 : (∑ w : Fin 165, if w = u then (0 : ℤ) else 1) = 164 := by
      have hn : (∑ w : Fin 165, if w = u then (0 : ℕ) else 1) = 164 := by
        have hs : (∑ w : Fin 165, if w = u then (0 : ℕ) else 1) =
            ∑ w : Fin 165, if w ∈ Finset.univ.erase u then 1 else 0 := by
          refine Finset.sum_congr rfl fun w _ => ?_
          by_cases h : w = u <;> simp [h, Finset.mem_erase]
        rw [hs, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
      exact_mod_cast hn
    rw [hd, h1]; norm_num
  cases i with
  | none =>
    cases j with
    | none => simp [confMat]
    | some v =>
      simp only [confMat, zero_mul, zero_add, one_mul]
      have hne : (none : Option (Fin 165)) ≠ some v := by simp
      rw [if_neg hne, mul_zero]
      have hsw : (∑ w : Fin 165, (if w = v then (0 : ℤ) else if G.Adj w v then 1 else -1)) =
          ∑ w : Fin 165, (if v = w then (0 : ℤ) else if G.Adj v w then 1 else -1) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [eq_comm, G.adj_comm]
      rw [hsw, sum_edge_sgn v]
  | some u =>
    cases j with
    | none =>
      have hne : (some u : Option (Fin 165)) ≠ none := by simp
      simp only [confMat, mul_zero, zero_add, mul_one, if_neg hne]
      exact sum_edge_sgn u
    | some v =>
      by_cases huv : u = v
      · subst huv
        have hsq : ∀ w : Fin 165,
            confMat G (some u) (some w) * confMat G (some w) (some u) =
            if w = u then 0 else 1 := by
          intro w; dsimp [confMat]
          by_cases h : u = w
          · subst h; simp
          · by_cases a : G.Adj u w <;> simp [h, a, G.adj_comm]
        simp_rw [hsq]
        simp only [confMat, mul_one]
        have hn : (∑ w : Fin 165, if w = u then (0 : ℕ) else 1) = 164 := by
          have hs : (∑ w : Fin 165, if w = u then (0 : ℕ) else 1) =
              ∑ w : Fin 165, if w ∈ Finset.univ.erase u then 1 else 0 := by
            refine Finset.sum_congr rfl fun w _ => ?_
            by_cases h : w = u <;> simp [h, Finset.mem_erase]
          rw [hs, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
        have hz : (∑ w : Fin 165, if w = u then (0 : ℤ) else 1) = 164 := by exact_mod_cast hn
        rw [hz]; norm_num
      · have hne : (some u : Option (Fin 165)) ≠ some v := by simp [huv]
        simp only [if_neg hne, mul_zero, confMat, one_mul]
        have h_sub : ∀ w : Fin 165,
            (if u = w then (0 : ℤ) else if G.Adj u w then 1 else -1) *
            (if w = v then (0 : ℤ) else if G.Adj w v then 1 else -1) =
            4 * (if G.Adj u w ∧ G.Adj v w then (1 : ℤ) else 0)
            - 2 * (if G.Adj u w then (1 : ℤ) else 0)
            - 2 * (if G.Adj v w then (1 : ℤ) else 0)
            + 2 * (if w = v then (if G.Adj u v then (1 : ℤ) else 0) else 0)
            + 2 * (if w = u then (if G.Adj u v then (1 : ℤ) else 0) else 0)
            + (if w = u ∨ w = v then (0 : ℤ) else 1) := by
          intro w
          by_cases hwu : w = u
          · subst w
            by_cases a : G.Adj u v <;> simp [huv, G.adj_comm]
          · by_cases hwv : w = v
            · subst w
              by_cases a : G.Adj u v <;> simp [Ne.symm huv]
            · by_cases a1 : G.Adj u w <;> by_cases a2 : G.Adj v w <;>
                simp [hwu, hwv, Ne.symm hwu, a1, a2, G.adj_comm]
        simp_rw [h_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hd_u : (∑ w : Fin 165, if G.Adj u w then (1 : ℤ) else 0) = 82 := by
          exact_mod_cast (by
            rw [← hdeg u, ← G.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
            congr 1; ext w; simp [mem_neighborFinset] :
            (∑ w : Fin 165, if G.Adj u w then (1 : ℕ) else 0) = 82)
        have hd_v : (∑ w : Fin 165, if G.Adj v w then (1 : ℤ) else 0) = 82 := by
          exact_mod_cast (by
            rw [← hdeg v, ← G.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
            congr 1; ext w; simp [mem_neighborFinset] :
            (∑ w : Fin 165, if G.Adj v w then (1 : ℕ) else 0) = 82)
        have hv_pt : (∑ w : Fin 165, if w = v then (if G.Adj u v then (1 : ℤ) else 0) else 0) =
            if G.Adj u v then 1 else 0 := by
          simp [Finset.sum_ite_eq']
        have hu_pt : (∑ w : Fin 165, if w = u then (if G.Adj u v then (1 : ℤ) else 0) else 0) =
            if G.Adj u v then 1 else 0 := by
          simp [Finset.sum_ite_eq']
        have h_163 : (∑ w : Fin 165, if w = u ∨ w = v then (0 : ℤ) else 1) = 163 := by
          have hn : (∑ w : Fin 165, if w = u ∨ w = v then (0 : ℕ) else 1) = 163 := by
            have hs : (∑ w : Fin 165, if w = u ∨ w = v then (0 : ℕ) else 1) =
                ∑ w : Fin 165, if w ∈ (Finset.univ.erase u).erase v then 1 else 0 := by
              refine Finset.sum_congr rfl fun w _ => ?_
              by_cases hwu : w = u <;> by_cases hwv : w = v <;> simp [hwu, hwv, Finset.mem_erase]
            rw [hs, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
              Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem,
              Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
            exact Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩
          exact_mod_cast hn
        have h_both : (∑ w : Fin 165, if G.Adj u w ∧ G.Adj v w then (1 : ℤ) else 0) =
            ((G.neighborFinset u ∩ G.neighborFinset v).card : ℤ) := by
          exact_mod_cast (by
            rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
            congr 1; ext w; simp [mem_neighborFinset] :
            (∑ w : Fin 165, if G.Adj u w ∧ G.Adj v w then (1 : ℕ) else 0) =
            (G.neighborFinset u ∩ G.neighborFinset v).card)
        have h_both_val : (G.neighborFinset u ∩ G.neighborFinset v).card = if G.Adj u v then 40 else 41 := by
          by_cases av : G.Adj u v
          · simp [av, hred u v av]
          · rw [if_neg av]
            have hnb := hblue u v ⟨huv, av⟩
            have h_neither : (∑ w : Fin 165, if ¬ G.Adj u w ∧ ¬ G.Adj v w ∧ w ≠ u ∧ w ≠ v then (1 : ℕ) else 0) = 40 := by
              rw [← hnb, Finset.card_eq_sum_ones, ← Finset.sum_filter]
              congr 1; ext w
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, mem_neighborFinset, compl_adj]
              exact ⟨fun ⟨n1, n2, h1, h2⟩ => ⟨⟨h1.symm, n1⟩, ⟨h2.symm, n2⟩⟩,
                     fun ⟨⟨h1, n1⟩, ⟨h2, n2⟩⟩ => ⟨n1, n2, h1.symm, h2.symm⟩⟩
            have h_pt3 : ∀ w : Fin 165,
                (if ¬ G.Adj u w ∧ ¬ G.Adj v w ∧ w ≠ u ∧ w ≠ v then (1 : ℤ) else 0) =
                (if w = u ∨ w = v then (0 : ℤ) else 1)
                - (if G.Adj u w then 1 else 0) - (if G.Adj v w then 1 else 0)
                + (if G.Adj u w ∧ G.Adj v w then 1 else 0) := by
              intro w
              by_cases hwu : w = u <;> by_cases hwv : w = v
              · subst hwu; exact absurd hwv huv
              · subst w
                have nav' : ¬ G.Adj v u := fun h => av ((G.adj_comm v u).mp h)
                simp [huv, nav']
              · subst w; simp [Ne.symm huv]; exact av
              · by_cases a1 : G.Adj u w <;> by_cases a2 : G.Adj v w <;> simp [hwu, hwv, a1, a2]
            have hz : (∑ w : Fin 165, if ¬ G.Adj u w ∧ ¬ G.Adj v w ∧ w ≠ u ∧ w ≠ v then (1 : ℤ) else 0) = 40 := by
              exact_mod_cast h_neither
            simp_rw [h_pt3, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hz
            rw [h_163, hd_u, hd_v, h_both] at hz
            omega
        rw [hd_u, hd_v, hv_pt, hu_pt, h_163, h_both, h_both_val]
        by_cases av : G.Adj u v <;> simp [av]

private lemma det_ne_zero_of_linearIndependent_cols {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 3))
    (hli : LinearIndependent (ZMod 3) Mᵀ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hsum : (∑ j : Fin n, v j • Mᵀ j) = 0 := by
    ext i
    have hi := congr_fun hMv i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hi
  exact hv0 (funext (Fintype.linearIndependent_iff.mp hli v hsum))

private lemma prime_dvd_right_of_dvd_mul_pow {p : ℤ} (hp : Prime p) {a b : ℤ} (hpa : ¬ p ∣ a) :
    ∀ k : ℕ, p ^ k ∣ a * b → p ^ k ∣ b := by
  intro k
  induction k generalizing b with
  | zero => intro _; simp
  | succ k ih =>
    intro ⟨m, hm⟩
    have h1 : p ∣ a * b := ⟨p ^ k * m, by rw [hm, pow_succ']; ring⟩
    have hpb : p ∣ b := (hp.dvd_mul.mp h1).resolve_left hpa
    rcases hpb with ⟨b', rfl⟩
    have h2 : p ^ k ∣ a * b' := ⟨m, by
      have hmul : p * (a * b') = p * (p ^ k * m) := by
        calc p * (a * b') = a * (p * b') := by ring
          _ = p ^ (k + 1) * m := hm
          _ = p * (p ^ k * m) := by rw [pow_succ']; ring
      exact mul_left_cancel₀ hp.ne_zero hmul⟩
    rcases ih h2 with ⟨q, hq⟩
    exact ⟨q, by rw [hq, pow_succ']; ring⟩

private lemma rank_ge_83_of_sq_165 (C : Matrix (Fin 166) (Fin 166) ℤ)
    (hC : C * C = (165 : ℤ) • (1 : Matrix (Fin 166) (Fin 166) ℤ)) :
    Module.finrank (ZMod 3)
      (LinearMap.ker (C.map (Int.castRingHom (ZMod 3))).mulVecLin) ≤ 83 := by
  by_contra hlt
  have h84 : 84 ≤ Module.finrank (ZMod 3)
      (LinearMap.ker (C.map (Int.castRingHom (ZMod 3))).mulVecLin) := by omega
  let Cb : Matrix (Fin 166) (Fin 166) (ZMod 3) := C.map (Int.castRingHom (ZMod 3))
  let K : Submodule (ZMod 3) (Fin 166 → ZMod 3) := LinearMap.ker Cb.mulVecLin
  obtain ⟨U, hKU⟩ := Submodule.exists_isCompl K
  let k := Module.finrank (ZMod 3) K
  let u := Module.finrank (ZMod 3) U
  have hku : k + u = 166 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hKU
    rw [Module.finrank_fin_fun] at h1
    exact h1
  let eIdx : Fin k ⊕ Fin u ≃ Fin 166 := finSumFinEquiv.trans (finCongr hku)
  let bK := Module.finBasis (ZMod 3) K
  let bU := Module.finBasis (ZMod 3) U
  let bFull : Module.Basis (Fin 166) (ZMod 3) (Fin 166 → ZMod 3) :=
    (((bK.prod bU).map (Submodule.prodEquivOfIsCompl K U hKU)).reindex eIdx)
  let Pb : Matrix (Fin 166) (Fin 166) (ZMod 3) := fun i j => bFull j i
  have hPb_det : Pb.det ≠ 0 := by
    refine det_ne_zero_of_linearIndependent_cols Pb ?_
    change LinearIndependent (ZMod 3) fun j i => bFull j i
    exact bFull.linearIndependent
  have hCbPb : ∀ (i j : Fin 166), j.val < 84 → (Cb * Pb) i j = 0 := by
    intro i j hj
    let jK : Fin k := ⟨j.val, Nat.lt_of_lt_of_le hj h84⟩
    have he : eIdx (Sum.inl jK) = j := by
      ext; simp [eIdx, finSumFinEquiv_apply_left, finCongr_apply, jK]
    have hsymm : eIdx.symm j = Sum.inl jK := eIdx.symm_apply_eq.mpr he.symm
    have hbK : bFull j = (bK jK : Fin 166 → ZMod 3) := by
      simp only [bFull, Module.Basis.coe_reindex, Function.comp_apply, Module.Basis.map_apply,
        hsymm, Module.Basis.prod_apply, Sum.elim_inl, LinearMap.inl_apply]
      change K.subtype (bK jK) + U.subtype 0 = (bK jK : Fin 166 → ZMod 3)
      simp
    have hker_j : Cb.mulVec (bFull j) = 0 := by
      rw [hbK]
      exact (bK jK).2
    calc (Cb * Pb) i j = ∑ x : Fin 166, Cb i x * Pb x j := by rw [Matrix.mul_apply]
      _ = (Cb.mulVec (bFull j)) i := rfl
      _ = 0 := congr_fun hker_j i
  let P : Matrix (Fin 166) (Fin 166) ℤ := fun i j => ((Pb i j).val : ℤ)
  have hP_map : P.map (Int.castRingHom (ZMod 3)) = Pb := by
    ext i j
    change (((Pb i j).val : ℤ) : ZMod 3) = Pb i j
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h3ndvdP : ¬ ((3 : ℤ) ∣ P.det) := by
    intro h
    have hz : ((P.det : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd P.det 3).mpr h
    have hdet : ((P.det : ℤ) : ZMod 3) = Pb.det := by
      change (Int.castRingHom (ZMod 3)) P.det = Pb.det
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hP_map]
    exact hPb_det (hdet ▸ hz)
  have hdvd : ∀ (i j : Fin 166), j.val < 84 → (3 : ℤ) ∣ (C * P) i j := by
    intro i j hj
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((C * P) i j) 3).mp ?_
    have hmod : (((C * P) i j : ℤ) : ZMod 3) = (Cb * Pb) i j := by
      calc (((C * P) i j : ℤ) : ZMod 3)
          = ((∑ x, C i x * P x j : ℤ) : ZMod 3) := by rw [Matrix.mul_apply]
        _ = ∑ x, ((C i x : ℤ) : ZMod 3) * ((P x j : ℤ) : ZMod 3) := by simp
        _ = ∑ x, Cb i x * Pb x j := by
              refine Finset.sum_congr rfl fun x _ => ?_
              have hx : ((P x j : ℤ) : ZMod 3) = Pb x j := by
                change (((Pb x j).val : ℤ) : ZMod 3) = Pb x j
                rw [Int.cast_natCast, ZMod.natCast_zmod_val]
              rw [hx]; rfl
        _ = (Cb * Pb) i j := by rw [Matrix.mul_apply]
    rw [hmod, hCbPb i j hj]
  let M : Matrix (Fin 166) (Fin 166) ℤ := fun i j =>
    if j.val < 84 then (C * P) i j / 3 else (C * P) i j
  let d : Fin 166 → ℤ := fun j => if j.val < 84 then 3 else 1
  let D : Matrix (Fin 166) (Fin 166) ℤ := Matrix.diagonal d
  have hCPM : C * P = M * D := by
    ext i j
    dsimp only [D]
    rw [Matrix.mul_diagonal]
    by_cases hj : j.val < 84
    · simpa [M, d, hj] using (Int.ediv_mul_cancel (hdvd i j hj)).symm
    · simp [M, d, hj]
  have hDdet : D.det = (3 : ℤ) ^ 84 := by
    dsimp only [D]
    rw [Matrix.det_diagonal]
    have hcard : (Finset.univ.filter fun j : Fin 166 => j.val < 84).card = 84 := by decide
    simp only [d, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, hcard]
  have hdet_dvd : (3 : ℤ) ^ 84 ∣ P.det * C.det := by
    refine ⟨M.det, ?_⟩
    calc P.det * C.det = (C * P).det := by rw [Matrix.det_mul, mul_comm]
      _ = (M * D).det := by rw [hCPM]
      _ = (3 : ℤ) ^ 84 * M.det := by rw [Matrix.det_mul, hDdet, mul_comm]
  have h3_C : (3 : ℤ) ^ 84 ∣ C.det :=
    prime_dvd_right_of_dvd_mul_pow Int.prime_three h3ndvdP 84 hdet_dvd
  have hCdet_sq : C.det * C.det = (165 : ℤ) ^ 166 := by
    rw [← Matrix.det_mul, hC, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have h3_168 : (3 : ℤ) ^ 168 ∣ (165 : ℤ) ^ 166 := by
    rw [← hCdet_sq]
    have h84sq : (3 : ℤ) ^ 168 = (3 : ℤ) ^ 84 * (3 : ℤ) ^ 84 := by norm_num
    rw [h84sq]
    exact mul_dvd_mul h3_C h3_C
  have h165 : (165 : ℤ) ^ 166 = (3 : ℤ) ^ 166 * (55 : ℤ) ^ 166 := by
    rw [← mul_pow]; norm_num
  rw [h165] at h3_168
  have h3_55 : (3 : ℤ) ^ 2 ∣ (55 : ℤ) ^ 166 := by
    rcases h3_168 with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have h168 : (3 : ℤ) ^ 168 = (3 : ℤ) ^ 166 * (3 : ℤ) ^ 2 := by norm_num
    rw [h168, mul_assoc] at hq
    exact mul_left_cancel₀ (by norm_num) hq
  have h3_dvd : (3 : ℤ) ∣ 55 := Int.prime_three.dvd_of_dvd_pow (dvd_trans ⟨3, by norm_num⟩ h3_55)
  omega

private lemma no_isotropic_83 (Cb : Matrix (Fin 166) (Fin 166) (ZMod 3))
    (hsym : Cbᵀ = Cb) (hsq : Cb * Cb = 0)
    (hker : Module.finrank (ZMod 3) (LinearMap.ker Cb.mulVecLin) ≤ 83) : False := by
  let K : Submodule (ZMod 3) (Fin 166 → ZMod 3) := LinearMap.ker Cb.mulVecLin
  let R : Submodule (ZMod 3) (Fin 166 → ZMod 3) := LinearMap.range Cb.mulVecLin
  have hRK : R ≤ K := by
    rintro x ⟨u, rfl⟩
    change Cb.mulVec (Cb.mulVec u) = 0
    rw [Matrix.mulVec_mulVec, hsq, Matrix.zero_mulVec]
  have hrk : Module.finrank (ZMod 3) R + Module.finrank (ZMod 3) K = 166 := by
    have h := LinearMap.finrank_range_add_finrank_ker Cb.mulVecLin
    rw [Module.finrank_fin_fun] at h
    exact h
  have hr_le_k : Module.finrank (ZMod 3) R ≤ Module.finrank (ZMod 3) K := Submodule.finrank_mono hRK
  have hk_le : Module.finrank (ZMod 3) K ≤ 83 := hker
  have hk : Module.finrank (ZMod 3) K = 83 := by omega
  have hReqK : R = K := Submodule.eq_of_le_of_finrank_eq hRK (by omega)
  have hiso : ∀ x y : Fin 166 → ZMod 3, x ∈ K → y ∈ K → x ⬝ᵥ y = 0 := by
    intro x y hx hy
    have hxR : x ∈ R := hReqK ▸ hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hxR
    have hy0 : Cb.mulVec y = 0 := hy
    calc Cb.mulVecLin u ⬝ᵥ y = y ⬝ᵥ Cb.mulVec u := by rw [Matrix.mulVecLin_apply, dotProduct_comm]
      _ = Matrix.vecMul y Cb ⬝ᵥ u := Matrix.dotProduct_mulVec y Cb u
      _ = Matrix.vecMul y Cbᵀ ⬝ᵥ u := by rw [hsym]
      _ = Cb.mulVec y ⬝ᵥ u := by rw [Matrix.vecMul_transpose]
      _ = 0 := by rw [hy0, zero_dotProduct]
  let b : Module.Basis (Fin 83) (ZMod 3) K := (Module.finBasis (ZMod 3) K).reindex (finCongr hk)
  let B : Matrix (Fin 83) (Fin 166) (ZMod 3) := fun r j => (b r : Fin 166 → ZMod 3) j
  have hBB : B * Bᵀ = 0 := by
    ext r s
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact hiso (b r : Fin 166 → ZMod 3) (b s : Fin 166 → ZMod 3) (b r).2 (b s).2
  have hspan : Submodule.span (ZMod 3) (Set.range Bᵀ) = ⊤ := by
    by_contra hlt
    have hlt' : Submodule.span (ZMod 3) (Set.range Bᵀ) < ⊤ := lt_top_iff_ne_top.mpr hlt
    obtain ⟨φ, hφ0, hφker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt'
    let a : Fin 83 → ZMod 3 := fun r => φ (Pi.single r 1)
    have hsum_zero : (∑ r : Fin 83, a r • (b r : Fin 166 → ZMod 3)) = 0 := by
      ext j
      have hj : Bᵀ j ∈ φ.ker := hφker (Submodule.subset_span ⟨j, rfl⟩)
      have hcol : Bᵀ j = ∑ r : Fin 83, (b r : Fin 166 → ZMod 3) j • Pi.single r (1 : ZMod 3) := by
        ext r; simp [Pi.single_apply]; rfl
      rw [LinearMap.mem_ker, hcol, map_sum] at hj
      simpa [a, map_smul, smul_eq_mul, mul_comm] using hj
    have hsumK : (∑ r : Fin 83, a r • b r) = 0 :=
      Subtype.ext (by simpa [Submodule.coe_sum, Submodule.coe_smul] using hsum_zero)
    have ha0 : ∀ r : Fin 83, a r = 0 := Fintype.linearIndependent_iff.mp b.linearIndependent a hsumK
    apply hφ0
    refine LinearMap.ext fun x => ?_
    have hx : x = ∑ r : Fin 83, x r • Pi.single r (1 : ZMod 3) := by
      ext j; simp [Pi.single_apply]
    rw [hx, map_sum]
    simp [a, ha0, map_smul]
  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent (ZMod 3) (Set.range Bᵀ)
  have : Fintype t := Set.Finite.fintype ((Set.finite_range Bᵀ).subset ht_sub)
  let bT : Module.Basis t (ZMod 3) (Fin 83 → ZMod 3) :=
    Module.Basis.mk ht_li (by rw [Subtype.range_coe, ht_span, hspan])
  have ht_card : Fintype.card t = 83 := by
    have h1 := Module.finrank_eq_card_basis bT
    rw [Module.finrank_fin_fun] at h1
    exact h1.symm
  let idx : t → Fin 166 := fun x => Classical.choose (ht_sub x.2)
  have hidx_spec : ∀ x : t, Bᵀ (idx x) = x.1 := fun x => Classical.choose_spec (ht_sub x.2)
  have hidx_inj : Function.Injective idx := by
    intro x y hxy
    apply Subtype.ext
    rw [← hidx_spec x, ← hidx_spec y, hxy]
  let S : Finset (Fin 166) := Finset.univ.image idx
  have hS_card : S.card = 83 := by
    rw [Finset.card_image_of_injective _ hidx_inj, Finset.card_univ, ht_card]
  have hSc_card : Fintype.card ↥(Sᶜ) = 83 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hS_card]
  let e_t : Fin 83 ≃ t := (Fintype.equivFinOfCardEq ht_card).symm
  let e2 : Fin 83 ≃ ↥(Sᶜ) := (Fintype.equivFinOfCardEq hSc_card).symm
  let B1 : Matrix (Fin 83) (Fin 83) (ZMod 3) := fun r k => B r (idx (e_t k))
  let B2 : Matrix (Fin 83) (Fin 83) (ZMod 3) := fun r k => B r (e2 k).1
  have hB12 : B1 * B1ᵀ = (-1 : ZMod 3) • (B2 * B2ᵀ) := by
    ext r s
    have h0 := congr_fun (congr_fun hBB r) s
    rw [Matrix.mul_apply, Matrix.zero_apply, ← Finset.sum_add_sum_compl S] at h0
    have hs1 : (∑ j ∈ S, B r j * Bᵀ j s) = (B1 * B1ᵀ) r s := by
      rw [Finset.sum_image (fun x _ y _ h => hidx_inj h), Matrix.mul_apply]
      symm
      exact Fintype.sum_equiv e_t _ _ fun _ => rfl
    have hs2 : (∑ j ∈ Sᶜ, B r j * Bᵀ j s) = (B2 * B2ᵀ) r s := by
      rw [← Finset.sum_coe_sort Sᶜ, Matrix.mul_apply]
      symm
      exact Fintype.sum_equiv e2 _ _ fun _ => rfl
    rw [hs1, hs2] at h0
    have hneg : (B1 * B1ᵀ) r s = -((B2 * B2ᵀ) r s) := eq_neg_of_add_eq_zero_left h0
    simpa [Matrix.smul_apply, smul_eq_mul] using hneg
  have hB1_det : B1.det ≠ 0 := by
    refine det_ne_zero_of_linearIndependent_cols B1 ?_
    have hEq : B1ᵀ = Subtype.val ∘ e_t := by
      ext k r
      change B r (idx (e_t k)) = (e_t k).1 r
      exact congr_fun (hidx_spec (e_t k)) r
    rw [hEq]
    exact ht_li.comp e_t e_t.injective
  have hneg1 : (-1 : ZMod 3) ^ 83 = -1 := Odd.neg_one_pow ⟨41, rfl⟩
  have hdet_eq : B1.det * B1.det = -(B2.det * B2.det) := by
    calc B1.det * B1.det = (B1 * B1ᵀ).det := by rw [Matrix.det_mul, Matrix.det_transpose]
      _ = ((-1 : ZMod 3) • (B2 * B2ᵀ)).det := by rw [hB12]
      _ = (-1 : ZMod 3) ^ 83 * (B2 * B2ᵀ).det := by rw [Matrix.det_smul, Fintype.card_fin]
      _ = -(B2.det * B2.det) := by rw [hneg1, neg_one_mul, Matrix.det_mul, Matrix.det_transpose]
  have h3 : ∀ a b : ZMod 3, a ≠ 0 → a * a = -(b * b) → False := by decide
  exact h3 B1.det B2.det hB1_det hdet_eq

end Helpers

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1.H3 := by
  intro G _ hdeg hred hblue _ _
  obtain ⟨hd, hr, hb⟩ := srg_params G hdeg hred hblue
  let e : Option (Fin 165) ≃ Fin 166 := Fintype.equivFinOfCardEq (by simp)
  let C : Matrix (Fin 166) (Fin 166) ℤ := Matrix.reindex e e (confMat G)
  have hCsym : Cᵀ = C := by
    dsimp only [C]
    rw [Matrix.transpose_reindex, confMat_transpose]
  have hCsq : C * C = (165 : ℤ) • (1 : Matrix (Fin 166) (Fin 166) ℤ) := by
    ext i j
    dsimp only [C]
    rw [Matrix.mul_apply]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Fintype.sum_equiv e.symm _
      (fun w : Option (Fin 165) => confMat G (e.symm i) w * confMat G w (e.symm j))
      (fun _ => rfl)]
    have h1 := congr_fun (congr_fun (confMat_mul_self G hd hr hb) (e.symm i)) (e.symm j)
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using h1
  have hker := rank_ge_83_of_sq_165 C hCsq
  let Cb : Matrix (Fin 166) (Fin 166) (ZMod 3) := C.map (Int.castRingHom (ZMod 3))
  have hCbsym : Cbᵀ = Cb := by
    ext i j
    change ((C j i : ℤ) : ZMod 3) = ((C i j : ℤ) : ZMod 3)
    have h := congr_fun (congr_fun hCsym i) j
    rw [← h]; rfl
  have hCbsq : Cb * Cb = 0 := by
    ext i j
    have h1 := congr_arg (Int.castRingHom (ZMod 3)) (congr_fun (congr_fun hCsq i) j)
    have h165 : (165 : ZMod 3) = 0 := by decide
    calc (Cb * Cb) i j = ∑ x : Fin 166, Cb i x * Cb x j := by rw [Matrix.mul_apply]
      _ = ((∑ x : Fin 166, C i x * C x j : ℤ) : ZMod 3) := by simp [Cb]
      _ = (((C * C) i j : ℤ) : ZMod 3) := by rw [Matrix.mul_apply]
      _ = (((((165 : ℤ) • (1 : Matrix (Fin 166) (Fin 166) ℤ)) i j : ℤ) : ZMod 3)) := h1
      _ = 0 := by simp [Matrix.smul_apply, Matrix.one_apply, h165]
  exact no_isotropic_83 Cb hCbsym hCbsq hker
