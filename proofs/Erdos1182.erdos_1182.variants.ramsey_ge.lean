import FormalConjectures.ErdosProblems.«1182»

/-! A complete bipartite graph with both parts smaller than the connected
target witnesses the lower bound. The finite Ramsey theorem supplies a
nonempty set over which to take the infimum. The bipartite witness follows
Ian Qvist’s merged proof of the tree case in the F_ge_pred variant. -/

open SimpleGraph

lemma OMA.ramseyCliqueCopy {N k : ℕ} {C : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} (hcard : S.card = k) (hclique : C.IsClique (S : Set (Fin N))) :
    (⊤ : SimpleGraph (Fin k)) ⊑ C := by
  have hsize : Fintype.card S = k := by simpa using hcard
  let e := (Fintype.equivFinOfCardEq hsize).symm
  let f : Fin k ↪ Fin N := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  exact ⟨⟨⟨f, fun {i j} hij => hclique (e i).property (e j).property
    (fun h => hij (f.injective h))⟩, f.injective⟩⟩

lemma OMA.triangleRamseyFinite {n : ℕ} (G : SimpleGraph (Fin n)) :
    {N | ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ G ⊑ Cᶜ}.Nonempty := by
  classical
  let N := (3 + n).choose 3
  refine ⟨N, ?_⟩
  intro C
  let color (e : Finset (Fin N)) : Bool := decide (¬ ∃ u ∈ e, ∃ v ∈ e, C.Adj u v)
  have hcolor := Combinatorics.Diagonal.hasRamseyProperty_choose 3 n color Finset.univ
    (by simp [N])
  rcases hcolor with ⟨S, _, hcard, hS⟩ | ⟨S, _, hcard, hS⟩
  · left
    apply OMA.ramseyCliqueCopy hcard
    intro u hu v hv huv
    have he := hS (insert u {v}) (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (by simp [huv])
    simp only [color, decide_eq_false_iff_not, not_not] at he
    obtain ⟨a, ha, b, hb, hab⟩ := he
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (C.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (C.irrefl hab).elim
  · right
    have hcopy : (⊤ : SimpleGraph (Fin n)) ⊑ Cᶜ := by
      apply OMA.ramseyCliqueCopy hcard
      intro u hu v hv huv
      have he := hS (insert u {v}) (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
        (by simp [huv])
      simp only [color, decide_eq_true_eq] at he
      exact ⟨huv, fun hadj => he ⟨u, by simp, v, by simp, hadj⟩⟩
    obtain ⟨f⟩ := hcopy
    exact ⟨⟨⟨f, fun {_ _} h => f.toHom.map_adj h.ne⟩, f.injective⟩⟩

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.ramsey_ge := by
  classical
  intro n G hG
  unfold graphRamsey
  apply le_csInf (OMA.triangleRamseyFinite G)
  intro N hN
  by_contra! hlt
  let side (v : Fin N) : Bool := decide (v.val < n - 1)
  let C : SimpleGraph (Fin N) := (⊤ : SimpleGraph Bool).comap side
  rcases hN C with htri | hcopy
  · obtain ⟨f⟩ := htri
    have hinj : Function.Injective (fun i : Fin 3 => side (f i)) := by
      intro i j hij
      by_contra hne
      exact f.toHom.map_adj (show (⊤ : SimpleGraph (Fin 3)).Adj i j from hne) hij
    have hcard := Fintype.card_le_of_injective _ hinj
    norm_num at hcard
  · obtain ⟨f⟩ := hcopy
    have hside (i j : Fin n) : side (f i) = side (f j) := by
      obtain ⟨w⟩ := hG.preconnected i j
      induction w with
      | nil => rfl
      | cons h _ ih => exact (not_ne_iff.mp (f.toHom.map_adj h).2).trans ih
    let pos (i : Fin n) : Fin (n - 1) :=
      ⟨if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1), by
        have hi := (f i).isLt
        split <;> omega⟩
    have hinj : Function.Injective pos := by
      intro i j hij
      have h := congrArg Fin.val hij
      change (if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1)) =
        (if (f j).val < n - 1 then (f j).val else (f j).val - (n - 1)) at h
      have hs : (f i).val < n - 1 ↔ (f j).val < n - 1 :=
        decide_eq_decide.mp (hside i j)
      apply f.injective
      apply Fin.ext
      change (f i).val = (f j).val
      by_cases hi : (f i).val < n - 1
      · simpa only [if_pos hi, if_pos (hs.mp hi)] using h
      · have hj : ¬ (f j).val < n - 1 := fun hj => hi (hs.mpr hj)
        simp only [if_neg hi, if_neg hj] at h
        omega
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hcard
    omega
