import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-!
The maximal complex tensor rank is at most twice the generic rank.

Following Blekherman and Teitler (2015), Theorem 1, write a tensor as the sum of two tensors
in the dense open set of generic rank and apply subadditivity of tensor rank.
-/

-- Credit: @aspher1

open scoped Arxiv.«0805.3777»

private lemma tensor_rank_add_le {ds : List ℕ} (S T : Holor ℂ ds) :
    (S + T).cprank ≤ S.cprank + T.cprank := by
  classical
  have hS : Holor.CPRankMax S.cprank S :=
    Nat.find_spec (p := fun n => Holor.CPRankMax n S)
      (H := ⟨ds.prod, Holor.cprankMax_upper_bound S⟩)
  have hT : Holor.CPRankMax T.cprank T :=
    Nat.find_spec (p := fun n => Holor.CPRankMax n T)
      (H := ⟨ds.prod, Holor.cprankMax_upper_bound T⟩)
  unfold Holor.cprank
  exact Nat.find_min' _ (Holor.cprankMax_add hS hT)

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank := by
  intro ds r R hr hR
  let : IsTopologicalAddGroup (Holor ℂ ds) :=
    inferInstanceAs (IsTopologicalAddGroup (HolorIndex ds → ℂ))
  obtain ⟨U, hU, hUd, hUr⟩ := hr
  obtain ⟨T, rfl⟩ := hR.1
  change T.cprank ≤ 2 * r
  have hpre : IsOpen {S : Holor ℂ ds | T - S ∈ U} :=
    hU.preimage (continuous_const.sub continuous_id)
  have hne : {S : Holor ℂ ds | T - S ∈ U}.Nonempty := by
    obtain ⟨S, hS⟩ := hUd.nonempty
    exact ⟨T - S, by simpa using hS⟩
  obtain ⟨S, hTS, hS⟩ := hUd.inter_open_nonempty _ hpre hne
  have hsum := tensor_rank_add_le S (T - S)
  have heq : S + (T - S) = T := by
    simp [sub_eq_add_neg, add_left_comm]
  rw [heq, hUr S hS, hUr (T - S) hTS] at hsum
  omega
