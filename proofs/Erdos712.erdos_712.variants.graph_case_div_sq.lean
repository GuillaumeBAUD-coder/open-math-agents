import FormalConjectures.ErdosProblems.«712»

-- Problem: Erdős Problem 712 — graph case div sq
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/712.lean:73 (declaration Erdos712.erdos_712.variants.graph_case_div_sq)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter
open scoped Topology

private lemma sym2_toFinset_inj {α : Type*} [DecidableEq α] {z₁ z₂ : Sym2 α}
    (h₁ : ¬ z₁.IsDiag) (h₂ : ¬ z₂.IsDiag) (heq : z₁.toFinset = z₂.toFinset) : z₁ = z₂ := by
  induction z₁ with | h a₁ b₁ =>
  induction z₂ with | h a₂ b₂ =>
  simp only [Sym2.mk_isDiag_iff] at h₁ h₂
  simp only [Sym2.toFinset_mk_eq] at heq
  have ha : a₁ ∈ ({a₂, b₂} : Finset α) := heq ▸ Finset.mem_insert_self a₁ {b₁}
  have hb : b₁ ∈ ({a₂, b₂} : Finset α) :=
    heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b₁)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (h₁ rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (h₁ rfl).elim

open scoped Classical in
private lemma cliqueExtremalNumber_two (n k : ℕ) (hk : 2 ≤ k) :
    Hypergraph.cliqueExtremalNumber n 2 k = (SimpleGraph.turanGraph n (k - 1)).edgeFinset.card := by
  apply le_antisymm
  · unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
    apply Finset.sup_le
    intro H hH
    simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    rcases hH with ⟨hHsub, hHcf⟩
    let G : SimpleGraph (Fin n) :=
      { Adj := fun u v ↦ u ≠ v ∧ ({u, v} : Finset (Fin n)) ∈ H
        symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
        loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
    have himg : G.edgeFinset.image Sym2.toFinset = H := by
      ext e
      simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        induction z with | h u v =>
        rw [SimpleGraph.mem_edgeSet] at hz
        simpa [Sym2.toFinset_mk_eq] using hz.2
      · intro he
        have hcard : e.card = 2 := (Finset.mem_powersetCard.mp (hHsub he)).2
        obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
        exact ⟨s(u, v), ⟨huv, he⟩, Sym2.toFinset_mk_eq⟩
    have hcard_eq : H.card = G.edgeFinset.card := by
      conv_lhs => rw [← himg]
      apply Finset.card_image_of_injOn
      intro z₁ hz₁ z₂ hz₂ heq
      exact sym2_toFinset_inj (G.not_isDiag_of_mem_edgeFinset hz₁)
        (G.not_isDiag_of_mem_edgeFinset hz₂) heq
    have hcf : G.CliqueFree (k - 1 + 1) := by
      rw [show k - 1 + 1 = k by omega]
      intro S hS
      apply hHcf
      refine ⟨S, hS.card_eq, ?_⟩
      intro e he
      rw [Finset.mem_powersetCard] at he
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he.2
      have hu : u ∈ S := he.1 (Finset.mem_insert_self u {v})
      have hv : v ∈ S := he.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
      exact (hS.isClique hu hv huv).2
    have hle := hcf.card_edgeFinset_le
    dsimp only at hle
    rw [Fintype.card_fin, ← SimpleGraph.card_edgeFinset_turanGraph] at hle
    exact hcard_eq.trans_le hle
  · let T := SimpleGraph.turanGraph n (k - 1)
    let H := T.edgeFinset.image Sym2.toFinset
    have hHcard : H.card = T.edgeFinset.card := by
      apply Finset.card_image_of_injOn
      intro z₁ hz₁ z₂ hz₂ heq
      exact sym2_toFinset_inj (T.not_isDiag_of_mem_edgeFinset hz₁)
        (T.not_isDiag_of_mem_edgeFinset hz₂) heq
    have hHmem : H ∈ ((Finset.univ : Finset (Fin n)).powersetCard 2).powerset.filter
        (fun H ↦ ¬ H.ContainsCompleteHypergraph 2 k) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro e he
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _,
          Sym2.card_toFinset_of_not_isDiag _ (T.not_isDiag_of_mem_edgeFinset hz)⟩
      · rintro ⟨S, hScard, hSsub⟩
        have hcf : T.CliqueFree k := by
          rw [show k = (k - 1) + 1 by omega]
          exact SimpleGraph.turanGraph_cliqueFree (by omega)
        apply hcf S
        refine ⟨?_, hScard⟩
        intro u hu v hv huv
        have he : ({u, v} : Finset (Fin n)) ∈ S.powersetCard 2 := by
          rw [Finset.mem_powersetCard]
          refine ⟨?_, Finset.card_pair huv⟩
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp (hSsub he)
        have hze : z = s(u, v) :=
          sym2_toFinset_inj (T.not_isDiag_of_mem_edgeFinset hz)
            (by simpa [Sym2.mk_isDiag_iff] using huv) (hzeq.trans Sym2.toFinset_mk_eq.symm)
        rw [hze, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hz
        exact hz
    unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
    exact hHcard.symm.trans_le (Finset.le_sup (f := Finset.card) (by convert hHmem))

theorem OMA.solution : type_of% @Erdos712.erdos_712.variants.graph_case_div_sq := by
  intro k hk
  have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hk1_ne : (k : ℝ) - 1 ≠ 0 := hk1_pos.ne'
  let c : ℝ := ((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))
  have hc_eq : (1 / 2 : ℝ) * (1 - 1 / ((k : ℝ) - 1)) = c := by
    dsimp [c]
    field_simp
    ring
  rw [hc_eq]
  let C : ℝ := ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2 + 1
  have h_upper : ∀ n : ℕ, (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) ≤ c * (n : ℝ) ^ 2 := by
    intro n
    rw [cliqueExtremalNumber_two n k hk]
    have hnat : 2 * (k - 1) * (SimpleGraph.turanGraph n (k - 1)).edgeFinset.card ≤ (k - 1 - 1) * n ^ 2 :=
      SimpleGraph.mul_card_edgeFinset_turanGraph_le
    have hreal : (2 * ((k : ℝ) - 1)) * ((SimpleGraph.turanGraph n (k - 1)).edgeFinset.card : ℝ) ≤
        ((k : ℝ) - 2) * (n : ℝ) ^ 2 := by
      have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      have hk2 : ((k - 1 - 1 : ℕ) : ℝ) = (k : ℝ) - 2 := by
        rw [show k - 1 - 1 = k - 2 by omega, Nat.cast_sub (by omega)]; norm_num
      have hcast : ((2 * (k - 1) * (SimpleGraph.turanGraph n (k - 1)).edgeFinset.card : ℕ) : ℝ) ≤
          (((k - 1 - 1) * n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast [hk1, hk2] at hcast
      linarith
    dsimp [c]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have h_lower : ∀ n : ℕ, c * (n : ℝ) ^ 2 - C ≤ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) := by
    intro n
    rw [cliqueExtremalNumber_two n k hk]
    let r := k - 1
    have hr_pos : 0 < r := by omega
    have hcard := SimpleGraph.card_edgeFinset_turanGraph (n := n) (r := r)
    have hdiv_le : (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) ≤
        (SimpleGraph.turanGraph n r).edgeFinset.card := by
      rw [hcard]
      exact Nat.le_add_right _ _
    have hmul_div : (n ^ 2 - (n % r) ^ 2) * (r - 1) ≤
        2 * r * (SimpleGraph.turanGraph n r).edgeFinset.card + 2 * r := by
      have h1 : (n ^ 2 - (n % r) ^ 2) * (r - 1) <
          2 * r * ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r)) + 2 * r := by
        have hdm := Nat.div_add_mod ((n ^ 2 - (n % r) ^ 2) * (r - 1)) (2 * r)
        have hml := Nat.mod_lt ((n ^ 2 - (n % r) ^ 2) * (r - 1)) (by positivity : 0 < 2 * r)
        omega
      have h2 := Nat.mul_le_mul_left (2 * r) hdiv_le
      omega
    have hmod_sq : (n % r) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.mod_le n r) 2
    have hmod_lt : ((n % r : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
      have : n % r ≤ r := (Nat.mod_lt n hr_pos).le
      have : ((n % r : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
      have hk1 : (r : ℝ) = (k : ℝ) - 1 := by dsimp [r]; rw [Nat.cast_sub (by omega)]; norm_num
      linarith
    have hcast : ((n : ℝ) ^ 2 - ((n % r : ℕ) : ℝ) ^ 2) * ((k : ℝ) - 2) ≤
        2 * ((k : ℝ) - 1) * ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) + 2 * ((k : ℝ) - 1) := by
      have hk1 : (r : ℝ) = (k : ℝ) - 1 := by dsimp [r]; rw [Nat.cast_sub (by omega)]; norm_num
      have hk2 : ((r - 1 : ℕ) : ℝ) = (k : ℝ) - 2 := by
        have hr1 : r - 1 = k - 2 := by dsimp [r]; omega
        rw [hr1, Nat.cast_sub (by omega)]; norm_num
      have hnat_real : (((n ^ 2 - (n % r) ^ 2) * (r - 1) : ℕ) : ℝ) ≤
          ((2 * r * (SimpleGraph.turanGraph n r).edgeFinset.card + 2 * r : ℕ) : ℝ) := by
        exact_mod_cast hmul_div
      rw [Nat.cast_mul, Nat.cast_sub hmod_sq] at hnat_real
      push_cast [hk1, hk2] at hnat_real
      exact hnat_real
    have hmod_sq_real : ((n % r : ℕ) : ℝ) ^ 2 ≤ ((k : ℝ) - 1) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ (n % r : ℕ) from Nat.cast_nonneg _]
    have hk2_nonneg : (0 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hbound : ((n : ℝ) ^ 2 - ((k : ℝ) - 1) ^ 2) * ((k : ℝ) - 2) ≤
        2 * ((k : ℝ) - 1) * ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) + 2 * ((k : ℝ) - 1) := by
      nlinarith
    dsimp [c, C]
    have hden_pos : (0 : ℝ) < 2 * ((k : ℝ) - 1) := by positivity
    rw [sub_le_iff_le_add, div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    linarith
  have h_tend_sq : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h_tend_low : Tendsto (fun n : ℕ ↦ c - C / (n : ℝ) ^ 2) atTop (𝓝 c) := by
    have hdiv : Tendsto (fun n : ℕ ↦ C / (n : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h_tend_sq
    have hsub : Tendsto (fun n : ℕ ↦ c - C / (n : ℝ) ^ 2) atTop (𝓝 (c - 0)) :=
      tendsto_const_nhds.sub hdiv
    simpa using hsub
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_tend_low tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h := div_le_div_of_nonneg_right (h_lower n) hn_pos.le
    rw [sub_div, mul_div_assoc, div_self hn_pos.ne', mul_one] at h
    exact h
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hn_pos]
    exact h_upper n
