import FormalConjectures.ErdosProblems.«753»

-- Problem: Erdős Problem 753 — Alon's upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/753.lean:66 (declaration Erdos753.erdos_753.variants.alon)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős 753: a graph with small choice number and small complementary choice number

Split `Fin n` into blocks `{v : v / m = j}` of size at most `m = ⌈√(n log n)⌉`, and let `G` be
the disjoint union of the cliques on the blocks. `G` is `m`-choosable: inside a block, Hall's
theorem picks distinct colours from the lists. Its complement is complete `K`-partite with
`K = n / m + 1` parts, and it is `ℓ`-choosable for `ℓ = ⌊K log n⌋ + 1`: send every colour to one
of the `K` parts; a vertex is stuck when no colour of its list goes to its own part, which
happens for `(K-1)^ℓ K^(M-ℓ)` of the `K^M` maps, and `n (1 - 1/K)^ℓ < n e^{-ℓ/K} < 1`, so some
map leaves no vertex stuck. Then `m + ℓ ≤ 5 √(n log n)`.
-/

open SimpleGraph

namespace OMA753

/-- Disjoint union of cliques: blocks `{v : v / m = j}`. -/
def G (n m : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => (u : ℕ) / m = (v : ℕ) / m

lemma G_adj {n m : ℕ} {u v : Fin n} : (G n m).Adj u v ↔ u ≠ v ∧ (u : ℕ) / m = (v : ℕ) / m := by
  simp only [G, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩ <;> exact ⟨h, by omega⟩
  · rintro ⟨h, h'⟩; exact ⟨h, Or.inl h'⟩

lemma block_card_le {n m : ℕ} (hm : 0 < m) (j : ℕ) (s : Finset {v : Fin n // (v : ℕ) / m = j}) :
    s.card ≤ m := by
  have : s.card ≤ (Finset.range m).card := by
    apply Finset.card_le_card_of_injOn (fun x => (x.1 : ℕ) % m)
    · intro x _; simp [Nat.mod_lt _ hm]
    · intro x _ y _ hxy
      apply Subtype.ext; apply Fin.ext
      have hx := Nat.div_add_mod (x.1 : ℕ) m
      have hy := Nat.div_add_mod (y.1 : ℕ) m
      simp only at hxy
      rw [x.2] at hx; rw [y.2] at hy
      omega
  simpa using this

lemma choosable_G {n m : ℕ} (hm : 0 < m) : (G n m).IsKChoosable m := by
  intro L hL
  have hall : ∀ j : ℕ, ∃ F : {v : Fin n // (v : ℕ) / m = j} → ℕ,
      Function.Injective F ∧ ∀ x, F x ∈ L x.1 := by
    intro j
    apply (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun x : {v : Fin n // (v : ℕ) / m = j} => L x.1)).1
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · calc s.card ≤ m := block_card_le hm j s
        _ = (L x.1).card := (hL _).symm
        _ ≤ _ := Finset.card_le_card (Finset.subset_biUnion_of_mem (fun y : {v : Fin n // (v : ℕ) / m = j} => L y.1) hx)
  choose F hFi hFm using hall
  have key : ∀ (v : Fin n) (j : ℕ) (h : (v : ℕ) / m = j),
      F ((v : ℕ) / m) ⟨v, rfl⟩ = F j ⟨v, h⟩ := by
    rintro v j rfl; rfl
  refine ⟨Coloring.mk (fun v => F ((v : ℕ) / m) ⟨v, rfl⟩) ?_, fun v => hFm _ _⟩
  intro u v huv heq
  rw [G_adj] at huv
  rw [key v ((u : ℕ) / m) huv.2.symm] at heq
  have := hFi _ heq
  exact huv.1 (congrArg Subtype.val this)

lemma listChromaticNumber_G_le {n m : ℕ} (hm : 0 < m) :
    listChromaticNumber (G n m) ≤ m :=
  Nat.sInf_le (choosable_G hm)


lemma card_filter_mem {M : ℕ} (A : Finset ℕ) (hA : ∀ c ∈ A, c < M) :
    (Finset.univ.filter (fun c : Fin M => (c : ℕ) ∈ A)).card = A.card := by
  rw [← Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext c
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd, rfl⟩; exact hd
  · intro hc; exact ⟨⟨c, hA c hc⟩, hc, rfl⟩

lemma choosable_compl {n m K ℓ : ℕ} (hK : n / m < K) (hℓ : n * (K - 1) ^ ℓ < K ^ ℓ) :
    (G n m)ᶜ.IsKChoosable ℓ := by
  intro L hL
  classical
  set M := (Finset.univ.biUnion L).sup id + 1 with hMdef
  have hLM : ∀ v, ∀ c ∈ L v, c < M := by
    intro v c hc
    have : c ≤ (Finset.univ.biUnion L).sup id :=
      Finset.le_sup (f := id) (Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, hc⟩)
    omega
  let part : Fin n → Fin K := fun v =>
    ⟨(v : ℕ) / m, lt_of_le_of_lt (Nat.div_le_div_right v.isLt.le) hK⟩
  let bad : Fin n → Finset (Fin M → Fin K) := fun v =>
    Finset.univ.filter (fun g => ∀ c : Fin M, (c : ℕ) ∈ L v → g c ≠ part v)
  have hK1 : 1 ≤ K := Nat.lt_of_le_of_lt (Nat.zero_le _) hK
  have hbad : ∀ v, (bad v).card ≤ (K - 1) ^ ℓ * K ^ (M - ℓ) := by
    intro v
    have hsub : bad v ⊆ Fintype.piFinset
        (fun c : Fin M => if (c : ℕ) ∈ L v then Finset.univ.erase (part v) else Finset.univ) := by
      intro g hg
      rw [Fintype.mem_piFinset]
      intro c
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      split_ifs with hc
      · exact Finset.mem_erase.2 ⟨hg c hc, Finset.mem_univ _⟩
      · exact Finset.mem_univ _
    refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    have : ∀ c : Fin M, ((if (c : ℕ) ∈ L v then Finset.univ.erase (part v) else Finset.univ) :
        Finset (Fin K)).card = if (c : ℕ) ∈ L v then K - 1 else K := by
      intro c
      split_ifs <;> simp [Finset.card_erase_of_mem]
    simp_rw [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, card_filter_mem _ (hLM v), hL]
    congr 1
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M)))
      (fun c : Fin M => (c : ℕ) ∈ L v)
    rw [card_filter_mem _ (hLM v), hL, Finset.card_univ, Fintype.card_fin] at h1
    congr 1
    omega
  have hex : ∃ g : Fin M → Fin K, ∀ v, ∃ c : Fin M, (c : ℕ) ∈ L v ∧ g c = part v := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact ⟨fun _ => ⟨0, hK1⟩, fun v => absurd v.isLt (by omega)⟩
    by_contra hno
    push_neg at hno
    have hcov : (Finset.univ : Finset (Fin M → Fin K)) ⊆ Finset.univ.biUnion bad := by
      intro g _
      obtain ⟨v, hv⟩ := hno g
      exact Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, fun c hc => hv c hc⟩⟩
    have h1 := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h1
    have h2 : ∑ v : Fin n, (bad v).card ≤ n * ((K - 1) ^ ℓ * K ^ (M - ℓ)) := by
      calc ∑ v : Fin n, (bad v).card ≤ ∑ _v : Fin n, (K - 1) ^ ℓ * K ^ (M - ℓ) :=
            Finset.sum_le_sum fun v _ => hbad v
        _ = _ := by simp
    have hℓM : ℓ ≤ M := by
      have := card_filter_mem (M := M) _ (hLM ⟨0, hn⟩)
      rw [hL] at this
      rw [← this]
      exact (Finset.card_le_univ _).trans (by simp)
    have h3 : K ^ M = K ^ ℓ * K ^ (M - ℓ) := by rw [← pow_add]; congr 1; omega
    have h4 : 0 < K ^ (M - ℓ) := pow_pos (by omega) _
    have h5 : n * (K - 1) ^ ℓ * K ^ (M - ℓ) < K ^ ℓ * K ^ (M - ℓ) :=
      Nat.mul_lt_mul_of_pos_right hℓ h4
    rw [mul_assoc] at h5
    omega
  obtain ⟨g, hg⟩ := hex
  choose c hcL hcg using hg
  refine ⟨Coloring.mk (fun v => (c v : ℕ)) ?_, fun v => hcL v⟩
  intro u v huv heq
  rw [SimpleGraph.compl_adj, G_adj] at huv
  have hc : c u = c v := Fin.ext heq
  have : part u = part v := by rw [← hcg u, ← hcg v, hc]
  apply huv.2 ⟨huv.1, ?_⟩
  exact congrArg Fin.val this


lemma count_ineq (n K : ℕ) (hn : 1 ≤ n) (hK : 1 ≤ K) :
    n * (K - 1) ^ (⌊(K : ℝ) * Real.log n⌋₊ + 1) < K ^ (⌊(K : ℝ) * Real.log n⌋₊ + 1) := by
  set ℓ := ⌊(K : ℝ) * Real.log n⌋₊ + 1 with hℓ
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : (K : ℝ) * Real.log n < ℓ := by
    rw [hℓ]; push_cast; exact Nat.lt_floor_add_one _
  have hcast : ((K - 1 : ℕ) : ℝ) = K - 1 := by rw [Nat.cast_sub hK]; simp
  suffices h : (n : ℝ) * ((K : ℝ) - 1) ^ ℓ < (K : ℝ) ^ ℓ by
    rw [← hcast] at h; exact_mod_cast h
  have hKpos : (0 : ℝ) < K := by linarith
  have hb0 : 0 ≤ 1 - 1 / (K : ℝ) := by
    rw [sub_nonneg, div_le_one hKpos]; exact hKR
  have hb1 : 1 - 1 / (K : ℝ) ≤ Real.exp (-(1 / (K : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (K : ℝ))); linarith
  have hfac : (K : ℝ) - 1 = K * (1 - 1 / K) := by field_simp
  rw [hfac, mul_pow]
  have hpow : (1 - 1 / (K : ℝ)) ^ ℓ ≤ Real.exp (-(ℓ / (K : ℝ))) := by
    calc (1 - 1 / (K : ℝ)) ^ ℓ ≤ Real.exp (-(1 / (K : ℝ))) ^ ℓ := pow_le_pow_left₀ hb0 hb1 ℓ
      _ = Real.exp (-(ℓ / (K : ℝ))) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp : (n : ℝ) * Real.exp (-(ℓ / (K : ℝ))) < 1 := by
    have h1 : Real.log n < ℓ / (K : ℝ) := by rw [lt_div_iff₀ hKpos]; linarith
    have h2 : Real.exp (-(ℓ / (K : ℝ))) < Real.exp (-Real.log n) := Real.exp_lt_exp.2 (by linarith)
    have h2' : Real.exp (-Real.log n) = (n : ℝ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by linarith)]
    rw [h2'] at h2
    have h3 : (n : ℝ) * Real.exp (-(ℓ / (K : ℝ))) < n * (n : ℝ)⁻¹ :=
      mul_lt_mul_of_pos_left h2 (by linarith)
    rwa [mul_inv_cancel₀ (by linarith)] at h3
  have hKl : (0 : ℝ) < (K : ℝ) ^ ℓ := pow_pos hKpos ℓ
  calc (n : ℝ) * ((K : ℝ) ^ ℓ * (1 - 1 / (K : ℝ)) ^ ℓ)
      ≤ (n : ℝ) * ((K : ℝ) ^ ℓ * Real.exp (-(ℓ / (K : ℝ)))) := by gcongr
    _ = (K : ℝ) ^ ℓ * ((n : ℝ) * Real.exp (-(ℓ / (K : ℝ)))) := by ring
    _ < (K : ℝ) ^ ℓ * 1 := mul_lt_mul_of_pos_left hexp hKl
    _ = (K : ℝ) ^ ℓ := mul_one _

theorem alon : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ G : SimpleGraph (Fin n),
      (listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ) ≤
        C * ((n : ℝ) * Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) := by
  refine ⟨5, by norm_num, fun n hn => ?_⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hlog2 : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  set s := Real.sqrt ((n : ℝ) * Real.log n) with hs
  have hsq : s ^ 2 = n * Real.log n := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hls : Real.log n ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hs1 : 1 ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    nlinarith
  set m := ⌈s⌉₊ with hm
  have hm0 : 0 < m := Nat.ceil_pos.2 hspos
  have hm1 : s ≤ m := Nat.le_ceil s
  have hm2 : (m : ℝ) < s + 1 := Nat.ceil_lt_add_one hspos.le
  set K := n / m + 1 with hK
  have hK1 : 1 ≤ K := Nat.le_add_left 1 _
  have hKR : (K : ℝ) ≤ n / s + 1 := by
    have : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
    have h2 : (n : ℝ) / m ≤ n / s := div_le_div_of_nonneg_left (by positivity) hspos hm1
    rw [hK]; push_cast; linarith
  set ℓ := ⌊(K : ℝ) * Real.log n⌋₊ + 1 with hℓ
  have hℓR : (ℓ : ℝ) ≤ K * Real.log n + 1 := by
    rw [hℓ]; push_cast
    have := Nat.floor_le (show 0 ≤ (K : ℝ) * Real.log n by positivity); linarith
  have hns : (n : ℝ) / s * Real.log n = s := by
    field_simp; nlinarith [hsq]
  refine ⟨G n m, ?_⟩
  have h1 : (listChromaticNumber (G n m) : ℝ) ≤ m := by
    exact_mod_cast listChromaticNumber_G_le hm0
  have h2 : (listChromaticNumber (G n m)ᶜ : ℝ) ≤ ℓ := by
    exact_mod_cast Nat.sInf_le
      (choosable_compl (K := K) (ℓ := ℓ) (Nat.lt_succ_self _) (count_ineq n K (by omega) hK1))
  rw [← Real.sqrt_eq_rpow, ← hs]
  have h3 : (K : ℝ) * Real.log n ≤ (n / s + 1) * Real.log n :=
    mul_le_mul_of_nonneg_right hKR hlog.le
  nlinarith

end OMA753

theorem OMA.solution : type_of% @Erdos753.erdos_753.variants.alon := by
  exact OMA753.alon
