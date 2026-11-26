import FormalConjectures.Wikipedia.SidorenkoConjecture

-- Problem: Case: complete bipartite graphs `K_{s,t}` (Sidorenko 1993).
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SidorenkoConjecture.lean:776 (declaration SidorenkoConjecture.sidorenko_conjecture.variants.complete_bipartite)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset SimpleGraph

namespace OMA

/-- Edge count of `K_{s,t}`. -/
theorem card_edges_Kst (s t : ℕ)
    [DecidableRel (completeBipartiteGraph (Fin s) (Fin t)).Adj] :
    (completeBipartiteGraph (Fin s) (Fin t)).edgeFinset.card = s * t := by
  have h := encard_edgeSet_completeBipartiteGraph (W₁ := Fin s) (W₂ := Fin t)
  rw [← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard] at h
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h
  exact_mod_cast h

/-- Homomorphisms `K_{s,t} → G`: choose the images `f` of the left side, then each right vertex
goes to a common neighbour of the `f i`. -/
theorem homCount_Kst (s t : ℕ)
    [DecidableRel (completeBipartiteGraph (Fin s) (Fin t)).Adj]
    {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homCount (completeBipartiteGraph (Fin s) (Fin t)) G =
      ∑ f : Fin s → W, (#{y : W | ∀ i, G.Adj (f i) y}) ^ t := by
  unfold homCount
  have hEquiv : (completeBipartiteGraph (Fin s) (Fin t) →g G) ≃
      Σ f : Fin s → W, (Fin t → {y : W // y ∈ ({y : W | ∀ i, G.Adj (f i) y} : Finset W)}) := by
    refine
      { toFun := fun φ => ⟨fun i => φ (Sum.inl i), fun j => ⟨φ (Sum.inr j), ?_⟩⟩
        invFun := fun x =>
          { toFun := fun v =>
              match v with
              | Sum.inl i => x.1 i
              | Sum.inr j => (x.2 j).val
            map_rel' := ?_ }
        left_inv := ?_
        right_inv := ?_ }
    · rw [mem_filter]
      exact ⟨mem_univ _, fun i => φ.map_adj (by simp [completeBipartiteGraph])⟩
    · rintro a b hab
      obtain ⟨f, g⟩ := x
      cases a with
      | inl i =>
        cases b with
        | inl k => simp [completeBipartiteGraph] at hab
        | inr j =>
          have hj := (g j).property
          rw [mem_filter] at hj
          exact hj.2 i
      | inr j =>
        cases b with
        | inl k =>
          have hj := (g j).property
          rw [mem_filter] at hj
          exact (hj.2 k).symm
        | inr k => simp [completeBipartiteGraph] at hab
    · intro φ
      ext v
      cases v with
      | inl i => rfl
      | inr j => rfl
    · rintro ⟨f, g⟩
      rfl
  rw [Fintype.card_congr hEquiv, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro f _
  rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

/-- Double counting: `∑_f #commonNbrs(f) = ∑_y d(y)^s`. -/
theorem sum_common_eq (s : ℕ) {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    ∑ f : Fin s → W, #{y : W | ∀ i, G.Adj (f i) y} = ∑ y : W, (G.degree y) ^ s := by
  simp only [card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [← card_filter]
  have : ({f : Fin s → W | ∀ i, G.Adj (f i) y} : Finset (Fin s → W)) =
      Fintype.piFinset (fun _ : Fin s => G.neighborFinset y) := by
    ext f
    simp [Fintype.mem_piFinset, adj_comm]
  rw [this, Fintype.card_piFinset]
  simp

/-- Power mean in a division-free form valid for every exponent. -/
theorem pow_sum_mul_card_le {ι : Type} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i)
    (k : ℕ) : (∑ i ∈ S, f i) ^ k * (#S : ℝ) ≤ (#S : ℝ) ^ k * ∑ i ∈ S, f i ^ k := by
  cases k with
  | zero => simp
  | succ n =>
    have h := pow_sum_le_card_mul_sum_pow hf n
    have hc : (0 : ℝ) ≤ (#S : ℝ) := by positivity
    calc (∑ i ∈ S, f i) ^ (n + 1) * (#S : ℝ)
        ≤ ((#S : ℝ) ^ n * ∑ i ∈ S, f i ^ (n + 1)) * (#S : ℝ) :=
          mul_le_mul_of_nonneg_right h hc
      _ = (#S : ℝ) ^ (n + 1) * ∑ i ∈ S, f i ^ (n + 1) := by ring

end OMA

theorem OMA.solution : type_of% @SidorenkoConjecture.sidorenko_conjecture.variants.complete_bipartite := by
  intro s t _ W _ _ _ G _
  rw [OMA.card_edges_Kst]
  set n : ℝ := (Fintype.card W : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set m : ℝ := ∑ c : W, (G.degree c : ℝ) with hm
  set S1 : ℝ := ∑ y : W, (G.degree y : ℝ) ^ s with hS1
  set H : ℝ := ∑ f : Fin s → W, ((#{y : W | ∀ i, G.Adj (f i) y} : ℕ) : ℝ) ^ t with hH
  have hL : homDensity (completeGraph (Fin 2)) G = m / n ^ 2 := by
    unfold homDensity
    rw [SidorenkoConjecture.homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset,
      ← G.sum_degrees_eq_twice_card_edges]
    simp only [Fintype.card_fin]
    push_cast
    rfl
  have hR : homDensity (completeBipartiteGraph (Fin s) (Fin t)) G = H / n ^ (s + t) := by
    unfold homDensity
    rw [OMA.homCount_Kst]
    have hcardV : Fintype.card (Fin s ⊕ Fin t) = s + t := by simp
    rw [hcardV]
    push_cast
    rfl
  -- Jensen 1: m^s * n ≤ n^s * S1
  have h1 : m ^ s * n ≤ n ^ s * S1 := by
    have := OMA.pow_sum_mul_card_le (Finset.univ : Finset W) (fun c => (G.degree c : ℝ))
      (fun _ _ => by positivity) s
    simpa [Finset.card_univ] using this
  -- Jensen 2: S1^t * n^s ≤ (n^s)^t * H
  have hS1' : S1 = ∑ f : Fin s → W, ((#{y : W | ∀ i, G.Adj (f i) y} : ℕ) : ℝ) := by
    rw [hS1]
    have := OMA.sum_common_eq s G
    have h2 := congrArg (fun k : ℕ => (k : ℝ)) this
    push_cast at h2
    exact h2.symm
  have h2 : S1 ^ t * n ^ s ≤ (n ^ s) ^ t * H := by
    have := OMA.pow_sum_mul_card_le (Finset.univ : Finset (Fin s → W))
      (fun f => ((#{y : W | ∀ i, G.Adj (f i) y} : ℕ) : ℝ)) (fun _ _ => by positivity) t
    rw [← hS1'] at this
    simpa [Finset.card_univ] using this
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hS0 : 0 ≤ S1 := by rw [hS1]; positivity
  rw [hL, hR, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  -- goal: m^(s*t) * n^(s+t) ≤ H * (n^2)^(s*t)
  have h3 : (m ^ s * n) ^ t ≤ (n ^ s * S1) ^ t := pow_le_pow_left₀ (by positivity) h1 t
  calc m ^ (s * t) * n ^ (s + t) = (m ^ s * n) ^ t * n ^ s := by ring
    _ ≤ (n ^ s * S1) ^ t * n ^ s := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (n ^ s) ^ t * (S1 ^ t * n ^ s) := by ring
    _ ≤ (n ^ s) ^ t * ((n ^ s) ^ t * H) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = H * (n ^ 2) ^ (s * t) := by ring
