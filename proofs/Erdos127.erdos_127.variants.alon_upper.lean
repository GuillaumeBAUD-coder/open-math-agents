import FormalConjectures.ErdosProblems.«127»

/-!
# Proof of `Erdos127.erdos_127.variants.alon_upper`

Alon's upper bound `f m ≤ C m^(1/4)`, with `C = 2`, by an explicit graph.

1. Write `m = C(n,2) + r` with `r < n`, then `r = C(s,2) + r'` with `r' < s`.
2. Take `G = K_n ⊔ K_s ⊔ K_{1,r'}` (disjoint sum), which has exactly `m` edges.
3. A bipartite subgraph of `G` splits along the sum; on `K_n` it has at most `n^2/4` edges
   (`IsBipartite.four_mul_encard_edgeSet_le`), on `K_s` at most `s^2/4`, on the star at most `r'`.
4. Since `√(8m+1) ≥ 2n - 1`, any admissible `k` satisfies `k ≤ s/4 + r'/2 + 1/4 < s`, so
   `f m ≤ s - 1 =: t`, and `t^4 ≤ 8m` from `C(s,2) ≤ r ≤ n - 1` and `C(n,2) ≤ m`.
-/

open SimpleGraph

namespace OMA127


lemma ncard_sum {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr edgeSetSumEquiv, Nat.card_sum]

lemma ncard_top (n : ℕ) : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin]

lemma ncard_cb (r : ℕ) : (completeBipartiteGraph (Fin 1) (Fin r)).edgeSet.ncard = r := by
  have h := encard_edgeSet_completeBipartiteGraph (W₁ := Fin 1) (W₂ := Fin r)
  rw [Set.ncard, h]
  simp

lemma le_sum_comap {V W : Type} (G : SimpleGraph V) (G' : SimpleGraph W) (H : SimpleGraph (V ⊕ W))
    (hH : H ≤ G ⊕g G') : H ≤ (H.comap Sum.inl) ⊕g (H.comap Sum.inr) := by
  intro x y hxy
  have hg := hH hxy
  rcases x with x | x <;> rcases y with y | y <;> simp_all [sum_adj, comap_adj]

lemma comap_le {V W : Type} (G : SimpleGraph V) (G' : SimpleGraph W) (H : SimpleGraph (V ⊕ W))
    (hH : H ≤ G ⊕g G') : H.comap Sum.inl ≤ G ∧ H.comap Sum.inr ≤ G' := by
  constructor
  · intro x y hxy
    have := hH hxy
    simpa [sum_adj] using this
  · intro x y hxy
    have := hH hxy
    simpa [sum_adj] using this

lemma bip_comap {V W : Type} (f : V → W) (H : SimpleGraph W) (hH : H.IsBipartite) :
    (H.comap f).IsBipartite := Colorable.of_hom (Hom.comap f H) hH

lemma bip_bound (n : ℕ) (H : SimpleGraph (Fin n)) (hH : H.IsBipartite) :
    4 * (H.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h := hH.four_mul_encard_edgeSet_le
  have hf : H.edgeSet.Finite := Set.toFinite _
  rw [← hf.cast_ncard_eq] at h
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h
  have h2 : 4 * H.edgeSet.ncard ≤ n ^ 2 := by exact_mod_cast h
  exact_mod_cast h2

lemma decomp (r : ℕ) : ∃ s, s.choose 2 ≤ r ∧ r < s.choose 2 + s := by
  induction r with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨s, h1, h2⟩ := ih
    by_cases h : r + 1 < s.choose 2 + s
    · exact ⟨s, by omega, h⟩
    · have e : (s+1).choose 2 = s.choose 2 + s := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
      refine ⟨s + 1, ?_, ?_⟩ <;> rw [e] <;> omega

/-- Main estimate: `f m ≤ t` with `t ^ 4 ≤ 8 m`. -/
lemma key (m : ℕ) : ∃ t : ℕ, Erdos127.f m ≤ t ∧ (t : ℝ) ^ 4 ≤ 8 * m := by
  obtain ⟨n, hn1, hn2⟩ := decomp m
  obtain ⟨s, hs1, hs2⟩ := decomp (m - n.choose 2)
  set r' := m - n.choose 2 - s.choose 2 with hr'
  have hs : 1 ≤ s := by omega
  refine ⟨s - 1, ?_, ?_⟩
  · apply csSup_le'
    intro k hk
    let G : SimpleGraph (Fin n ⊕ (Fin s ⊕ (Fin 1 ⊕ Fin r'))) :=
      (⊤ : SimpleGraph (Fin n)) ⊕g ((⊤ : SimpleGraph (Fin s)) ⊕g
        completeBipartiteGraph (Fin 1) (Fin r'))
    have hG : G.edgeSet.ncard = m := by
      simp only [G, ncard_sum, ncard_top, ncard_cb]
      omega
    obtain ⟨H, hHG, hHb, hHk⟩ := hk _ G hG
    -- split H
    set H1 := H.comap Sum.inl
    set H2 := H.comap Sum.inr
    have hle := le_sum_comap _ _ H hHG
    obtain ⟨_, hH2G⟩ := comap_le _ _ H hHG
    have hle2 := le_sum_comap _ _ H2 hH2G
    obtain ⟨_, hH22G⟩ := comap_le _ _ H2 hH2G
    have hc1 : H.edgeSet.ncard ≤ H1.edgeSet.ncard + H2.edgeSet.ncard := by
      rw [← ncard_sum]
      exact Set.ncard_le_ncard (edgeSet_mono hle)
    have hc2 : H2.edgeSet.ncard ≤
        (H2.comap Sum.inl).edgeSet.ncard + (H2.comap Sum.inr).edgeSet.ncard := by
      rw [← ncard_sum]
      exact Set.ncard_le_ncard (edgeSet_mono hle2)
    have hc3 : (H2.comap Sum.inr).edgeSet.ncard ≤ r' := by
      exact (Set.ncard_le_ncard (edgeSet_mono hH22G)).trans (ncard_cb r').le
    have hb1 := bip_bound n H1 (bip_comap _ _ hHb)
    have hb2 := bip_bound s (H2.comap Sum.inl) (bip_comap _ _ (bip_comap _ _ hHb))
    have hmR : (m : ℝ) = n * (n - 1) / 2 + s * (s - 1) / 2 + r' := by
      have : m = n.choose 2 + s.choose 2 + r' := by omega
      rw [this]; push_cast [Nat.cast_choose_two]; ring
    have hsq : 2 * (n : ℝ) - 1 ≤ √(8 * m + 1) := by
      calc 2 * (n : ℝ) - 1 ≤ |2 * (n : ℝ) - 1| := le_abs_self _
        _ = √((2 * (n : ℝ) - 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(8 * m + 1) := by
          apply Real.sqrt_le_sqrt
          have : (n.choose 2 : ℝ) ≤ m := by exact_mod_cast hn1
          rw [Nat.cast_choose_two] at this
          nlinarith
    have hr's : (r' : ℝ) + 1 ≤ s := by
      have : r' + 1 ≤ s := by omega
      exact_mod_cast this
    have hc1R : (H.edgeSet.ncard : ℝ) ≤ H1.edgeSet.ncard + H2.edgeSet.ncard := by
      exact_mod_cast hc1
    have hc2R : (H2.edgeSet.ncard : ℝ) ≤
        (H2.comap Sum.inl).edgeSet.ncard + (H2.comap Sum.inr).edgeSet.ncard := by
      exact_mod_cast hc2
    have hc3R : ((H2.comap Sum.inr).edgeSet.ncard : ℝ) ≤ r' := by exact_mod_cast hc3
    have hkR : (k : ℝ) < s := by nlinarith
    have : k < s := by exact_mod_cast hkR
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : ((t + 1).choose 2 : ℝ) ≤ (m - n.choose 2 : ℕ) := by exact_mod_cast hs1
    have h2 : (m - n.choose 2 : ℕ) + 1 ≤ n := by omega
    have h2R : ((m - n.choose 2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h2
    have h3 : (n.choose 2 : ℝ) ≤ m := by exact_mod_cast hn1
    rw [Nat.cast_choose_two] at h1 h3
    push_cast at h1
    have ht0 : (0 : ℝ) ≤ t := by positivity
    have h1' : (t : ℝ) * (t + 1) ≤ 2 * ((m - n.choose 2 : ℕ) : ℝ) := by
      ring_nf at h1 ⊢; linarith
    have ht : (t : ℝ) ^ 2 ≤ 2 * ((n : ℝ) - 1) := by nlinarith
    have hn : ((n : ℝ) - 1) ^ 2 ≤ 2 * m := by nlinarith
    have h0 : (0 : ℝ) ≤ (t : ℝ) ^ 2 := by positivity
    nlinarith

end OMA127

theorem OMA.solution : type_of% @Erdos127.erdos_127.variants.alon_upper := by
  refine ⟨2, fun m => ?_⟩
  obtain ⟨t, ht, h4⟩ := OMA127.key m
  have htR : (Erdos127.f m : ℝ) ≤ t := by exact_mod_cast ht
  refine htR.trans ?_
  by_contra hlt
  push Not at hlt
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hq : (0 : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have h44 : ((m : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = m := by
    have := Real.rpow_inv_natCast_pow (x := (m : ℝ)) (n := 4) hm0 (by norm_num)
    rw [one_div]; exact_mod_cast this
  have : (2 * (m : ℝ) ^ (1 / 4 : ℝ)) ^ 4 < (t : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  rw [mul_pow, h44] at this
  nlinarith
