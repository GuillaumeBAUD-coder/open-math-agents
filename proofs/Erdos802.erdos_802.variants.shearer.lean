import FormalConjectures.ErdosProblems.«802»

-- Problem: Erdős Problem 802 — shearer
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/802.lean:80 (declaration Erdos802.erdos_802.variants.shearer)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset

variable {V : Type*} [DecidableEq V]

/-- Independence of a finset in a graph. -/
abbrev Ind (G : SimpleGraph V) (I : Finset V) : Prop := ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (Ind G) := fun I => by
  unfold Ind; infer_instance

lemma greedy (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (D : ℕ)
    (hD : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D) :
    ∃ I ⊆ S, Ind G I ∧ S.card ≤ (D + 1) * I.card := by
  have hne : (S.powerset.filter (Ind G)).Nonempty := ⟨∅, by simp [Ind]⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [mem_filter, mem_powerset] at hI
  refine ⟨I, hI.1, hI.2, ?_⟩
  have hcover : S ⊆ I ∪ I.biUnion (fun s => S.filter (G.Adj s)) := by
    intro v hv
    by_contra hcon
    simp only [mem_union, mem_biUnion, mem_filter, not_or, not_exists, not_and] at hcon
    obtain ⟨hvI, hadj⟩ := hcon
    have hind : Ind G (insert v I) := by
      intro a ha b hb
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact G.irrefl
      · exact fun h => hadj b hb hv h.symm
      · exact fun h => hadj a ha hv h
      · exact hI.2 a ha b hb
    have := hmax (insert v I)
      (by rw [mem_filter, mem_powerset]; exact ⟨insert_subset hv hI.1, hind⟩)
    rw [card_insert_of_notMem hvI] at this
    omega
  calc S.card ≤ _ := card_le_card hcover
    _ ≤ I.card + (I.biUnion (fun s => S.filter (G.Adj s))).card := card_union_le _ _
    _ ≤ I.card + I.card * D := by
        gcongr
        refine card_biUnion_le.trans ?_
        calc ∑ s ∈ I, (S.filter (G.Adj s)).card ≤ ∑ _s ∈ I, D :=
              sum_le_sum fun s hs => hD s (hI.1 hs)
          _ = I.card * D := by simp
    _ = (D + 1) * I.card := by ring

lemma ramsey (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) : ∀ (s : ℕ) (F : Finset V),
    (∀ T ⊆ F, ¬ G.IsNClique (s + 1) T) → m ^ s ≤ F.card → ∃ I ⊆ F, Ind G I ∧ m ≤ I.card := by
  intro s
  induction s with
  | zero =>
    intro F hF hc
    exfalso
    rw [pow_zero] at hc
    obtain ⟨v, hv⟩ := card_pos.mp hc
    exact hF {v} (by simpa using hv) (by simp [SimpleGraph.isNClique_iff])
  | succ s ih =>
    intro F hF hc
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨∅, by simp, by simp [Ind], by simp⟩
    by_cases h : ∃ v ∈ F, m ^ s ≤ (F.filter (G.Adj v)).card
    · obtain ⟨v, hv, hvc⟩ := h
      obtain ⟨I, hI, hind, hcard⟩ := ih (F.filter (G.Adj v)) (by
        intro T hT hcl
        have := hcl.insert (a := v) (fun b hb => (mem_filter.mp (hT hb)).2)
        refine hF _ ?_ this
        exact insert_subset hv (hT.trans (filter_subset _ _))) hvc
      exact ⟨I, hI.trans (filter_subset _ _), hind, hcard⟩
    · push Not at h
      have hpos : 0 < m ^ s := Nat.pow_pos hm
      obtain ⟨I, hI, hind, hcard⟩ := greedy G F (m ^ s - 1)
        (fun v hv => by have := h v hv; omega)
      refine ⟨I, hI, hind, ?_⟩
      rw [Nat.sub_add_cancel hpos] at hcard
      have : m ^ s * m ≤ m ^ s * I.card := by rw [← pow_succ]; exact hc.trans hcard
      exact Nat.le_of_mul_le_mul_left this hpos

lemma card_small_subsets (F : Finset V) (k : ℕ) :
    (F.powerset.filter (fun A => A.card ≤ k)).card ≤ (F.card + 1) ^ k := by
  induction k with
  | zero =>
    have : F.powerset.filter (fun A => A.card ≤ 0) ⊆ {∅} := by
      intro A hA
      rw [mem_filter] at hA
      rw [mem_singleton]
      exact card_eq_zero.mp (by omega)
    simpa using card_le_card this
  | succ k ih =>
    have hsub : F.powerset.filter (fun A => A.card ≤ k + 1) ⊆
        F.powerset.filter (fun A => A.card ≤ k) ∪ F.powersetCard (k + 1) := by
      intro A hA
      rw [mem_filter, mem_powerset] at hA
      rw [mem_union, mem_filter, mem_powerset, mem_powersetCard]
      rcases Nat.lt_or_ge A.card (k + 1) with h | h
      · left; exact ⟨hA.1, by omega⟩
      · right; exact ⟨hA.1, by omega⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ + _ := card_union_le _ _
      _ ≤ (F.card + 1) ^ k + F.card ^ (k + 1) := by
          gcongr
          rw [card_powersetCard]; exact Nat.choose_le_pow _ _
      _ ≤ (F.card + 1) ^ (k + 1) := by
          have h1 : F.card ^ k ≤ (F.card + 1) ^ k := Nat.pow_le_pow_left (by omega) k
          have h2 := Nat.mul_le_mul_right F.card h1
          rw [pow_succ, pow_succ]; linarith

lemma fiber_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) (hv : v ∈ S)
    (Δ k m q : ℕ) (hK : G.CliqueFree (q + 2))
    (hdeg : (S.filter (G.Adj v)).card ≤ Δ)
    (H1 : k * (2 * (m ^ q) ^ k) ≤ 4 * Δ)
    (H2 : 2 * (Δ + 1) ^ k ≤ 2 ^ m) (J : Finset V) :
    k * ((S.powerset.filter (Ind G)).filter
        (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J)).card
      ≤ 4 * ∑ I ∈ (S.powerset.filter (Ind G)).filter
          (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J),
          ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
  set Φ := (S.powerset.filter (Ind G)).filter
        (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J) with hΦ
  rcases Φ.eq_empty_or_nonempty with h0 | ⟨I0, hI0⟩
  · rw [h0]; simp
  have memΦ : ∀ I, I ∈ Φ ↔
      (I ⊆ S ∧ Ind G I ∧ I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J) := by
    intro I; rw [hΦ, mem_filter, mem_filter, mem_powerset, and_assoc]
  obtain ⟨hI0S, hI0ind, hI0J⟩ := (memΦ I0).mp hI0
  have hJS : J ⊆ S := by rw [← hI0J]; exact (filter_subset _ _).trans hI0S
  have hJind : Ind G J := by
    intro a ha b hb; rw [← hI0J] at ha hb
    exact hI0ind a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
  have hJv : ∀ u ∈ J, u ≠ v ∧ ¬ G.Adj v u := by
    intro u hu; rw [← hI0J] at hu; exact (mem_filter.mp hu).2
  have hdecomp : ∀ I ∈ Φ, v ∉ I → I = J ∪ I.filter (G.Adj v) := by
    intro I hI hvI
    obtain ⟨_, _, hIJ⟩ := (memΦ I).mp hI
    rw [← hIJ]
    ext u
    simp only [mem_union, mem_filter]
    constructor
    · intro hu
      by_cases hadj : G.Adj v u
      · exact Or.inr ⟨hu, hadj⟩
      · exact Or.inl ⟨hu, fun h => hvI (h ▸ hu), hadj⟩
    · rintro (h | h) <;> exact h.1
  have hJsub : ∀ I ∈ Φ, J ⊆ I := by
    intro I hI; rw [← ((memΦ I).mp hI).2.2]; exact filter_subset _ _
  have hIvΦ : insert v J ∈ Φ := by
    rw [memΦ]
    refine ⟨insert_subset hv hJS, ?_, ?_⟩
    · intro a ha b hb
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact G.irrefl
      · exact (hJv b hb).2
      · exact fun h => (hJv a ha).2 h.symm
      · exact hJind a ha b hb
    · ext u
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨h | h, h2⟩
        · exact absurd h h2.1
        · exact h
      · intro h; exact ⟨Or.inr h, hJv u h⟩
  set Φ' := Φ.filter (fun I => ¬ v ∈ I) with hΦ'
  set Φv := Φ.filter (fun I => v ∈ I) with hΦv
  have hcardΦ : Φv.card + Φ'.card = Φ.card := card_filter_add_card_filter_not _
  have hΦv1 : Φv.card ≤ 1 := by
    rw [card_le_one]
    have key : ∀ I ∈ Φv, I = insert v J := by
      intro I hI
      rw [mem_filter] at hI
      obtain ⟨hIΦ, hvI⟩ := hI
      obtain ⟨_, hind, hIJ⟩ := (memΦ I).mp hIΦ
      rw [← hIJ]
      ext u
      simp only [mem_insert, mem_filter]
      constructor
      · intro hu
        by_cases huv : u = v
        · exact Or.inl huv
        · exact Or.inr ⟨hu, huv, hind v hvI u hu⟩
      · rintro (h | h)
        · exact h ▸ hvI
        · exact h.1
    intro a ha b hb; rw [key a ha, key b hb]
  have hsum : ∑ I ∈ Φv, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) +
      ∑ I ∈ Φ', ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) =
      ∑ I ∈ Φ, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
    sum_filter_add_sum_filter_not _ _ _
  have hsumv : Δ ≤ ∑ I ∈ Φv, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
    have hmem : insert v J ∈ Φv := mem_filter.mpr ⟨hIvΦ, mem_insert_self _ _⟩
    refine le_trans ?_ (single_le_sum
      (f := fun I => (if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card)
      (fun _ _ => Nat.zero_le _) hmem)
    simp
  have hsum' : ∑ I ∈ Φ', (I.filter (G.Adj v)).card ≤
      ∑ I ∈ Φ', ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
    sum_le_sum (fun I _ => Nat.le_add_left _ _)
  set F := Φ'.biUnion (fun I => I.filter (G.Adj v)) with hF
  have hFS : F ⊆ S.filter (G.Adj v) := by
    intro u hu
    rw [mem_biUnion] at hu
    obtain ⟨I, hI, huI⟩ := hu
    rw [mem_filter] at huI ⊢
    exact ⟨((memΦ I).mp (mem_filter.mp hI).1).1 huI.1, huI.2⟩
  have hx : F.card ≤ Δ := (card_le_card hFS).trans hdeg
  have hinj : Set.InjOn (fun I : Finset V => I.filter (G.Adj v)) (Φ' : Set (Finset V)) := by
    intro I hI I' hI' heq
    rw [mem_coe, mem_filter] at hI hI'
    have h1 := hdecomp I hI.1 hI.2
    have h2 := hdecomp I' hI'.1 hI'.2
    simp only at heq
    calc I = J ∪ I.filter (G.Adj v) := h1
      _ = J ∪ I'.filter (G.Adj v) := by rw [heq]
      _ = I' := h2.symm
  have hsmall : (Φ'.filter (fun I => (I.filter (G.Adj v)).card ≤ k)).card ≤ (F.card + 1) ^ k := by
    refine le_trans ?_ (card_small_subsets F k)
    refine card_le_card_of_injOn (fun I => I.filter (G.Adj v)) ?_ (hinj.mono ?_)
    · intro I hI
      rw [mem_coe, mem_filter] at hI
      rw [mem_coe, mem_filter, mem_powerset]
      exact ⟨subset_biUnion_of_mem (fun I => I.filter (G.Adj v)) hI.1, hI.2⟩
    · intro I hI
      rw [mem_coe, mem_filter] at hI
      exact mem_coe.mpr hI.1
  have hbig : k * Φ'.card ≤ ∑ I ∈ Φ', (I.filter (G.Adj v)).card + k * (F.card + 1) ^ k := by
    have h1 : (Φ'.filter (fun I => (I.filter (G.Adj v)).card ≤ k)).card +
        (Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k)).card = Φ'.card :=
      card_filter_add_card_filter_not _
    have h2 : k * (Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k)).card ≤
        ∑ I ∈ Φ', (I.filter (G.Adj v)).card := by
      calc _ = ∑ _I ∈ Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k), k := by
            simp [mul_comm]
        _ ≤ ∑ I ∈ Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k),
              (I.filter (G.Adj v)).card :=
            sum_le_sum (fun I hI => by have := (mem_filter.mp hI).2; omega)
        _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
    rw [← h1, mul_add]
    have := Nat.mul_le_mul_left k hsmall
    omega
  by_cases hA : 2 * (F.card + 1) ^ k ≤ Φ'.card
  · have h1 : 2 * (k * (F.card + 1) ^ k) ≤ k * Φ'.card := by
      calc 2 * (k * (F.card + 1) ^ k) = k * (2 * (F.card + 1) ^ k) := by ring
        _ ≤ _ := Nat.mul_le_mul_left k hA
    have hk1 : k * Φ.card ≤ k * (1 + Φ'.card) := Nat.mul_le_mul_left k (by omega)
    have hpos : 0 < (F.card + 1) ^ k := Nat.pow_pos (by omega)
    have hki : k ≤ k * Φ'.card := Nat.le_mul_of_pos_right _ (by omega)
    rw [mul_add, mul_one] at hk1
    omega
  · push Not at hA
    have hk1 : k * Φ.card ≤ k * (2 * (F.card + 1) ^ k) := Nat.mul_le_mul_left k (by omega)
    by_cases hL : F.card < m ^ q
    · have hP : (F.card + 1) ^ k ≤ (m ^ q) ^ k := Nat.pow_le_pow_left hL k
      have : k * (2 * (F.card + 1) ^ k) ≤ k * (2 * (m ^ q) ^ k) :=
        Nat.mul_le_mul_left k (by omega)
      omega
    · exfalso
      push Not at hL
      obtain ⟨A, hAF, hAind, hAm⟩ := ramsey G m q F (by
        intro T hT hcl
        have := hcl.insert (a := v) (fun b hb => (mem_filter.mp (hFS (hT hb))).2)
        exact hK _ this) hL
      have key : ∀ A' ⊆ A, (J ∪ A').filter (G.Adj v) = A' := by
        intro A' hA'
        ext u
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨h | h, h2⟩
          · exact absurd h2 (hJv u h).2
          · exact h
        · intro h; exact ⟨Or.inr h, (mem_filter.mp (hFS (hAF (hA' h)))).2⟩
      have hpow : A.powerset.card ≤ Φ'.card := by
        refine card_le_card_of_injOn (fun A' => J ∪ A') ?_ ?_
        · intro A' hA'
          rw [mem_coe, mem_powerset] at hA'
          have hA'F := hA'.trans hAF
          rw [mem_coe, hΦ', mem_filter, memΦ]
          refine ⟨⟨union_subset hJS (fun u hu => (mem_filter.mp (hFS (hA'F hu))).1), ?_, ?_⟩, ?_⟩
          · intro a ha b hb
            rw [mem_union] at ha hb
            have cross : ∀ a ∈ J, ∀ b ∈ A', ¬ G.Adj a b := by
              intro a ha b hb
              obtain ⟨I, hI, hbI⟩ := mem_biUnion.mp (hA'F hb)
              have hIΦ := (mem_filter.mp hI).1
              exact ((memΦ I).mp hIΦ).2.1 a (hJsub I hIΦ ha) b (mem_filter.mp hbI).1
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact hJind a ha b hb
            · exact cross a ha b hb
            · exact fun h => cross b hb a ha h.symm
            · exact hAind a (hA' ha) b (hA' hb)
          · ext u
            simp only [mem_filter, mem_union]
            constructor
            · rintro ⟨h | h, h2⟩
              · exact h
              · exact absurd (mem_filter.mp (hFS (hA'F h))).2 h2.2
            · intro h; exact ⟨Or.inl h, hJv u h⟩
          · intro hvm
            rw [mem_union] at hvm
            rcases hvm with h | h
            · exact (hJv v h).1 rfl
            · exact G.irrefl (mem_filter.mp (hFS (hA'F h))).2
        · intro A1 h1 A2 h2 heq
          rw [mem_coe, mem_powerset] at h1 h2
          simp only at heq
          calc A1 = (J ∪ A1).filter (G.Adj v) := (key A1 h1).symm
            _ = (J ∪ A2).filter (G.Adj v) := by rw [heq]
            _ = A2 := key A2 h2
      rw [card_powerset] at hpow
      have h3 : 2 ^ m ≤ 2 ^ A.card := Nat.pow_le_pow_right (by norm_num) hAm
      have h4 : (F.card + 1) ^ k ≤ (Δ + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      omega

lemma main_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (Δ k m q : ℕ) (hK : G.CliqueFree (q + 2))
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ Δ)
    (H1 : k * (2 * (m ^ q) ^ k) ≤ 4 * Δ)
    (H2 : 2 * (Δ + 1) ^ k ≤ 2 ^ m) :
    ∃ I ⊆ S, Ind G I ∧ k * S.card ≤ 8 * Δ * I.card := by
  set 𝓘 := S.powerset.filter (Ind G) with h𝓘
  have hne : 𝓘.Nonempty := ⟨∅, by simp [h𝓘, Ind]⟩
  have hv : ∀ v ∈ S, k * 𝓘.card ≤
      4 * ∑ I ∈ 𝓘, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
    intro v hv
    have hmaps : (𝓘 : Set (Finset V)).MapsTo
        (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u))
        (𝓘.image (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)) : Finset (Finset V)) :=
      fun I hI => mem_coe.mpr (mem_image_of_mem _ hI)
    rw [card_eq_sum_card_fiberwise hmaps, ← sum_fiberwise_of_maps_to hmaps, mul_sum, mul_sum]
    exact sum_le_sum (fun J _ => fiber_bound G S v hv Δ k m q hK (hdeg v hv) H1 H2 J)
  have hI : ∀ I ∈ 𝓘, ∑ v ∈ S, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card)
      ≤ 2 * Δ * I.card := by
    intro I hI
    rw [h𝓘, mem_filter, mem_powerset] at hI
    rw [sum_add_distrib]
    have h1 : ∑ v ∈ S, (if v ∈ I then Δ else 0) = I.card * Δ := by
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hI.1]; simp
    have h2 : ∑ v ∈ S, (I.filter (G.Adj v)).card = ∑ u ∈ I, (S.filter (G.Adj u)).card := by
      simp only [card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
      simp only [SimpleGraph.adj_comm]
    have h3 : ∑ u ∈ I, (S.filter (G.Adj u)).card ≤ I.card * Δ := by
      calc _ ≤ ∑ _u ∈ I, Δ := sum_le_sum fun u hu => hdeg u (hI.1 hu)
        _ = _ := by simp
    rw [h1, h2]; linarith
  by_contra hcon
  push Not at hcon
  have hlt : ∀ I ∈ 𝓘, 8 * Δ * I.card < k * S.card := fun I hI => by
    rw [h𝓘, mem_filter, mem_powerset] at hI; exact hcon I hI.1 hI.2
  have hsumlt : ∑ I ∈ 𝓘, 8 * Δ * I.card < ∑ _I ∈ 𝓘, k * S.card :=
    sum_lt_sum_of_nonempty hne hlt
  have htot : S.card * (k * 𝓘.card) ≤ 4 * ∑ I ∈ 𝓘, 2 * Δ * I.card := by
    calc S.card * (k * 𝓘.card) = ∑ _v ∈ S, k * 𝓘.card := by simp
      _ ≤ ∑ v ∈ S, 4 * ∑ I ∈ 𝓘, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
          sum_le_sum hv
      _ = 4 * ∑ I ∈ 𝓘, ∑ v ∈ S, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
          rw [← mul_sum, sum_comm]
      _ ≤ _ := Nat.mul_le_mul_left 4 (sum_le_sum hI)
  simp only [sum_const, smul_eq_mul, ← mul_sum] at hsumlt htot
  nlinarith

lemma numerics (q D k : ℕ) (hq : 1 ≤ q) (hD : D ≠ 0)
    (hk : k = Nat.log 2 D / (8 * q * (Nat.log 2 (Nat.log 2 D) + 1))) (hk1 : 1 ≤ k) :
    k * (2 * ((1 + (Nat.log 2 D + 1) * k) ^ q) ^ k) ≤ 4 * D ∧
      2 * (D + 1) ^ k ≤ 2 ^ (1 + (Nat.log 2 D + 1) * k) := by
  set l := Nat.log 2 D with hl
  set a := Nat.log 2 l + 1 with ha
  have hl1 : 2 ^ l ≤ D := Nat.pow_log_le_self 2 hD
  have hl2 : D < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have h8 : k * (8 * q * a) ≤ l := by rw [hk]; exact Nat.div_mul_le_self _ _
  have ha1 : 1 ≤ a := by omega
  have hqa : 1 ≤ q * a := Nat.mul_pos hq ha1
  have hz1 : a ≤ q * a * k := by
    calc a = 1 * a * 1 := by ring
      _ ≤ q * a * k := Nat.mul_le_mul (Nat.mul_le_mul hq le_rfl) hk1
  have e1 : a * 2 * q * k = 2 * (q * a * k) := by ring
  have e2 : k * (8 * q * a) = 8 * (q * a * k) := by ring
  have hkz : k ≤ q * a * k := by
    calc k = 1 * k := by ring
      _ ≤ q * a * k := Nat.mul_le_mul hqa le_rfl
  have hkl : k ≤ l := by omega
  have hla : l < 2 ^ a := Nat.lt_pow_succ_log_self (by norm_num) l
  constructor
  · have hm : 1 + (l + 1) * k ≤ (2 ^ a) ^ 2 := by
      have h1 : l + 1 ≤ 2 ^ a := hla
      have h2 := Nat.mul_le_mul_left (l + 1) hkl
      have h3 := Nat.mul_le_mul h1 h1
      nlinarith
    have h1 : ((1 + (l + 1) * k) ^ q) ^ k ≤ 2 ^ (a * 2 * q * k) := by
      calc _ ≤ (((2 ^ a) ^ 2) ^ q) ^ k := Nat.pow_le_pow_left (Nat.pow_le_pow_left hm q) k
        _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
    have hexp : a + 1 + a * 2 * q * k ≤ l + 2 := by omega
    calc k * (2 * ((1 + (l + 1) * k) ^ q) ^ k) ≤ 2 ^ a * (2 * 2 ^ (a * 2 * q * k)) := by
          gcongr; omega
      _ = 2 ^ (a + 1 + a * 2 * q * k) := by ring
      _ ≤ 2 ^ (l + 2) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = 4 * 2 ^ l := by ring
      _ ≤ 4 * D := by omega
  · calc 2 * (D + 1) ^ k ≤ 2 * (2 ^ (l + 1)) ^ k := by gcongr; omega
      _ = 2 ^ (1 + (l + 1) * k) := by rw [← pow_mul, pow_add, pow_one]

lemma real_ineq (t : ℝ) (ht : 2 ≤ t) :
    Real.log t ≤ (Nat.log 2 ⌊2 * t⌋₊ : ℝ) ∧
    ((Nat.log 2 (Nat.log 2 ⌊2 * t⌋₊) : ℕ) : ℝ) + 1 ≤ 40 * Real.log (Real.log (t + 1)) ∧
    0 < Real.log (Real.log (t + 1)) := by
  set D := ⌊2 * t⌋₊ with hD
  set l := Nat.log 2 D with hl
  have hDle : (D : ℝ) ≤ 2 * t := Nat.floor_le (by linarith)
  have hDlt : 2 * t < D + 1 := Nat.lt_floor_add_one _
  have hD4 : 4 ≤ D := Nat.le_floor (by push_cast; linarith)
  have hl1 : 2 ^ l ≤ D := Nat.pow_log_le_self 2 (by omega)
  have hl2 : D < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have hl0 : l ≠ 0 := by
    intro h; rw [h] at hl2; omega
  have hlam1 : 2 ^ (Nat.log 2 l) ≤ l := Nat.pow_log_le_self 2 hl0
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2' : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hx : (12:ℝ) / 11 ≤ Real.log (t + 1) := by
    have h3 := Real.log_three_gt_d9
    have : Real.log 3 ≤ Real.log (t + 1) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set x := Real.log (t + 1) with hxdef
  have hy : (1:ℝ) / 12 ≤ Real.log x := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < x by linarith)
    have h2 : x⁻¹ ≤ 11 / 12 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
    linarith
  refine ⟨?_, ?_, by linarith⟩
  · have h1 : t < 2 ^ l := by
      have : ((D + 1 : ℕ) : ℝ) ≤ ((2 ^ (l + 1) : ℕ) : ℝ) := by exact_mod_cast hl2
      push_cast at this
      rw [pow_succ] at this; linarith
    have h2 : Real.log t ≤ Real.log (2 ^ l) := Real.log_le_log (by linarith) h1.le
    rw [Real.log_pow] at h2
    have : (l:ℝ) * Real.log 2 ≤ l * 1 := by gcongr
    linarith
  · have hlR : (l:ℝ) * Real.log 2 ≤ 2 * x := by
      have h1 : ((2 ^ l : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hl1
      push_cast at h1
      have h2 : (2:ℝ) ^ l ≤ (t + 1) ^ 2 := by nlinarith
      have h3 := Real.log_le_log (by positivity) h2
      rw [Real.log_pow, Real.log_pow] at h3
      push_cast at h3; linarith
    have hl4 : (l:ℝ) ≤ 4 * x := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) l) (by linarith : (0:ℝ) ≤ Real.log 2 - 1 / 2)]
    have hlpos : (0:ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl0
    have h5 : Real.log l ≤ Real.log (4 * x) := Real.log_le_log hlpos hl4
    rw [Real.log_mul (by norm_num) (by linarith)] at h5
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h6 : ((Nat.log 2 l : ℕ) : ℝ) * Real.log 2 ≤ Real.log l := by
      have h1 : ((2 ^ (Nat.log 2 l) : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlam1
      push_cast at h1
      have := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow] at this
    have h7 : ((Nat.log 2 l : ℕ) : ℝ) - 2 ≤ 2 * Real.log x := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ((Nat.log 2 l : ℕ) : ℝ) - 2)
        (by linarith : (0:ℝ) ≤ Real.log 2 - 1 / 2)]
    linarith

lemma core (q : ℕ) (hq : 1 ≤ q) {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hK : G.CliqueFree (q + 2)) (ht : 2 ≤ G.averageDegree) :
    (1 / (20480 * q : ℝ)) * (Real.log G.averageDegree /
      (Real.log (Real.log (G.averageDegree + 1)) * G.averageDegree)) * Fintype.card V
      ≤ G.indepNum := by
  have ht2' : (2:ℝ) ≤ (G.averageDegree : ℝ) := by exact_mod_cast ht
  set t : ℝ := (G.averageDegree : ℝ) with htdef
  have ht2 : (2:ℝ) ≤ t := ht2'
  obtain ⟨hlogt, hlam, hy⟩ := real_ineq t ht2
  set D := ⌊2 * t⌋₊ with hD
  set l := Nat.log 2 D with hl
  set a := Nat.log 2 l + 1 with ha
  have hDle : (D : ℝ) ≤ 2 * t := Nat.floor_le (by linarith)
  have hDlt : 2 * t < D + 1 := Nat.lt_floor_add_one _
  have hD4 : 4 ≤ D := Nat.le_floor (by push_cast; linarith)
  have hn : (0:ℝ) < Fintype.card V := by
    rw [Nat.cast_pos, Fintype.card_pos_iff]
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have : G.averageDegree = 0 := by simp [SimpleGraph.averageDegree]
    rw [this] at ht; norm_num at ht
  have hsum : (∑ v, (G.degree v : ℝ)) = t * Fintype.card V := by
    rw [htdef, SimpleGraph.averageDegree]; push_cast; field_simp
  set S := (univ : Finset V).filter (fun v => G.degree v ≤ D) with hS
  have hSn : Fintype.card V ≤ 2 * S.card := by
    have hc : S.card + (univ.filter (fun v => ¬ G.degree v ≤ D)).card = Fintype.card V := by
      rw [hS, card_filter_add_card_filter_not, card_univ]
    have h1 : ((univ.filter (fun v => ¬ G.degree v ≤ D)).card : ℝ) * (2 * t) ≤
        ∑ v, (G.degree v : ℝ) := by
      calc _ = ∑ _v ∈ univ.filter (fun v => ¬ G.degree v ≤ D), (2 * t) := by simp
        _ ≤ ∑ v ∈ univ.filter (fun v => ¬ G.degree v ≤ D), (G.degree v : ℝ) := by
            refine sum_le_sum fun v hv => ?_
            have h := (mem_filter.mp hv).2
            have : (D : ℝ) + 1 ≤ G.degree v := by
              exact_mod_cast (by omega : D + 1 ≤ G.degree v)
            linarith
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => by positivity)
    rw [hsum] at h1
    have h2 : ((univ.filter (fun v => ¬ G.degree v ≤ D)).card : ℝ) * 2 ≤ Fintype.card V := by
      nlinarith
    have h3 : (Fintype.card V : ℝ) ≤ 2 * S.card := by
      have h4 : ((S.card + (univ.filter (fun v => ¬ G.degree v ≤ D)).card : ℕ) : ℝ) =
          Fintype.card V := by rw [hc]
      push_cast at h4; linarith
    exact_mod_cast h3
  have hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D := by
    intro v hv
    calc (S.filter (G.Adj v)).card ≤ (univ.filter (G.Adj v)).card :=
          card_le_card (filter_subset_filter _ (subset_univ _))
      _ = G.degree v := by
          rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ D := (mem_filter.mp hv).2
  have hα : ∀ I : Finset V, Ind G I → I.card ≤ G.indepNum := by
    intro I hI
    have : G.IsIndepSet (I : Set V) := fun a ha b hb _ => hI a ha b hb
    exact this.card_le_indepNum
  set k := l / (8 * q * a) with hk
  have hb : 0 < 8 * q * a := by positivity
  have hlk : l < (k + 1) * (8 * q * a) := by
    rw [← Nat.div_lt_iff_lt_mul hb]; omega
  have key : l * Fintype.card V ≤ 256 * q * a * D * G.indepNum := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · obtain ⟨I, _, hI, hc⟩ := greedy G S D hdeg
      have hIα := hα I hI
      rw [hk0] at hlk
      calc l * Fintype.card V ≤ (8 * q * a) * (2 * S.card) := Nat.mul_le_mul (by omega) hSn
        _ ≤ (8 * q * a) * (2 * ((D + 1) * G.indepNum)) := by
            gcongr; exact hc.trans (Nat.mul_le_mul_left _ hIα)
        _ ≤ (8 * q * a) * (2 * ((2 * D) * G.indepNum)) := by gcongr; omega
        _ ≤ _ := by nlinarith [Nat.zero_le (q * a * D * G.indepNum)]
    · obtain ⟨hH1, hH2⟩ := numerics q D k hq (by omega) hk hk1
      obtain ⟨I, _, hI, hc⟩ := main_bound G S D k _ q hK hdeg hH1 hH2
      have hIα := hα I hI
      have hl2k : l ≤ 2 * k * (8 * q * a) := by
        have := Nat.mul_le_mul_right (8 * q * a) (show k + 1 ≤ 2 * k by omega)
        omega
      calc l * Fintype.card V ≤ (2 * k * (8 * q * a)) * (2 * S.card) := Nat.mul_le_mul hl2k hSn
        _ = 32 * q * a * (k * S.card) := by ring
        _ ≤ 32 * q * a * (8 * D * G.indepNum) :=
            Nat.mul_le_mul_left _ (hc.trans (Nat.mul_le_mul_left _ hIα))
        _ = _ := by ring
  have keyR : (l:ℝ) * Fintype.card V ≤ 256 * q * a * D * G.indepNum := by exact_mod_cast key
  have haR : (a:ℝ) ≤ 40 * Real.log (Real.log (t + 1)) := by rw [ha]; push_cast; exact hlam
  set y := Real.log (Real.log (t + 1)) with hy'
  have hfin : Real.log t * Fintype.card V ≤ 20480 * q * y * t * G.indepNum := by
    calc Real.log t * Fintype.card V ≤ l * Fintype.card V := by gcongr
      _ ≤ 256 * q * a * D * G.indepNum := keyR
      _ ≤ 256 * q * (40 * y) * (2 * t) * G.indepNum := by gcongr
      _ = _ := by ring
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  rw [show (1 / (20480 * q : ℝ)) * (Real.log t / (y * t)) * Fintype.card V =
    (Real.log t * Fintype.card V) / (20480 * q * y * t) by field_simp]
  rw [div_le_iff₀ (by positivity)]
  linarith

end OMA

theorem OMA.solution : type_of% @Erdos802.erdos_802.variants.shearer := by
  classical
  intro r
  rcases Nat.lt_or_ge r 3 with hr | hr
  · refine ⟨1, one_pos, ?_⟩
    intro n G hK ht
    exfalso
    have hK2 : G.CliqueFree 2 := hK.mono (by omega)
    rw [SimpleGraph.cliqueFree_two] at hK2
    have h0 : G.averageDegree = 0 := by
      unfold SimpleGraph.averageDegree
      have hd : ∀ v, G.degree v = 0 := by
        intro v
        rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
        ext w; simp [hK2]
      simp [hd]
    rw [h0] at ht; norm_num at ht
  · obtain ⟨q, rfl⟩ : ∃ q, r = q + 2 := ⟨r - 2, by omega⟩
    have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    refine ⟨1 / (20480 * q), by positivity, ?_⟩
    intro n G hK ht
    have := @OMA.core q (by omega) _ _ _ G _ hK ht
    simpa using this
