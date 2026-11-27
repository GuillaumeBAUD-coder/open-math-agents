import FormalConjectures.ErdosProblems.«926»

-- Problem: Erdős Problem 926 — aks
-- Credit: @senamakel
-- Proof: the Alon–Krivelevich–Sudakov argument (CPC 2003, Theorem 6.1, case t = 2, s = 1):
-- a bipartite subgraph with half the edges, a random common neighbourhood of two vertices,
-- a random k-subset with small weighted count of low-codegree pairs, and Hall's theorem.
open Finset SimpleGraph


namespace OMA926
open Erdos926
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def nb (P S : Finset V) : Finset V := P.filter (fun z => ∀ y ∈ S, G.Adj z y)

noncomputable def wt (P : Finset V) (M : ℕ) (S : Finset V) : ℝ :=
  if #(nb G P S) ≤ M then 1 / (#(nb G P S) : ℝ) else 0

noncomputable def Ysum (P : Finset V) (M : ℕ) (U : Finset V) : ℝ :=
  ∑ S ∈ U.powersetCard 2, wt G P M S

lemma wt_nonneg (P : Finset V) (M : ℕ) (S : Finset V) : 0 ≤ wt G P M S := by
  unfold wt; split_ifs <;> positivity

lemma emb (k : ℕ) (P Q : Finset V) (hPQ : Disjoint P Q) (a : V) (ha : a ∈ P)
    (U1 : Finset V) (hU1Q : U1 ⊆ Q) (hcard : #U1 = k) (hadj : ∀ y ∈ U1, G.Adj a y)
    (hY : Ysum G P (k * k) U1 < 1) : (H k) ⊑ G := by
  classical
  let ι := {S // S ∈ U1.powersetCard 2}
  let t : ι → Finset V := fun S => (nb G P S.1).erase a
  have ha_nb : ∀ S : ι, a ∈ nb G P S.1 := by
    intro S
    have hS := (mem_powersetCard.1 S.2).1
    simp only [nb, mem_filter]
    exact ⟨ha, fun y hy => hadj y (hS hy)⟩
  have hall : ∀ F : Finset ι, #F ≤ #(F.biUnion t) := by
    intro F
    by_contra hlt
    push Not at hlt
    have hFpos : 0 < #F := lt_of_le_of_lt (Nat.zero_le _) hlt
    have hFle : #F ≤ k * k := by
      have h1 : #F ≤ #(univ : Finset ι) := card_le_univ F
      have h2 : #(univ : Finset ι) = k.choose 2 := by
        rw [card_univ, Fintype.card_coe, card_powersetCard, hcard]
      have h3 : k.choose 2 ≤ k * k := by
        rw [Nat.choose_two_right]
        exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      omega
    have hnbS : ∀ S ∈ F, #(nb G P S.1) ≤ #F := by
      intro S hS
      have h1 : #(t S) ≤ #(F.biUnion t) := card_le_card (subset_biUnion_of_mem t hS)
      have h2 : #(t S) + 1 = #(nb G P S.1) := card_erase_add_one (ha_nb S)
      omega
    have hwt : ∀ S ∈ F, (1 : ℝ) / #F ≤ wt G P (k * k) S.1 := by
      intro S hS
      have h1 := hnbS S hS
      have h0 : 0 < #(nb G P S.1) := card_pos.2 ⟨a, ha_nb S⟩
      unfold wt
      rw [if_pos (h1.trans hFle)]
      apply one_div_le_one_div_of_le
      · exact_mod_cast h0
      · exact_mod_cast h1
    have hsum1 : (1 : ℝ) ≤ ∑ S ∈ F, wt G P (k * k) S.1 := by
      have := Finset.card_nsmul_le_sum F (fun S => wt G P (k * k) S.1) _ hwt
      rw [nsmul_eq_mul] at this
      have hF : ((#F : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hFpos.ne'
      rwa [mul_one_div_cancel hF] at this
    have hsum2 : ∑ S ∈ F, wt G P (k * k) S.1 ≤ Ysum G P (k * k) U1 := by
      unfold Ysum
      calc ∑ S ∈ F, wt G P (k * k) S.1 ≤ ∑ S : ι, wt G P (k * k) S.1 :=
            sum_le_sum_of_subset_of_nonneg (subset_univ F) (fun S _ _ => wt_nonneg G P _ S.1)
        _ = ∑ S ∈ U1.powersetCard 2, wt G P (k * k) S :=
            Finset.sum_coe_sort (U1.powersetCard 2) (wt G P (k * k))
    linarith
  obtain ⟨f, hfinj, hfmem⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hfP : ∀ S : ι, f S ∈ P ∧ f S ≠ a ∧ ∀ y ∈ S.1, G.Adj (f S) y := by
    intro S
    have h := hfmem S
    simp only [t, mem_erase, nb, mem_filter] at h
    exact ⟨h.2.1, h.1, h.2.2⟩
  let e : Fin k → V := fun i => (U1.equivFin.symm (Fin.cast hcard.symm i) : V)
  have he_mem : ∀ i, e i ∈ U1 := fun i => (U1.equivFin.symm (Fin.cast hcard.symm i)).2
  have he_inj : Function.Injective e := by
    intro i j hij
    have := Subtype.ext hij
    simpa using this
  have he_Q : ∀ i, e i ∈ Q := fun i => hU1Q (he_mem i)
  have hpair : ∀ p : {p : Fin k × Fin k // p.1 < p.2},
      ({e p.1.1, e p.1.2} : Finset V) ∈ U1.powersetCard 2 := by
    intro p
    rw [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl <;> exact he_mem _
    · exact card_pair (fun h => (ne_of_lt p.2) (he_inj h))
  let Sp : {p : Fin k × Fin k // p.1 < p.2} → ι := fun p => ⟨_, hpair p⟩
  have hSp_inj : Function.Injective Sp := by
    intro p q hpq
    have h : ({e p.1.1, e p.1.2} : Finset V) = {e q.1.1, e q.1.2} := congrArg Subtype.val hpq
    have h1 : e p.1.1 ∈ ({e q.1.1, e q.1.2} : Finset V) := h ▸ (by simp)
    have h2 : e p.1.2 ∈ ({e q.1.1, e q.1.2} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at h1 h2
    have hp := p.2; have hq := q.2
    apply Subtype.ext
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      have h1' := he_inj h1 <;> have h2' := he_inj h2
    · exact absurd (h1'.trans h2'.symm) (ne_of_lt hp)
    · exact Prod.ext h1' h2'
    · rw [h1', h2'] at hp; exact absurd (hp.trans hq) (lt_irrefl _)
    · exact absurd (h1'.trans h2'.symm) (ne_of_lt hp)
  let φ : Unit ⊕ (Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2}) → V := fun x =>
    match x with
    | Sum.inl _ => a
    | Sum.inr (Sum.inl i) => e i
    | Sum.inr (Sum.inr p) => f (Sp p)
  have hφ : ∀ x y, (H k).Adj x y → G.Adj (φ x) (φ y) := by
    intro x y hxy
    rcases x with _ | i | p <;> rcases y with _ | j | q <;> simp [H] at hxy
    · exact hadj _ (he_mem j)
    · exact (hadj _ (he_mem i)).symm
    · refine ((hfP (Sp q)).2.2 (e i) ?_).symm
      rcases hxy with rfl | rfl <;> simp [Sp]
    · refine ((hfP (Sp p)).2.2 (e j) ?_)
      rcases hxy with rfl | rfl <;> simp [Sp]
  have hφinj : Function.Injective φ := by
    have hdisj : ∀ {u}, u ∈ P → u ∈ Q → False := fun hu hv => disjoint_left.1 hPQ hu hv
    intro x y hxy
    rcases x with ⟨⟩ | i | p <;> rcases y with ⟨⟩ | j | q <;> simp only [φ] at hxy
    · rfl
    · exact (hdisj ha (hxy ▸ he_Q j)).elim
    · exact ((hfP (Sp q)).2.1 hxy.symm).elim
    · exact (hdisj ha (hxy ▸ he_Q i)).elim
    · rw [he_inj hxy]
    · exact (hdisj (hfP (Sp q)).1 (hxy ▸ he_Q i)).elim
    · exact ((hfP (Sp p)).2.1 hxy).elim
    · exact (hdisj (hfP (Sp p)).1 (hxy ▸ he_Q j)).elim
    · rw [hSp_inj (hfinj hxy)]
  exact ⟨⟨⟨φ, fun {x y} h => hφ x y h⟩, hφinj⟩⟩


lemma avg (P : Finset V) (M k : ℕ) (hk : 2 ≤ k) (U : Finset V) (hX : 4 * k * k < #U)
    (hY : Ysum G P M U < 2 * #U) : ∃ U1 ⊆ U, #U1 = k ∧ Ysum G P M U1 < 1 := by
  classical
  by_contra hcon
  push Not at hcon
  set A := U.powersetCard k with hA
  have h1 : ((#A : ℕ) : ℝ) ≤ ∑ U1 ∈ A, Ysum G P M U1 := by
    have := Finset.card_nsmul_le_sum A (fun U1 => Ysum G P M U1) 1 (by
      intro U1 hU1
      rw [hA, mem_powersetCard] at hU1
      exact hcon U1 hU1.1 hU1.2)
    simpa using this
  have h2 : ∑ U1 ∈ A, Ysum G P M U1 =
      ∑ S ∈ U.powersetCard 2, ((#(A.filter (fun U1 => S ⊆ U1)) : ℕ) : ℝ) * wt G P M S := by
    unfold Ysum
    rw [Finset.sum_comm' (t' := U.powersetCard 2) (s' := fun S => A.filter (fun U1 => S ⊆ U1))]
    · apply sum_congr rfl
      intro S _
      rw [sum_const, nsmul_eq_mul]
    · intro U1 S
      simp only [hA, mem_powersetCard, mem_filter]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨⟨h1, h2⟩, h3⟩, h3.trans h1, h4⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, _, h4⟩
        exact ⟨⟨h1, h2⟩, h3, h4⟩
  set X := #U with hXdef
  have hkX : k ≤ X := by nlinarith
  have h3 : ∀ S ∈ U.powersetCard 2, #(A.filter (fun U1 => S ⊆ U1)) = (X - 2).choose (k - 2) := by
    intro S hS
    rw [mem_powersetCard] at hS
    rw [hA, card_filter_powersetCard_subset S U k hS.1 (by omega), hS.2]
  have h4 : ∑ U1 ∈ A, Ysum G P M U1 = ((X - 2).choose (k - 2) : ℝ) * Ysum G P M U := by
    rw [h2, Ysum, mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [h3 S hS]
  have hAcard : #A = X.choose k := by rw [hA, card_powersetCard]
  have hc : 0 < (X - 2).choose (k - 2) := Nat.choose_pos (by omega)
  have hid : X.choose k * k.choose 2 = X.choose 2 * (X - 2).choose (k - 2) := Nat.choose_mul hk
  have hid' : ((X.choose k : ℕ) : ℝ) * (k * (k - 1) / 2) =
      (X * (X - 1) / 2) * ((X - 2).choose (k - 2) : ℕ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_choose_two] at this
    linarith
  rw [h4, hAcard] at h1
  have hYnn : 0 ≤ Ysum G P M U := sum_nonneg (fun S _ => wt_nonneg G P M S)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hXR : (4 * k * k : ℝ) < X := by exact_mod_cast hX
  have hcR : (0 : ℝ) < ((X - 2).choose (k - 2) : ℕ) := by exact_mod_cast hc
  have hkey : Ysum G P M U * (k * (k - 1) / 2) < X * (X - 1) / 2 := by
    have : Ysum G P M U * (k * (k - 1) / 2) < 2 * X * (k * (k - 1) / 2) := by
      apply mul_lt_mul_of_pos_right hY; nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ k * (k - 1) / 2 by nlinarith)
  rw [hid'] at this
  nlinarith

def deg (S : Finset V) (v : V) : ℕ := #(S.filter (G.Adj v))

def Ucn (Q : Finset V) (a b : V) : Finset V := Q.filter (fun v => G.Adj a v ∧ G.Adj b v)

lemma sumX (P Q : Finset V) :
    ∑ a ∈ P, ∑ b ∈ P, ((#(Ucn G Q a b) : ℕ) : ℝ) = ∑ v ∈ Q, ((deg G P v : ℕ) : ℝ) ^ 2 := by
  have h1 : ∀ a b, ((#(Ucn G Q a b) : ℕ) : ℝ) =
      ∑ v ∈ Q, (if G.Adj v a then (1:ℝ) else 0) * (if G.Adj v b then (1:ℝ) else 0) := by
    intro a b
    rw [Ucn, card_filter]
    push_cast
    apply sum_congr rfl
    intro v _
    by_cases h1 : G.Adj a v <;> by_cases h2 : G.Adj b v <;>
      simp [h1, h2, G.adj_comm v a, G.adj_comm v b]
  have h2 : ∀ v, ((deg G P v : ℕ) : ℝ) = ∑ a ∈ P, (if G.Adj v a then (1:ℝ) else 0) := by
    intro v; rw [deg, card_filter]; push_cast; rfl
  simp_rw [h1, h2, sq, sum_mul_sum]
  calc _ = ∑ a ∈ P, ∑ v ∈ Q, ∑ b ∈ P,
        (if G.Adj v a then (1:ℝ) else 0) * (if G.Adj v b then (1:ℝ) else 0) :=
          sum_congr rfl (fun a _ => sum_comm)
    _ = _ := sum_comm

lemma sumY (P Q : Finset V) (M : ℕ) :
    ∑ a ∈ P, ∑ b ∈ P, Ysum G P M (Ucn G Q a b) ≤ ∑ z ∈ P, ((deg G Q z : ℕ) : ℝ) ^ 2 / 2 := by
  classical
  let pr : Finset V → V → Prop := fun S a => ∀ y ∈ S, G.Adj a y
  have hU : ∀ a ∈ P, ∀ b ∈ P, (Ucn G Q a b).powersetCard 2 =
      (Q.powersetCard 2).filter (fun S => pr S a ∧ pr S b) := by
    intro a _ b _
    ext S
    simp only [mem_powersetCard, mem_filter, Ucn, subset_iff, pr]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun y hy => (h1 hy).1, h2⟩, fun y hy => (h1 hy).2.1, fun y hy => (h1 hy).2.2⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨fun y hy => ⟨h1 hy, h3 y hy, h4 y hy⟩, h2⟩
  have hstep : ∑ a ∈ P, ∑ b ∈ P, Ysum G P M (Ucn G Q a b) =
      ∑ S ∈ Q.powersetCard 2, ((#(nb G P S) : ℕ) : ℝ) ^ 2 * wt G P M S := by
    have e1 : ∀ a ∈ P, ∑ b ∈ P, Ysum G P M (Ucn G Q a b) =
        ∑ b ∈ P, ∑ S ∈ Q.powersetCard 2,
          (if pr S a then (1:ℝ) else 0) * ((if pr S b then (1:ℝ) else 0) * wt G P M S) := by
      intro a ha
      apply sum_congr rfl
      intro b hb
      rw [Ysum, hU a ha b hb, sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases h1 : pr S a <;> by_cases h2 : pr S b <;> simp [h1, h2]
    rw [sum_congr rfl e1]
    have e2 : ∀ S : Finset V, ((#(nb G P S) : ℕ) : ℝ) = ∑ a ∈ P, (if pr S a then (1:ℝ) else 0) := by
      intro S; rw [nb, card_filter]; push_cast; rfl
    simp_rw [e2, sq, sum_mul_sum, sum_mul]
    calc _ = ∑ a ∈ P, ∑ S ∈ Q.powersetCard 2, ∑ b ∈ P,
          (if pr S a then (1:ℝ) else 0) * ((if pr S b then (1:ℝ) else 0) * wt G P M S) :=
            sum_congr rfl (fun a _ => sum_comm)
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl; intro S _
        apply sum_congr rfl; intro a _
        apply sum_congr rfl; intro b _
        ring
  rw [hstep]
  have hterm : ∀ S, ((#(nb G P S) : ℕ) : ℝ) ^ 2 * wt G P M S ≤ ((#(nb G P S) : ℕ) : ℝ) := by
    intro S
    unfold wt
    split_ifs
    · rcases Nat.eq_zero_or_pos (#(nb G P S)) with h0 | h0
      · simp [h0]
      · have : ((#(nb G P S) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
        field_simp; rfl
    · simp
  have hcount : ∑ S ∈ Q.powersetCard 2, ((#(nb G P S) : ℕ) : ℝ) =
      ∑ z ∈ P, (((deg G Q z).choose 2 : ℕ) : ℝ) := by
    have e3 : ∀ S : Finset V, ((#(nb G P S) : ℕ) : ℝ) = ∑ z ∈ P, (if pr S z then (1:ℝ) else 0) := by
      intro S; rw [nb, card_filter]; push_cast; rfl
    simp_rw [e3]
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, deg, ← card_powersetCard]
    congr 2
    ext S
    simp only [mem_filter, mem_powersetCard, subset_iff, pr]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun y hy => ⟨h1 hy, h3 y hy⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨fun y hy => (h1 hy).1, h2⟩, fun y hy => (h1 hy).2⟩
  calc _ ≤ ∑ S ∈ Q.powersetCard 2, ((#(nb G P S) : ℕ) : ℝ) := sum_le_sum (fun S _ => hterm S)
    _ = _ := hcount
    _ ≤ _ := by
      apply sum_le_sum; intro z _
      rw [Nat.cast_choose_two]
      have : (0:ℝ) ≤ ((deg G Q z : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith

lemma core (k : ℕ) (hk : 2 ≤ k) (P Q : Finset V) (hPQ : Disjoint P Q)
    (hsq : ∑ z ∈ P, ((deg G Q z : ℕ) : ℝ) ^ 2 ≤ ∑ v ∈ Q, ((deg G P v : ℕ) : ℝ) ^ 2)
    (hbig : 16 * (k : ℝ) ^ 2 * (#P : ℝ) ^ 2 < 3 * ∑ v ∈ Q, ((deg G P v : ℕ) : ℝ) ^ 2) :
    (H k) ⊑ G := by
  classical
  have hX := sumX G P Q
  have hY := sumY G P Q (k * k)
  have hex : ∃ a ∈ P, ∃ b ∈ P, 0 < ((#(Ucn G Q a b) : ℕ) : ℝ) -
      Ysum G P (k * k) (Ucn G Q a b) / 2 - 4 * (k : ℝ) ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hle : ∑ a ∈ P, ∑ b ∈ P, (((#(Ucn G Q a b) : ℕ) : ℝ) -
        Ysum G P (k * k) (Ucn G Q a b) / 2 - 4 * (k : ℝ) ^ 2) ≤ 0 :=
      sum_nonpos (fun a ha => sum_nonpos (fun b hb => hcon a ha b hb))
    have heq : ∑ a ∈ P, ∑ b ∈ P, (((#(Ucn G Q a b) : ℕ) : ℝ) -
        Ysum G P (k * k) (Ucn G Q a b) / 2 - 4 * (k : ℝ) ^ 2) =
        (∑ a ∈ P, ∑ b ∈ P, ((#(Ucn G Q a b) : ℕ) : ℝ)) -
        (∑ a ∈ P, ∑ b ∈ P, Ysum G P (k * k) (Ucn G Q a b)) / 2 -
        4 * (k : ℝ) ^ 2 * (#P : ℝ) ^ 2 := by
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, sum_div]
      ring
    rw [heq, hX] at hle
    have : ∑ z ∈ P, ((deg G Q z : ℕ) : ℝ) ^ 2 / 2 = (∑ z ∈ P, ((deg G Q z : ℕ) : ℝ) ^ 2) / 2 := by
      rw [sum_div]
    linarith
  obtain ⟨a, ha, b, hb, hpos⟩ := hex
  have hYnn : 0 ≤ Ysum G P (k * k) (Ucn G Q a b) := sum_nonneg (fun S _ => wt_nonneg G P _ S)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  have hXbig : 4 * k * k < #(Ucn G Q a b) := by
    have : (4 * k * k : ℝ) < ((#(Ucn G Q a b) : ℕ) : ℝ) := by nlinarith
    exact_mod_cast this
  have hYlt : Ysum G P (k * k) (Ucn G Q a b) < 2 * ((#(Ucn G Q a b) : ℕ) : ℝ) := by nlinarith
  obtain ⟨U1, hU1, hcard, hY1⟩ := avg G P (k * k) k hk (Ucn G Q a b) hXbig hYlt
  refine emb G k P Q hPQ a ha U1 (hU1.trans (filter_subset _ _)) hcard ?_ hY1
  intro y hy
  exact (mem_filter.1 (hU1 hy)).2.1

lemma count_split (u v : V) (huv : u ≠ v) :
    #((univ : Finset V).powerset.filter (fun A => u ∈ A ∧ v ∉ A)) = 2 ^ (Fintype.card V - 2) := by
  have himg : (univ : Finset V).powerset.filter (fun A => u ∈ A ∧ v ∉ A) =
      (((univ : Finset V).erase u).erase v).powerset.image (insert u) := by
    ext A
    simp only [mem_filter, mem_powerset, subset_univ, true_and, mem_image]
    constructor
    · rintro ⟨hu, hv⟩
      refine ⟨A.erase u, ?_, insert_erase hu⟩
      intro x hx
      simp only [mem_erase] at hx ⊢
      exact ⟨fun h => hv (h ▸ hx.2), hx.1, mem_univ _⟩
    · rintro ⟨B, hB, rfl⟩
      refine ⟨mem_insert_self _ _, ?_⟩
      simp only [mem_insert, not_or]
      refine ⟨huv.symm, fun h => ?_⟩
      have := hB h
      simp at this
  rw [himg, card_image_of_injOn, card_powerset]
  · congr 1
    rw [card_erase_of_mem (by simp [huv.symm]), card_erase_of_mem (mem_univ _), card_univ]
    omega
  · intro B1 hB1 B2 hB2 h
    have hu1 : u ∉ B1 := fun h' => by simpa using (mem_powerset.1 hB1) h'
    have hu2 : u ∉ B2 := fun h' => by simpa using (mem_powerset.1 hB2) h'
    have := congrArg (fun A => A.erase u) h
    simpa [erase_insert hu1, erase_insert hu2] using this

lemma cut : ∃ A : Finset V, (#G.edgeFinset : ℝ) ≤ 2 * ∑ v ∈ Aᶜ, ((deg G A v : ℕ) : ℝ) := by
  classical
  by_cases hE : #G.edgeFinset = 0
  · exact ⟨∅, by rw [hE]; simp only [Nat.cast_zero]; positivity⟩
  have e1 : ∀ A : Finset V, ∑ v ∈ Aᶜ, ((deg G A v : ℕ) : ℝ) =
      ∑ u : V, ∑ v : V, if (u ∈ A ∧ v ∉ A) ∧ G.Adj v u then (1 : ℝ) else 0 := by
    intro A
    rw [sum_comm]
    have : ∀ v : V, (∑ u : V, if (u ∈ A ∧ v ∉ A) ∧ G.Adj v u then (1 : ℝ) else 0) =
        if v ∈ Aᶜ then ((deg G A v : ℕ) : ℝ) else 0 := by
      intro v
      by_cases hv : v ∈ A
      · simp [hv]
      · simp only [hv, mem_compl, not_false_eq_true, and_true, if_true, deg, card_filter]
        push_cast
        rw [← sum_filter, ← sum_filter]
        congr 1
        ext x
        simp
    simp_rw [this]
    rw [← sum_filter]
    congr 1
    ext x
    simp
  have hN : 2 ≤ Fintype.card V := by
    obtain ⟨e, he⟩ := card_pos.1 (Nat.pos_of_ne_zero hE)
    induction e using Sym2.ind with
    | h x y =>
      have hxy : G.Adj x y := by simpa using he
      have := card_le_univ ({x, y} : Finset V)
      rw [card_pair hxy.ne] at this
      exact this
  have htot : ∑ A ∈ (univ : Finset V).powerset, ∑ v ∈ Aᶜ, ((deg G A v : ℕ) : ℝ) =
      (2 : ℝ) ^ (Fintype.card V - 2) * (2 * #G.edgeFinset) := by
    simp_rw [e1]
    rw [sum_comm]
    have h2 : ∀ u : V, ∑ A ∈ (univ : Finset V).powerset, ∑ v : V,
        (if (u ∈ A ∧ v ∉ A) ∧ G.Adj v u then (1 : ℝ) else 0) =
        (2 : ℝ) ^ (Fintype.card V - 2) * (G.degree u : ℝ) := by
      intro u
      rw [sum_comm]
      have h3 : ∀ v : V, ∑ A ∈ (univ : Finset V).powerset,
          (if (u ∈ A ∧ v ∉ A) ∧ G.Adj v u then (1 : ℝ) else 0) =
          if G.Adj v u then (2 : ℝ) ^ (Fintype.card V - 2) else 0 := by
        intro v
        by_cases hvu : G.Adj v u
        · simp only [hvu, and_true, if_true]
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, count_split u v hvu.ne.symm]
          push_cast; rfl
        · simp [hvu]
      rw [sum_congr rfl (fun v _ => h3 v), ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      congr 2
      rw [← card_neighborFinset_eq_degree]
      congr 1
      ext v
      simp [G.adj_comm]
    rw [sum_congr rfl (fun u _ => h2 u), ← mul_sum]
    congr 1
    exact_mod_cast sum_degrees_eq_twice_card_edges G
  by_contra hcon
  push Not at hcon
  have hlt : ∑ A ∈ (univ : Finset V).powerset, (2 * ∑ v ∈ Aᶜ, ((deg G A v : ℕ) : ℝ)) <
      ∑ A ∈ (univ : Finset V).powerset, (#G.edgeFinset : ℝ) :=
    sum_lt_sum_of_nonempty ⟨∅, by simp⟩ (fun A _ => hcon A)
  rw [← mul_sum, htot, sum_const, card_powerset, card_univ, nsmul_eq_mul] at hlt
  have : (2 : ℝ) ^ Fintype.card V = 4 * 2 ^ (Fintype.card V - 2) := by
    rw [show Fintype.card V = (Fintype.card V - 2) + 2 by omega, pow_add]
    simp; ring
  push_cast at hlt
  rw [this] at hlt
  nlinarith

lemma dsum_eq (P Q : Finset V) :
    ∑ z ∈ P, ((deg G Q z : ℕ) : ℝ) = ∑ v ∈ Q, ((deg G P v : ℕ) : ℝ) := by
  have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s := P) (t := Q)
  have h2 : ∑ b ∈ Q, #(bipartiteBelow G.Adj P b) = ∑ v ∈ Q, deg G P v := by
    apply sum_congr rfl; intro v _
    simp only [bipartiteBelow, deg]
    congr 1; ext x; simp [G.adj_comm]
  rw [h2] at this
  exact_mod_cast this

lemma cs (P Q : Finset V) :
    (∑ v ∈ Q, ((deg G P v : ℕ) : ℝ)) ^ 2 ≤ (#Q : ℝ) * ∑ v ∈ Q, ((deg G P v : ℕ) : ℝ) ^ 2 :=
  sq_sum_le_card_mul_sum_sq

lemma main_bound (k : ℕ) (hk : 2 ≤ k) (hfree : (H k).Free G) :
    (#G.edgeFinset : ℝ) ≤ 8 * k * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA⟩ := cut G
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  set e1 := ∑ v ∈ Aᶜ, ((deg G A v : ℕ) : ℝ) with he1
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hpow : ((N ^ (3 / 2 : ℝ)) ^ 2) = N ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hpow0 : 0 ≤ N ^ (3 / 2 : ℝ) := Real.rpow_nonneg hN0 _
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have he1big : 4 * k * N ^ (3 / 2 : ℝ) < e1 := by linarith
  have he1sq : 16 * (k : ℝ) ^ 2 * N ^ 3 < e1 ^ 2 := by
    have h0 : 0 ≤ 4 * k * N ^ (3 / 2 : ℝ) := by positivity
    have := mul_self_lt_mul_self h0 he1big
    nlinarith
  have hPN : ((#A : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast card_le_univ A
  have hQN : ((#Aᶜ : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast card_le_univ Aᶜ
  have hPn : (0 : ℝ) ≤ (#A : ℕ) := Nat.cast_nonneg _
  have hQn : (0 : ℝ) ≤ (#Aᶜ : ℕ) := Nat.cast_nonneg _
  have hdisj : Disjoint A Aᶜ := disjoint_compl_right
  have key : ∀ P Q : Finset V, ((#P : ℕ) : ℝ) ≤ N → ((#Q : ℕ) : ℝ) ≤ N →
      (∑ v ∈ Q, ((deg G P v : ℕ) : ℝ)) = e1 →
      16 * (k : ℝ) ^ 2 * (#P : ℝ) ^ 2 < 3 * ∑ v ∈ Q, ((deg G P v : ℕ) : ℝ) ^ 2 := by
    intro P Q hP hQ hsum
    have hc := cs G P Q
    rw [hsum] at hc
    set T := ∑ v ∈ Q, ((deg G P v : ℕ) : ℝ) ^ 2
    have hT : 0 ≤ T := sum_nonneg (fun v _ => sq_nonneg _)
    have hP0 : (0 : ℝ) ≤ (#P : ℕ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ (#Q : ℕ) := Nat.cast_nonneg _
    have h1 : ((#P : ℕ) : ℝ) ^ 2 * (#Q : ℕ) ≤ N ^ 3 := by
      have := mul_le_mul (pow_le_pow_left₀ hP0 hP 2) hQ hQ0 (by positivity)
      nlinarith
    have h2 : 16 * (k : ℝ) ^ 2 * (((#P : ℕ) : ℝ) ^ 2 * (#Q : ℕ)) < (#Q : ℕ) * T := by
      have : 16 * (k : ℝ) ^ 2 * (((#P : ℕ) : ℝ) ^ 2 * (#Q : ℕ)) ≤ 16 * (k : ℝ) ^ 2 * N ^ 3 := by
        apply mul_le_mul_of_nonneg_left h1; positivity
      linarith
    have hQpos : (0 : ℝ) < (#Q : ℕ) := by
      rcases hQ0.lt_or_eq with h | h
      · exact h
      · rw [← h] at h2; simp at h2
    have h3 : 16 * (k : ℝ) ^ 2 * ((#P : ℕ) : ℝ) ^ 2 < T := by
      by_contra hh; push Not at hh
      have := mul_le_mul_of_nonneg_left hh hQpos.le
      nlinarith
    have : (0:ℝ) ≤ 16 * (k : ℝ) ^ 2 * ((#P : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  rcases le_or_gt (∑ z ∈ A, ((deg G Aᶜ z : ℕ) : ℝ) ^ 2) (∑ v ∈ Aᶜ, ((deg G A v : ℕ) : ℝ) ^ 2)
    with hle | hlt2
  · exact hfree (core G k hk A Aᶜ hdisj hle (key A Aᶜ hPN hQN rfl))
  · exact hfree (core G k hk Aᶜ A hdisj.symm hlt2.le (key Aᶜ A hQN hPN (dsum_eq G A Aᶜ)))

theorem solution : ∃ C : ℝ, ∀ k : ℕ, 4 ≤ k → ∀ n : ℕ,
    (extremalNumber n (H k) : ℝ) ≤ C * k * (n : ℝ) ^ (3 / 2 : ℝ) := by
  refine ⟨8, fun k hk n => ?_⟩
  have h := extremalNumber_le_iff_of_nonneg (V := Fin n) (H k)
    (m := 8 * (k : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ)) (by positivity)
  rw [Fintype.card_fin] at h
  refine h.2 ?_
  intro G _ hfree
  have := main_bound G k (by omega) hfree
  simpa using this

end OMA926

theorem OMA.solution : type_of% @Erdos926.erdos_926.variants.aks := OMA926.solution
