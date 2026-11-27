import FormalConjectures.ErdosProblems.«150»

-- Problem: Erdős Problem 150 — upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/150.lean:114 (declaration Erdos150.erdos_150.variants.upper_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Route (direct counting, no contraction):
-- a minimal cut T is the outer neighbourhood N(A) of a connected set A with
-- 2|A| + |N(A)| ≤ n (A = the smaller of two components of G - T), and a branching
-- count shows that at most fib (n - 1) such sets A contain a fixed vertex a.
-- Hence c(n) ≤ n * fib (n - 1) ≤ n * φ ^ n and c(n) ^ (1 / n) ≤ n ^ (1 / n) * φ → φ.

namespace OMA

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Outer neighbourhood of a finite vertex set.
noncomputable def nbr (G : SimpleGraph V) (A : Finset V) : Finset V :=
  Finset.filter (fun v => v ∉ A ∧ ∃ u ∈ A, G.Adj u v) Finset.univ

lemma mem_nbr (G : SimpleGraph V) (A : Finset V) (v : V) :
    v ∈ nbr G A ↔ v ∉ A ∧ ∃ u ∈ A, G.Adj u v := by
  unfold nbr
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩⟩

-- Connectivity of a finite vertex set, stated without walks.
def Conn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ K : Finset V, K ⊆ A → K.Nonempty → K ≠ A → ∃ k ∈ K, ∃ u ∈ A, u ∉ K ∧ G.Adj k u

def Good (G : SimpleGraph V) (A : Finset V) : Prop :=
  Conn G A ∧ 2 * A.card + (nbr G A).card ≤ Fintype.card V

lemma size_le (G : SimpleGraph V) (X K A : Finset V) (hX : ∀ x ∈ X, x ∈ nbr G K)
    (hKA : K ⊆ A) (hAX : Disjoint A X) (hA : Good G A) :
    X.card + 2 * K.card ≤ Fintype.card V := by
  have h1 : X ⊆ nbr G A := by
    intro x hx
    have hxK := (mem_nbr G K x).mp (hX x hx)
    obtain ⟨u, huK, hux⟩ := hxK.2
    exact (mem_nbr G A x).mpr
      ⟨fun hxA => Finset.disjoint_left.mp hAX hxA hx, u, hKA huK, hux⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.card_le_card hKA
  have h4 := hA.2
  omega

lemma eq_of_closed (G : SimpleGraph V) (X K A : Finset V) (hK : K.Nonempty) (hKA : K ⊆ A)
    (hAX : Disjoint A X) (hA : Conn G A) (hcl : ∀ u, u ∈ nbr G K → u ∈ X) : A = K := by
  by_contra hne
  obtain ⟨k, hkK, u, huA, huK, hadj⟩ := hA K hKA hK (fun h => hne h.symm)
  exact Finset.disjoint_left.mp hAX huA (hcl u ((mem_nbr G K u).mpr ⟨huK, k, hkK, hadj⟩))

lemma fib_step (N a b : ℕ) (h : a + 2 * b ≤ N) :
    Nat.fib (N + 1 - a - 2 * (b + 1)) + Nat.fib (N + 1 - (a + 1) - 2 * b) ≤
      Nat.fib (N + 1 - a - 2 * b) := by
  obtain ⟨t, ht⟩ : ∃ t, N = a + 2 * b + t := ⟨N - (a + 2 * b), by omega⟩
  have e1 : N + 1 - a - 2 * (b + 1) = t - 1 := by omega
  have e2 : N + 1 - (a + 1) - 2 * b = t := by omega
  have e3 : N + 1 - a - 2 * b = t + 1 := by omega
  rw [e1, e2, e3]
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]
    simp
  · obtain ⟨k, hk⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    have e4 : t - 1 = k := by omega
    have e5 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := @Nat.fib_add_two k
    exact le_of_eq (by rw [e4, hk, e5])

lemma card_zero_of_big (G : SimpleGraph V) (X K : Finset V) (fam : Finset (Finset V))
    (hX : ∀ x ∈ X, x ∈ nbr G K) (hbig : Fintype.card V < X.card + 2 * K.card)
    (hfam : ∀ A ∈ fam, K ⊆ A ∧ Disjoint A X ∧ Good G A) : fam.card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro A hA
  obtain ⟨hKA, hAX, hG⟩ := hfam A hA
  have hsz := size_le G X K A hX hKA hAX hG
  omega

-- Branching count: the sets A ⊇ K avoiding X ⊆ N(K) that are Good.
lemma count_le (G : SimpleGraph V) :
    ∀ (m : ℕ) (X K : Finset V) (fam : Finset (Finset V)),
      K.Nonempty → (∀ x ∈ X, x ∈ nbr G K) →
      Fintype.card V + 1 ≤ X.card + 2 * K.card + m →
      (∀ A ∈ fam, K ⊆ A ∧ Disjoint A X ∧ Good G A) →
      fam.card ≤ Nat.fib (Fintype.card V + 1 - X.card - 2 * K.card) := by
  intro m
  induction m with
  | zero =>
    intro X K fam hK hX hm hfam
    have h0 := card_zero_of_big G X K fam hX (by omega) hfam
    rw [h0]
    exact Nat.zero_le _
  | succ m ih =>
    intro X K fam hK hX hm hfam
    by_cases hbig : Fintype.card V < X.card + 2 * K.card
    · have h0 := card_zero_of_big G X K fam hX hbig hfam
      rw [h0]
      exact Nat.zero_le _
    · by_cases hex : ∃ u, u ∈ nbr G K ∧ u ∉ X
      · obtain ⟨u, huN, huX⟩ := hex
        have huK : u ∉ K := ((mem_nbr G K u).mp huN).1
        have h1 : (fam.filter (fun A => u ∈ A)).card ≤
            Nat.fib (Fintype.card V + 1 - X.card - 2 * (insert u K).card) := by
          refine ih X (insert u K) (fam.filter (fun A => u ∈ A))
            (Finset.insert_nonempty u K) ?_ ?_ ?_
          · intro x hx
            have hxK := (mem_nbr G K x).mp (hX x hx)
            obtain ⟨w, hwK, hwx⟩ := hxK.2
            refine (mem_nbr G (insert u K) x).mpr
              ⟨?_, w, Finset.mem_insert_of_mem hwK, hwx⟩
            intro hxi
            rcases Finset.mem_insert.mp hxi with hxu | hxK'
            · rw [hxu] at hx
              exact huX hx
            · exact hxK.1 hxK'
          · rw [Finset.card_insert_of_notMem huK]
            omega
          · intro A hA
            have hA' := Finset.mem_filter.mp hA
            obtain ⟨hKA, hAX, hG⟩ := hfam A hA'.1
            exact ⟨Finset.insert_subset_iff.mpr ⟨hA'.2, hKA⟩, hAX, hG⟩
        have h2 : (fam.filter (fun A => ¬ u ∈ A)).card ≤
            Nat.fib (Fintype.card V + 1 - (insert u X).card - 2 * K.card) := by
          refine ih (insert u X) K (fam.filter (fun A => ¬ u ∈ A)) hK ?_ ?_ ?_
          · intro x hx
            rcases Finset.mem_insert.mp hx with hxu | hxX
            · rw [hxu]
              exact huN
            · exact hX x hxX
          · rw [Finset.card_insert_of_notMem huX]
            omega
          · intro A hA
            have hA' := Finset.mem_filter.mp hA
            obtain ⟨hKA, hAX, hG⟩ := hfam A hA'.1
            exact ⟨hKA, Finset.disjoint_insert_right.mpr ⟨hA'.2, hAX⟩, hG⟩
        have hsplit := Finset.card_filter_add_card_filter_not (s := fam) (fun A => u ∈ A)
        have hfib := fib_step (Fintype.card V) X.card K.card (by omega)
        rw [Finset.card_insert_of_notMem huK] at h1
        rw [Finset.card_insert_of_notMem huX] at h2
        rw [← hsplit]
        exact le_trans (Nat.add_le_add h1 h2) hfib
      · have hcl : ∀ u, u ∈ nbr G K → u ∈ X := by
          intro u hu
          by_contra huX
          exact hex ⟨u, hu, huX⟩
        have hsub : fam ⊆ ({K} : Finset (Finset V)) := by
          intro A hA
          obtain ⟨hKA, hAX, hG⟩ := hfam A hA
          exact Finset.mem_singleton.mpr (eq_of_closed G X K A hK hKA hAX hG.1 hcl)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_singleton] at hc
        have hpos : 0 < Nat.fib (Fintype.card V + 1 - X.card - 2 * K.card) :=
          Nat.fib_pos.mpr (by omega)
        omega

lemma good_count (G : SimpleGraph V) (a : V) (fam : Finset (Finset V))
    (h : ∀ A ∈ fam, a ∈ A ∧ Good G A) : fam.card ≤ Nat.fib (Fintype.card V - 1) := by
  have key := count_le G (Fintype.card V) (∅ : Finset V) ({a} : Finset V) fam
    (Finset.singleton_nonempty a)
    (fun x hx => absurd hx (Finset.notMem_empty x))
    (by rw [Finset.card_singleton]; omega)
    (fun A hA => ⟨Finset.singleton_subset_iff.mpr (h A hA).1,
      Finset.disjoint_empty_right A, (h A hA).2⟩)
  have e : Fintype.card V + 1 - (∅ : Finset V).card - 2 * ({a} : Finset V).card =
      Fintype.card V - 1 := by
    rw [Finset.card_empty, Finset.card_singleton]
    omega
  rw [e] at key
  exact key

-- The vertices reachable from x after deleting T.
def reach (G : SimpleGraph V) (T : Set V) (x : V) : Set V :=
  {v | ∃ (hx : x ∈ Tᶜ) (hv : v ∈ Tᶜ), (G.induce Tᶜ).Reachable ⟨x, hx⟩ ⟨v, hv⟩}

lemma mem_reach (G : SimpleGraph V) (T : Set V) (x v : V) :
    v ∈ reach G T x ↔
      ∃ (hx : x ∈ Tᶜ) (hv : v ∈ Tᶜ), (G.induce Tᶜ).Reachable ⟨x, hx⟩ ⟨v, hv⟩ :=
  Iff.rfl

lemma reach_self (G : SimpleGraph V) (T : Set V) (x : V) (hx : x ∉ T) : x ∈ reach G T x :=
  (mem_reach G T x x).mpr ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

lemma reach_sub (G : SimpleGraph V) (T : Set V) (x v : V) (hv : v ∈ reach G T x) : v ∉ T := by
  obtain ⟨_, hv', _⟩ := (mem_reach G T x v).mp hv
  exact hv'

lemma reach_adj (G : SimpleGraph V) (T : Set V) (x v w : V) (hv : v ∈ reach G T x)
    (hw : w ∉ T) (hadj : G.Adj v w) : w ∈ reach G T x := by
  obtain ⟨hx, hv', hr⟩ := (mem_reach G T x v).mp hv
  have hstep : (G.induce Tᶜ).Reachable ⟨v, hv'⟩ ⟨w, hw⟩ :=
    (show (G.induce Tᶜ).Adj ⟨v, hv'⟩ ⟨w, hw⟩ from hadj).reachable
  exact (mem_reach G T x w).mpr ⟨hx, hw, hr.trans hstep⟩

-- Every vertex of a minimal cut has a neighbour in each component it separates.
lemma cut_adj (G : SimpleGraph V) (T : Set V)
    (hmin : ∀ S, S ⊂ T → (G.induce Sᶜ).Preconnected)
    (x y : V) (hx : x ∉ T) (hy : y ∉ T) (hxy : y ∉ reach G T x) (t : V) (ht : t ∈ T) :
    ∃ u, u ∈ reach G T x ∧ G.Adj u t := by
  have hS : T \ {t} ⊂ T := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨fun v hv => hv.1, ?_⟩
    intro heq
    have htm : t ∈ T \ {t} := by
      rw [heq]
      exact ht
    exact htm.2 (Set.mem_singleton t)
  have hxS : x ∈ (T \ {t})ᶜ := fun h => hx h.1
  have hyS : y ∈ (T \ {t})ᶜ := fun h => hy h.1
  obtain ⟨p⟩ := hmin (T \ {t}) hS ⟨x, hxS⟩ ⟨y, hyS⟩
  obtain ⟨⟨⟨⟨u, huS⟩, ⟨w, hwS⟩⟩, hadj'⟩, _, hd1, hd2⟩ :=
    p.exists_boundary_dart {z : ↥((T \ {t})ᶜ : Set V) | (z : V) ∈ reach G T x}
      (reach_self G T x hx) hxy
  have hu : u ∈ reach G T x := hd1
  have hw : w ∉ reach G T x := hd2
  have hadj : G.Adj u w := hadj'
  have hwT : w ∈ T := by
    by_contra hwT
    exact hw (reach_adj G T x u w hu hwT hadj)
  have hwt : w = t := by
    by_contra hne
    exact hwS ⟨hwT, hne⟩
  rw [hwt] at hadj
  exact ⟨u, hu, hadj⟩

noncomputable def reachF (G : SimpleGraph V) (T : Set V) (x : V) : Finset V :=
  Finset.filter (fun v => v ∈ reach G T x) Finset.univ

lemma mem_reachF (G : SimpleGraph V) (T : Set V) (x v : V) :
    v ∈ reachF G T x ↔ v ∈ reach G T x := by
  unfold reachF
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩⟩

lemma nbr_reachF (G : SimpleGraph V) (T : Set V)
    (hmin : ∀ S, S ⊂ T → (G.induce Sᶜ).Preconnected)
    (x y : V) (hx : x ∉ T) (hy : y ∉ T) (hxy : y ∉ reach G T x) (v : V) :
    v ∈ nbr G (reachF G T x) ↔ v ∈ T := by
  constructor
  · intro hv
    obtain ⟨hvA, u, hu, hadj⟩ := (mem_nbr G (reachF G T x) v).mp hv
    by_contra hvT
    exact hvA ((mem_reachF G T x v).mpr
      (reach_adj G T x u v ((mem_reachF G T x u).mp hu) hvT hadj))
  · intro hvT
    obtain ⟨u, hu, hadj⟩ := cut_adj G T hmin x y hx hy hxy v hvT
    exact (mem_nbr G (reachF G T x) v).mpr
      ⟨fun h => reach_sub G T x v ((mem_reachF G T x v).mp h) hvT,
        u, (mem_reachF G T x u).mpr hu, hadj⟩

lemma conn_reachF (G : SimpleGraph V) (T : Set V) (x : V) : Conn G (reachF G T x) := by
  intro K hKA hK hne
  obtain ⟨k0, hk0⟩ := hK
  obtain ⟨u0, hu0A, hu0K⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hKA, hne⟩)
  obtain ⟨hx, hk0T, hr1⟩ := (mem_reach G T x k0).mp ((mem_reachF G T x k0).mp (hKA hk0))
  obtain ⟨hx', hu0T, hr2⟩ := (mem_reach G T x u0).mp ((mem_reachF G T x u0).mp hu0A)
  have hr : (G.induce Tᶜ).Reachable ⟨k0, hk0T⟩ ⟨u0, hu0T⟩ := hr1.symm.trans hr2
  obtain ⟨p⟩ := hr
  obtain ⟨⟨⟨⟨u, huT⟩, ⟨w, hwT⟩⟩, hadj'⟩, _, hd1, hd2⟩ :=
    p.exists_boundary_dart {z : ↥(Tᶜ : Set V) | (z : V) ∈ K} hk0 hu0K
  have hu : u ∈ K := hd1
  have hw : w ∉ K := hd2
  have hadj : G.Adj u w := hadj'
  exact ⟨u, hu, w, (mem_reachF G T x w).mpr
    (reach_adj G T x u w ((mem_reachF G T x u).mp (hKA hu)) hwT hadj), hw, hadj⟩

lemma card_three (A B C : Finset V) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) : A.card + B.card + C.card ≤ Fintype.card V := by
  have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB
  have h2 : ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)
  have h3 := Finset.card_le_univ ((A ∪ B) ∪ C)
  omega

noncomputable def nbrSet (G : SimpleGraph V) (A : Finset V) : Set V := (↑(nbr G A) : Set V)

-- A minimal cut is the neighbourhood of a Good set (the smaller of two components).
lemma exists_good (G : SimpleGraph V) (T : Set V) (hT : Erdos150.IsMinimalCut G T) :
    ∃ (a : V) (A : Finset V), a ∈ A ∧ Good G A ∧ nbrSet G A = T := by
  obtain ⟨hnot, hmin⟩ := hT
  have hex : ∃ x y : V, x ∉ T ∧ y ∉ T ∧ y ∉ reach G T x := by
    by_contra hcon
    apply hnot
    intro a b
    by_contra hab
    refine hcon ⟨(a : V), (b : V), a.2, b.2, ?_⟩
    intro hmem
    obtain ⟨ha, hb, hr⟩ := (mem_reach G T (a : V) (b : V)).mp hmem
    exact hab hr
  obtain ⟨x, y, hx, hy, hxy⟩ := hex
  have hyx : x ∉ reach G T y := by
    intro hmem
    obtain ⟨hy', hx', hr⟩ := (mem_reach G T y x).mp hmem
    exact hxy ((mem_reach G T x y).mpr ⟨hx', hy', hr.symm⟩)
  have hdis : Disjoint (reachF G T x) (reachF G T y) := by
    rw [Finset.disjoint_left]
    intro v hvx hvy
    obtain ⟨hx1, hv1, hr1⟩ := (mem_reach G T x v).mp ((mem_reachF G T x v).mp hvx)
    obtain ⟨hy2, hv2, hr2⟩ := (mem_reach G T y v).mp ((mem_reachF G T y v).mp hvy)
    exact hxy ((mem_reach G T x y).mpr ⟨hx1, hy2, hr1.trans hr2.symm⟩)
  have hNx : ∀ v, v ∈ nbr G (reachF G T x) ↔ v ∈ T :=
    nbr_reachF G T hmin x y hx hy hxy
  have hNy : ∀ v, v ∈ nbr G (reachF G T y) ↔ v ∈ T :=
    nbr_reachF G T hmin y x hy hx hyx
  have hsub : ∀ z v, v ∈ reachF G T z → v ∉ T :=
    fun z v hv => reach_sub G T z v ((mem_reachF G T z v).mp hv)
  have hd1 : ∀ z, Disjoint (reachF G T z) (nbr G (reachF G T x)) := by
    intro z
    rw [Finset.disjoint_left]
    intro v hv hvn
    exact hsub z v hv ((hNx v).mp hvn)
  have hd2 : ∀ z, Disjoint (reachF G T z) (nbr G (reachF G T y)) := by
    intro z
    rw [Finset.disjoint_left]
    intro v hv hvn
    exact hsub z v hv ((hNy v).mp hvn)
  have hc1 := card_three (reachF G T x) (reachF G T y) (nbr G (reachF G T x))
    hdis (hd1 x) (hd1 y)
  have hc2 := card_three (reachF G T x) (reachF G T y) (nbr G (reachF G T y))
    hdis (hd2 x) (hd2 y)
  rcases le_total (reachF G T x).card (reachF G T y).card with hle | hle
  · have hsz : 2 * (reachF G T x).card + (nbr G (reachF G T x)).card ≤ Fintype.card V := by
      omega
    refine ⟨x, reachF G T x, (mem_reachF G T x x).mpr (reach_self G T x hx),
      ⟨conn_reachF G T x, hsz⟩, ?_⟩
    exact Set.ext (fun v => Finset.mem_coe.trans (hNx v))
  · have hsz : 2 * (reachF G T y).card + (nbr G (reachF G T y)).card ≤ Fintype.card V := by
      omega
    refine ⟨y, reachF G T y, (mem_reachF G T y y).mpr (reach_self G T y hy),
      ⟨conn_reachF G T y, hsz⟩, ?_⟩
    exact Set.ext (fun v => Finset.mem_coe.trans (hNy v))

noncomputable def goodFam (G : SimpleGraph V) (a : V) : Finset (Finset V) :=
  Finset.filter (fun A => a ∈ A ∧ Good G A) Finset.univ

lemma mem_goodFam (G : SimpleGraph V) (a : V) (A : Finset V) :
    A ∈ goodFam G a ↔ a ∈ A ∧ Good G A := by
  unfold goodFam
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ A, h⟩⟩

lemma cuts_ncard_le (G : SimpleGraph V) :
    {T : Set V | Erdos150.IsMinimalCut G T}.ncard ≤
      Fintype.card V * Nat.fib (Fintype.card V - 1) := by
  have hF : ∀ a ∈ (Finset.univ : Finset V),
      (goodFam G a).card ≤ Nat.fib (Fintype.card V - 1) := by
    intro a _
    exact good_count G a (goodFam G a) (fun A hA => (mem_goodFam G a A).mp hA)
  have hU : ((Finset.univ : Finset V).biUnion (goodFam G)).card ≤
      Fintype.card V * Nat.fib (Fintype.card V - 1) := by
    have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset V) (goodFam G)
      (Nat.fib (Fintype.card V - 1)) hF
    rw [Finset.card_univ] at h
    exact h
  have hsub : {T : Set V | Erdos150.IsMinimalCut G T} ⊆
      (nbrSet G) '' (↑((Finset.univ : Finset V).biUnion (goodFam G)) : Set (Finset V)) := by
    intro T hT
    obtain ⟨a, A, haA, hG, hN⟩ := exists_good G T hT
    exact ⟨A, Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, (mem_goodFam G a A).mpr ⟨haA, hG⟩⟩), hN⟩
  have hfin : (↑((Finset.univ : Finset V).biUnion (goodFam G)) : Set (Finset V)).Finite :=
    Finset.finite_toSet _
  have h1 := Set.ncard_le_ncard hsub (hfin.image (nbrSet G))
  have h2 : ((nbrSet G) ''
      (↑((Finset.univ : Finset V).biUnion (goodFam G)) : Set (Finset V))).ncard ≤
      (↑((Finset.univ : Finset V).biUnion (goodFam G)) : Set (Finset V)).ncard :=
    Set.ncard_image_le hfin
  have h3 : (↑((Finset.univ : Finset V).biUnion (goodFam G)) : Set (Finset V)).ncard =
      ((Finset.univ : Finset V).biUnion (goodFam G)).card := Set.ncard_coe_finset _
  exact h1.trans (h2.trans (h3.le.trans hU))

lemma maxMinimalCuts_le (n : ℕ) : Erdos150.maxMinimalCuts n ≤ n * Nat.fib (n - 1) := by
  unfold Erdos150.maxMinimalCuts
  refine csSup_le ⟨_, ⟨⊥, rfl⟩⟩ ?_
  rintro k ⟨G, rfl⟩
  have h := cuts_ncard_le G
  rw [Fintype.card_fin] at h
  exact h

lemma one_le_sqrt5 : (1 : ℝ) ≤ Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  by_contra hlt
  have hlt' : Real.sqrt 5 < 1 := lt_of_not_ge hlt
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hlt'.le), h5]

lemma phi_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 4 : ℝ) * h5

lemma fib_le_pow (r : ℝ) (h1 : 1 ≤ r) (h2 : r ^ 2 = r + 1) (k : ℕ) :
    (Nat.fib k : ℝ) ≤ r ^ k ∧ (Nat.fib (k + 1) : ℝ) ≤ r ^ (k + 1) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
    · simpa using h1
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hfib : (Nat.fib (k + 1 + 1) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ) := by
      have h : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := @Nat.fib_add_two k
      rw [h, Nat.cast_add]
    have hpow : r ^ (k + 1 + 1) = r ^ k + r ^ (k + 1) := by
      have e : r ^ (k + 1 + 1) = r ^ k * r ^ 2 := by ring
      rw [e, h2]
      ring
    rw [hfib, hpow]
    exact add_le_add ih.1 ih.2

end OMA

theorem OMA.solution : type_of% @Erdos150.erdos_150.variants.upper_bound := by
  intro α hα
  have hs1 : (1 : ℝ) ≤ Real.sqrt 5 := OMA.one_le_sqrt5
  have hφ1 : (1 : ℝ) ≤ (1 + Real.sqrt 5) / 2 := by linarith
  have hφ0 : (0 : ℝ) ≤ (1 + Real.sqrt 5) / 2 := by linarith
  have hpt : ∀ n : ℕ, 1 ≤ n →
      (Erdos150.maxMinimalCuts n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤
        (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * ((1 + Real.sqrt 5) / 2) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hc : (Erdos150.maxMinimalCuts n : ℝ) ≤ (n : ℝ) * ((1 + Real.sqrt 5) / 2) ^ n := by
      have h1 : (Erdos150.maxMinimalCuts n : ℝ) ≤ (n : ℝ) * (Nat.fib (n - 1) : ℝ) := by
        exact_mod_cast OMA.maxMinimalCuts_le n
      have h2 : (Nat.fib (n - 1) : ℝ) ≤ ((1 + Real.sqrt 5) / 2) ^ (n - 1) :=
        (OMA.fib_le_pow _ hφ1 OMA.phi_sq (n - 1)).1
      have h3 : ((1 + Real.sqrt 5) / 2) ^ (n - 1) ≤ ((1 + Real.sqrt 5) / 2) ^ n :=
        pow_le_pow_right₀ hφ1 (Nat.sub_le n 1)
      exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hn0.le)
    have hc0 : (0 : ℝ) ≤ (Erdos150.maxMinimalCuts n : ℝ) := Nat.cast_nonneg _
    have hexp : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := div_nonneg zero_le_one hn0.le
    have hstep := Real.rpow_le_rpow hc0 hc hexp
    have e : (((1 + Real.sqrt 5) / 2) ^ n) ^ ((1 : ℝ) / (n : ℝ)) = (1 + Real.sqrt 5) / 2 := by
      rw [← Real.rpow_natCast ((1 + Real.sqrt 5) / 2) n, ← Real.rpow_mul hφ0,
        mul_one_div_cancel hn0.ne', Real.rpow_one]
    have hmul : ((n : ℝ) * ((1 + Real.sqrt 5) / 2) ^ n) ^ ((1 : ℝ) / (n : ℝ)) =
        (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * ((1 + Real.sqrt 5) / 2) := by
      rw [Real.mul_rpow hn0.le (pow_nonneg hφ0 n), e]
    rw [hmul] at hstep
    exact hstep
  have hlim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * ((1 + Real.sqrt 5) / 2))
      Filter.atTop (nhds (1 * ((1 + Real.sqrt 5) / 2))) :=
    Filter.Tendsto.mul_const ((1 + Real.sqrt 5) / 2)
      (tendsto_rpow_div.comp tendsto_natCast_atTop_atTop)
  rw [one_mul] at hlim
  have hev : Filter.Eventually (fun n : ℕ =>
      (Erdos150.maxMinimalCuts n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤
        (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * ((1 + Real.sqrt 5) / 2)) Filter.atTop :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hpt n hn⟩
  exact le_of_tendsto_of_tendsto hα hlim hev
