import FormalConjectures.ErdosProblems.«554»

-- Problem: Erdős Problem 554 — upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/554.lean:116 (declaration Erdos554.erdos_554.variants.upper_bound)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Odd cycles in k-coloured complete graphs: R_k(C_{2n+1}) at most 2n(k+2)!

Fix a vertex v of minimum missing degree. Inside the colour-c neighbourhood S of v, colour c has
no path on 2n vertices (with v it would close a C_{2n+1}), so every subset of S has a vertex of
colour-c degree at most 2n-2, and colour c spans at most (2n-2)|X| edges on each X in S. Pass to
S with colour c removed and treat its edges as missing. The missing pairs stay sparse, and the
bound recursion gives at most 3(2K(2n-2)+1)K! vertices, which is below 2n(K+2)!.
-/

open SimpleGraph Finset
namespace OMA554

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma greedy_path (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (L : ℕ)
    (hdeg : ∀ w ∈ W, L ≤ (W.filter (G.Adj w)).card) (w₀ : V) (hw₀ : w₀ ∈ W) :
    ∀ m, m ≤ L → ∃ u w : V, ∃ p : G.Walk u w, p.IsPath ∧ p.length = m ∧ ∀ x ∈ p.support, x ∈ W := by
  intro m
  induction m with
  | zero => intro _; exact ⟨w₀, w₀, Walk.nil, Walk.IsPath.nil, rfl, by simp [hw₀]⟩
  | succ m ih =>
    intro hm
    obtain ⟨u, w, p, hp, hlen, hsup⟩ := ih (by omega)
    have huW : u ∈ W := hsup u (Walk.start_mem_support p)
    have : ∃ x ∈ W.filter (G.Adj u), x ∉ p.support := by
      by_contra hcon
      push Not at hcon
      have hsub : W.filter (G.Adj u) ⊆ p.support.toFinset.erase u := by
        intro x hx
        rw [Finset.mem_erase, List.mem_toFinset]
        refine ⟨?_, hcon x hx⟩
        rintro rfl
        exact G.irrefl (Finset.mem_filter.mp hx).2
      have h1 := Finset.card_le_card hsub
      have h2 : (p.support.toFinset.erase u).card ≤ m := by
        rw [Finset.card_erase_of_mem (by simp)]
        have := List.toFinset_card_le p.support
        rw [Walk.length_support] at this
        omega
      have := hdeg u huW
      omega
    obtain ⟨x, hx, hxp⟩ := this
    have hadj : G.Adj x u := (Finset.mem_filter.mp hx).2.symm
    refine ⟨x, w, Walk.cons hadj p, ?_, by simp [hlen], ?_⟩
    · exact (Walk.cons_isPath_iff hadj p).mpr ⟨hp, hxp⟩
    · intro y hy
      rw [Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact (Finset.mem_filter.mp hx).1
      · exact hsup y hy

lemma cycle_of_path (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (v u w : V) (p : G.Walk u w)
    (hp : p.IsPath) (hlen : p.length = 2 * n - 1) (hv : v ∉ p.support)
    (hvu : G.Adj v u) (hwv : G.Adj w v) : cycleGraph (2 * n + 1) ⊑ G := by
  rw [cycleGraph_isContained_iff (by omega)]
  refine ⟨v, Walk.cons hvu (p.concat hwv), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hp.concat hv hwv, ?_⟩
    rw [Walk.edges_concat]
    intro hmem
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with h | h
    · exact hv (p.fst_mem_support_of_mem_edges h)
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hv (h1 ▸ p.end_mem_support)
      · subst h2
        have := Walk.isPath_iff_nil.mp hp
        rw [Walk.nil_iff_length_eq] at this
        omega
  · simp [Walk.length_concat, hlen]; omega


section counting
variable {W : Type*} [DecidableEq W]

def dg (P : W → W → Prop) [DecidableRel P] (X : Finset W) (x : W) : ℕ := (X.filter (P x)).card

def oc (P : W → W → Prop) [DecidableRel P] (X : Finset W) : ℕ := ∑ x ∈ X, dg P X x

lemma oc_le_or (P Q R : W → W → Prop) [DecidableRel P] [DecidableRel Q] [DecidableRel R]
    (h : ∀ x y, R x y → P x y ∨ Q x y) (X : Finset W) : oc R X ≤ oc P X + oc Q X := by
  unfold oc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  unfold dg
  calc (X.filter (R x)).card ≤ (X.filter (P x) ∪ X.filter (Q x)).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases h x y hy.2 with h1 | h1
        · exact Or.inl ⟨hy.1, h1⟩
        · exact Or.inr ⟨hy.1, h1⟩
    _ ≤ _ := Finset.card_union_le _ _

lemma oc_erase (P : W → W → Prop) [DecidableRel P] (hsymm : ∀ x y, P x y → P y x)
    (X : Finset W) (x : W) (hx : x ∈ X) :
    oc P X ≤ oc P (X.erase x) + 2 * dg P X x := by
  unfold oc
  rw [← Finset.add_sum_erase X _ hx]
  have h1 : ∀ y ∈ X.erase x, dg P X y ≤ dg P (X.erase x) y + (if P y x then 1 else 0) := by
    intro y _
    unfold dg
    calc (X.filter (P y)).card ≤ ((X.erase x).filter (P y) ∪ ({x} : Finset W).filter (P y)).card := by
          apply Finset.card_le_card
          intro z hz
          rw [Finset.mem_filter] at hz
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_erase,
            Finset.mem_singleton]
          by_cases hzx : z = x
          · exact Or.inr ⟨hzx, hz.2⟩
          · exact Or.inl ⟨⟨hzx, hz.1⟩, hz.2⟩
      _ ≤ _ := Finset.card_union_le _ _
      _ = _ := by rw [Finset.filter_singleton]; split_ifs <;> simp
  have h2 : ∑ y ∈ X.erase x, (if P y x then 1 else 0) ≤ dg P X x := by
    rw [← Finset.card_filter]
    unfold dg
    apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_filter, Finset.mem_erase] at hy
    rw [Finset.mem_filter]
    exact ⟨hy.1.2, hsymm _ _ hy.2⟩
  have h3 := Finset.sum_le_sum h1
  rw [Finset.sum_add_distrib] at h3
  omega

lemma sparse_of_low (P : W → W → Prop) [DecidableRel P] (hsymm : ∀ x y, P x y → P y x)
    (S : Finset W) (q : ℕ) (hlow : ∀ X ⊆ S, X.Nonempty → ∃ x ∈ X, dg P X x ≤ q) :
    ∀ X ⊆ S, oc P X ≤ 2 * q * X.card := by
  intro X
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hXS
    rcases X.eq_empty_or_nonempty with rfl | hne
    · simp [oc]
    obtain ⟨x, hx, hdx⟩ := hlow X hXS hne
    have h1 := oc_erase P hsymm X x hx
    have h2 := ih (X.erase x) (Finset.erase_ssubset hx) ((Finset.erase_subset _ _).trans hXS)
    have h3 := Finset.card_erase_add_one hx
    nlinarith

lemma exists_low (P : W → W → Prop) [DecidableRel P] (X : Finset W) (hne : X.Nonempty) (s : ℕ)
    (h : oc P X ≤ 2 * s * X.card) : ∃ x ∈ X, dg P X x ≤ 2 * s := by
  apply Finset.exists_le_of_sum_le hne
  rw [Finset.sum_const, smul_eq_mul]
  unfold oc at h
  linarith

lemma oc_ne (X : Finset W) : oc (fun x y : W => x ≠ y) X = X.card * (X.card - 1) := by
  unfold oc dg
  rw [Finset.sum_congr rfl (g := fun _ => X.card - 1)]
  · simp
  · intro x hx
    rw [Finset.filter_ne, Finset.card_erase_of_mem hx]

end counting

def bnd (q : ℕ) : ℕ → ℕ → ℕ
  | s, 0 => 2 * s + 1
  | s, k + 1 => 1 + 2 * s + (k + 1) * bnd q (s + q) k

lemma bnd_le (q : ℕ) : ∀ k s, bnd q s k + (2 * (s + k * q) + 1) ≤ 3 * (2 * (s + k * q) + 1) * k.factorial := by
  intro k
  induction k with
  | zero => intro s; simp [bnd]; omega
  | succ k ih =>
    intro s
    have h := ih (s + q)
    have e : s + q + k * q = s + (k + 1) * q := by ring
    rw [e] at h
    set C := 2 * (s + (k + 1) * q) + 1 with hC
    have hs : 1 + 2 * s ≤ C := by rw [hC]; nlinarith
    simp only [bnd]
    rw [Nat.factorial_succ]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [bnd, Nat.factorial_zero] at h ⊢
      nlinarith
    · have hf : 1 ≤ k.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
      nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma main_count (n : ℕ) (hn : 1 ≤ n) {K : ℕ} (C : TopEdgeLabeling V (Fin K))
    (hfree : ∀ c, ¬ cycleGraph (2 * n + 1) ⊑ C.labelGraph c) :
    ∀ k (A : Finset (Fin K)), A.card = k → ∀ s (U : Finset V),
      (∀ X ⊆ U, oc (fun x y => x ≠ y ∧ ∀ c ∈ A, ¬ (C.labelGraph c).Adj x y) X ≤ 2 * s * X.card) →
      U.card ≤ bnd (2 * n - 2) s k := by
  intro k
  induction k with
  | zero =>
    intro A hA s U hU
    rw [Finset.card_eq_zero] at hA
    subst hA
    have h := hU U le_rfl
    have e : oc (fun x y => x ≠ y ∧ ∀ c ∈ (∅ : Finset (Fin K)), ¬ (C.labelGraph c).Adj x y) U
        = oc (fun x y : V => x ≠ y) U := by
      unfold oc dg; simp
    rw [e, oc_ne] at h
    simp only [bnd]
    rcases Nat.eq_zero_or_pos U.card with h0 | h0
    · omega
    · have : U.card - 1 ≤ 2 * s := by
        by_contra hc; push Not at hc
        nlinarith
      omega
  | succ k ih =>
    intro A hA s U hU
    rcases U.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨v, hvU, hv⟩ := exists_low _ U hne s (hU U le_rfl)
    set G := fun c => C.labelGraph c
    -- each colour neighbourhood is small
    have hS : ∀ c ∈ A, (U.filter ((C.labelGraph c).Adj v)).card ≤ bnd (2 * n - 2) (s + (2 * n - 2)) k := by
      intro c hc
      set S := U.filter ((C.labelGraph c).Adj v) with hSdef
      have hlow : ∀ X ⊆ S, X.Nonempty → ∃ x ∈ X, dg (C.labelGraph c).Adj X x ≤ 2 * n - 2 := by
        intro X hXS hXne
        by_contra hcon
        push Not at hcon
        obtain ⟨w₀, hw₀⟩ := hXne
        obtain ⟨u, w, p, hp, hlen, hsup⟩ := greedy_path (C.labelGraph c) X (2 * n - 1)
          (fun w hw => by have := hcon w hw; unfold dg at this; omega) w₀ hw₀ (2 * n - 1) le_rfl
        have hvS : ∀ y ∈ X, (C.labelGraph c).Adj v y := fun y hy =>
          (Finset.mem_filter.mp (hXS hy)).2
        refine hfree c (cycle_of_path _ n hn v u w p hp hlen ?_ ?_ ?_)
        · intro hvp
          exact (C.labelGraph c).irrefl (hvS v (hsup v hvp))
        · exact hvS u (hsup u p.start_mem_support)
        · exact (hvS w (hsup w p.end_mem_support)).symm
      have hsp := sparse_of_low (C.labelGraph c).Adj (fun x y h => h.symm) S (2 * n - 2) hlow
      have hcard : (A.erase c).card = k := by rw [Finset.card_erase_of_mem hc, hA]; rfl
      apply ih (A.erase c) hcard (s + (2 * n - 2)) S
      intro X hXS
      have hXU : X ⊆ U := hXS.trans (Finset.filter_subset _ _)
      have h1 := oc_le_or (fun x y => x ≠ y ∧ ∀ c ∈ A, ¬ (C.labelGraph c).Adj x y)
        (C.labelGraph c).Adj (fun x y => x ≠ y ∧ ∀ c' ∈ A.erase c, ¬ (C.labelGraph c').Adj x y)
        (by
          intro x y ⟨hxy, hno⟩
          by_cases hc' : (C.labelGraph c).Adj x y
          · exact Or.inr hc'
          · refine Or.inl ⟨hxy, fun c' hc'A => ?_⟩
            by_cases e : c' = c
            · subst e; exact hc'
            · exact hno c' (Finset.mem_erase.mpr ⟨e, hc'A⟩)) X
      have h2 := hU X hXU
      have h3 := hsp X hXS
      nlinarith
    -- cover U
    have hcover : U ⊆ insert v (U.filter (fun u => v ≠ u ∧ ∀ c ∈ A, ¬ (C.labelGraph c).Adj v u) ∪
        A.biUnion (fun c => U.filter ((C.labelGraph c).Adj v))) := by
      intro u hu
      rw [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
      by_cases huv : u = v
      · exact Or.inl huv
      right
      by_cases hall : ∀ c ∈ A, ¬ (C.labelGraph c).Adj v u
      · exact Or.inl ⟨hu, Ne.symm huv, hall⟩
      · push Not at hall
        obtain ⟨c, hcA, hadj⟩ := hall
        exact Or.inr ⟨c, hcA, Finset.mem_filter.mpr ⟨hu, hadj⟩⟩
    have hc1 := Finset.card_le_card hcover
    have hc2 := Finset.card_insert_le v (U.filter (fun u => v ≠ u ∧ ∀ c ∈ A, ¬ (C.labelGraph c).Adj v u) ∪
        A.biUnion (fun c => U.filter ((C.labelGraph c).Adj v)))
    have hc3 := Finset.card_union_le (U.filter (fun u => v ≠ u ∧ ∀ c ∈ A, ¬ (C.labelGraph c).Adj v u))
        (A.biUnion (fun c => U.filter ((C.labelGraph c).Adj v)))
    have hc4 := Finset.card_biUnion_le (s := A) (t := fun c => U.filter ((C.labelGraph c).Adj v))
    have hc5 : ∑ c ∈ A, (U.filter ((C.labelGraph c).Adj v)).card ≤
        A.card * bnd (2 * n - 2) (s + (2 * n - 2)) k := by
      have := Finset.sum_le_sum hS
      rw [Finset.sum_const, smul_eq_mul] at this
      exact this
    have hvdeg : (U.filter (fun u => v ≠ u ∧ ∀ c ∈ A, ¬ (C.labelGraph c).Adj v u)).card ≤ 2 * s := hv
    simp only [bnd]
    rw [hA] at hc5
    omega

lemma final_num (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    bnd (2 * n - 2) 0 k < 2 * n * (k + 2).factorial := by
  have h := bnd_le (2 * n - 2) k 0
  simp only [zero_add] at h
  have e : (k + 2).factorial = (k + 2) * (k + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; ring
  rw [e]
  have hf : 1 ≤ k.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e2 : 2 * (m + 1) - 2 = 2 * m := by omega
  rw [e2] at h
  have key : 3 * (2 * (k * (2 * m)) + 1) ≤ 2 * (m + 1) * ((k + 2) * (k + 1)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    nlinarith [Nat.mul_le_mul_left m (Nat.le_mul_self j)]
  rw [e2]
  have h4 := Nat.mul_le_mul_right k.factorial key
  nlinarith

theorem upper (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    SimpleGraph.multicolourGraphRamsey k (cycleGraph (2 * n + 1)) ≤ 2 * n * (k + 2).factorial := by
  apply Nat.sInf_le
  intro C
  by_contra hcon
  push Not at hcon
  have h := main_count n hn C (fun c ⟨f⟩ => (hcon c).false f) k Finset.univ (by simp) 0 Finset.univ (by
    intro X _
    have : oc (fun x y => x ≠ y ∧ ∀ c ∈ (Finset.univ : Finset (Fin k)), ¬ (C.labelGraph c).Adj x y) X = 0 := by
      unfold oc dg
      apply Finset.sum_eq_zero
      intro x _
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro y - ⟨hxy, hno⟩
      exact hno (C.get x y hxy) (Finset.mem_univ _) ((TopEdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, rfl⟩)
    rw [this]; exact Nat.zero_le _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have := final_num n k hn hk
  omega

end OMA554

theorem OMA.solution : type_of% @Erdos554.erdos_554.variants.upper_bound := by
  intro n hn k hk
  exact OMA554.upper n hn k hk
