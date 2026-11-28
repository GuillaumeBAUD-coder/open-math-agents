import OMAStatements.S_oeis_a285972

-- Problem: A285972: {10->1}-transform of the Thue-Morse word A010060.
-- Upstream: formal-conjectures statements/oeis-a285972.lean:0 (declaration OMA.S_oeis_a285972.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OEISA285972Proof

open OMA.S_oeis_a285972

private lemma length_le_two_mul_rep10 (w : List ℕ) :
    w.length ≤ 2 * (rep10 w).length := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h k ih =>
    subst hn
    match w with
    | [] => simp [rep10]
    | [_] => simp [rep10]
    | 1 :: 0 :: v =>
      have hv : v.length ≤ 2 * (rep10 v).length := ih v.length (by simp) v rfl
      change (1 :: 0 :: v).length ≤ 2 * (1 :: rep10 v).length
      simp only [List.length_cons]
      omega
    | 0 :: d :: v =>
      have hv : (d :: v).length ≤ 2 * (rep10 (d :: v)).length := ih (d :: v).length (by simp) (d :: v) rfl
      change (0 :: d :: v).length ≤ 2 * (0 :: rep10 (d :: v)).length
      simp only [List.length_cons] at hv ⊢
      omega
    | 1 :: (d + 1) :: v =>
      have hv : ((d + 1) :: v).length ≤ 2 * (rep10 ((d + 1) :: v)).length :=
        ih ((d + 1) :: v).length (by simp) ((d + 1) :: v) rfl
      change (1 :: (d + 1) :: v).length ≤ 2 * (1 :: rep10 ((d + 1) :: v)).length
      simp only [List.length_cons] at hv ⊢
      omega
    | (c + 2) :: d :: v =>
      have hv : (d :: v).length ≤ 2 * (rep10 (d :: v)).length := ih (d :: v).length (by simp) (d :: v) rfl
      change ((c + 2) :: d :: v).length ≤ 2 * ((c + 2) :: rep10 (d :: v)).length
      simp only [List.length_cons] at hv ⊢
      omega

private lemma rep10_prefix_rep01 (u : List ℕ) (hu : ∀ x ∈ u, x = 0 ∨ x = 1) :
    rep10 (1 :: u) <+: 1 :: rep01 u ∧ rep10 (0 :: u) <+: 0 :: rep01 (0 :: u) := by
  induction hn : u.length using Nat.strong_induction_on generalizing u with
  | h k ih =>
    constructor
    · match u with
      | [] =>
        simp [rep10, rep01]
      | c :: v =>
        have hc : c = 0 ∨ c = 1 := hu c (List.mem_cons_self)
        have hv : ∀ x ∈ v, x = 0 ∨ x = 1 := fun x hx => hu x (List.mem_cons_of_mem c hx)
        rcases hc with rfl | rfl
        · -- u = 0 :: v
          simp only [rep10]
          match v with
          | [] =>
            exact ⟨[0], by simp [rep10, rep01]⟩
          | d :: w =>
            have hd : d = 0 ∨ d = 1 := hv d (List.mem_cons_self)
            have hw : ∀ x ∈ w, x = 0 ∨ x = 1 := fun x hx => hv x (List.mem_cons_of_mem d hx)
            have ihw := ih w.length (by simp [← hn]) w hw rfl
            rcases hd with rfl | rfl
            · -- v = 0 :: w
              simp only [rep01]
              exact List.cons_prefix_cons.mpr ⟨rfl, ihw.2⟩
            · -- v = 1 :: w
              simp only [rep01]
              exact List.cons_prefix_cons.mpr ⟨rfl, ihw.1⟩
        · -- u = 1 :: v
          have ihv := ih v.length (by simp [← hn]) v hv rfl
          simp only [rep10, rep01]
          exact List.cons_prefix_cons.mpr ⟨rfl, ihv.1⟩
    · match u with
      | [] =>
        exact ⟨[0], by simp [rep10, rep01]⟩
      | c :: v =>
        have hc : c = 0 ∨ c = 1 := hu c (List.mem_cons_self)
        have hv : ∀ x ∈ v, x = 0 ∨ x = 1 := fun x hx => hu x (List.mem_cons_of_mem c hx)
        have ihv := ih v.length (by simp [← hn]) v hv rfl
        rcases hc with rfl | rfl
        · -- u = 0 :: v
          simp only [rep10, rep01]
          exact List.cons_prefix_cons.mpr ⟨rfl, ihv.2⟩
        · -- u = 1 :: v
          simp only [rep10, rep01]
          exact List.cons_prefix_cons.mpr ⟨rfl, ihv.1⟩

private lemma getD_eq_of_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma tm_binary (i : ℕ) : tm i = 0 ∨ tm i = 1 := by
  dsimp [tm]
  omega

private lemma tm_zero : tm 0 = 0 := by
  decide

private lemma tmWord_succ (L : ℕ) :
    ∃ u : List ℕ, tmWord (L + 1) = 0 :: u ∧ ∀ x ∈ u, x = 0 ∨ x = 1 := by
  refine ⟨(List.range L).map (fun i => tm (i + 1)), ?_, ?_⟩
  · dsimp [tmWord]
    rw [List.range_succ_eq_map, List.map_cons, tm_zero, List.map_map]
    rfl
  · intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact tm_binary (i + 1)

end OEISA285972Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a285972.main := by
  intro n hn
  dsimp [OMA.S_oeis_a285972.a, OMA.S_oeis_a285972.A285960]
  have hlen_eq : 2 * (n - 1) + 4 = 2 * n + 2 := by omega
  rw [hlen_eq]
  obtain ⟨u, hw, hu⟩ := OEISA285972Proof.tmWord_succ (2 * n + 1)
  have hpref : OMA.S_oeis_a285972.rep10 (OMA.S_oeis_a285972.tmWord (2 * n + 2)) <+:
      0 :: OMA.S_oeis_a285972.rep01 (OMA.S_oeis_a285972.tmWord (2 * n + 2)) := by
    rw [hw]
    exact (OEISA285972Proof.rep10_prefix_rep01 u hu).2
  have hlen : (OMA.S_oeis_a285972.tmWord (2 * n + 2)).length ≤
      2 * (OMA.S_oeis_a285972.rep10 (OMA.S_oeis_a285972.tmWord (2 * n + 2))).length :=
    OEISA285972Proof.length_le_two_mul_rep10 _
  have htm_len : (OMA.S_oeis_a285972.tmWord (2 * n + 2)).length = 2 * n + 2 := by
    simp [OMA.S_oeis_a285972.tmWord]
  have hidx : n - 1 < (OMA.S_oeis_a285972.rep10 (OMA.S_oeis_a285972.tmWord (2 * n + 2))).length := by
    omega
  rw [OEISA285972Proof.getD_eq_of_prefix hpref hidx]
  have hsub : n - 1 = (n - 1 - 1) + 1 := by omega
  rw [hsub]
  rfl
