import FormalConjectures.ErdosProblems.«1028»

-- Problem: Erdős Problem 1028 — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1028.lean:70 (declaration Erdos1028.erdos_1028.variants.lower_bound)
-- Credit: @NoahPuckett-IO (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof sketch, for `n ≥ 128` and any colouring `f` with values `±1`.

* Halving five times inside `{1, …, n}` gives five vertices `x₁, …, x₅` and a set `R` of three
  further vertices such that every edge from `xᵢ` to `R` has the same colour.
* For a vertex `x ∉ R` let `e x = ∑_{r ∈ R} f(x, r)`. It is an odd number, so `|e x| ≥ 1`,
  and `|e xᵢ| = 3`. Hence `∑_{x ∉ R} |e x| ≥ (n - 3) + 10`.
* Let `T` be the vertices outside `R` where `e` is positive (or where it is not positive).
  For one of them `|∑_{x ∈ T} e x| ≥ (n + 7) / 2`.
* Since `S(R ∪ T) = S(R) + S(T) + ∑_{x ∈ T} e x` and `|S(R)| ≤ 3`, one of `R ∪ T` and `T`
  has imbalance at least `(n + 1) / 4`.
-/

namespace OMA.E1028

open Finset

/-- The colour of the edge `{x, y}`. -/
def g (f : ℕ → ℕ → ℤ) (x y : ℕ) : ℤ := if x < y then f x y else f y x

/-- The signed sum of the edges inside `X`. -/
def s (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ :=
  ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y

/-- The signed degree of `x` into `R`. -/
def e (f : ℕ → ℕ → ℤ) (R : Finset ℕ) (x : ℕ) : ℤ := ∑ r ∈ R, g f x r

lemma g_pm {f : ℕ → ℕ → ℤ} (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (x y : ℕ) :
    g f x y = 1 ∨ g f x y = -1 := by
  unfold g
  split_ifs
  · exact hf _ _
  · exact hf _ _

lemma s_insert (f : ℕ → ℕ → ℤ) {X : Finset ℕ} {b : ℕ} (hb : b ∉ X) :
    s f (insert b X) = s f X + ∑ x ∈ X, g f b x := by
  unfold s
  rw [sum_insert hb]
  have h1 : ∀ x ∈ X, ∑ y ∈ (insert b X).filter (fun y => x < y), f x y =
      ∑ y ∈ X.filter (fun y => x < y), f x y + (if x < b then f x b else 0) := by
    intro x _
    rw [filter_insert]
    split_ifs with h
    · rw [sum_insert (by simp [hb])]
      ring
    · simp
  have h2 : ∑ y ∈ (insert b X).filter (fun y => b < y), f b y =
      ∑ y ∈ X.filter (fun y => b < y), f b y := by
    rw [filter_insert]
    simp
  rw [sum_congr rfl h1, h2, sum_add_distrib]
  have h3 : ∑ x ∈ X, g f b x = ∑ y ∈ X.filter (fun y => b < y), f b y +
      ∑ x ∈ X, (if x < b then f x b else 0) := by
    rw [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    have hxb : x ≠ b := fun h => hb (h ▸ hx)
    unfold g
    split_ifs <;> first | (exfalso; omega) | simp
  rw [h3]
  ring

lemma s_union (f : ℕ → ℕ → ℤ) (R T : Finset ℕ) (h : Disjoint R T) :
    s f (R ∪ T) = s f R + s f T + ∑ t ∈ T, e f R t := by
  induction T using Finset.induction_on with
  | empty => simp [s]
  | insert t T ht ih =>
    have hR : t ∉ R := fun hr => disjoint_left.1 h hr (mem_insert_self t T)
    have hd : Disjoint R T := disjoint_of_subset_right (subset_insert t T) h
    rw [union_insert, s_insert f (by simp [hR, ht]), ih hd, s_insert f ht, sum_insert ht,
      sum_union hd]
    unfold e
    ring

lemma abs_s_three {f : ℕ → ℕ → ℤ} (hf : ∀ x y, f x y = 1 ∨ f x y = -1) {R : Finset ℕ}
    (hR : R.card = 3) : |s f R| ≤ 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 hR
  rw [s_insert f (by simp [hab, hac]), s_insert f (by simp [hbc])]
  have h0 : s f {c} = 0 := by simp [s, Finset.filter_singleton]
  rw [h0, sum_singleton, sum_insert (by simp [hbc]), sum_singleton]
  rcases g_pm hf b c with h1 | h1 <;> rcases g_pm hf a b with h2 | h2 <;>
    rcases g_pm hf a c with h3 | h3 <;> rw [h1, h2, h3] <;> norm_num

lemma one_le_abs_e {f : ℕ → ℕ → ℤ} (hf : ∀ x y, f x y = 1 ∨ f x y = -1) {R : Finset ℕ}
    (hR : R.card = 3) (x : ℕ) : 1 ≤ |e f R x| := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 hR
  unfold e
  rw [sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton]
  rcases g_pm hf x a with h1 | h1 <;> rcases g_pm hf x b with h2 | h2 <;>
    rcases g_pm hf x c with h3 | h3 <;> rw [h1, h2, h3] <;> norm_num

/-- Repeated halving: `k` vertices, each monochromatic towards a set of size at least `c`. -/
lemma mono {f : ℕ → ℕ → ℤ} (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (k : ℕ) :
    ∀ (c : ℕ) (A : Finset ℕ), 2 ^ k * (c + 1) ≤ A.card →
      ∃ F B : Finset ℕ, F ⊆ A ∧ F.card = k ∧ B ⊆ A ∧ Disjoint F B ∧ c ≤ B.card ∧
        ∀ x ∈ F, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ b ∈ B, g f x b = σ := by
  induction k with
  | zero =>
    intro c A hA
    refine ⟨∅, A, empty_subset _, rfl, subset_refl _, disjoint_empty_left _, by simp at hA; omega,
      by simp⟩
  | succ k ih =>
    intro c A hA
    have hA' : 2 ^ k * ((2 * c + 1) + 1) ≤ A.card := by
      have : 2 ^ (k + 1) * (c + 1) = 2 ^ k * ((2 * c + 1) + 1) := by ring
      omega
    obtain ⟨F, B, hFA, hFc, hBA, hFB, hBc, hm⟩ := ih (2 * c + 1) A hA'
    have hBne : B.Nonempty := card_pos.1 (by omega)
    obtain ⟨x, hx⟩ := hBne
    have hsplit := card_filter_add_card_filter_not (s := B.erase x) (fun b => g f x b = 1)
    have hcard : (B.erase x).card + 1 = B.card := card_erase_add_one hx
    have hxF : x ∉ F := fun h => disjoint_left.1 hFB h hx
    have key : ∀ B' : Finset ℕ, B' ⊆ B.erase x → c ≤ B'.card → ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
        (∀ b ∈ B', g f x b = σ) →
        ∃ F B : Finset ℕ, F ⊆ A ∧ F.card = k + 1 ∧ B ⊆ A ∧ Disjoint F B ∧ c ≤ B.card ∧
          ∀ x ∈ F, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ b ∈ B, g f x b = σ := by
      intro B' hB' hc σ hσ hxσ
      have hB'B : B' ⊆ B := hB'.trans (erase_subset x B)
      refine ⟨insert x F, B', insert_subset (hBA hx) hFA, by rw [card_insert_of_notMem hxF, hFc],
        hB'B.trans hBA, ?_, hc, ?_⟩
      · rw [disjoint_insert_left]
        exact ⟨fun h => (notMem_erase x B) (hB' h), disjoint_of_subset_right hB'B hFB⟩
      · intro y hy
        rw [mem_insert] at hy
        rcases hy with rfl | hy
        · exact ⟨σ, hσ, hxσ⟩
        · obtain ⟨τ, hτ, hyτ⟩ := hm y hy
          exact ⟨τ, hτ, fun b hb => hyτ b (hB'B hb)⟩
    by_cases h1 : c ≤ ((B.erase x).filter (fun b => g f x b = 1)).card
    · exact key _ (filter_subset _ _) h1 1 (Or.inl rfl) (fun b hb => (mem_filter.1 hb).2)
    · refine key ((B.erase x).filter (fun b => ¬ g f x b = 1)) (filter_subset _ _) (by omega)
        (-1) (Or.inr rfl) ?_
      intro b hb
      rcases g_pm hf x b with h | h
      · exact absurd h (mem_filter.1 hb).2
      · exact h

theorem main (n : ℕ) (hn : 128 ≤ n) (f : ℕ → ℕ → ℤ) (hf : ∀ x y, f x y = 1 ∨ f x y = -1)
    (m : ℕ) (hm : ∀ X ⊆ Icc 1 n, Erdos1028.imbalance f X ≤ (m : ℤ)) : n + 1 ≤ 4 * m := by
  have hm' : ∀ X ⊆ Icc 1 n, |s f X| ≤ (m : ℤ) := hm
  obtain ⟨F, B, hFA, hFc, hBA, hFB, hBc, hmono⟩ :=
    mono hf 5 3 (Icc 1 n) (by rw [Nat.card_Icc]; omega)
  obtain ⟨R, hRB, hRc⟩ := exists_subset_card_eq (show 3 ≤ B.card from hBc)
  have hRI : R ⊆ Icc 1 n := hRB.trans hBA
  set U := Icc 1 n \ R with hUdef
  have hUc : U.card + 3 = n := by
    have := card_sdiff_add_card_eq_card hRI
    rw [← hUdef, Nat.card_Icc, hRc] at this
    omega
  have hFU : F ⊆ U := by
    intro x hx
    rw [mem_sdiff]
    exact ⟨hFA hx, fun hr => disjoint_left.1 hFB hx (hRB hr)⟩
  -- the signed degrees
  have hF3 : ∀ x ∈ F, |e f R x| = 3 := by
    intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := hmono x hx
    have : e f R x = 3 * σ := by
      unfold e
      rw [sum_congr rfl (fun r hr => hxσ r (hRB hr)), sum_const, hRc]
      simp
    rw [this]
    rcases hσ with rfl | rfl <;> norm_num
  have hsumF : ∑ x ∈ F, |e f R x| = 15 := by
    rw [sum_congr rfl hF3, sum_const, hFc]
    norm_num
  have hsumUF : ((U \ F).card : ℤ) ≤ ∑ x ∈ U \ F, |e f R x| := by
    have : ∑ x ∈ U \ F, (1 : ℤ) ≤ ∑ x ∈ U \ F, |e f R x| :=
      sum_le_sum (fun x _ => one_le_abs_e hf hRc x)
    simpa using this
  have hUFc : (U \ F).card + 5 = U.card := by
    have := card_sdiff_add_card_eq_card hFU
    rw [hFc] at this
    exact this
  have hsumU : (n : ℤ) + 7 ≤ ∑ x ∈ U, |e f R x| := by
    rw [← sum_sdiff hFU, hsumF]
    have h1 : ((U \ F).card : ℤ) + 5 = U.card := by exact_mod_cast hUFc
    have h2 : (U.card : ℤ) + 3 = n := by exact_mod_cast hUc
    linarith
  -- split by the sign of the degree
  set Tp := U.filter (fun x => 0 < e f R x) with hTp
  set Tm := U.filter (fun x => ¬ 0 < e f R x) with hTm
  have hsplit : ∑ x ∈ U, |e f R x| = ∑ x ∈ Tp, e f R x + ∑ x ∈ Tm, (- e f R x) := by
    rw [← sum_filter_add_sum_filter_not U (fun x => 0 < e f R x)]
    congr 1
    · apply sum_congr rfl
      intro x hx
      exact abs_of_pos (mem_filter.1 hx).2
    · apply sum_congr rfl
      intro x hx
      exact abs_of_nonpos (not_lt.1 (mem_filter.1 hx).2)
  -- the bound for any `T ⊆ U`
  have bound : ∀ T ⊆ U, |∑ x ∈ T, e f R x| ≤ 2 * (m : ℤ) + 3 := by
    intro T hT
    have hTI : T ⊆ Icc 1 n := hT.trans sdiff_subset
    have hdis : Disjoint R T := by
      rw [disjoint_right]
      intro x hx hr
      exact (mem_sdiff.1 (hT hx)).2 hr
    have hu := s_union f R T hdis
    have h1 := hm' (R ∪ T) (union_subset hRI hTI)
    have h2 := hm' T hTI
    have h3 := abs_s_three hf hRc
    have : ∑ x ∈ T, e f R x = s f (R ∪ T) - s f R - s f T := by rw [hu]; ring
    rw [this]
    calc |s f (R ∪ T) - s f R - s f T| ≤ |s f (R ∪ T)| + |s f R| + |s f T| := by
          have := abs_sub (s f (R ∪ T) - s f R) (s f T)
          have := abs_sub (s f (R ∪ T)) (s f R)
          linarith
      _ ≤ 2 * (m : ℤ) + 3 := by linarith
  have bp := bound Tp (filter_subset _ _)
  have bm := bound Tm (filter_subset _ _)
  have hneg : ∑ x ∈ Tm, (- e f R x) = - ∑ x ∈ Tm, e f R x := sum_neg_distrib _
  rw [abs_le] at bp bm
  have : (n : ℤ) + 7 ≤ 2 * (2 * (m : ℤ) + 3) := by
    rw [hsplit, hneg] at hsumU
    linarith [bp.2, bm.1]
  omega

end OMA.E1028

open Filter OMA.E1028 in
theorem OMA.solution : type_of% @Erdos1028.erdos_1028.variants.lower_bound := by
  refine eventually_atTop.2 ⟨128, fun n hn => ?_⟩
  have hne : {m : ℕ | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
      ∀ X ⊆ Finset.Icc 1 n, Erdos1028.imbalance f X ≤ (m : ℤ)}.Nonempty := by
    refine ⟨(Finset.Icc 1 n).powerset.sup
      (fun X => (Erdos1028.imbalance (fun _ _ => (1 : ℤ)) X).toNat),
      fun _ _ => 1, fun _ _ => Or.inl rfl, fun X hX => ?_⟩
    have h1 := Int.self_le_toNat (Erdos1028.imbalance (fun _ _ => (1 : ℤ)) X)
    have h2 : (Erdos1028.imbalance (fun _ _ => (1 : ℤ)) X).toNat ≤
        (Finset.Icc 1 n).powerset.sup
          (fun X => (Erdos1028.imbalance (fun _ _ => (1 : ℤ)) X).toNat) :=
      Finset.le_sup (f := fun X => (Erdos1028.imbalance (fun _ _ => (1 : ℤ)) X).toNat)
        (Finset.mem_powerset.2 hX)
    have h3 : ((Erdos1028.imbalance (fun _ _ => (1 : ℤ)) X).toNat : ℤ) ≤
        (((Finset.Icc 1 n).powerset.sup
          (fun X => (Erdos1028.imbalance (fun _ _ => (1 : ℤ)) X).toNat) : ℕ) : ℤ) := by
      exact_mod_cast h2
    exact h1.trans h3
  obtain ⟨f, hf, hm⟩ := Nat.sInf_mem hne
  have key : n + 1 ≤ 4 * Erdos1028.H n := main n hn f hf _ hm
  have hreal : (n : ℝ) ≤ 4 * (Erdos1028.H n : ℝ) := by exact_mod_cast (by omega : n ≤ 4 * Erdos1028.H n)
  linarith
