import FormalConjectures.ErdosProblems.«717»

-- Problem: Erdős Problem 717 — erdos fajtlowicz
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/717.lean:137 (declaration Erdos717.erdos_717.variants.erdos_fajtlowicz)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Erdős–Fajtlowicz: almost every graph has χ(G) > (1/100)(√n / log n) σ(G), by a first-moment
count of graphs with a large independent set or a dense set of r ≈ 4√n vertices. -/

open SimpleGraph Finset
open scoped Classical

namespace LB

noncomputable def pairs {n : ℕ} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  S.offDiag.image (Function.uncurry Sym2.mk)

lemma card_pairs {n : ℕ} (S : Finset (Fin n)) : (pairs S).card = S.card.choose 2 := by
  unfold pairs; convert Sym2.card_image_offDiag S

lemma pairs_subset {n : ℕ} (S : Finset (Fin n)) :
    pairs S ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset := by
  intro e he
  simp only [pairs, mem_image, mem_offDiag] at he
  obtain ⟨⟨x, y⟩, ⟨-, -, hxy⟩, rfl⟩ := he
  simpa using hxy

lemma card_top {n : ℕ} : (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2 := by
  simpa using card_edgeFinset_top_eq_card_choose_two (V := Fin n)

lemma edge_sub {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.edgeFinset ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset :=
  edgeFinset_mono le_top

lemma count_indep {n : ℕ} (S : Finset (Fin n)) :
    (univ.filter fun G : SimpleGraph (Fin n) => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y).card ≤
      2 ^ (n.choose 2 - S.card.choose 2) := by
  set E := (⊤ : SimpleGraph (Fin n)).edgeFinset
  have hinj : Set.InjOn (fun G : SimpleGraph (Fin n) => G.edgeFinset) Set.univ :=
    fun a _ b _ h => edgeFinset_inj.mp h
  rw [← card_image_of_injOn (f := fun G : SimpleGraph (Fin n) => G.edgeFinset)
    (fun a _ b _ h => edgeFinset_inj.mp h)]
  calc _ ≤ ((E \ pairs S).powerset).card := by
        apply card_le_card
        intro s hs
        simp only [mem_image, mem_filter, mem_univ, true_and] at hs
        obtain ⟨G, hG, rfl⟩ := hs
        rw [mem_powerset]
        intro e he
        rw [mem_sdiff]
        refine ⟨edge_sub G he, ?_⟩
        intro hp
        simp only [pairs, mem_image, mem_offDiag] at hp
        obtain ⟨⟨x, y⟩, ⟨hx, hy, -⟩, rfl⟩ := hp
        exact hG x hx y hy (by simpa using he)
    _ = _ := by
        rw [card_powerset, card_sdiff_of_subset (pairs_subset S), card_top, card_pairs]

lemma count_sub (M : ℕ) {α : Type*} (T : Finset α) (hT : T.card = M) (a : ℕ) :
    (T.powerset.filter fun t => t.card ≤ a).card ≤ ∑ j ∈ range (a+1), M.choose j := by
  calc _ ≤ ((range (a+1)).biUnion fun j => T.powersetCard j).card := by
        apply card_le_card
        intro t ht
        simp only [mem_filter, mem_powerset] at ht
        simp only [mem_biUnion, mem_range, mem_powersetCard]
        exact ⟨t.card, by omega, ht.1, rfl⟩
    _ ≤ _ := by
        refine card_biUnion_le.trans (le_of_eq ?_)
        simp [card_powersetCard, hT]

lemma count_dense {n : ℕ} (S : Finset (Fin n)) (a : ℕ) :
    (univ.filter fun G : SimpleGraph (Fin n) => (pairs S \ G.edgeFinset).card ≤ a).card ≤
      (∑ j ∈ range (a+1), (S.card.choose 2).choose j) * 2 ^ (n.choose 2 - S.card.choose 2) := by
  set E := (⊤ : SimpleGraph (Fin n)).edgeFinset
  set T := pairs S
  rw [← card_image_of_injOn (f := fun G : SimpleGraph (Fin n) => G.edgeFinset)
    (fun a _ b _ h => edgeFinset_inj.mp h)]
  have key : ((univ.filter fun G : SimpleGraph (Fin n) => (T \ G.edgeFinset).card ≤ a).image
      (fun G => G.edgeFinset)).card ≤
      ((T.powerset.filter fun t => t.card ≤ a) ×ˢ (E \ T).powerset).card := by
    apply card_le_card_of_injOn (fun s => (T \ s, s \ T))
    · intro s hs
      simp only [coe_image, coe_filter, mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq] at hs
      obtain ⟨G, hG, rfl⟩ := hs
      simp only [coe_product, coe_filter, coe_powerset, Set.mem_prod, Set.mem_ofPred_eq,
        Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
      refine ⟨⟨mem_powerset.mpr sdiff_subset, hG⟩, ?_⟩
      exact sdiff_subset_sdiff (edge_sub G) le_rfl
    · intro s hs t ht h
      simp only [coe_image, coe_filter, mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq] at hs ht
      simp only [Prod.mk.injEq] at h
      ext e
      by_cases he : e ∈ T
      · have := congrArg (e ∈ ·) h.1
        simp only [mem_sdiff, he, true_and, eq_iff_iff] at this
        exact not_iff_not.mp this
      · have := congrArg (e ∈ ·) h.2
        simpa [mem_sdiff, he] using this
  refine key.trans ?_
  rw [card_product, card_powerset, card_sdiff_of_subset (pairs_subset S), card_top]
  have := count_sub (S.card.choose 2) T (card_pairs S) a
  rw [card_pairs]
  exact Nat.mul_le_mul_right _ this

lemma binom_bound (M a : ℕ) (h : a ≤ M) :
    (∑ j ∈ range (a+1), M.choose j) * 8 ^ (M - a) ≤ 9 ^ M := by
  have h9 : (9:ℕ) ^ M = ∑ j ∈ range (M+1), 1 ^ j * 8 ^ (M - j) * M.choose j := by
    rw [show (9:ℕ) = 1 + 8 by rfl, add_pow]; simp only [Nat.cast_id]
  rw [h9, sum_mul]
  calc ∑ j ∈ range (a+1), M.choose j * 8 ^ (M - a)
      ≤ ∑ j ∈ range (a+1), 1 ^ j * 8 ^ (M - j) * M.choose j := by
        apply sum_le_sum; intro j hj
        have hj' : j ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hj)
        rw [one_pow, one_mul, mul_comm]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hj' M))
    _ ≤ _ := sum_le_sum_of_subset (range_subset_range.mpr (by omega))


open Erdos717 in
lemma interior_mem {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (huv : u ≠ v) (hadj : ¬ G.Adj u v) : p.getVert 1 ∈ walkInteriorSet p := by
  have h0 : p.length ≠ 0 := fun h => huv (SimpleGraph.Walk.eq_of_length_eq_zero h)
  have h1 : p.length ≠ 1 := fun h => hadj (SimpleGraph.Walk.adj_of_length_eq_one h)
  refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
  · intro h
    have := hp.getVert_injOn (show 1 ∈ {i | i ≤ p.length} by simp; omega)
      (show 0 ∈ {i | i ≤ p.length} by simp) (by rw [h, SimpleGraph.Walk.getVert_zero])
    omega
  · intro h
    have := hp.getVert_injOn (show 1 ∈ {i | i ≤ p.length} by simp; omega)
      (show p.length ∈ {i | i ≤ p.length} by simp) (by rw [h, SimpleGraph.Walk.getVert_length])
    omega

open Erdos717 in
lemma contains_sigma {n : ℕ} (G : SimpleGraph (Fin n)) :
    ContainsCliqueSubdivision G (cliqueSubdivisionNumber G) := by
  unfold cliqueSubdivisionNumber
  refine Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ?_
  exact ⟨{ branch := ⟨Fin.elim0, fun a => a.elim0⟩
           path := fun e => e.1.1.elim0
           path_isPath := fun e => e.1.1.elim0
           interior_avoids_branch := fun e => e.1.1.elim0
           interior_pairwise := fun e => e.1.1.elim0 }⟩

open Erdos717 in
lemma sub_dense {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ)
    (hr : r ≤ cliqueSubdivisionNumber G) :
    ∃ S : Finset (Fin n), S.card = r ∧ (pairs S \ G.edgeFinset).card ≤ n := by
  obtain ⟨D⟩ := contains_sigma G
  set m := cliqueSubdivisionNumber G
  set b := D.branch
  let ι : Fin r → Fin m := Fin.castLE hr
  have hι : Function.Injective ι := Fin.castLE_injective hr
  let S : Finset (Fin n) := univ.image (fun i => b (ι i))
  have hS : S.card = r := by
    have : S = univ.image (b ∘ ι) := rfl
    rw [this, card_image_of_injective _ (b.injective.comp hι)]; simp
  refine ⟨S, hS, ?_⟩
  let P : Finset (CliqueEdge m) := univ.filter (fun e => e.1.1.val < r ∧ e.1.2.val < r ∧
    ¬ G.Adj (b e.1.1) (b e.1.2))
  let f : CliqueEdge m → Fin n := fun e => (D.path e).getVert 1
  have hint : ∀ e ∈ P, f e ∈ walkInteriorSet (D.path e) := by
    intro e he
    simp only [P, mem_filter, mem_univ, true_and] at he
    refine interior_mem _ (D.path_isPath e) ?_ he.2.2
    intro h
    exact (ne_of_lt e.2) (b.injective h)
  have hP : P.card ≤ n := by
    have : P.card ≤ (univ : Finset (Fin n)).card := by
      apply card_le_card_of_injOn f (fun _ _ => mem_coe.mpr (mem_univ _))
      intro e he e' he' hee
      by_contra hne
      have hd := D.interior_pairwise hne
      exact Set.disjoint_left.mp hd (hint e he) (hee ▸ hint e' he')
    simpa using this
  refine le_trans (card_le_card (t := P.image (fun e => s(b e.1.1, b e.1.2))) ?_)
    (card_image_le.trans hP)
  intro z hz
  rw [mem_sdiff] at hz
  obtain ⟨hz, hzG⟩ := hz
  simp only [pairs, mem_image, mem_offDiag] at hz
  obtain ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩ := hz
  simp only [S, mem_image, mem_univ, true_and] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hij : i ≠ j := fun h => hxy (by rw [h])
  have hnadj : ¬ G.Adj (b (ι i)) (b (ι j)) := by
    intro h; exact hzG (by simpa using h)
  rcases lt_or_gt_of_ne hij with h | h
  · refine mem_image.mpr ⟨⟨(ι i, ι j), by simpa [ι] using h⟩, ?_, rfl⟩
    simp only [P, mem_filter, mem_univ, true_and]
    exact ⟨by simp [ι], by simp [ι], hnadj⟩
  · refine mem_image.mpr ⟨⟨(ι j, ι i), by simpa [ι] using h⟩, ?_, ?_⟩
    · simp only [P, mem_filter, mem_univ, true_and]
      exact ⟨by simp [ι], by simp [ι], fun h' => hnadj h'.symm⟩
    · simp [Sym2.eq_swap]

lemma chi_bound {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (h : ∀ S : Finset (Fin n), S.card = k → ¬ ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    n ≤ (k - 1) * G.chromaticNumber.toNat := by
  obtain ⟨C⟩ := colorable_chromaticNumber_of_fintype G
  have := card_le_mul_card_image_of_maps_to (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin G.chromaticNumber.toNat))) (f := C) (fun _ _ => mem_univ _) (k - 1) ?_
  · simpa using this
  intro c _
  by_contra hc
  push Not at hc
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (s := univ.filter fun a => C a = c)
    (n := k) (by omega)
  apply h T hTc
  intro x hx y hy hxy
  have hx' := (mem_filter.mp (hT hx)).2
  have hy' := (mem_filter.mp (hT hy)).2
  exact C.valid hxy (hx'.trans hy'.symm)

end LB

namespace LB
open Finset
open scoped Classical

noncomputable def kk (n : ℕ) : ℕ := 2 * (Nat.log 2 n + 1) + 3
def rr (n : ℕ) : ℕ := 4 * Nat.sqrt n + 5

lemma choose_two_kk (n : ℕ) : (kk n).choose 2 = kk n * (Nat.log 2 n + 2) := by
  rw [Nat.choose_two_right]
  have : kk n - 1 = 2 * (Nat.log 2 n + 2) := by unfold kk; omega
  rw [this, show kk n * (2 * (Nat.log 2 n + 2)) = 2 * (kk n * (Nat.log 2 n + 2)) by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma term1 (n : ℕ) :
    n * (n.choose (kk n) * 2 ^ (n.choose 2 - (kk n).choose 2)) ≤ 2 ^ (n.choose 2) := by
  by_cases hk : n < kk n
  · simp [Nat.choose_eq_zero_of_lt hk]
  push Not at hk
  have hc : (kk n).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hk
  have hL : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hnk : n ≤ 2 ^ kk n := by
    refine hL.le.trans (Nat.pow_le_pow_right (by norm_num) ?_); unfold kk; omega
  have key : n * n.choose (kk n) ≤ 2 ^ (kk n).choose 2 := by
    calc n * n.choose (kk n) ≤ 2 ^ kk n * n ^ kk n :=
          Nat.mul_le_mul hnk (Nat.choose_le_pow n (kk n))
      _ = (2 * n) ^ kk n := by rw [mul_pow]
      _ ≤ (2 ^ (Nat.log 2 n + 2)) ^ kk n := by
          apply Nat.pow_le_pow_left; rw [pow_succ]; linarith
      _ = _ := by rw [choose_two_kk, ← pow_mul, mul_comm]
  calc n * (n.choose (kk n) * 2 ^ (n.choose 2 - (kk n).choose 2))
      = (n * n.choose (kk n)) * 2 ^ (n.choose 2 - (kk n).choose 2) := by ring
    _ ≤ 2 ^ (kk n).choose 2 * 2 ^ (n.choose 2 - (kk n).choose 2) := Nat.mul_le_mul_right _ key
    _ = _ := by rw [← pow_add]; congr 1; omega

lemma M_ge (n : ℕ) : 8 * n ≤ (rr n).choose 2 := by
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
  have h := Nat.lt_succ_sqrt n
  have h1 : rr n - 1 = 4 * Nat.sqrt n + 4 := by unfold rr; omega
  rw [h1]; unfold rr
  simp only [Nat.succ_eq_add_one] at h
  nlinarith

lemma term2 (n : ℕ) (hp : n ^ (rr n + 1) ≤ 12 ^ n) :
    n * (n.choose (rr n) * ((∑ j ∈ range (n+1), ((rr n).choose 2).choose j) *
      2 ^ (n.choose 2 - (rr n).choose 2))) ≤ 2 ^ (n.choose 2) := by
  by_cases hk : n < rr n
  · simp [Nat.choose_eq_zero_of_lt hk]
  push Not at hk
  have h8 := M_ge n
  have hc : (rr n).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hk
  set M := (rr n).choose 2 with hM
  set A := ∑ j ∈ range (n+1), M.choose j
  have hA := binom_bound M n (by omega)
  have h1 : n * n.choose (rr n) ≤ n ^ (rr n + 1) := by
    rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
  have key : n * n.choose (rr n) * A ≤ 2 ^ M := by
    apply Nat.le_of_mul_le_mul_right (c := 8 ^ M) _ (by positivity)
    have e8 : 8 ^ M = 8 ^ (M - n) * 8 ^ n := by rw [← pow_add]; congr 1; omega
    have e9 : 9 ^ M = (9 ^ 8) ^ n * 9 ^ (M - 8 * n) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have e16 : 2 ^ M * 8 ^ M = (16 ^ 8) ^ n * 16 ^ (M - 8 * n) := by
      rw [← mul_pow, ← pow_mul, ← pow_add]; congr 1; omega
    calc n * n.choose (rr n) * A * 8 ^ M
        = n * n.choose (rr n) * (A * 8 ^ (M - n)) * 8 ^ n := by rw [e8]; ring
      _ ≤ 12 ^ n * 9 ^ M * 8 ^ n := Nat.mul_le_mul (Nat.mul_le_mul (h1.trans hp) hA) le_rfl
      _ = (12 * 8 * 9 ^ 8) ^ n * 9 ^ (M - 8 * n) := by rw [e9, mul_pow, mul_pow]; ring
      _ ≤ (16 ^ 8) ^ n * 16 ^ (M - 8 * n) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) n) (Nat.pow_le_pow_left (by norm_num) _)
      _ = _ := e16.symm
  calc n * (n.choose (rr n) * (A * 2 ^ (n.choose 2 - M)))
      = (n * n.choose (rr n) * A) * 2 ^ (n.choose 2 - M) := by ring
    _ ≤ 2 ^ M * 2 ^ (n.choose 2 - M) := Nat.mul_le_mul_right _ key
    _ = _ := by rw [← pow_add]; congr 1; omega

lemma pow_ev : ∀ᶠ n : ℕ in Filter.atTop, n ^ (rr n + 1) ≤ 12 ^ n := by
  have h := (isLittleO_log_rpow_atTop (r := (1/2:ℝ)) (by norm_num)).bound
    (c := 1/20) (by norm_num)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', Filter.eventually_ge_atTop 1] with n hn hn1
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hsq : Real.sqrt n = (n:ℝ) ^ (1/2:ℝ) := Real.sqrt_eq_rpow _
  rw [← hsq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx),
    abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  set q := Real.sqrt (n:ℝ)
  have hq2 : q ^ 2 = n := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : 1 ≤ q := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx
  have hs : (Nat.sqrt n : ℝ) ≤ q := Real.nat_sqrt_le_real_sqrt
  have hl2 := Real.log_two_gt_d9
  have hl12 : Real.log 2 ≤ Real.log 12 := Real.log_le_log (by norm_num) (by norm_num)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hx
  have key : ((rr n + 1 : ℕ) : ℝ) * Real.log n ≤ (n : ℝ) * Real.log 12 := by
    have hr : ((rr n + 1 : ℕ) : ℝ) ≤ 4 * q + 6 := by unfold rr; push_cast; linarith
    calc ((rr n + 1 : ℕ) : ℝ) * Real.log n ≤ (4 * q + 6) * (1/20 * q) :=
          mul_le_mul hr hn hlogn (by positivity)
      _ ≤ (n : ℝ) * Real.log 2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hl12 (by linarith)
  have : ((n:ℝ)) ^ (rr n + 1) ≤ (12:ℝ) ^ n := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    exact_mod_cast key
  exact_mod_cast this

open Erdos717 in
lemma good {n : ℕ} (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (h1 : ∀ S : Finset (Fin n), S.card = kk n → ¬ ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
    (h2 : ∀ S : Finset (Fin n), S.card = rr n → ¬ (pairs S \ G.edgeFinset).card ≤ n) :
    (1/100 : ℝ) * (Real.sqrt n / Real.log n) * (cliqueSubdivisionNumber G : ℝ) <
      (G.chromaticNumber.toNat : ℝ) := by
  have hχ := chi_bound G (kk n) h1
  have hσ : cliqueSubdivisionNumber G ≤ 4 * Nat.sqrt n + 4 := by
    by_contra hc
    push Not at hc
    obtain ⟨S, hS, hS'⟩ := sub_dense G (rr n) (by unfold rr; omega)
    exact h2 S hS hS'
  have hx : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hlog8 : (2:ℝ) ≤ Real.log n := by
    have : Real.log 8 ≤ Real.log n := Real.log_le_log (by norm_num) hx
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hL : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h0 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    have h0' : ((2:ℝ)) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast h0
    have := Real.log_le_log (by positivity) h0'
    rwa [Real.log_pow] at this
  have hL0 : (0:ℝ) ≤ Nat.log 2 n := by positivity
  have hk1 : ((kk n - 1 : ℕ) : ℝ) = 2 * (Nat.log 2 n : ℝ) + 4 := by
    rw [show kk n - 1 = 2 * Nat.log 2 n + 4 by unfold kk; omega]; push_cast; ring
  have hkb : ((kk n - 1 : ℕ) : ℝ) ≤ 5 * Real.log n := by
    rw [hk1]; nlinarith
  have hχr : (n:ℝ) ≤ ((kk n - 1 : ℕ) : ℝ) * (G.chromaticNumber.toNat : ℝ) := by
    exact_mod_cast hχ
  set ℓ := Real.log (n:ℝ)
  set χ : ℝ := (G.chromaticNumber.toNat : ℝ)
  have hχ0 : 0 ≤ χ := by positivity
  have hχ2 : (n:ℝ) ≤ 5 * ℓ * χ := hχr.trans (mul_le_mul_of_nonneg_right hkb hχ0)
  set q := Real.sqrt (n:ℝ)
  have hq2 : q ^ 2 = n := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : 1 ≤ q := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hs : (Nat.sqrt n : ℝ) ≤ q := Real.nat_sqrt_le_real_sqrt
  have hσr : (cliqueSubdivisionNumber G : ℝ) ≤ 4 * q + 4 := by
    have : (cliqueSubdivisionNumber G : ℝ) ≤ 4 * (Nat.sqrt n : ℝ) + 4 := by exact_mod_cast hσ
    linarith
  have hσ0 : (0:ℝ) ≤ cliqueSubdivisionNumber G := by positivity
  have hℓ : 0 < ℓ := by linarith
  rw [show (1/100 : ℝ) * (q / ℓ) * (cliqueSubdivisionNumber G : ℝ) =
      q * (cliqueSubdivisionNumber G : ℝ) / (100 * ℓ) by field_simp]
  rw [div_lt_iff₀ (by positivity)]
  have : q * (cliqueSubdivisionNumber G : ℝ) ≤ q * (4 * q + 4) :=
    mul_le_mul_of_nonneg_left hσr hq0
  nlinarith

open Erdos717 in
theorem main : ∃ C : ℝ, 0 < C ∧
      Filter.Tendsto (fun n : ℕ =>
        (Nat.card {G : SimpleGraph (Fin n) //
          ¬ (C * (Real.sqrt n / Real.log n) * (cliqueSubdivisionNumber G : ℝ) <
            (G.chromaticNumber.toNat : ℝ))} : ℝ) / 2 ^ n.choose 2) Filter.atTop (nhds 0) := by
  refine ⟨1/100, by norm_num, ?_⟩
  have hb : ∀ᶠ n : ℕ in Filter.atTop, (Nat.card {G : SimpleGraph (Fin n) //
          ¬ ((1/100 : ℝ) * (Real.sqrt n / Real.log n) * (cliqueSubdivisionNumber G : ℝ) <
            (G.chromaticNumber.toNat : ℝ))} : ℝ) / 2 ^ n.choose 2 ≤ 2 / n := by
    filter_upwards [pow_ev, Filter.eventually_ge_atTop 8] with n hp hn
    set P : SimpleGraph (Fin n) → Prop := fun G =>
      ¬ ((1/100 : ℝ) * (Real.sqrt n / Real.log n) * (cliqueSubdivisionNumber G : ℝ) <
            (G.chromaticNumber.toNat : ℝ))
    have hsub : (univ.filter P) ⊆
        ((powersetCard (kk n) univ).biUnion fun S =>
          univ.filter fun G : SimpleGraph (Fin n) => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) ∪
        ((powersetCard (rr n) univ).biUnion fun S =>
          univ.filter fun G : SimpleGraph (Fin n) => (pairs S \ G.edgeFinset).card ≤ n) := by
      intro G hG
      simp only [P, mem_filter, mem_univ, true_and] at hG
      by_contra hc
      simp only [mem_union, mem_biUnion, mem_powersetCard, subset_univ, true_and, mem_filter,
        mem_univ, not_or, not_exists, not_and] at hc
      exact hG (good hn G (fun S hS => hc.1 S hS) (fun S hS => hc.2 S hS))
    have hcard : Nat.card {G : SimpleGraph (Fin n) // P G} ≤
        n.choose (kk n) * 2 ^ (n.choose 2 - (kk n).choose 2) +
        n.choose (rr n) * ((∑ j ∈ range (n+1), ((rr n).choose 2).choose j) *
          2 ^ (n.choose 2 - (rr n).choose 2)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
      · refine card_biUnion_le.trans ?_
        refine (sum_le_sum (g := fun _ => 2 ^ (n.choose 2 - (kk n).choose 2))
          fun S hS => ?_).trans (le_of_eq ?_)
        · have := count_indep S
          rw [(mem_powersetCard.mp hS).2] at this
          exact this
        · rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
      · refine card_biUnion_le.trans ?_
        refine (sum_le_sum (g := fun _ => (∑ j ∈ range (n+1), ((rr n).choose 2).choose j) *
            2 ^ (n.choose 2 - (rr n).choose 2)) fun S hS => ?_).trans (le_of_eq ?_)
        · have := count_dense S n
          rw [(mem_powersetCard.mp hS).2] at this
          exact this
        · rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
    have t1 := term1 n
    have t2 := term2 n hp
    have hnat : Nat.card {G : SimpleGraph (Fin n) // P G} * n ≤ 2 * 2 ^ n.choose 2 := by
      nlinarith
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_le_div_iff₀ (by positivity) hn0]
    exact_mod_cast hnat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 2)
    (Filter.Eventually.of_forall fun n => by positivity) hb

end LB

theorem OMA.solution : type_of% @Erdos717.erdos_717.variants.erdos_fajtlowicz := LB.main
