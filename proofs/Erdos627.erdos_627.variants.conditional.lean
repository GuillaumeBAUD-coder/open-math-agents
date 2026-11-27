import FormalConjectures.ErdosProblems.«627»

/-! Araujo–Filipe–Miyazaki's conditional asymptotic for the chromatic-to-clique ratio.
Credit: @JaviSoto. The finite coloring and clique estimates in the lower bound build on @Halldon's proof. -/

open SimpleGraph Filter
open scoped Asymptotics Topology

namespace Erdos627Upper

open Combinatorics.Diagonal

private theorem ramsey_choose_succ (s t : ℕ) :
    HasRamseyProperty ((s + t).choose s) (s + 1) (t + 1) := by
  induction s generalizing t with
  | zero =>
    rw [Nat.choose_zero_right]
    exact hasRamseyProperty_one_left (t + 1)
  | succ s ihs =>
    induction t with
    | zero =>
      rw [Nat.add_zero, Nat.choose_self]
      exact hasRamseyProperty_one_right (s + 2)
    | succ t iht =>
      have hs : HasRamseyProperty ((s + (t + 1)).choose s) (s + 1) (t + 2) := ihs (t + 1)
      have hpos : 1 ≤ (s + (t + 1)).choose s := Nat.choose_pos (by omega)
      have hp : ((s + 1) + (t + 1)).choose (s + 1) =
          (s + (t + 1)).choose s + ((s + 1) + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega, Nat.choose_succ_succ]
        rw [show s + (t + 1) = (s + 1) + t by omega]
      rw [hp]
      intro m c V hV
      exact HasRamseyProperty.step hs iht hpos c V hV

theorem indep_of_choose_le
    {n s t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hclique : G.cliqueNum ≤ s)
    (hn : (s + t).choose s ≤ S.card) :
    ∃ T ⊆ S, T.card = t + 1 ∧ G.IsIndepSet (T : Set (Fin n)) := by
  classical
  let c (e : Finset (Fin n)) : Bool := decide (¬ G.IsClique (e : Set (Fin n)))
  obtain ⟨T, _, hT, hmono⟩ | ⟨T, hTS, hT, hmono⟩ := ramsey_choose_succ s t c S hn
  · have hTc : G.IsClique (T : Set (Fin n)) := by
      intro x hx y hy hxy
      have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (by simp [hxy])
      simpa [c, SimpleGraph.isClique_pair, hxy] using h
    have hle := hTc.card_le_cliqueNum
    omega
  · refine ⟨T, hTS, hT, ?_⟩
    intro x hx y hy hxy
    have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (by simp [hxy])
    simpa [c, SimpleGraph.isClique_pair, hxy] using h

end Erdos627Upper

open SimpleGraph

lemma greedyColor627 {n m t : ℕ} (G : SimpleGraph (Fin n)) (ht : 1 ≤ t)
    (hlarge : ∀ S : Finset (Fin n), m ≤ S.card →
      ∃ T : Finset (Fin n), T ⊆ S ∧ t ≤ T.card ∧ G.IsIndepSet (T : Set (Fin n))) :
    G.chromaticNumber.toNat ≤ n / t + m := by
  classical
  let rec color (S : Finset (Fin n)) :
      (G.induce (S : Set (Fin n))).Colorable (S.card / t + m) := by
    by_cases hS : m ≤ S.card
    · obtain ⟨T, hTS, htT, hI⟩ := hlarge S hS
      let R := S \ T
      have hRT : R.card + T.card = S.card := Finset.card_sdiff_add_card_eq_card hTS
      have hlt : R.card < S.card := by omega
      obtain ⟨c⟩ := color R
      let f (x : (S : Set (Fin n))) : Fin ((R.card / t + m) + 1) :=
        if hx : x.val ∈ T then Fin.last _ else
          (c ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩).castSucc
      have hdiv : R.card / t + 1 ≤ S.card / t := by
        apply (Nat.le_div_iff_mul_le ht).mpr
        rw [Nat.add_mul, Nat.one_mul]
        have := Nat.div_mul_le_self R.card t
        omega
      apply Colorable.mono (show R.card / t + m + 1 ≤ S.card / t + m by omega)
      refine ⟨Coloring.mk f ?_⟩
      intro x y hxy
      have hxy' : G.Adj x.val y.val := hxy
      by_cases hx : x.val ∈ T <;> by_cases hy : y.val ∈ T
      · exact ((hI hx hy hxy'.ne) hxy').elim
      · simp only [f, dif_pos hx, dif_neg hy]
        exact (Fin.castSucc_ne_last _).symm
      · simp [f, hx, hy, Fin.castSucc_ne_last]
      · simp only [f, dif_neg hx, dif_neg hy]
        apply (Fin.castSucc_injective _).ne
        exact c.valid (show (G.induce (R : Set (Fin n))).Adj
          ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩
          ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩ from hxy')
    · apply Colorable.mono _ (G.induce (S : Set (Fin n))).colorable_of_fintype
      simpa using (Nat.le_of_lt (Nat.lt_of_not_ge hS)).trans (Nat.le_add_left m (S.card / t))
  termination_by S.card
  let U : Finset (Fin n) := Finset.univ
  let inclusion : G →g G.induce (U : Set (Fin n)) :=
    { toFun := fun x => ⟨x, Finset.mem_univ x⟩, map_rel' := fun h => h }
  have h := (color U).of_hom inclusion
  apply ENat.toNat_le_of_le_natCast
  simpa [U] using h.chromaticNumber_le

open Filter

lemma eventually_ceil_rpow_le_627 {η r : ℝ} (hη : 0 < η) (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop, (⌈(n : ℝ) ^ r⌉₊ : ℝ) ≤ η * ((n : ℝ) / Real.logb 2 n ^ 2) := by
  have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hO := (isLittleO_log_rpow_rpow_atTop 2 (sub_pos.mpr hr1)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hO.bound (show 0 < η * Real.log 2 ^ 2 / 2 by positivity)
  filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnp := zero_lt_one.trans hn1
  have hlp := Real.log_pos hn1
  change ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ η * Real.log 2 ^ 2 / 2 * ‖(n : ℝ) ^ (1 - r)‖ at hn
  rw [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnp.le _)] at hn
  have hc : (⌈(n : ℝ)^r⌉₊ : ℝ) ≤ 2 * (n : ℝ)^r := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hnp.le r)
    have := Real.one_le_rpow hn1.le hr.le
    linarith
  have hratio : Real.logb 2 n ^ 2 ≤ (η / 2) * (n : ℝ) ^ (1-r) := by
    rw [Real.logb, div_pow, div_le_iff₀ (sq_pos_of_pos hb)]
    linarith
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos (Real.logb_pos (by norm_num) hn1))]
  calc
    _ ≤ (2 * (n : ℝ)^r) * ((η / 2) * (n : ℝ)^(1-r)) :=
      mul_le_mul hc hratio (sq_nonneg _) (by positivity)
    _ = η * ((n : ℝ)^r * (n : ℝ)^(1-r)) := by ring
    _ = η * n := by rw [← Real.rpow_add hnp, show r+(1-r) = 1 by ring, Real.rpow_one]

/- Restrict the graph to a subset of Ramsey size, then transport the independent set back. -/

open SimpleGraph

namespace OMA.E627Conditional

theorem indep_of_classicalRamsey_le
    (choose_bound : ∀ {n w t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)),
      G.cliqueNum ≤ w → (w+t).choose w ≤ S.card →
      ∃ T ⊆ S, T.card = t+1 ∧ G.IsIndepSet (T : Set (Fin n)))
    {n w t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hw : G.cliqueNum ≤ w) (hs : classicalRamsey (w+1) (t+1) ≤ S.card) :
    ∃ T ⊆ S, T.card = t+1 ∧ G.IsIndepSet (T : Set (Fin n)) := by
  classical
  let good := {m : ℕ | ∀ H : SimpleGraph (Fin m),
    (completeGraph (Fin (w+1))).IsContained H ∨ (completeGraph (Fin (t+1))).IsContained Hᶜ}
  have hex : good.Nonempty := by
    refine ⟨(w+t).choose w, ?_⟩
    intro H
    by_cases h : H.cliqueNum ≤ w
    · right
      obtain ⟨T, _, hc, hi⟩ := choose_bound (t := t) H Finset.univ h (by simp)
      exact (Hᶜ.not_cliqueFree_iff_top_isContained _).mp
        (IsNClique.not_cliqueFree ⟨(H.isClique_compl).mpr hi, hc⟩)
    · left
      obtain ⟨T, hT⟩ := H.exists_isNClique_cliqueNum
      apply (H.not_cliqueFree_iff_top_isContained _).mp
      exact fun hf => hT.not_cliqueFree (CliqueFree.mono (by omega) hf)
  let R := classicalRamsey (w+1) (t+1)
  have hr : R ∈ good := Nat.sInf_mem hex
  let i : Fin R ↪ Fin n := ((Fin.castLEEmb hs).trans S.equivFin.symm.toEmbedding).trans
    (Function.Embedding.subtype (· ∈ S))
  have hi (v : Fin R) : i v ∈ S := (S.equivFin.symm ((Fin.castLEEmb hs) v)).property
  let H := G.comap i
  rcases hr H with h | h
  · have hn := h.not_cliqueFree
    unfold CliqueFree at hn
    obtain ⟨U, hU⟩ := not_forall_not.mp hn
    have hc : G.IsClique ((U.map i : Finset (Fin n)) : Set (Fin n)) := by
      intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
      exact hU.isClique hx hy (fun e => hab (congrArg i e))
    have hbad := hc.card_le_cliqueNum
    rw [Finset.card_map, hU.card_eq] at hbad
    omega
  · have hn := h.not_cliqueFree
    unfold CliqueFree at hn
    obtain ⟨U, hU⟩ := not_forall_not.mp hn
    refine ⟨U.map i, ?_, by simpa using hU.card_eq, ?_⟩
    · intro a ha
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
      exact hi x
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
      exact (H.isClique_compl.mp hU.isClique) hx hy (fun e => hab (congrArg i e))

end OMA.E627Conditional

/- The diagonal Ramsey growth rate bounds the normalized chromatic-to-clique ratio from below.
The finite clique and coloring estimates are adapted from @Halldon's proof of the Erdős 627 lower bound. -/

open Filter SimpleGraph Erdos627
open scoped Topology

namespace OMA.E627ConditionalLower

private lemma clique_le_of_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (h : ¬ (completeGraph (Fin k)).IsContained G) : G.cliqueNum ≤ k := by
  by_contra! hlt
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hfree : G.CliqueFree k := by
    by_contra hf
    exact h ((G.not_cliqueFree_iff_top_isContained k).1 hf)
  exact hs.not_cliqueFree (CliqueFree.mono hlt.le hfree)

private lemma ratio_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (G : SimpleGraph (Fin n)) (hc : G.cliqueNum ≤ k) (hi : G.indepNum ≤ k) :
    (n : ℝ) / (k : ℝ) ^ 2 ≤ Erdos627.maxChromaticCliqueRatio n := by
  classical
  have one_le (H : SimpleGraph (Fin n)) : 1 ≤ H.cliqueNum := by
    let v : Fin n := ⟨0, hn⟩
    have h : H.IsClique (({v} : Finset (Fin n)) : Set (Fin n)) := by simp
    simpa using h.card_le_cliqueNum
  have hpω : 0 < (G.cliqueNum : ℝ) := by exact_mod_cast one_le G
  have hα : 0 < G.indepNum := (by decide : 0 < 1).trans_le (by simpa using one_le Gᶜ)
  have hχ : G.chromaticNumber ≠ ⊤ :=
    chromaticNumber_ne_top_iff_exists.mpr ⟨_, G.colorable_of_fintype⟩
  have hcolor := card_div_indepNum_le_chromaticNumber (G := G)
  rw [← ENat.natCast_toNat hχ] at hcolor
  have hceil : ⌈((n : ℚ≥0) / G.indepNum)⌉₊ ≤ G.chromaticNumber.toNat := by
    simpa [Nat.card_eq_fintype_card] using hcolor
  have hnn := (div_le_iff₀ (show 0 < (G.indepNum : ℚ≥0) by exact_mod_cast hα)).mp
    (Nat.ceil_le.mp hceil)
  have hnc : n ≤ G.chromaticNumber.toNat * G.indepNum := by exact_mod_cast hnn
  have hnk : (n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) * k := by
    exact_mod_cast hnc.trans (Nat.mul_le_mul_left _ hi)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio : (n : ℝ) / (k : ℝ)^2 ≤ (G.chromaticNumber.toNat : ℝ) / G.cliqueNum := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hk') hpω]
    calc
      (n : ℝ) * G.cliqueNum ≤ (n : ℝ) * k := by gcongr
      _ ≤ ((G.chromaticNumber.toNat : ℝ) * k) * k := by gcongr
      _ = _ := by ring
  exact le_ciSup_of_le (Set.finite_range _).bddAbove G hratio

private theorem ratio_of_lt_ramsey {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hr : n < diagonalRamsey k) : (n : ℝ) / (k : ℝ)^2 ≤ maxChromaticCliqueRatio n := by
  classical
  have hnot : ¬ ∀ G : SimpleGraph (Fin n), (completeGraph (Fin k)).IsContained G ∨
      (completeGraph (Fin k)).IsContained Gᶜ := fun h => (not_le_of_gt hr) (Nat.sInf_le h)
  obtain ⟨G, hbad⟩ := not_forall.mp hnot
  obtain ⟨hG, hGc⟩ := not_or.mp hbad
  exact ratio_bound hn hk G (clique_le_of_free G hG) (by simpa using clique_le_of_free Gᶜ hGc)

theorem eventual_lower_of_diagonal_growth (ℓ : ℝ)
    (hlim : Tendsto (fun k : ℕ ↦ Real.logb 2 (diagonalRamsey k : ℝ) / (k : ℝ)) atTop (𝓝 ℓ)) :
    ∀ c : ℝ, c < ℓ ^ 2 → ∀ᶠ n : ℕ in atTop,
      c < maxChromaticCliqueRatio n / ((n : ℝ) / Real.logb 2 n ^ 2) := by
  have hℓ : 0 ≤ ℓ := by
    apply ge_of_tendsto hlim
    exact .of_forall fun k => div_nonneg
      (div_nonneg (Real.log_natCast_nonneg _) (Real.log_pos (by norm_num)).le) (Nat.cast_nonneg _)
  intro c hc
  by_cases hc0 : c < 0
  · apply Filter.Eventually.of_forall
    intro n
    apply lt_of_lt_of_le hc0
    refine div_nonneg ?_ (by positivity)
    unfold maxChromaticCliqueRatio
    exact le_ciSup_of_le (Set.finite_range _).bddAbove (⊥ : SimpleGraph (Fin n)) (by positivity)
  have hcpos : 0 ≤ c := le_of_not_gt hc0
  obtain ⟨a, hca, haℓ⟩ := exists_between ((Real.sqrt_lt hcpos hℓ).mpr hc)
  obtain ⟨b, hab, hbℓ⟩ := exists_between haℓ
  have ha : 0 < a := (Real.sqrt_nonneg c).trans_lt hca
  let L (n : ℕ) := Real.logb 2 n
  let K (n : ℕ) := ⌊L n / a⌋₊
  have htL : Tendsto L atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have htK : Tendsto K atTop atTop := tendsto_nat_floor_atTop.comp (htL.atTop_div_const ha)
  have htKr : Tendsto (fun n : ℕ => (K n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp htK
  filter_upwards [(hlim.comp htK) (eventually_gt_nhds hbℓ), htKr (eventually_gt_atTop (a/(b-a))),
    eventually_gt_atTop (1 : ℕ)] with n hg hlarge hn
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hL : 0 < L n := Real.logb_pos (by norm_num) (by exact_mod_cast hn)
  have hlk : a / (b-a) < (K n : ℝ) := hlarge
  have hk : 0 < (K n : ℝ) := (div_pos ha (sub_pos.mpr hab)).trans hlk
  have hlo : (K n : ℝ) * a ≤ L n := (le_div_iff₀ ha).mp (Nat.floor_le (div_nonneg hL.le ha.le))
  have hhi : L n < ((K n : ℝ) + 1) * a := (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one _)
  have hlog : L n < Real.logb 2 (diagonalRamsey (K n)) := by
    have hgap := (div_lt_iff₀ (sub_pos.mpr hab)).mp hlk
    have hrate : b * (K n : ℝ) < Real.logb 2 (diagonalRamsey (K n)) := (lt_div_iff₀ hk).mp hg
    nlinarith
  have hr : n < diagonalRamsey (K n) := by
    have hR0 : diagonalRamsey (K n) ≠ 0 := by
      intro h
      rw [h] at hlog
      simp at hlog
      linarith
    exact_mod_cast (Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 2) hnr
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hR0))).mp hlog
  have hratio := ratio_of_lt_ramsey (n := n) (by omega) (Nat.cast_pos.mp hk) hr
  have hal : a ≤ L n / (K n : ℝ) := (le_div_iff₀ hk).mpr (by linarith)
  calc c < a ^ 2 := (Real.sqrt_lt hcpos ha.le).mp hca
       _ ≤ (L n / (K n : ℝ)) ^ 2 := by gcongr
       _ = ((n : ℝ) / (K n : ℝ)^2) / ((n : ℝ) / L n ^ 2) := by field_simp
       _ ≤ _ := div_le_div_of_nonneg_right hratio (div_nonneg hnr.le (sq_nonneg _))

end OMA.E627ConditionalLower

/- Choosing the greedy color-class size in the conditional chromatic-to-clique bound. -/

namespace Conditional627Upper

lemma normalized_of_coloring {n w colors : ℕ} (hn : 2 ≤ n) (hw : 0 < w)
    {d r η : ℝ} (hd : 0 < d)
    (htail : (⌈(n : ℝ) ^ r⌉₊ : ℝ) ≤ η * ((n : ℝ) / (Real.logb 2 n)^2))
    (hc : ∀ t : ℕ, (w : ℝ) * t ≤ (d * Real.logb 2 n)^2 →
      colors ≤ n / (t + 1) + ⌈(n : ℝ) ^ r⌉₊) :
    (colors : ℝ) / w ≤ (1 / d^2 + η) * ((n : ℝ) / (Real.logb 2 n)^2) := by
  let L := Real.logb 2 n
  let u := (d*L)^2 / w
  let t := ⌊u⌋₊
  let m := ⌈(n : ℝ)^r⌉₊
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < L := Real.logb_pos (by norm_num) hn'
  have hw' : (0 : ℝ) < w := Nat.cast_pos.mpr hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hu : 0 ≤ u := div_nonneg (sq_nonneg _) hw'.le
  have hwt : (w : ℝ)*t ≤ (d*L)^2 := by
    rw [mul_comm]
    exact (le_div_iff₀ hw').mp (Nat.floor_le hu)
  have hcap := hc t hwt
  have hcolor : (colors : ℝ) ≤ (n : ℝ) / (t + 1) + m := calc
    _ ≤ ((n / (t + 1) + m : ℕ) : ℝ) := by exact_mod_cast hcap
    _ ≤ _ := by push_cast; gcongr; exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := n) (n := t+1))
  have hunit : (d*L)^2 ≤ ((t : ℝ)+1)*w :=
    ((div_lt_iff₀ hw').mp (Nat.lt_floor_add_one u)).le
  have hmain : ((n : ℝ) / ((t : ℝ)+1)) / w ≤ (1/d^2)*((n : ℝ)/L^2) := calc
    _ = (n : ℝ) / (((t : ℝ)+1)*w) := div_div _ _ _
    _ ≤ (n : ℝ) / (d*L)^2 := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hunit
    _ = _ := by field_simp
  have hmdiv : (m : ℝ) / w ≤ η * ((n : ℝ)/L^2) :=
    (div_le_self (Nat.cast_nonneg _) hw1).trans htail
  calc
    (colors : ℝ)/w ≤ ((n : ℝ) / ((t : ℝ)+1) + m)/w := by gcongr
    _ ≤ _ := by rw [add_div, add_mul]; exact add_le_add hmain hmdiv

end Conditional627Upper

/- Off-diagonal Ramsey upper bound when the diagonal growth rate exists. -/

open Filter SimpleGraph
open scoped Topology

namespace Conditional627Upper

lemma polylogCutoff (K : ℕ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, (2 * (d * Real.logb 2 n)^2)^K ≤ (n : ℝ)^r := by
  let B := 2 * (d / Real.log 2)^2
  have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have h := ((isLittleO_log_rpow_rpow_atTop ((2*K : ℕ) : ℝ) hr).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show 0 < 1 / B^K by positivity)
  filter_upwards [h] with n hn
  have hnlog := Real.log_natCast_nonneg n
  change ‖Real.log (n:ℝ) ^ ((2*K : ℕ) : ℝ)‖ ≤ (1/B^K)*‖(n:ℝ)^r‖ at hn
  rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  have hid : 2 * (d * Real.logb 2 n)^2 = B * (Real.log n)^2 := by
    dsimp [B, Real.logb]; ring
  rw [hid, mul_pow, ← pow_mul]
  rw [one_div_mul_eq_div] at hn
  simpa [mul_comm] using (le_div_iff₀ (pow_pos hB K)).mp hn

lemma chooseSmall {w t K : ℕ} (hw : 1 ≤ w) (ht : 1 ≤ t) (h : w ≤ K ∨ t ≤ K) :
    (w+t).choose w ≤ (2 * (w*t))^K := by
  have hw' : w ≤ w*t := Nat.le_mul_of_pos_right _ ht
  have ht' : t ≤ w*t := Nat.le_mul_of_pos_left _ hw
  have hs : w+t ≤ 2*(w*t) := by omega
  refine le_trans ?_ (Nat.pow_le_pow_left hs K)
  rcases h with h | h
  · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right (by omega) h)
  · rw [Nat.choose_symm_add]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right (by omega) h)

lemma rectangleCutoff {ℓ d b r : ℝ} (hd : 0 < d) (hb : 0 < b) (hlb : ℓ < b)
    (hr : 0 < r) (hrd : b*d < r)
    (hrect : ∀ s t k : ℕ, s*t ≤ k^2 → classicalRamsey s t ≤ diagonalRamsey k)
    (hlim : Tendsto (fun k : ℕ => Real.logb 2 (diagonalRamsey k : ℝ) / k) atTop (𝓝 ℓ)) :
    ∀ᶠ n : ℕ in atTop, ∀ w t : ℕ, 1 ≤ w → 1 ≤ t →
      (w : ℝ)*t ≤ (d*Real.logb 2 n)^2 →
      ((w+t).choose w : ℝ) ≤ (n : ℝ)^r ∨
        (classicalRamsey (w+1) (t+1) : ℝ) ≤ (n : ℝ)^r := by
  let e := r/b
  have he : d < e := (lt_div_iff₀ hb).mpr (by linarith)
  have he0 := hd.trans he
  let g := (e+d)/(2*d)
  have hg : 1 < g := (lt_div_iff₀ (by positivity : 0 < 2*d)).mpr (by linarith)
  have hgd : 0 < e-g*d := by
    have hh : g*d = (e+d)/2 := by dsimp [g]; field_simp
    linarith
  let K := ⌈1/(g-1)⌉₊
  let L (n : ℕ) := Real.logb 2 n
  have hL : Tendsto L atTop atTop := (Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp
    tendsto_natCast_atTop_atTop
  let k (n : ℕ) := ⌊e*L n⌋₊
  have hk : Tendsto k atTop atTop := tendsto_nat_floor_atTop.comp (hL.const_mul_atTop he0)
  have hD := hk.eventually (hlim.eventually_lt_const hlb)
  filter_upwards [polylogCutoff K hd hr, hD, hk.eventually_ge_atTop 1,
    (hL.const_mul_atTop hgd).eventually_ge_atTop 1, eventually_ge_atTop 2] with n hpoly hD hk1 hgap hn
  intro w t hw ht hwt
  have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 := zero_lt_one.trans hn1
  have hlpos : 0 < L n := Real.logb_pos (by norm_num) hn1
  by_cases hsmall : w ≤ K ∨ t ≤ K
  · left
    have hsw : (((w+t).choose w : ℕ) : ℝ) ≤ (2 * ((w:ℝ)*t))^K := by
      exact_mod_cast chooseSmall hw ht hsmall
    exact hsw.trans ((pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hwt (by norm_num : (0:ℝ)≤2)) K).trans hpoly)
  · push Not at hsmall
    have step (u : ℕ) (hu : K < u) : (u:ℝ)+1 ≤ g*u := by
      have hh : 1/(g-1) ≤ (u:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hu.le)
      have := (div_le_iff₀ (sub_pos.mpr hg)).mp hh
      linarith
    have hfloor : g*(d*L n) ≤ k n := by
      have hh := Nat.lt_floor_add_one (e*L n)
      change 1 ≤ (e-g*d)*L n at hgap
      change g*(d*L n) ≤ (⌊e*L n⌋₊ : ℝ)
      linarith
    have hnat : (w+1)*(t+1) ≤ (k n)^2 := by
      have hprod := mul_le_mul (step w hsmall.1) (step t hsmall.2) (by positivity) (by positivity)
      have hh : ((w:ℝ)+1)*((t:ℝ)+1) ≤ ((k n:ℕ):ℝ)^2 := calc
        _ ≤ (g*w)*(g*t) := hprod
        _ = g^2 * ((w:ℝ)*t) := by ring
        _ ≤ g^2 * (d*L n)^2 := mul_le_mul_of_nonneg_left hwt (sq_nonneg _)
        _ = (g*(d*L n))^2 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hfloor 2
      exact_mod_cast hh
    right
    have hRle : ((classicalRamsey (w+1) (t+1) : ℕ) : ℝ) ≤ diagonalRamsey (k n) := by
      exact_mod_cast hrect (w+1) (t+1) (k n) hnat
    refine hRle.trans ?_
    rcases eq_or_ne (diagonalRamsey (k n)) 0 with hzero | hpos
    · rw [hzero, Nat.cast_zero]; positivity
    apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hpos))
      (Real.rpow_pos_of_pos hn0 r)).mp
    rw [Real.logb_rpow_eq_mul_logb_of_pos hn0]
    have hkpos : (0:ℝ) < k n := by exact_mod_cast hk1
    have hlog := (div_lt_iff₀ hkpos).mp hD
    have hfl : (k n : ℝ) ≤ e*L n := Nat.floor_le (by positivity)
    calc
      _ ≤ b*(k n) := hlog.le
      _ ≤ b*(e*L n) := mul_le_mul_of_nonneg_left hfl hb.le
      _ = r*Real.logb 2 n := by dsimp [e,L]; field_simp


lemma upperBound
    (chooseIndep : ∀ {n w t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)),
      G.cliqueNum ≤ w → (w+t).choose w ≤ S.card →
        ∃ T ⊆ S, T.card = t+1 ∧ G.IsIndepSet (T : Set (Fin n)))
    (ramseyIndep : ∀ {n w t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)),
      G.cliqueNum ≤ w → classicalRamsey (w+1) (t+1) ≤ S.card →
        ∃ T ⊆ S, T.card = t+1 ∧ G.IsIndepSet (T : Set (Fin n)))
    (greedy : ∀ {n m t : ℕ} (G : SimpleGraph (Fin n)), 1 ≤ t →
      (∀ S : Finset (Fin n), m ≤ S.card →
        ∃ T : Finset (Fin n), T ⊆ S ∧ t ≤ T.card ∧ G.IsIndepSet (T : Set (Fin n))) →
        G.chromaticNumber.toNat ≤ n / t + m)
    (tail : ∀ {η r : ℝ}, 0 < η → 0 < r → r < 1 →
      ∀ᶠ n : ℕ in atTop, (⌈(n : ℝ)^r⌉₊ : ℝ) ≤ η * ((n:ℝ) / Real.logb 2 n ^ 2))
    (normed : ∀ {n w colors : ℕ}, 2 ≤ n → 0 < w → ∀ {d r η : ℝ}, 0 < d →
      (⌈(n:ℝ)^r⌉₊ : ℝ) ≤ η*((n:ℝ)/(Real.logb 2 n)^2) →
      (∀ t : ℕ, (w:ℝ)*t ≤ (d*Real.logb 2 n)^2 → colors ≤ n/(t+1)+⌈(n:ℝ)^r⌉₊) →
      (colors:ℝ)/w ≤ (1/d^2 + η)*((n:ℝ)/(Real.logb 2 n)^2))
    {ℓ : ℝ}
    (hrect : ∀ s t k : ℕ, s*t ≤ k^2 → classicalRamsey s t ≤ diagonalRamsey k)
    (hlim : Tendsto (fun k : ℕ => Real.logb 2 (diagonalRamsey k : ℝ) / k) atTop (𝓝 ℓ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Erdos627.maxChromaticCliqueRatio n ≤
      (ℓ^2+ε)*((n:ℝ) / Real.logb 2 n ^ 2) := by
  classical
  let A := Real.sqrt (ℓ^2+ε/2)
  let b := (max 0 ℓ + A) / 2
  let d := 1/A
  let r := (b/A + 1) / 2
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hAsq : A^2 = ℓ^2+ε/2 := Real.sq_sqrt (by positivity)
  have hℓA : ℓ < A := by nlinarith
  have hmaxA : max 0 ℓ < A := max_lt hA hℓA
  have hb : 0 < b := by dsimp [b]; positivity
  have hbA : b < A := by dsimp [b]; linarith
  have hℓb : ℓ < b := by dsimp [b]; linarith [le_max_right 0 ℓ]
  have hd : 0 < d := one_div_pos.mpr hA
  have hf : b / A < 1 := (div_lt_one hA).mpr hbA
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrd : b*d < r := by dsimp [r,d]; rw [mul_one_div]; linarith
  have hnrm : 1/d^2 + ε/2 = ℓ^2 + ε := by dsimp [d]; rw [div_pow]; field_simp; linarith
  filter_upwards [rectangleCutoff hd hb hℓb hr hrd hrect hlim,
    tail (half_pos hε) hr hr1, eventually_ge_atTop 2] with n hcut htail hn
  apply ciSup_le
  intro G
  have hw : 0 < G.cliqueNum := by
    let v : Fin n := ⟨0, by omega⟩
    have hv : G.IsClique (({v} : Finset (Fin n)) : Set (Fin n)) := by simp
    change 1 ≤ G.cliqueNum
    simpa using hv.card_le_cliqueNum
  rw [← hnrm]
  apply normed hn hw hd htail
  intro t hwt
  rcases eq_or_ne t 0 with rfl | ht
  · have hcol : G.chromaticNumber.toNat ≤ n := by
      apply ENat.toNat_le_of_le_natCast
      simpa using G.colorable_of_fintype.chromaticNumber_le
    simpa using hcol.trans (Nat.le_add_right _ _)
  apply greedy G (by omega : 1 ≤ t+1)
  intro S hS
  have hSn : (n : ℝ)^r ≤ S.card :=
    (Nat.le_ceil _).trans (by exact_mod_cast hS)
  have hI : ∃ T ⊆ S, T.card = t+1 ∧ G.IsIndepSet (T : Set (Fin n)) := by
    rcases hcut G.cliqueNum t hw (Nat.pos_of_ne_zero ht) hwt with h | h
    · apply chooseIndep G S le_rfl
      exact_mod_cast h.trans hSn
    · apply ramseyIndep G S le_rfl
      exact_mod_cast h.trans hSn
  obtain ⟨T, hTS, hcard, hI⟩ := hI
  exact ⟨T, hTS, hcard.ge, hI⟩

end Conditional627Upper

theorem OMA.solution : type_of% @Erdos627.erdos_627.variants.conditional := by
  intro ℓ hR hlim
  refine tendsto_order.mpr ⟨OMA.E627ConditionalLower.eventual_lower_of_diagonal_growth ℓ hlim, ?_⟩
  intro b hb
  let ε := (b - ℓ^2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have h := Conditional627Upper.upperBound (@Erdos627Upper.indep_of_choose_le)
    (fun {_ _ _} => OMA.E627Conditional.indep_of_classicalRamsey_le (@Erdos627Upper.indep_of_choose_le))
    (@greedyColor627) (@eventually_ceil_rpow_le_627) (@Conditional627Upper.normalized_of_coloring)
    hR hlim ε hε
  filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
  have hnpos : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnpos
  exact ((div_le_iff₀ (div_pos (by linarith) (sq_pos_of_pos hlog))).mpr hn).trans_lt
    (show ℓ^2 + ε < b by dsimp [ε]; linarith)
