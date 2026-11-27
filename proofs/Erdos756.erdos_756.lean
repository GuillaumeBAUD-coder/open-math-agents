import FormalConjectures.ErdosProblems.«756»

-- Problem: Erdős Problem 756
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/756.lean (declaration Erdos756.erdos_756)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Construction (Bhowmick): a regular m-gon P together with its image Q under a point
-- reflection z ↦ c - z. For c = 2 the two copies share one vertex (n = 2 m - 1 points); for
-- c = 1 + ζ they share an edge (n = 2 m - 2 points). Every chord length of P occurs at least
-- n + 1 times, which gives about n / 4 rich distances.

namespace OMA.O7b

open Erdos756 Complex Finset
open scoped EuclideanGeometry ComplexConjugate

noncomputable def e : ℂ ≃ₗᵢ[ℝ] ℝ² := Complex.orthonormalBasisOneI.repr

lemma dist_e (x y : ℂ) : dist (e x) (e y) = ‖x - y‖ := by
  rw [LinearIsometryEquiv.dist_map, dist_eq_norm]

lemma unit_conj {u : ℂ} (hu : ‖u‖ = 1) : u * conj u = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp

lemma unit_pair {u v x y : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hS : u + v = x + y) (h0 : x + y ≠ 0) : u = x ∨ u = y := by
  have cu := unit_conj hu
  have cv := unit_conj hv
  have cx := unit_conj hx
  have cy := unit_conj hy
  have h1 : u * v * (conj u + conj v) = u + v := by linear_combination v * cu + u * cv
  have h2 : x * y * (conj x + conj y) = x + y := by linear_combination y * cx + x * cy
  have hc : conj u + conj v = conj x + conj y := by rw [← map_add, ← map_add, hS]
  have hc0 : conj x + conj y ≠ 0 := by
    intro h
    apply h0
    have := congrArg conj h
    rw [map_add, Complex.conj_conj, Complex.conj_conj, map_zero] at this
    exact this
  have huv : u * v = x * y := by
    have h3 : (u * v - x * y) * (conj x + conj y) = 0 := by
      linear_combination h1 - h2 - u * v * hc + hS
    rcases mul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc0
  have h4 : (u - x) * (u - y) = 0 := by linear_combination u * hS - huv
  rcases mul_eq_zero.mp h4 with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

noncomputable def ζ (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

lemma prim {m : ℕ} (hm : m ≠ 0) : IsPrimitiveRoot (ζ m) m := Complex.isPrimitiveRoot_exp m hm

lemma normz {m : ℕ} (hm : m ≠ 0) (a : ℕ) : ‖ζ m ^ a‖ = 1 := by
  rw [norm_pow, (prim hm).norm'_eq_one hm, one_pow]

lemma ζ_ne {m : ℕ} (hm : m ≠ 0) : ζ m ≠ 0 := by
  intro h
  have := normz hm 1
  rw [pow_one, h, norm_zero] at this
  exact zero_ne_one this

lemma pow_mod' {m : ℕ} (hm : m ≠ 0) (k : ℕ) : ζ m ^ k = ζ m ^ (k % m) := by
  conv_lhs => rw [← Nat.mod_add_div k m, pow_add, pow_mul, (prim hm).pow_eq_one, one_pow, mul_one]

lemma pow_cancel {m : ℕ} (hm : m ≠ 0) {a k l : ℕ} (h : ζ m ^ (a + k) = ζ m ^ (a + l)) :
    ζ m ^ k = ζ m ^ l := by
  rw [pow_add, pow_add] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (ζ_ne hm)) h

/-- the chord length of step `s` -/
noncomputable def d (m s : ℕ) : ℝ := ‖1 - ζ m ^ s‖

lemma dist_step {m : ℕ} (hm : m ≠ 0) (a s : ℕ) : ‖ζ m ^ a - ζ m ^ (a + s)‖ = d m s := by
  have : ζ m ^ a - ζ m ^ (a + s) = ζ m ^ a * (1 - ζ m ^ s) := by rw [pow_add]; ring
  rw [this, norm_mul, normz hm, one_mul, d]

lemma dist_step' {m : ℕ} (hm : m ≠ 0) {s : ℕ} (hs : s ≤ m) (a : ℕ) :
    ‖ζ m ^ a - ζ m ^ (a + (m - s))‖ = d m s := by
  rw [dist_step hm, d, d]
  have h1 : ζ m ^ (m - s) * ζ m ^ s = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hs, (prim hm).pow_eq_one]
  have : 1 - ζ m ^ (m - s) = ζ m ^ (m - s) * (ζ m ^ s - 1) := by linear_combination -h1
  rw [this, norm_mul, normz hm, one_mul, norm_sub_rev]

/-- image of the m-gon under a map `g` -/
noncomputable def S (g : ℂ → ℝ²) (m : ℕ) : Finset ℝ² :=
  (range m).image (fun a => g (ζ m ^ a))

lemma memS {g : ℂ → ℝ²} {m : ℕ} (hm : m ≠ 0) (k : ℕ) : g (ζ m ^ k) ∈ S g m := by
  refine Finset.mem_image.mpr ⟨k % m, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
  rw [← pow_mod' hm]

lemma g_inj {g : ℂ → ℝ²} (hg : ∀ x y, dist (g x) (g y) = ‖x - y‖) {x y : ℂ} (h : g x = g y) :
    x = y := by
  have := hg x y
  rw [h, dist_self] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this.symm)

lemma cardS {g : ℂ → ℝ²} (hg : ∀ x y, dist (g x) (g y) = ‖x - y‖) {m : ℕ} (hm : m ≠ 0) :
    (S g m).card = m := by
  unfold S
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb h
  exact (prim hm).pow_inj (Finset.mem_range.mp (Finset.mem_coe.mp ha))
    (Finset.mem_range.mp (Finset.mem_coe.mp hb)) (g_inj hg h)

lemma count {g : ℂ → ℝ²} (hg : ∀ x y, dist (g x) (g y) = ‖x - y‖) {m s : ℕ} (hm : 3 ≤ m)
    (hs1 : 1 ≤ s) (hs2 : 2 * s < m) :
    2 * m ≤ ((S g m).offDiag.filter (fun pr => dist pr.1 pr.2 = d m s)).card := by
  have hm0 : m ≠ 0 := by omega
  have hz1 : ζ m ^ s ≠ 1 := by
    intro h
    have := (prim hm0).pow_eq_one_iff_dvd s |>.mp h
    have := Nat.le_of_dvd (by omega) this
    omega
  have hz2 : ζ m ^ (m - s) ≠ 1 := by
    intro h
    have := (prim hm0).pow_eq_one_iff_dvd (m - s) |>.mp h
    have := Nat.le_of_dvd (by omega) this
    omega
  have hz3 : ζ m ^ s ≠ ζ m ^ (m - s) := by
    intro h
    have := (prim hm0).pow_inj (by omega) (by omega) h
    omega
  let f : ℕ × Bool → ℝ² × ℝ² := fun p =>
    if p.2 then (g (ζ m ^ p.1), g (ζ m ^ (p.1 + s)))
    else (g (ζ m ^ p.1), g (ζ m ^ (p.1 + (m - s))))
  have h := Finset.card_le_card_of_injOn (s := (range m) ×ˢ (univ : Finset Bool))
    (t := (S g m).offDiag.filter (fun pr => dist pr.1 pr.2 = d m s)) f ?_ ?_
  · rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool] at h
    linarith
  · intro p _
    rcases p with ⟨a, b⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_offDiag]
    cases b
    · simp only [f, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨memS hm0 _, memS hm0 _, ?_⟩, ?_⟩
      · intro h
        have h' := g_inj hg h
        rw [← add_zero a] at h'
        rw [add_zero] at h'
        have := pow_cancel hm0 (a := a) (k := 0) (l := m - s) (by rw [add_zero]; exact h')
        rw [pow_zero] at this
        exact hz2 this.symm
      · rw [hg]; exact dist_step' hm0 (by omega) a
    · simp only [f, ↓reduceIte]
      refine ⟨⟨memS hm0 _, memS hm0 _, ?_⟩, ?_⟩
      · intro h
        have h' := g_inj hg h
        have := pow_cancel hm0 (a := a) (k := 0) (l := s) (by rw [add_zero]; exact h')
        rw [pow_zero] at this
        exact hz1 this.symm
      · rw [hg]; exact dist_step hm0 a s
  · intro p hp q hq hpq
    rcases p with ⟨a, b⟩
    rcases q with ⟨a', b'⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp hq
    have h1 : g (ζ m ^ a) = g (ζ m ^ a') := by
      have := congrArg Prod.fst hpq
      cases b <;> cases b' <;> simpa [f] using this
    have ha : a = a' := (prim hm0).pow_inj hp.1 hq.1 (g_inj hg h1)
    subst ha
    have h2 := congrArg Prod.snd hpq
    cases b <;> cases b'
    · rfl
    · exfalso
      simp only [f, Bool.false_eq_true, ↓reduceIte] at h2
      exact hz3 (pow_cancel hm0 (g_inj hg h2)).symm
    · exfalso
      simp only [f, Bool.false_eq_true, ↓reduceIte] at h2
      exact hz3 (pow_cancel hm0 (g_inj hg h2))
    · rfl

/-- chord lengths of different steps are different -/
lemma d_inj {m s t : ℕ} (hm : 3 ≤ m) (hs1 : 1 ≤ s) (hs2 : 2 * s < m) (ht1 : 1 ≤ t)
    (ht2 : 2 * t < m) (h : d m s = d m t) : s = t := by
  have hm0 : m ≠ 0 := by omega
  have key : ∀ w : ℂ, ‖w‖ = 1 → ‖1 - w‖ ^ 2 = 2 - 2 * w.re := by
    intro w hw
    have h1 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at h1 ⊢
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    nlinarith
  have hre : (ζ m ^ s).re = (ζ m ^ t).re := by
    have e1 := key _ (normz hm0 s)
    have e2 := key _ (normz hm0 t)
    unfold d at h
    rw [h] at e1
    linarith
  have hn1 := normz hm0 s
  have hn2 := normz hm0 t
  have hsq : (ζ m ^ s).im ^ 2 = (ζ m ^ t).im ^ 2 := by
    have a1 : ‖ζ m ^ s‖ ^ 2 = 1 := by rw [hn1]; norm_num
    have a2 : ‖ζ m ^ t‖ ^ 2 = 1 := by rw [hn2]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at a1 a2
    rw [hre] at a1
    linear_combination a1 - a2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh
  · have : ζ m ^ s = ζ m ^ t := Complex.ext hre hh
    exact (prim hm0).pow_inj (by omega) (by omega) this
  · exfalso
    -- ζ^s is the conjugate of ζ^t, which is ζ^(m - t)
    have hconj : ζ m ^ s = conj (ζ m ^ t) :=
      Complex.ext (by rw [Complex.conj_re]; exact hre) (by rw [Complex.conj_im]; exact hh)
    have c1 := unit_conj (normz hm0 t)
    have c2 : ζ m ^ t * ζ m ^ (m - t) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega), (prim hm0).pow_eq_one]
    have : conj (ζ m ^ t) = ζ m ^ (m - t) :=
      mul_left_cancel₀ (pow_ne_zero _ (ζ_ne hm0)) (c1.trans c2.symm)
    rw [this] at hconj
    have := (prim hm0).pow_inj (by omega) (by omega) hconj
    omega

noncomputable def gQ (c : ℂ) : ℂ → ℝ² := fun z => e (c - z)

lemma hg_Q (c : ℂ) : ∀ x y, dist (gQ c x) (gQ c y) = ‖x - y‖ := by
  intro x y
  unfold gQ
  rw [dist_e, show c - x - (c - y) = -(x - y) by ring, norm_neg]

lemma inter_odd {m : ℕ} (hm : 3 ≤ m) : S e m ∩ S (gQ 2) m = {e 1} := by
  have hm0 : m ≠ 0 := by omega
  ext w
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h2
    have hab : (2 : ℂ) - ζ m ^ b = ζ m ^ a := g_inj dist_e hb
    have hS : ζ m ^ a + ζ m ^ b = 1 + 1 := by linear_combination -hab
    rcases unit_pair (normz hm0 a) (normz hm0 b) norm_one norm_one hS (by norm_num) with h | h <;>
      rw [h]
  · rintro rfl
    refine ⟨?_, ?_⟩
    · have := memS (g := e) hm0 0
      rwa [pow_zero] at this
    · have := memS (g := gQ 2) hm0 0
      unfold gQ at this
      rwa [pow_zero, show (2 : ℂ) - 1 = 1 by norm_num] at this

lemma inter_even {m : ℕ} (hm : 3 ≤ m) :
    (S e m ∩ S (gQ (1 + ζ m)) m).card = 2 := by
  have hm0 : m ≠ 0 := by omega
  have hz1 : ‖ζ m‖ = 1 := by have := normz hm0 1; rwa [pow_one] at this
  have hne1 : ζ m ≠ 1 := by
    intro h
    have := (prim hm0).pow_eq_one_iff_dvd 1 |>.mp (by rw [pow_one]; exact h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hc0 : (1 : ℂ) + ζ m ≠ 0 := by
    intro h
    have h' : ζ m = -1 := by linear_combination h
    have h2 : ζ m ^ 2 = 1 := by rw [h']; norm_num
    have := (prim hm0).pow_eq_one_iff_dvd 2 |>.mp h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have : S e m ∩ S (gQ (1 + ζ m)) m = {e 1, e (ζ m)} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h2
      have hab : (1 + ζ m) - ζ m ^ b = ζ m ^ a := g_inj dist_e hb
      have hS : ζ m ^ a + ζ m ^ b = 1 + ζ m := by linear_combination -hab
      rcases unit_pair (normz hm0 a) (normz hm0 b) norm_one hz1 hS hc0 with h | h
      · left; rw [h]
      · right; rw [h]
    · rintro (rfl | rfl)
      · refine ⟨?_, ?_⟩
        · have := memS (g := e) hm0 0
          rwa [pow_zero] at this
        · have := memS (g := gQ (1 + ζ m)) hm0 1
          unfold gQ at this
          rwa [pow_one, show (1 : ℂ) + ζ m - ζ m = 1 by ring] at this
      · refine ⟨?_, ?_⟩
        · have := memS (g := e) hm0 1
          rwa [pow_one] at this
        · have := memS (g := gQ (1 + ζ m)) hm0 0
          unfold gQ at this
          rwa [pow_zero, show (1 : ℂ) + ζ m - 1 = ζ m by ring] at this
  rw [this, Finset.card_pair]
  intro h
  exact hne1 (g_inj dist_e h).symm

lemma bdd (n : ℕ) : BddAbove {x | ∃ (A : Finset ℝ²) (_ : A.card = n),
    (richDistances A (n + 1)).card = x} := by
  refine ⟨n * n, ?_⟩
  rintro x ⟨B, hB, rfl⟩
  unfold richDistances distanceSet
  calc _ ≤ (B.offDiag.image fun pair : ℝ² × ℝ² => dist pair.1 pair.2).card :=
        Finset.card_filter_le _ _
    _ ≤ B.offDiag.card := Finset.card_image_le
    _ ≤ n * n := by rw [Finset.offDiag_card, hB]; omega

lemma rich_lower {m : ℕ} (hm : 3 ≤ m) (c : ℂ) (k : ℕ) (hk : k = 1 ∨ k = 2)
    (hI : (S e m ∩ S (gQ c) m).card = k) : (m - 1) / 2 ≤ maxRichDistances (2 * m - k) := by
  have hm0 : m ≠ 0 := by omega
  have hcardA : (S e m ∪ S (gQ c) m).card = 2 * m - k := by
    have h1 := Finset.card_union_add_card_inter (S e m) (S (gQ c) m)
    have h2 := cardS dist_e hm0 (m := m)
    have h3 := cardS (hg_Q c) hm0 (m := m)
    omega
  set A := S e m ∪ S (gQ c) m with hA
  have hcount : ∀ s, 1 ≤ s → 2 * s < m →
      (2 * m - k + 1) * 2 ≤ (A.offDiag.filter (fun pr => dist pr.1 pr.2 = d m s)).card := by
    intro s hs1 hs2
    have hX := count dist_e hm hs1 hs2
    have hY := count (hg_Q c) hm hs1 hs2
    set X := (S e m).offDiag.filter (fun pr => dist pr.1 pr.2 = d m s)
    set Y := (S (gQ c) m).offDiag.filter (fun pr => dist pr.1 pr.2 = d m s)
    have hXY : X ∪ Y ⊆ A.offDiag.filter (fun pr => dist pr.1 pr.2 = d m s) := by
      intro pr hpr
      simp only [X, Y, A, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag] at hpr ⊢
      tauto
    have hXI : X ∩ Y ⊆ (S e m ∩ S (gQ c) m).offDiag := by
      intro pr hpr
      simp only [X, Y, Finset.mem_inter, Finset.mem_filter, Finset.mem_offDiag] at hpr ⊢
      tauto
    have h1 := Finset.card_union_add_card_inter X Y
    have h2 := Finset.card_le_card hXY
    have h3 : (X ∩ Y).card ≤ k * k - k := by
      have := Finset.card_le_card hXI
      rwa [Finset.offDiag_card, hI] at this
    rcases hk with rfl | rfl
    · omega
    · omega
  have hsub : (Finset.Icc 1 ((m - 1) / 2)).image (d m) ⊆ richDistances A (2 * m - k + 1) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_Icc] at hs
    have hs2 : 2 * s < m := by omega
    have hc := hcount s hs.1 hs2
    unfold richDistances
    rw [Finset.mem_filter]
    constructor
    · have hpos : 0 < (A.offDiag.filter (fun pr => dist pr.1 pr.2 = d m s)).card := by omega
      obtain ⟨pr, hpr⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hpr
      unfold distanceSet
      exact Finset.mem_image.mpr ⟨pr, hpr.1, hpr.2⟩
    · unfold distanceMultiplicity
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      convert hc using 2
  have hcard : ((Finset.Icc 1 ((m - 1) / 2)).image (d m)).card = (m - 1) / 2 := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro s hs t ht h
      simp only [Finset.coe_Icc, Set.mem_Icc] at hs ht
      exact d_inj hm hs.1 (by omega) ht.1 (by omega) h
  calc (m - 1) / 2 = _ := hcard.symm
    _ ≤ (richDistances A (2 * m - k + 1)).card := Finset.card_le_card hsub
    _ ≤ maxRichDistances (2 * m - k) := by
      unfold maxRichDistances
      exact le_csSup (bdd _) ⟨A, hcardA, rfl⟩

end OMA.O7b

theorem OMA.solution : type_of% @Erdos756.erdos_756 := by
  apply Asymptotics.IsBigO.of_bound 8
  rw [Filter.eventually_atTop]
  refine ⟨10, fun n hn => ?_⟩
  have key : n ≤ 8 * Erdos756.maxRichDistances n := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · have h := OMA.O7b.rich_lower (m := k + 1) (by omega) (1 + OMA.O7b.ζ (k + 1)) 2
        (Or.inr rfl) (OMA.O7b.inter_even (by omega))
      have e : 2 * (k + 1) - 2 = n := by omega
      rw [e] at h
      omega
    · have h := OMA.O7b.rich_lower (m := k + 1) (by omega) 2 1 (Or.inl rfl)
        (by rw [OMA.O7b.inter_odd (by omega), Finset.card_singleton])
      have e : 2 * (k + 1) - 1 = n := by omega
      rw [e] at h
      omega
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast, Nat.abs_cast]
  exact_mod_cast key
