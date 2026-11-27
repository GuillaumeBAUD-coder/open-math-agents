import FormalConjectures.Arxiv.«2607.03582».LpRogersShephard

/-!
# Proof of `Arxiv.2607.03582.volume_lpSum_eq_of_isParallelogramAtOrigin`

Write `K = T [0,1]^2` with `T (s, t) = s a + t b`. With `α = ⟪a, u⟫`, `β = ⟪b, u⟫` the support
functions are `h_K = α⁺ + β⁺` and `h_{-K} = α⁻ + β⁻`, and `u ↦ (α, β)` is onto, so
`K ⊕_p -K = T R` where `R` is the set of `(s, t)` with `sα + tβ ≤ F(α, β)` for all `α, β`.
Testing coordinate directions and Hölder's inequality show `R` is the union of the squares
`[0,1]^2`, `[-1,0]^2` and the two mixed-sign quadrants of the unit `L_q` ball. The four
half-open quadrants are permuted by a rotation of determinant one, so each holds a quarter of
the `L_q` ball (`MeasureTheory.volume_sum_rpow_le`), giving `|R| = 2 + 2Γ(1+1/q)^2/Γ(1+2/q)`.
Both volumes then scale by `|det T|` (`addHaar_image_linearMap`).
-/

open MeasureTheory Real

open scoped EuclideanGeometry

namespace LpRSAux

noncomputable def F (p α β : ℝ) : ℝ :=
  ((max α 0 + max β 0) ^ p + (max (-α) 0 + max (-β) 0) ^ p) ^ (1 / p)

def P (q s t : ℝ) : Prop :=
  (0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1) ∨ (-1 ≤ s ∧ s ≤ 0 ∧ -1 ≤ t ∧ t ≤ 0) ∨
    (s * t ≤ 0 ∧ |s| ^ q + |t| ^ q ≤ 1)

lemma F_comm (p α β : ℝ) : F p α β = F p β α := by
  unfold F; rw [add_comm (max α 0), add_comm (max (-α) 0)]

lemma le_rpow_add {p x y : ℝ} (hp : 0 < p) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ≤ (x ^ p + y ^ p) ^ (1 / p) := by
  calc x = (x ^ p) ^ (1 / p) := by
        rw [← rpow_mul hx, mul_one_div_cancel hp.ne', rpow_one]
    _ ≤ _ := rpow_le_rpow (rpow_nonneg hx _) (by linarith [rpow_nonneg hy p]) (by positivity)

lemma rpow_add_mono {p x y x' y' : ℝ} (hp : 0 < p) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxx : x ≤ x') (hyy : y ≤ y') :
    (x ^ p + y ^ p) ^ (1 / p) ≤ (x' ^ p + y' ^ p) ^ (1 / p) := by
  apply rpow_le_rpow (by positivity) _ (by positivity)
  exact add_le_add (rpow_le_rpow hx hxx hp.le) (rpow_le_rpow hy hyy hp.le)

lemma F_ge1 {p : ℝ} (hp : 0 < p) (α β : ℝ) : max α 0 + max β 0 ≤ F p α β :=
  le_rpow_add hp (by positivity) (by positivity)

lemma F_ge2 {p : ℝ} (hp : 0 < p) (α β : ℝ) : max (-α) 0 + max (-β) 0 ≤ F p α β := by
  unfold F; rw [add_comm ((max α 0 + max β 0) ^ p)]
  exact le_rpow_add hp (by positivity) (by positivity)

lemma holder2 {p q : ℝ} (hpq : p.HolderConjugate q) {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x * a + y * b ≤ (x ^ q + y ^ q) ^ (1 / q) * (a ^ p + b ^ p) ^ (1 / p) := by
  have := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) (f := ![a, b]) (g := ![x, y])
    hpq (by intro i _; fin_cases i <;> simpa) (by intro i _; fin_cases i <;> simpa)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linarith [mul_comm x a, mul_comm y b, mul_comm ((a ^ p + b ^ p) ^ (1 / p)) ((x ^ q + y ^ q) ^ (1 / q))]

lemma mixed_le {p q : ℝ} (hpq : p.HolderConjugate q) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0)
    (h : s ^ q + (-t) ^ q ≤ 1) (α β : ℝ) : s * α + t * β ≤ F p α β := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have h1 : s * α ≤ s * max α 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hs
  have h2 : t * β ≤ (-t) * max (-β) 0 := by
    have := mul_le_mul_of_nonneg_left (le_max_left (-β) 0) (neg_nonneg.2 ht); linarith
  have h3 := holder2 hpq hs (neg_nonneg.2 ht) (le_max_right α 0) (le_max_right (-β) 0)
  have h4 : (s ^ q + (-t) ^ q) ^ (1 / q) ≤ 1 :=
    rpow_le_one (add_nonneg (rpow_nonneg hs _) (rpow_nonneg (neg_nonneg.2 ht) _)) h (by positivity)
  have h5 : ((max α 0) ^ p + (max (-β) 0) ^ p) ^ (1 / p) ≤ F p α β :=
    rpow_add_mono hp (le_max_right _ _) (le_max_right _ _)
      (by linarith [le_max_right β 0]) (by linarith [le_max_right (-α) 0])
  have h6 : 0 ≤ ((max α 0) ^ p + (max (-β) 0) ^ p) ^ (1 / p) := by positivity
  nlinarith

lemma mixed_ge {p q : ℝ} (hpq : p.HolderConjugate q) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0)
    (h : ∀ α β, s * α + t * β ≤ F p α β) : s ^ q + (-t) ^ q ≤ 1 := by
  have hp := hpq.pos
  have hq1 : 1 < q := hpq.symm.lt
  have hp1 : 1 < p := hpq.lt
  have hmul : (q - 1) * p = q := hpq.symm.sub_one_mul_conj
  have ht' : 0 ≤ -t := neg_nonneg.2 ht
  set α := s ^ (q - 1)
  set β := -((-t) ^ (q - 1))
  have hα : 0 ≤ α := rpow_nonneg hs _
  have hβ : 0 ≤ -β := by simp [β]; exact rpow_nonneg ht' _
  have key := h α β
  have e1 : s * α = s ^ q := by
    simp only [α]; rw [mul_comm, ← rpow_add_one' hs (by linarith)]; ring_nf
  have e2 : t * β = (-t) ^ q := by
    simp only [β]; rw [show t * -(-t) ^ (q - 1) = (-t) ^ (q - 1) * (-t) by ring,
      ← rpow_add_one' ht' (by linarith)]; ring_nf
  have eF : F p α β = (s ^ q + (-t) ^ q) ^ (1 / p) := by
    unfold F
    rw [max_eq_left hα, max_eq_right (by linarith : β ≤ 0), max_eq_right (by linarith : -α ≤ 0),
      max_eq_left hβ]
    simp only [add_zero, zero_add, β, neg_neg, α]
    rw [← rpow_mul hs, ← rpow_mul ht', hmul]
  rw [e1, e2, eF] at key
  by_contra hc
  push_neg at hc
  have : (s ^ q + (-t) ^ q) ^ (1 / p) < (s ^ q + (-t) ^ q) ^ (1 : ℝ) :=
    rpow_lt_rpow_of_exponent_lt hc (by rw [div_lt_one (by linarith)]; exact hp1)
  rw [rpow_one] at this
  linarith

lemma sq_le {p : ℝ} (hp : 0 < p) {s t : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 1) (h3 : 0 ≤ t) (h4 : t ≤ 1)
    (α β : ℝ) : s * α + t * β ≤ F p α β := by
  have := F_ge1 hp α β
  nlinarith [le_max_left α 0, le_max_right α 0, le_max_left β 0, le_max_right β 0]

lemma sqn_le {p : ℝ} (hp : 0 < p) {s t : ℝ} (h1 : -1 ≤ s) (h2 : s ≤ 0) (h3 : -1 ≤ t)
    (h4 : t ≤ 0) (α β : ℝ) : s * α + t * β ≤ F p α β := by
  have := F_ge2 hp α β
  nlinarith [le_max_left (-α) 0, le_max_right (-α) 0, le_max_left (-β) 0, le_max_right (-β) 0]

lemma abs_le_one_of {q x y : ℝ} (hq : 0 < q) (h : |x| ^ q + |y| ^ q ≤ 1) : |x| ≤ 1 := by
  by_contra hc; push_neg at hc
  have := one_lt_rpow hc hq
  linarith [rpow_nonneg (abs_nonneg y) q]

lemma char {p q : ℝ} (hpq : p.HolderConjugate q) (s t : ℝ) :
    (∀ α β, s * α + t * β ≤ F p α β) ↔ P q s t := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  constructor
  · intro h
    by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t
    · left
      have h1 := h 1 0; have h2 := h 0 1
      simp [F, zero_rpow hp.ne'] at h1 h2
      exact ⟨hs, by linarith, ht, by linarith⟩
    · right; right
      have := mixed_ge hpq hs (by linarith) h
      refine ⟨mul_nonpos_of_nonneg_of_nonpos hs (by linarith), ?_⟩
      rw [abs_of_nonneg hs, abs_of_neg (by linarith)]; exact this
    · right; right
      have := mixed_ge (t := s) hpq ht (by linarith) (fun α β => by
        have := h β α; rw [F_comm]; linarith)
      refine ⟨mul_nonpos_of_nonpos_of_nonneg (by linarith) ht, ?_⟩
      rw [abs_of_nonneg ht, abs_of_neg (by linarith)]; linarith
    · right; left
      have h1 := h (-1) 0; have h2 := h 0 (-1)
      simp [F, zero_rpow hp.ne'] at h1 h2
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩) α β
    · exact sq_le hp h1 h2 h3 h4 α β
    · exact sqn_le hp h1 h2 h3 h4 α β
    · have hs1 := abs_le_one_of hq h2
      have ht1 := abs_le_one_of hq (by rwa [add_comm] at h2)
      rw [abs_le] at hs1 ht1
      rcases le_total 0 s with hs | hs <;> rcases le_total 0 t with ht | ht
      · exact sq_le hp hs hs1.2 ht ht1.2 α β
      · rw [abs_of_nonneg hs, abs_of_nonpos ht] at h2
        exact mixed_le hpq hs ht h2 α β
      · rw [abs_of_nonpos hs, abs_of_nonneg ht] at h2
        have := mixed_le hpq ht hs (by linarith) β α
        rw [F_comm]; linarith
      · exact sqn_le hp hs1.1 hs ht1.1 ht α β

end LpRSAux


namespace LpRSAux
open Arxiv.«2607.03582»

noncomputable def T (a b : ℝ²) : ℝ² →ₗ[ℝ] ℝ² :=
  (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap.smulRight a +
  (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap.smulRight b

lemma T_apply (a b y : ℝ²) : T a b y = y 0 • a + y 1 • b := by
  simp [T]

lemma inner_T (a b y u : ℝ²) : inner ℝ (T a b y) u = y 0 * inner ℝ a u + y 1 * inner ℝ b u := by
  rw [T_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left]

lemma T_inj {a b : ℝ²} (h : LinearIndependent ℝ ![a, b]) : Function.Injective (T a b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  rw [T_apply] at hy
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.1 h _ _ hy
  ext i; fin_cases i <;> simp [h0, h1]

lemma T_surj {a b : ℝ²} (h : LinearIndependent ℝ ![a, b]) : Function.Surjective (T a b) :=
  LinearMap.injective_iff_surjective.1 (T_inj h)


lemma dual_surj {a b : ℝ²} (h : LinearIndependent ℝ ![a, b]) (α β : ℝ) :
    ∃ u : ℝ², inner ℝ a u = α ∧ inner ℝ b u = β := by
  let G : ℝ² →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.pi (fun i => innerₛₗ ℝ (![a, b] i))
  have hG : ∀ u i, G u i = inner ℝ (![a, b] i) u := fun u i => rfl
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have ha : inner ℝ a u = 0 := by simpa [hG] using congrFun hu 0
    have hb : inner ℝ b u = 0 := by simpa [hG] using congrFun hu 1
    obtain ⟨y, rfl⟩ := T_surj h u
    have : inner ℝ (T a b y) (T a b y) = 0 := by
      rw [inner_T, ha, hb]; ring
    exact inner_self_eq_zero.1 this
  have hsurj : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨u, hu⟩ := hsurj ![α, β]
  refine ⟨u, ?_, ?_⟩
  · have := congrFun hu 0; simpa [hG] using this
  · have := congrFun hu 1; simpa [hG] using this

lemma support_eq {S : Set ℝ²} {u : ℝ²} {M : ℝ} (hle : ∀ x ∈ S, inner ℝ x u ≤ M)
    (hex : ∃ x ∈ S, inner ℝ x u = M) : supportFunction S u = M := by
  obtain ⟨x0, hx0, hM⟩ := hex
  have : Nonempty S := ⟨⟨x0, hx0⟩⟩
  unfold supportFunction
  apply le_antisymm
  · exact ciSup_le fun x => hle x x.2
  · rw [← hM]
    exact le_ciSup (f := fun x : S => inner ℝ (x : ℝ²) u) ⟨M, by
      rintro _ ⟨x, rfl⟩; exact hle x x.2⟩ ⟨x0, hx0⟩

def Sq : Set ℝ² := {y | 0 ≤ y 0 ∧ y 0 ≤ 1 ∧ 0 ≤ y 1 ∧ y 1 ≤ 1}

lemma convex_Sq : Convex ℝ Sq := by
  intro x hx y hy c d hc hd hcd
  simp only [Sq, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨h5, h6, h7, h8⟩ := hy
  refine ⟨by positivity, by nlinarith, by positivity, by nlinarith⟩

lemma K_eq (a b : ℝ²) : convexHull ℝ {0, a, b, a + b} = T a b '' Sq := by
  apply le_antisymm
  · apply convexHull_min _ (convex_Sq.linear_image (T a b))
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [Sq], by simp⟩
    · exact ⟨EuclideanSpace.single 0 1, by simp [Sq], by simp [T_apply]⟩
    · exact ⟨EuclideanSpace.single 1 1, by simp [Sq], by simp [T_apply]⟩
    · exact ⟨EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1, by simp [Sq],
        by simp [T_apply]⟩
  · rintro _ ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩
    set c := convexHull ℝ ({0, a, b, a + b} : Set ℝ²)
    have hc : Convex ℝ c := convex_convexHull ℝ _
    have m0 : (0 : ℝ²) ∈ c := subset_convexHull ℝ _ (by simp)
    have ma : a ∈ c := subset_convexHull ℝ _ (by simp)
    have mb : b ∈ c := subset_convexHull ℝ _ (by simp)
    have mab : a + b ∈ c := subset_convexHull ℝ _ (by simp)
    have e1 : y 0 • a ∈ c := hc.smul_mem_of_zero_mem m0 ma ⟨h1, h2⟩
    have e2 : y 0 • a + b ∈ c := by
      have := hc mb mab (by linarith : (0:ℝ) ≤ 1 - y 0) h1 (by ring)
      convert this using 1; module
    have := hc e1 e2 (by linarith : (0:ℝ) ≤ 1 - y 1) h3 (by ring)
    rw [T_apply]; convert this using 1; module

lemma supp_K {a b : ℝ²} (u : ℝ²) :
    supportFunction (convexHull ℝ {0, a, b, a + b}) u =
      max (inner ℝ a u) 0 + max (inner ℝ b u) 0 := by
  apply support_eq
  · rw [K_eq]; rintro _ ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩
    rw [inner_T]
    nlinarith [le_max_left (inner ℝ a u) 0, le_max_right (inner ℝ a u) 0,
      le_max_left (inner ℝ b u) 0, le_max_right (inner ℝ b u) 0]
  · have mem : ∀ x ∈ ({0, a, b, a + b} : Set ℝ²), x ∈ convexHull ℝ {0, a, b, a + b} :=
      fun x hx => subset_convexHull ℝ _ hx
    rcases le_total 0 (inner ℝ a u) with ha | ha <;> rcases le_total 0 (inner ℝ b u) with hb | hb
    · exact ⟨a + b, mem _ (by simp), by rw [inner_add_left, max_eq_left ha, max_eq_left hb]⟩
    · exact ⟨a, mem _ (by simp), by rw [max_eq_left ha, max_eq_right hb, add_zero]⟩
    · exact ⟨b, mem _ (by simp), by rw [max_eq_right ha, max_eq_left hb, zero_add]⟩
    · exact ⟨0, mem _ (by simp), by rw [max_eq_right ha, max_eq_right hb, inner_zero_left]; ring⟩

lemma supp_negK {a b : ℝ²} (u : ℝ²) :
    supportFunction (-convexHull ℝ {0, a, b, a + b}) u =
      max (-inner ℝ a u) 0 + max (-inner ℝ b u) 0 := by
  apply support_eq
  · intro x hx
    rw [Set.mem_neg, K_eq] at hx
    obtain ⟨y, ⟨h1, h2, h3, h4⟩, hy⟩ := hx
    have : inner ℝ x u = -(inner ℝ (T a b y) u) := by rw [hy, inner_neg_left, neg_neg]
    rw [this, inner_T]
    nlinarith [le_max_left (-inner ℝ a u) 0, le_max_right (-inner ℝ a u) 0,
      le_max_left (-inner ℝ b u) 0, le_max_right (-inner ℝ b u) 0]
  · have mem : ∀ x ∈ ({0, a, b, a + b} : Set ℝ²), -x ∈ -convexHull ℝ {0, a, b, a + b} :=
      fun x hx => by rw [Set.mem_neg, neg_neg]; exact subset_convexHull ℝ _ hx
    rcases le_total 0 (inner ℝ a u) with ha | ha <;> rcases le_total 0 (inner ℝ b u) with hb | hb
    · exact ⟨-0, mem 0 (by simp), by
        rw [neg_zero, inner_zero_left, max_eq_right (by linarith), max_eq_right (by linarith)]; ring⟩
    · exact ⟨-b, mem _ (by simp), by
        rw [inner_neg_left, max_eq_right (by linarith), max_eq_left (by linarith), zero_add]⟩
    · exact ⟨-a, mem _ (by simp), by
        rw [inner_neg_left, max_eq_left (by linarith), max_eq_right (by linarith), add_zero]⟩
    · exact ⟨-(a + b), mem _ (by simp), by
        rw [inner_neg_left, inner_add_left, max_eq_left (by linarith), max_eq_left (by linarith)]
        ring⟩

lemma lpSum_eq {a b : ℝ²} (h : LinearIndependent ℝ ![a, b]) {p q : ℝ} (hpq : p.HolderConjugate q) :
    lpSum p (convexHull ℝ {0, a, b, a + b}) (-convexHull ℝ {0, a, b, a + b}) =
      T a b '' {y | P q (y 0) (y 1)} := by
  have key : ∀ y : ℝ², T a b y ∈ lpSum p (convexHull ℝ {0, a, b, a + b})
      (-convexHull ℝ {0, a, b, a + b}) ↔ ∀ α β, y 0 * α + y 1 * β ≤ F p α β := by
    intro y
    simp only [lpSum, Set.mem_setOf_eq, supp_K, supp_negK, inner_T]
    constructor
    · intro hu α β
      obtain ⟨u, rfl, rfl⟩ := dual_surj h α β
      exact hu u
    · intro hab u; exact hab _ _
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := T_surj h x
    exact ⟨y, (char hpq _ _).1 ((key y).1 hx), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (key y).2 ((char hpq _ _).2 hy)

end LpRSAux


namespace LpRSAux
open MeasureTheory

def Q1 : Set (Fin 2 → ℝ) := {x | 0 < x 0 ∧ 0 ≤ x 1}
def Q2 : Set (Fin 2 → ℝ) := {x | x 0 ≤ 0 ∧ 0 < x 1}
def Q3 : Set (Fin 2 → ℝ) := {x | x 0 < 0 ∧ x 1 ≤ 0}
def Q4 : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ x 1 < 0}

lemma mQ1 : MeasurableSet Q1 :=
  (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
    (measurableSet_le measurable_const (measurable_pi_apply 1))
lemma mQ2 : MeasurableSet Q2 :=
  (measurableSet_le (measurable_pi_apply 0) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_pi_apply 1))
lemma mQ3 : MeasurableSet Q3 :=
  (measurableSet_lt (measurable_pi_apply 0) measurable_const).inter
    (measurableSet_le (measurable_pi_apply 1) measurable_const)
lemma mQ4 : MeasurableSet Q4 :=
  (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    (measurableSet_lt (measurable_pi_apply 1) measurable_const)

lemma decomp (S : Set (Fin 2 → ℝ)) :
    volume S = volume (S ∩ Q1) + volume (S ∩ Q2) + volume (S ∩ Q3) + volume (S ∩ Q4) := by
  rw [← measure_inter_add_diff S mQ1, ← measure_inter_add_diff (S \ Q1) mQ2,
    ← measure_inter_add_diff ((S \ Q1) \ Q2) mQ3, ← measure_inter_add_diff (((S \ Q1) \ Q2) \ Q3) mQ4]
  have hnull : volume ((((S \ Q1) \ Q2) \ Q3) \ Q4) = 0 := by
    apply measure_mono_null _ (measure_singleton (0 : Fin 2 → ℝ))
    intro x hx
    simp only [Set.mem_diff, Q1, Q2, Q3, Q4, Set.mem_setOf_eq, not_and, not_lt, not_le] at hx
    obtain ⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, h4⟩ := hx
    have e0 : x 0 = 0 := by
      rcases lt_trichotomy (x 0) 0 with h | h | h
      · rcases le_or_gt (x 1) 0 with h' | h'
        · exact absurd (h3 h) (not_lt.2 h')
        · exact absurd (h2 h.le) (not_le.2 h')
      · exact h
      · rcases le_or_gt 0 (x 1) with h' | h'
        · exact absurd (h1 h) (not_lt.2 h')
        · exact absurd (h4 h.le) (not_le.2 h')
    have e1 : x 1 = 0 := by
      rcases lt_trichotomy (x 1) 0 with h | h | h
      · linarith [h4 e0.ge]
      · exact h
      · linarith [h2 e0.le]
    ext i; fin_cases i <;> simp [e0, e1]
  have a2 : S \ Q1 ∩ Q2 = S ∩ Q2 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Q1, Q2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, fun ⟨c, _⟩ => by linarith [h'.1]⟩, h'⟩
  have a3 : (S \ Q1) \ Q2 ∩ Q3 = S ∩ Q3 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Q1, Q2, Q3, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨⟨h, _⟩, _⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨⟨h, fun ⟨c, _⟩ => by linarith [h'.1]⟩, fun ⟨_, c⟩ => by linarith [h'.2]⟩, h'⟩
  have a4 : ((S \ Q1) \ Q2) \ Q3 ∩ Q4 = S ∩ Q4 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Q1, Q2, Q3, Q4, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨⟨⟨h, fun ⟨_, c⟩ => by linarith [h'.2]⟩, fun ⟨_, c⟩ => by linarith [h'.2]⟩,
        fun ⟨c, _⟩ => by linarith [h'.1]⟩, h'⟩
  rw [a2, a3, a4, hnull, add_zero]; ring

noncomputable def ρ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![0, -1; 1, 0]

lemma ρ_apply (x : Fin 2 → ℝ) : ρ x 0 = -x 1 ∧ ρ x 1 = x 0 := by
  simp [ρ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma vol_ρ (S : Set (Fin 2 → ℝ)) : volume (ρ ⁻¹' S) = volume S := by
  have hd : LinearMap.det ρ = 1 := by
    rw [ρ, LinearMap.det_toLin', Matrix.det_fin_two_of]; norm_num
  rw [Measure.addHaar_preimage_linearMap _ (by rw [hd]; norm_num), hd]; simp

def Bq (q : ℝ) : Set (Fin 2 → ℝ) := {x | (∑ i, |x i| ^ q) ^ (1 / q) ≤ 1}

lemma ρ_Bq (q : ℝ) : ρ ⁻¹' Bq q = Bq q := by
  ext x; simp only [Bq, Set.mem_preimage, Set.mem_setOf_eq, Fin.sum_univ_two, (ρ_apply x).1,
    (ρ_apply x).2, abs_neg]; rw [add_comm]

lemma ρQ2 : ρ ⁻¹' Q2 = Q1 := by
  ext x; simp only [Q1, Q2, Set.mem_preimage, Set.mem_setOf_eq, (ρ_apply x).1, (ρ_apply x).2]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
lemma ρQ3 : ρ ⁻¹' Q3 = Q2 := by
  ext x; simp only [Q3, Q2, Set.mem_preimage, Set.mem_setOf_eq, (ρ_apply x).1, (ρ_apply x).2]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
lemma ρQ4 : ρ ⁻¹' Q4 = Q3 := by
  ext x; simp only [Q3, Q4, Set.mem_preimage, Set.mem_setOf_eq, (ρ_apply x).1, (ρ_apply x).2]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma vol_Bq_quad (q : ℝ) :
    volume (Bq q ∩ Q2) = volume (Bq q ∩ Q1) ∧ volume (Bq q ∩ Q3) = volume (Bq q ∩ Q1) ∧
    volume (Bq q ∩ Q4) = volume (Bq q ∩ Q1) := by
  have h2 : volume (Bq q ∩ Q2) = volume (Bq q ∩ Q1) := by
    rw [← vol_ρ, Set.preimage_inter, ρ_Bq, ρQ2]
  have h3 : volume (Bq q ∩ Q3) = volume (Bq q ∩ Q2) := by
    rw [← vol_ρ, Set.preimage_inter, ρ_Bq, ρQ3]
  have h4 : volume (Bq q ∩ Q4) = volume (Bq q ∩ Q3) := by
    rw [← vol_ρ, Set.preimage_inter, ρ_Bq, ρQ4]
  exact ⟨h2, h3.trans h2, h4.trans (h3.trans h2)⟩


lemma P_mixed {q s t : ℝ} (hq : 0 < q) (h : P q s t) (hst : s * t ≤ 0) :
    |s| ^ q + |t| ^ q ≤ 1 := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨_, h⟩
  · have : s * t = 0 := le_antisymm hst (mul_nonneg h1 h3)
    rcases mul_eq_zero.1 this with rfl | rfl
    · rw [abs_zero, zero_rpow hq.ne', zero_add]
      exact rpow_le_one (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith) hq.le
    · rw [abs_zero, zero_rpow hq.ne', add_zero]
      exact rpow_le_one (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith) hq.le
  · have : s * t = 0 := le_antisymm hst (mul_nonneg_of_nonpos_of_nonpos h2 h4)
    rcases mul_eq_zero.1 this with rfl | rfl
    · rw [abs_zero, zero_rpow hq.ne', zero_add]
      exact rpow_le_one (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith) hq.le
    · rw [abs_zero, zero_rpow hq.ne', add_zero]
      exact rpow_le_one (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith) hq.le
  · exact h

lemma bq_iff {q : ℝ} (hq : 0 < q) (x : Fin 2 → ℝ) :
    x ∈ Bq q ↔ |x 0| ^ q + |x 1| ^ q ≤ 1 := by
  simp only [Bq, Set.mem_setOf_eq, Fin.sum_univ_two]
  have h0 : 0 ≤ |x 0| ^ q + |x 1| ^ q := by positivity
  constructor
  · intro h
    by_contra hc; push_neg at hc
    have := one_lt_rpow hc (by positivity : 0 < 1 / q)
    linarith
  · intro h; exact rpow_le_one h0 h (by positivity)

def R0 (q : ℝ) : Set (Fin 2 → ℝ) := {x | P q (x 0) (x 1)}

lemma R0_Q1 {q : ℝ} (hq : 0 < q) :
    R0 q ∩ Q1 = Set.univ.pi ![Set.Ioc (0 : ℝ) 1, Set.Icc 0 1] := by
  ext x
  simp only [R0, Q1, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_univ_pi, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioc, Set.mem_Icc]
  constructor
  · rintro ⟨h, h0, h1⟩
    rcases h with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩
    · exact ⟨⟨h0, a2⟩, a3, a4⟩
    · linarith
    · have e : x 1 = 0 := by nlinarith
      have := abs_le_one_of hq a2
      rw [abs_le] at this
      exact ⟨⟨h0, this.2⟩, by rw [e], by rw [e]; norm_num⟩
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨Or.inl ⟨h0.le, h1, h2, h3⟩, h0, h2⟩

lemma R0_Q3 {q : ℝ} (hq : 0 < q) :
    R0 q ∩ Q3 = Set.univ.pi ![Set.Ico (-1 : ℝ) 0, Set.Icc (-1) 0] := by
  ext x
  simp only [R0, Q3, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_univ_pi, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ico, Set.mem_Icc]
  constructor
  · rintro ⟨h, h0, h1⟩
    rcases h with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩
    · linarith
    · exact ⟨⟨a1, h0⟩, a3, a4⟩
    · have e : x 1 = 0 := by nlinarith
      have := abs_le_one_of hq a2
      rw [abs_le] at this
      exact ⟨⟨this.1, h0⟩, by rw [e]; norm_num, by rw [e]⟩
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨Or.inr (Or.inl ⟨h0, h1.le, h2, h3⟩), h1, h3⟩

lemma R0_Q2 {q : ℝ} (hq : 0 < q) : R0 q ∩ Q2 = Bq q ∩ Q2 := by
  ext x
  simp only [Set.mem_inter_iff, bq_iff hq]
  simp only [R0, Q2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, h0, h1⟩
    exact ⟨P_mixed hq h (mul_nonpos_of_nonpos_of_nonneg h0 h1.le), h0, h1⟩
  · rintro ⟨h, h0, h1⟩
    exact ⟨Or.inr (Or.inr ⟨mul_nonpos_of_nonpos_of_nonneg h0 h1.le, h⟩), h0, h1⟩

lemma R0_Q4 {q : ℝ} (hq : 0 < q) : R0 q ∩ Q4 = Bq q ∩ Q4 := by
  ext x
  simp only [Set.mem_inter_iff, bq_iff hq]
  simp only [R0, Q4, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, h0, h1⟩
    exact ⟨P_mixed hq h (mul_nonpos_of_nonneg_of_nonpos h0 h1.le), h0, h1⟩
  · rintro ⟨h, h0, h1⟩
    exact ⟨Or.inr (Or.inr ⟨mul_nonpos_of_nonneg_of_nonpos h0 h1.le, h⟩), h0, h1⟩

lemma vol_R0 {q : ℝ} (hq : 1 < q) :
    volume (R0 q) = ENNReal.ofReal
      (2 * Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q) + 2) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨h2, h3, h4⟩ := vol_Bq_quad q
  have hB := decomp (Bq q)
  rw [h2, h3, h4] at hB
  have hvol : volume (Bq q) = ENNReal.ofReal
      ((2 * Real.Gamma (1 / q + 1)) ^ 2 / Real.Gamma (2 / q + 1)) := by
    have := MeasureTheory.volume_sum_rpow_le (ι := Fin 2) hq.le 1
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul] at this
    rw [Bq, this]; norm_num
  set c := Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q)
  have hc : 0 ≤ c := by
    have := Real.Gamma_pos_of_pos (by positivity : 0 < 1 + 2 / q)
    positivity
  have hvol' : volume (Bq q) = 4 * ENNReal.ofReal c := by
    rw [hvol, show (2 * Real.Gamma (1 / q + 1)) ^ 2 / Real.Gamma (2 / q + 1) = 4 * c by
      simp only [c]; rw [add_comm (1 / q), add_comm (2 / q)]; ring,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hX : volume (Bq q ∩ Q1) = ENNReal.ofReal c := by
    have : 4 * volume (Bq q ∩ Q1) = 4 * ENNReal.ofReal c := by
      rw [← hvol', hB]; ring
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 this
  have hR := decomp (R0 q)
  rw [R0_Q1 hq0, R0_Q3 hq0, R0_Q2 hq0, R0_Q4 hq0, h2, h4, hX] at hR
  rw [hR]
  simp only [volume_pi_pi, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.volume_Ioc, Real.volume_Ico, Real.volume_Icc]
  rw [show 2 * Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q) + 2 = 1 + c + 1 + c by
      simp only [c]; ring,
    ENNReal.ofReal_add (by positivity) hc, ENNReal.ofReal_add (by positivity) (by norm_num),
    ENNReal.ofReal_add (by norm_num) hc]
  norm_num

end LpRSAux


namespace LpRSAux
open Arxiv.«2607.03582»

lemma vol_Sq : volume Sq = 1 := by
  have h1 : Sq = (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹'
      Set.univ.pi ![Set.Icc (0 : ℝ) 1, Set.Icc 0 1] := by
    ext y
    simp [Sq, Fin.forall_fin_two, and_assoc]
  rw [h1, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).measure_preimage_equiv]
  simp [volume_pi_pi, Fin.prod_univ_two]

lemma vol_R {q : ℝ} (hq : 1 < q) : volume {y : ℝ² | P q (y 0) (y 1)} =
    ENNReal.ofReal (2 * Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q) + 2) := by
  have h1 : {y : ℝ² | P q (y 0) (y 1)} = (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' R0 q := by
    ext y; simp [R0]
  rw [h1, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).measure_preimage_equiv,
    vol_R0 hq]

end LpRSAux

theorem OMA.solution : type_of% @Arxiv.«2607.03582».volume_lpSum_eq_of_isParallelogramAtOrigin := by
  intro K hpar p q hp hq
  obtain ⟨a, b, hli, rfl⟩ := hpar
  have hpq : p.HolderConjugate q := Real.holderConjugate_iff.2 ⟨hp, by simpa [one_div] using hq⟩
  rw [LpRSAux.lpSum_eq hli hpq, LpRSAux.K_eq, Measure.addHaar_image_linearMap,
    Measure.addHaar_image_linearMap, LpRSAux.vol_R hpq.symm.lt, LpRSAux.vol_Sq, Arxiv.«2607.03582».rsConstant]
  ring
