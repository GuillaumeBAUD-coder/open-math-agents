import FormalConjectures.ErdosProblems.«1082»
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Reducing the no-three-collinear distinct-distance problem

A circle containing more than (4d+2)/3 points forces a finite regular polygon via
small multiplicative doubling of its normalized points. The other case reduces to
the effect of deleting two points from a smallest counterexample.
-/

open EuclideanGeometry Polynomial
open scoped Classical Pointwise Polynomial

namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1

/-- Configurations determining at most three positive distances. The one-, two- and three-distance maxima are 3, 5 and 7. See Erdős and Fishburn, Maximum planar sets that determine k distances, Theorem 1. https://doi.org/10.1016/0012-365X(95)00153-N -/
def H1 : Prop := ∀ A : Finset ℝ², NonTrilinear (A : Set ℝ²) → distinctDistances A ≤ 3 →
    A.card / 2 ≤ distinctDistances A

/-- In the circle-sparse case, find two vertices meeting every pair at one length.
    The argument below shows that a smallest counterexample would violate this assertion. -/
def H2 : Prop := ∀ A : Finset ℝ², NonTrilinear (A : Set ℝ²) →
    A.card = 2 * distinctDistances A + 2 →
    (∃ d ∈ distanceSet A, A.card + 2 ≤ distanceMultiplicity A d) →
    (∀ (c : ℝ²) (r : ℝ), 3 * (A.filter (fun z => dist z c = r)).card ≤ 4 * distinctDistances A + 2) →
    ∃ x ∈ A, ∃ y ∈ A.erase x, ∃ d ∈ distanceSet A, d ∉ distanceSet ((A.erase x).erase y)

/-- Only the listed finite polygon orders require a base calculation. A repeated distance puts
    the off-circle point on a symmetry axis. Two distinct projections determining chord lengths
    then determine its signed radius as a ratio of differences of twice-cosines. All resulting
    equalities can be tested in the cyclotomic field of order twice the polygon order. -/
def H3 : Prop := ∀ (T : Finset Circle) (H : Subgroup Circle), (H : Set Circle) = T →
    7 ≤ T.card → T.card ≤ 31 → (Even T.card ∨ T.card = 7) →
    ∀ q : ℂ, q ≠ 0 → ‖q‖ ≠ 1 →
    2 * (T.filter (fun z : Circle => dist q (z : ℂ) ∈ distanceSet T)).card ≤ T.card

/-- Descent for orders divisible by four. A violation at order 2m must yield a violation
    at order m. The expected conjugation raises each root of unity to the power 1+m.
    Separating chord and vertex parities leaves a half-sized polygon and at most four
    exceptional vertices. An alternative large-order route uses Beukers and Smyth,
    Cyclotomic points on curves, Section 4.1. The chord equation has Newton-polygon
    area two and no one-dimensional torsion coset for a noncentral off-circle point.
    https://www.maths.ed.ac.uk/~chris/preprints/beukers_smyth.pdf -/
def H4 : Prop := ∀ (m : ℕ), 16 ≤ m → Even m → ∀ (T : Finset Circle) (H : Subgroup Circle),
    (H : Set Circle) = T → T.card = 2*m → ∀ q : ℂ, q ≠ 0 → ‖q‖ ≠ 1 →
    T.card < 2 * (T.filter (fun z : Circle => dist q (z : ℂ) ∈ distanceSet T)).card →
    ∃ (V : Finset Circle) (G : Subgroup Circle) (p : ℂ), (G : Set Circle) = V ∧ V.card = m ∧
      p ≠ 0 ∧ ‖p‖ ≠ 1 ∧ V.card < 2 * (V.filter (fun z : Circle => dist p (z : ℂ) ∈ distanceSet V)).card

lemma circle_pigeonhole (B : Finset ℝ²) (D : Finset ℝ) (c p : ℝ²) (r : ℝ)
    (hpc : c ≠ p) (hc : ∀ x ∈ B, dist x c = r) (hmap : ∀ x ∈ B, dist x p ∈ D) :
    B.card ≤ 2 * D.card := by
  classical
  by_contra! h
  obtain ⟨d, _, hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap (by
    simpa [Nat.mul_comm] using h : D.card * 2 < B.card)
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp hd
  obtain ⟨hx,hxd⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy,hyd⟩ := Finset.mem_filter.mp hy
  obtain ⟨hz,hzd⟩ := Finset.mem_filter.mp hz
  rcases eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (finrank_euclideanSpace_fin (n := 2)) hpc hxy
      (hc x hx) (hc y hy) (hc z hz) hxd hyd hzd with h | h
  · exact hxz h.symm
  · exact hyz h.symm

lemma dist_mem {A : Finset ℝ²} {x p : ℝ²} (hx : x ∈ A) (hp : p ∈ A) (hxp : x ≠ p) :
    dist x p ∈ distanceSet A :=
  Finset.mem_image.mpr ⟨(x,p), Finset.mem_offDiag.mpr ⟨hx,hp,hxp⟩, rfl⟩

lemma circle_subset_bound (A B : Finset ℝ²) (c p : ℝ²) (r : ℝ)
    (hp : p ∈ A) (hpc : c ≠ p) (hBA : B ⊆ A) (hpB : p ∉ B)
    (hc : ∀ x ∈ B, dist x c = r) : B.card ≤ 2 * distinctDistances A := by
  classical
  apply circle_pigeonhole B (distanceSet A) c p r hpc hc
  intro x hx
  apply dist_mem (hBA hx) hp
  rintro rfl
  exact hpB hx

lemma concyclic_bound (A : Finset ℝ²) (c : ℝ²) (r : ℝ) (hC : ∀ x ∈ A, dist x c = r) :
    A.card / 2 ≤ distinctDistances A := by
  classical
  by_cases h : ∃ p ∈ A, c ≠ p
  · obtain ⟨p,hp,hpc⟩ := h
    have hb := circle_subset_bound A (A.erase p) c p r hp hpc (Finset.erase_subset p A)
      (Finset.notMem_erase p A) (fun x hx => hC x (Finset.mem_of_mem_erase hx))
    have he := Finset.card_erase_add_one hp
    omega
  · have hsub : A ⊆ {c} := by
      intro x hx
      exact Finset.mem_singleton.mpr (by by_contra hn; exact h ⟨x,hx,Ne.symm hn⟩)
    have hb : A.card ≤ 1 := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton c)
    omega

lemma small_distance_multiplicities (A : Finset ℝ²)
    (h : ∀ d ∈ distanceSet A, distanceMultiplicity A d ≤ A.card + 1) :
    A.card / 2 ≤ distinctDistances A := by
  classical
  by_contra! hbad
  have hh := Finset.sum_le_sum h
  rw [sum_distanceMultiplicity, Finset.sum_const, nsmul_eq_mul] at hh
  change A.card.choose 2 ≤ distinctDistances A * (A.card + 1) at hh
  rw [Nat.choose_two_right] at hh
  have hc : A.card * (A.card - 1) ≤ 2 * (distinctDistances A * (A.card + 1)) + 1 := by omega
  have hd : 2 * (distinctDistances A + 1) ≤ A.card := by omega
  have hn : 0 < A.card := by omega
  have hg := Nat.mul_le_mul_right (A.card + 1) hd
  have hsub : A.card - 1 + 1 = A.card := by omega
  nlinarith [congrArg (A.card * ·) hsub]

lemma saturated_circle (A B : Finset ℝ²) (c p z : ℝ²) (r : ℝ)
    (hBA : B ⊆ A) (hB : ∀ x ∈ B, dist x c = r) (hsize : 2 * distinctDistances A < B.card)
    (hp : p ∈ B) (hpc : c ≠ p) (hz : dist z c = r) (hzd : dist z p ∈ distanceSet A) : z ∈ B := by
  classical
  by_contra hnot
  let E := insert z (B.erase p)
  have hznot : z ∉ B.erase p := fun hz => hnot (Finset.mem_of_mem_erase hz)
  have he : E.card = B.card := by
    rw [Finset.card_insert_of_notMem hznot, Finset.card_erase_add_one hp]
  have hb := circle_pigeonhole E (distanceSet A) c p r hpc (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hz
    · exact hB x (Finset.mem_of_mem_erase hx)) (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hzd
    · exact dist_mem (hBA (Finset.mem_of_mem_erase hx)) (hBA hp) (Finset.ne_of_mem_erase hx))
  change E.card ≤ 2 * distinctDistances A at hb
  omega

lemma saturated_radius_realized (A B : Finset ℝ²) (c p : ℝ²) (r : ℝ)
    (hBA : B ⊆ A) (hB : ∀ x ∈ B, dist x c = r) (hsize : 2 * distinctDistances A < B.card)
    (hp : p ∈ B) (hpc : c ≠ p) (hc : c ∈ A) : ∃ q ∈ B, dist q p = r := by
  classical
  by_contra! hnot
  have hr : r ∈ distanceSet A := hB p hp ▸ dist_mem (hBA hp) hc hpc.symm
  have hBD := circle_pigeonhole (B.erase p) ((distanceSet A).erase r) c p r hpc
    (fun x hx => hB x (Finset.mem_of_mem_erase hx)) (by
      intro x hx
      apply Finset.mem_erase.mpr
      exact ⟨hnot x (Finset.mem_of_mem_erase hx),
        dist_mem (hBA (Finset.mem_of_mem_erase hx)) (hBA hp) (Finset.ne_of_mem_erase hx)⟩)
  have he := Finset.card_erase_add_one hp
  have hd := Finset.card_erase_add_one hr
  unfold distinctDistances at hsize
  omega

lemma center_plus_circle_bound (A : Finset ℝ²) (c : ℝ²) (r : ℝ)
    (hc : c ∈ A) (hA : NonTrilinear (A : Set ℝ²)) (hC : ∀ x ∈ A.erase c, dist x c = r) :
    A.card / 2 ≤ distinctDistances A := by
  classical
  by_contra! hbad
  let B := A.erase c
  have hBA : B ⊆ A := Finset.erase_subset c A
  have hcard : B.card + 1 = A.card := Finset.card_erase_add_one hc
  have hlarge : 2 * distinctDistances A < B.card := by omega
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  have hpc : c ≠ p := (Finset.ne_of_mem_erase hp).symm
  have hpr := hC p hp
  have hr : r ∈ distanceSet A := hpr ▸ dist_mem (hBA hp) hc hpc.symm
  obtain ⟨q,hq,hqp⟩ := saturated_radius_realized A B c p r hBA hC hlarge hp hpc hc
  let t := c + (q - p)
  have ht_c : dist t c = r := by simpa [t,dist_eq_norm] using hqp
  have ht_q : dist t q = r := by
    have h : t - q = c - p := by dsimp [t]; abel
    rw [dist_eq_norm,h,←dist_eq_norm,dist_comm,hpr]
  have ht := saturated_circle A B c q t r hBA hC hlarge hq (Finset.ne_of_mem_erase hq).symm ht_c
    (ht_q ▸ hr)
  let u := c + (c - p)
  have hu_c : dist u c = r := by
    have h : u - c = c - p := by dsimp [u]; abel
    rw [dist_eq_norm,h,←dist_eq_norm,dist_comm,hpr]
  have hu_t : dist u t = r := by
    have h : u - t = c - q := by dsimp [t,u]; abel
    rw [dist_eq_norm,h,←dist_eq_norm,dist_comm,hC q hq]
  have hu := saturated_circle A B c t u r hBA hC hlarge ht (Finset.ne_of_mem_erase ht).symm hu_c
    (hu_t ▸ hr)
  have hpu : p ≠ u := by
    intro he
    apply hpc
    ext i
    have heq := congrArg (fun z : ℝ² => z i) he
    change p i = c i + (c i - p i) at heq
    linarith
  have hcol : Collinear ℝ ({c,p,u} : Set ℝ²) := by
    apply (collinear_iff_of_mem (k := ℝ) (Set.mem_insert c ({p,u} : Set ℝ²))).mpr
    refine ⟨p - c, ?_⟩
    intro x hx
    rcases hx with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · obtain rfl : x = u := h
      exact ⟨-1, by simp [u,sub_eq_add_neg]; abel⟩
  exact hA hc (hBA hp) (hBA hu) hpc hpu (Finset.ne_of_mem_erase hu).symm hcol

lemma all_but_one_concyclic (A : Finset ℝ²) (c : ℝ²) (r : ℝ)
    (hA : NonTrilinear (A : Set ℝ²)) (p : ℝ²) (hC : ∀ x ∈ A.erase p, dist x c = r) :
    A.card / 2 ≤ distinctDistances A := by
  classical
  by_cases hp : p ∈ A
  · by_cases he : c = p
    · subst p
      exact center_plus_circle_bound A c r hp hA hC
    · have hb := circle_subset_bound A (A.erase p) c p r hp he (Finset.erase_subset p A)
        (Finset.notMem_erase p A) hC
      have hs := Finset.card_erase_add_one hp
      omega
  · apply concyclic_bound A c r
    simpa [Finset.erase_eq_of_notMem hp] using hC

lemma subgroup_quotient_of_small {G : Type*} [CommGroup G] (A : Finset G)
    (hsmall : 2 * (A / A).card < 3 * A.card) :
    ∃ H : Subgroup G, (H : Set G) = (↑(A / A) : Set G) := by
  classical
  let D := A / A
  let good (x : G) := A.filter (fun z => z / x ∈ A)
  have hgood (x : G) (hx : x ∈ D) : 2 * A.card ≤ D.card + (good x).card := by
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_div.mp hx
    let X := A.image (fun t => t / a)
    let Y := A.image (fun t => t / b)
    have hX : X.card = A.card := Finset.card_image_of_injective _ (div_left_injective ..)
    have hY : Y.card = A.card := Finset.card_image_of_injective _ (div_left_injective ..)
    have hsub (u) (hu : u ∈ A) : A.image (fun t => t / u) ⊆ D := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_div.mpr ⟨t,ht,u,hu,rfl⟩
    have hu := Finset.card_le_card (Finset.union_subset (hsub a ha) (hsub b hb))
    have hi : ((X ∩ Y).image (fun z => z * a)) ⊆ good (a / b) := by
      intro z hz
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hat,hbt⟩ := Finset.mem_inter.mp ht
      obtain ⟨u,hu,hu'⟩ := Finset.mem_image.mp hat
      obtain ⟨v,hv,hv'⟩ := Finset.mem_image.mp hbt
      apply Finset.mem_filter.mpr
      constructor
      · simpa [← hu'] using hu
      · have he : t * a / (a / b) = v := by rw [← hv']; simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        simpa [he] using hv
    have hh := Finset.card_le_card hi
    rw [Finset.card_image_of_injective _ (mul_left_injective ..)] at hh
    have hir := Finset.card_union_add_card_inter X Y
    change (X ∪ Y).card ≤ D.card at hu
    omega
  have hn : 0 < A.card := by omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hn
  have hne : (↑D : Set G).Nonempty := ⟨a/a, Finset.mem_div.mpr ⟨a,ha,a,ha,rfl⟩⟩
  refine ⟨Subgroup.ofDiv D hne ?_, rfl⟩
  intro x hx y hy
  have hxl := hgood x hx
  have hyl := hgood y hy
  change 2 * D.card < 3 * A.card at hsmall
  obtain ⟨z,hz⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.filter_subset (fun z => z/x ∈ A) A) (Finset.filter_subset (fun z => z/y ∈ A) A)
    (show A.card < (good x).card + (good y).card by omega)
  obtain ⟨hxz,hyz⟩ := Finset.mem_inter.mp hz
  refine Finset.mem_div.mpr ⟨z/y,(Finset.mem_filter.mp hyz).2,z/x,(Finset.mem_filter.mp hxz).2, ?_⟩
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

lemma circle_quotient_card (A : Finset Circle) : (A / A).card ≤ 2 * distinctDistances A + 1 := by
  classical
  let B := (A / A).erase 1
  by_contra! h
  have hc : 2 * distinctDistances A < B.card := by
    by_cases he : (1 : Circle) ∈ A / A
    · have := Finset.card_erase_add_one he
      dsimp [B]; omega
    · simpa [B, Finset.erase_eq_of_notMem he] using (by omega : 2 * distinctDistances A < (A / A).card)
  have hmap (w : Circle) (hw : w ∈ B) : dist (w : ℂ) 1 ∈ distanceSet A := by
    obtain ⟨hw1,hwA⟩ := Finset.mem_erase.mp hw
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_div.mp hwA
    have huv : u ≠ v := by rintro rfl; simp at hw1
    apply Finset.mem_image.mpr
    refine ⟨(u,v),Finset.mem_offDiag.mpr ⟨hu,hv,huv⟩, ?_⟩
    change dist (u : ℂ) (v : ℂ) = dist ((u : ℂ) / v) 1
    rw [dist_eq_norm, dist_eq_norm, div_sub_one (Circle.coe_ne_zero v), norm_div, Circle.norm_coe, div_one]
  obtain ⟨d,_,hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap
    (show (distanceSet A).card * 2 < B.card by simpa [distinctDistances, Nat.mul_comm] using hc)
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hd
  have hz (u : Circle) : dist (u : ℂ) 0 = 1 := by rw [dist_zero_right, Circle.norm_coe]
  have h' := eq_of_dist_eq_of_dist_eq_of_finrank_eq_two Complex.finrank_real_complex
    (zero_ne_one : (0 : ℂ) ≠ 1) (Circle.coe_injective.ne hab) (hz a) (hz b) (hz c)
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
  rcases h' with hh | hh
  · exact hac (Circle.coe_injective hh.symm)
  · exact hbc (Circle.coe_injective hh.symm)

lemma large_circle_is_group_orbit (A : Finset Circle) (hA : 4 * distinctDistances A + 2 < 3 * A.card) :
    ∃ H : Subgroup Circle, (H : Set Circle) = (↑(A / A) : Set Circle) := by
  apply subgroup_quotient_of_small A
  have := circle_quotient_card A
  omega

lemma circle_fibers (B : Finset Circle) (p : ℂ) (hp : p ≠ 0) (d : ℝ) :
    (B.filter (fun x : Circle => dist p (x : ℂ) = d)).card ≤ 2 := by
  by_contra! h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp h
  have hz (u : Circle) : dist (u : ℂ) 0 = 1 := by rw [dist_zero_right,Circle.norm_coe]
  have he := eq_of_dist_eq_of_dist_eq_of_finrank_eq_two Complex.finrank_real_complex hp.symm
    (Circle.coe_injective.ne hab) (hz a) (hz b) (hz c)
    (by simpa [dist_comm] using (Finset.mem_filter.mp ha).2)
    (by simpa [dist_comm] using (Finset.mem_filter.mp hb).2)
    (by simpa [dist_comm] using (Finset.mem_filter.mp hc).2)
  rcases he with h | h
  · exact hac (Circle.coe_injective h.symm)
  · exact hbc (Circle.coe_injective h.symm)

lemma rotate_dist (x y : ℂ) (u : Circle) : dist (x / (u : ℂ)) (y / (u : ℂ)) = dist x y := by
  rw [dist_eq_norm,←sub_div,norm_div,Circle.norm_coe,div_one,dist_eq_norm]

lemma chord_from_quotient {a b u v : Circle} (h : a/b = u/v) : dist (a : ℂ) b = dist (u : ℂ) v := by
  have hh := congrArg (fun z : Circle => dist (z : ℂ) 1) h
  calc
    _ = dist ((a : ℂ)/b) ((b : ℂ)/b) := (rotate_dist _ _ b).symm
    _ = dist ((u : ℂ)/v) ((v : ℂ)/v) := by simpa using hh
    _ = _ := rotate_dist _ _ v

lemma doubled_chord_bound {L : Type*} [Field L] [CharZero L] (S : Finset L) (u v k u' v' k' : L) (hu : u ≠ 0) (hk : k ≠ 0)
    (hs : ∀ z ∈ S, z ≠ 0 ∧ (u*z + v/z + k)^2 - 2 = u'*z^2 + v'/z^2 + k') : S.card ≤ 4 := by
  classical
  let P : Polynomial L := C (u^2-u')*X^4 + C (2*u*k)*X^3 + C (k^2+2*u*v-2-k')*X^2 +
    C (2*v*k)*X + C (v^2-v')
  have hcoeff : P.coeff 3 = 2*u*k := by
    simp only [P,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]; norm_num
  have hne : P ≠ 0 := by
    intro he
    rw [he] at hcoeff
    simp at hcoeff
    tauto
  have hdeg : P.natDegree ≤ 4 := by dsimp [P]; compute_degree
  have hsub : S ⊆ P.roots.toFinset := by
    intro z hz
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hne).mpr
    obtain ⟨hnz,he⟩ := hs z hz
    change eval z P = 0
    simp only [P,eval_add,eval_mul,eval_C,eval_X,eval_pow]
    field_simp [hnz] at he
    linear_combination he
  exact (Finset.card_le_card hsub).trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' P).trans hdeg

lemma interpolated_coefficients (K : Subfield ℂ) (u v k x y z : ℂ)
    (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h1 : u*x^2+k*x+v ∈ K) (h2 : u*y^2+k*y+v ∈ K) (h3 : u*z^2+k*z+v ∈ K) :
    u ∈ K ∧ v ∈ K ∧ k ∈ K := by
  have hA : u*(x+y)+k ∈ K := by
    convert K.div_mem (K.sub_mem h1 h2) (K.sub_mem hx hy) using 1
    field_simp [sub_ne_zero.mpr hxy]; ring
  have hB : u*(y+z)+k ∈ K := by
    convert K.div_mem (K.sub_mem h2 h3) (K.sub_mem hy hz) using 1
    field_simp [sub_ne_zero.mpr hyz]; ring
  have hu : u ∈ K := by
    convert K.div_mem (K.sub_mem hA hB) (K.sub_mem hx hz) using 1
    field_simp [sub_ne_zero.mpr hxz]; ring
  have hk : k ∈ K := by
    convert K.sub_mem hA (K.mul_mem hu (K.add_mem hx hy)) using 1; ring
  refine ⟨hu, ?_, hk⟩
  convert K.sub_mem (K.sub_mem h1 (K.mul_mem hk hx)) (K.mul_mem hu (K.pow_mem hx 2)) using 1; ring

lemma odd_order_chord_bound {L : Type*} [Field L] [CharZero L] (S : Finset L)
    (σ : L →+* L) (u v k : L) (hu : u ≠ 0) (hk : k ≠ 0)
    (hs : ∀ z ∈ S, z ≠ 0 ∧ σ z = z^2 ∧ ∃ w : L, w ≠ 0 ∧ σ w = w^2 ∧
      w + w⁻¹ = u*z + v/z + k) : S.card ≤ 4 := by
  apply doubled_chord_bound S u v k (σ u) (σ v) (σ k) hu hk
  intro z hz
  obtain ⟨hnz,hσz,w,hnw,hσw,he⟩ := hs z hz
  refine ⟨hnz, ?_⟩
  have hm := congrArg σ he
  simp only [map_add,map_mul,map_div₀,map_inv₀,hσw,hσz] at hm
  rw [←he,←hm]
  field_simp [hnw]; ring

lemma automorphism_on_roots (n a : ℕ) [NeZero n] (ha : a.Coprime n) :
    ∃ K : IntermediateField ℚ ℂ, (∀ z : ℂ, z^n = 1 → z ∈ K) ∧
      ∃ σ : K →+* K, ∀ z : K, z^n = 1 → σ z = z^a := by
  classical
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (NeZero.ne _)
  let K := IntermediateField.adjoin ℚ {ζ}
  haveI : IsCyclotomicExtension {n} ℚ K :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin n ℚ ℂ K hζ).mpr rfl
  have hgen : ζ ∈ K := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  refine ⟨K,?_,?_⟩
  · intro z hz
    obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    exact K.pow_mem hgen i
  · let w := IsCyclotomicExtension.zeta n ℚ K
    have hw : IsPrimitiveRoot w n := IsCyclotomicExtension.zeta_spec _ _ _
    let σ := IsCyclotomicExtension.fromZetaAut (hw.pow_of_coprime a ha)
      (cyclotomic.irreducible_rat (NeZero.pos n))
    have hwσ : σ w = w^a := IsCyclotomicExtension.fromZetaAut_spec _ _
    refine ⟨σ.toRingEquiv.toRingHom, ?_⟩
    intro z hz
    obtain ⟨i, _, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    change σ (w^i) = (w^i)^a
    rw [map_pow,hwσ,←pow_mul,←pow_mul,Nat.mul_comm]

lemma finite_subgroup_root (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (z : Circle) (hz : z ∈ T) : (z : ℂ)^T.card = 1 := by
  have e : H ≃ T := Equiv.subtypeEquivRight (fun x => by change x ∈ (H : Set Circle) ↔ _; rw [hT]; rfl)
  have hn : Nat.card H = T.card := (Nat.card_congr e).trans (Nat.card_eq_finsetCard T)
  let x : H := ⟨z, by change z ∈ (H : Set Circle); rwa [hT]⟩
  have hh := pow_card_eq_one' (x := x)
  rw [hn] at hh
  have hs := congrArg (fun y : H => (y.1 : ℂ)) hh
  simpa [x] using hs

lemma chord_equation (p : ℂ) (z w : Circle) (h : dist p (z : ℂ) = dist (w : ℂ) 1) :
    (w : ℂ)+(w : ℂ)⁻¹ = starRingEnd ℂ p*(z : ℂ) + p/(z : ℂ) + (1 - (Complex.normSq p : ℂ)) := by
  rw [dist_eq_norm,dist_eq_norm] at h
  have hh := congrArg (fun r : ℝ => r^2) h
  change ‖p-(z:ℂ)‖^2 = ‖(w:ℂ)-1‖^2 at hh
  rw [Complex.sq_norm,Complex.sq_norm] at hh
  have hc := congrArg ((↑) : ℝ → ℂ) hh
  rw [Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self,map_sub,map_sub,map_one,
    ←Circle.coe_inv_eq_conj,←Circle.coe_inv_eq_conj, Circle.coe_inv,Circle.coe_inv] at hc
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [Circle.coe_ne_zero] at hc ⊢
  linear_combination hc

lemma chord_ratio (p : ℂ) (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (z : Circle) (h : dist p (z : ℂ) ∈ distanceSet T) :
    ∃ w ∈ T, (w : ℂ)+(w : ℂ)⁻¹ = starRingEnd ℂ p*(z : ℂ) + p/(z : ℂ) + (1 - (Complex.normSq p : ℂ)) := by
  classical
  obtain ⟨⟨x,y⟩,hxy,he⟩ := Finset.mem_image.mp h
  obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.mp hxy
  have hmem (w : Circle) : w ∈ H ↔ w ∈ T := by change w ∈ (H : Set Circle) ↔ _; rw [hT]; rfl
  refine ⟨x/y, (hmem _).mp (H.div_mem ((hmem _).mpr hx) ((hmem _).mpr hy)), chord_equation _ _ _ ?_⟩
  rw [←he]
  change dist (x : ℂ) (y : ℂ) = dist ((x : ℂ)/(y : ℂ)) 1
  rw [dist_eq_norm,dist_eq_norm,div_sub_one (Circle.coe_ne_zero _),norm_div,Circle.norm_coe,div_one]

lemma cyclic_chord_data (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (p : ℂ) (hp : p ≠ 0) (hnorm : ‖p‖ ≠ 1) (S : Finset Circle) (hST : S ⊆ T)
    (hin : ∀ z ∈ S, dist p (z : ℂ) ∈ distanceSet T) (hS : 2 < S.card)
    (a : ℕ) (ha : a.Coprime T.card) :
    ∃ (K : IntermediateField ℚ ℂ) (σ : K →+* K) (P : Finset K) (u v k : K),
      S.card = P.card ∧ u ≠ 0 ∧ v ≠ 0 ∧ k ≠ 0 ∧ k = 1-u*v ∧ ∀ z ∈ P,
      z ≠ 0 ∧ z^T.card = 1 ∧ σ z = z^a ∧ ∃ w : K, w ≠ 0 ∧ w^T.card = 1 ∧ σ w = w^a ∧
      w + w⁻¹ = u*z + v/z + k := by
  classical
  haveI : NeZero T.card := ⟨by have := Finset.card_le_card hST; omega⟩
  obtain ⟨K,hK,σ,hσ⟩ := automorphism_on_roots T.card a ha
  let u := starRingEnd ℂ p
  let v := p
  let k := 1-(Complex.normSq p : ℂ)
  have hmem (z : Circle) (hz : z ∈ T) : (z : ℂ) ∈ K := hK _ (finite_subgroup_root T H hT z hz)
  have hval (z : Circle) (hz : z ∈ S) : u*(z : ℂ)^2 + k*(z : ℂ) + v ∈ K := by
    obtain ⟨w,hw,he⟩ := chord_ratio p T H hT z (hin z hz)
    have hm := K.mul_mem (K.add_mem (hmem w hw) (K.inv_mem (hmem w hw))) (hmem z (hST hz))
    have heq : u*(z : ℂ)^2 + k*(z : ℂ) + v = ((w : ℂ)+(w : ℂ)⁻¹)*(z : ℂ) := by
      rw [he]; dsimp [u,v,k]; field_simp [Circle.coe_ne_zero]; ring
    rwa [heq]
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp hS
  obtain ⟨hu,hv,hk⟩ := interpolated_coefficients K.toSubfield u v k x y z
    (hmem x (hST hx)) (hmem y (hST hy)) (hmem z (hST hz))
    (Circle.coe_injective.ne hxy) (Circle.coe_injective.ne hyz) (Circle.coe_injective.ne hxz)
    (hval x hx) (hval y hy) (hval z hz)
  let lift (z : S) : K := ⟨(z.1 : ℂ),hmem z.1 (hST z.2)⟩
  let P := S.attach.image lift
  have hlift : Function.Injective lift := fun _ _ h => Subtype.ext (Circle.coe_injective (congrArg ((↑) : K → ℂ) h))
  have hP : P.card = S.card := by dsimp [P]; rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  refine ⟨K,σ,P,⟨u,hu⟩,⟨v,hv⟩,⟨k,hk⟩,hP.symm,?_,?_,?_,?_,?_⟩
  · intro he
    have : u = 0 := congrArg ((↑) : K → ℂ) he
    exact hp ((map_eq_zero (starRingEnd ℂ)).mp this)
  · exact fun he => hp (congrArg ((↑) : K → ℂ) he)
  · intro he
    have h0 : k = 0 := congrArg ((↑) : K → ℂ) he
    have h1 : (Complex.normSq p : ℂ) = 1 := (sub_eq_zero.mp h0).symm
    have h2 : Complex.normSq p = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    exact hnorm (by nlinarith [norm_nonneg p])
  · apply Subtype.ext
    change 1-(Complex.normSq p : ℂ) = 1 - starRingEnd ℂ p*p
    rw [Complex.normSq_eq_conj_mul_self]
  · intro t ht
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨w,hw,he⟩ := chord_ratio p T H hT j.1 (hin j.1 j.2)
    let wK : K := ⟨(w : ℂ),hmem w hw⟩
    have hroot : lift j ^ T.card = 1 := Subtype.ext (finite_subgroup_root _ _ hT j.1 (hST j.2))
    have wroot : wK ^ T.card = 1 := Subtype.ext (finite_subgroup_root _ _ hT w hw)
    exact ⟨(fun h => (Circle.coe_ne_zero j.1) (congrArg ((↑) : K → ℂ) h)),hroot,hσ _ hroot,
      wK,(fun h => (Circle.coe_ne_zero w) (congrArg ((↑) : K → ℂ) h)),wroot,hσ _ wroot,Subtype.ext he⟩

lemma odd_polygon_at_most_four (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (ho : Odd T.card) (p : ℂ) (hp : p ≠ 0) (hnorm : ‖p‖ ≠ 1) :
    (T.filter (fun z : Circle => dist p (z : ℂ) ∈ distanceSet T)).card ≤ 4 := by
  classical
  let S := T.filter (fun z : Circle => dist p (z : ℂ) ∈ distanceSet T)
  by_contra! h
  change 4 < S.card at h
  obtain ⟨K,σ,P,u,v,k,he,hu,_,hk,_,hl⟩ := cyclic_chord_data T H hT p hp hnorm S
    (Finset.filter_subset _ _) (fun _ hz => (Finset.mem_filter.mp hz).2) (by omega) 2 ho.coprime_two_left
  have h4 := odd_order_chord_bound P σ u v k hu hk (by
    intro z hz
    obtain ⟨hnz,_,hσz,w,hnw,_,hσw,hw⟩ := hl z hz
    exact ⟨hnz,hσz,w,hnw,hσw,hw⟩)
  omega

lemma signed_doubling_bound {L : Type*} [Field L] [CharZero L] (S : Finset L) (σ : L →+* L)
    (u v k : L) (hu : u ≠ 0) (hk : k ≠ 0) (s t : L) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (h : ∀ z ∈ S, z ≠ 0 ∧ σ z = s*z^2 ∧ ∃ w : L, w ≠ 0 ∧ σ w = t*w^2 ∧
      w+w⁻¹ = u*z+v/z+k) : S.card ≤ 4 := by
  apply doubled_chord_bound S u v k (t*s*σ u) (t*s*σ v) (t*σ k) hu hk
  intro z hz
  obtain ⟨hnz,hsz,w,hnw,htw,he⟩ := h z hz
  have hh := congrArg σ he
  simp only [map_add,map_mul,map_div₀,map_inv₀,hsz,htw] at hh
  refine ⟨hnz,?_⟩
  rw [←he]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp at hh ⊢ <;> field_simp [hnz,hnw] at hh ⊢ <;>
    first | linear_combination hh | linear_combination -hh

lemma signed_polygon_at_most_sixteen (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (m : ℕ) (hm : Odd m) (hM : T.card = 2*m) (p : ℂ) (hp : p ≠ 0) (hnorm : ‖p‖ ≠ 1) :
    (T.filter (fun z : Circle => dist p (z : ℂ) ∈ distanceSet T)).card ≤ 16 := by
  classical
  let S := T.filter (fun z : Circle => dist p (z : ℂ) ∈ distanceSet T)
  by_contra! h
  change 16 < S.card at h
  have hcop : (m+2).Coprime T.card := by
    rw [hM,Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.coprime_two_right]
      obtain ⟨j,hj⟩ := hm
      exact ⟨j+1,by omega⟩
    · rw [Nat.add_comm,Nat.coprime_add_self_left,Nat.coprime_two_left]; exact hm
  obtain ⟨K,σ,P,u,v,k,hP,hu,_,hk,_,hl⟩ := cyclic_chord_data T H hT p hp hnorm S
    (Finset.filter_subset _ _) (fun _ hz => (Finset.mem_filter.mp hz).2) (by omega) (m+2) hcop
  have hw (z : K) (hz : z ∈ P) : ∃ w : K, w ≠ 0 ∧ w^T.card = 1 ∧ σ w = w^(m+2) ∧
      w+w⁻¹ = u*z+v/z+k := (hl z hz).2.2.2
  let w (z : K) := if h : z ∈ P then (hw z h).choose else 0
  have hw' (z : K) (hz : z ∈ P) : w z ≠ 0 ∧ w z ^ T.card = 1 ∧ σ (w z) = w z ^(m+2) ∧
      w z + (w z)⁻¹ = u*z+v/z+k := by simpa [w,hz] using (hw z hz).choose_spec
  let cls (z : K) : Bool × Bool := (decide (z^m=1), decide (w z ^ m = 1))
  let eps (b : Bool) : K := if b then 1 else -1
  have signs (b : Bool) : eps b = 1 ∨ eps b = -1 := by cases b <;> simp [eps]
  have power (z : K) (hz : z^T.card = 1) : z^m = eps (decide (z^m=1)) := by
    have hs : (z^m)^2 = 1 := by rwa [←pow_mul,Nat.mul_comm,←hM]
    rcases sq_eq_one_iff.mp hs with hh | hh
    · simp [hh,eps]
    · simp [hh,eps]
  obtain ⟨b,_,hb⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun z (_ : z ∈ P) => Finset.mem_univ (cls z))
    (show (Finset.univ : Finset (Bool × Bool)).card * 4 < P.card by simpa [←hP] using h)
  have hb4 := signed_doubling_bound (P.filter (fun z => cls z = b)) σ u v k hu hk
    (eps b.1) (eps b.2) (signs _) (signs _) (by
      intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      obtain ⟨hnz,hrz,hsz,_⟩ := hl z hz
      obtain ⟨hnw,hrw,hsw,hw⟩ := hw' z hz
      obtain rfl : cls z = b := he
      refine ⟨hnz,?_,w z,hnw,?_,hw⟩
      · rw [hsz,pow_add,power z hrz]
      · rw [hsw,pow_add,power (w z) hrw])
  omega


lemma transfer_rich_circle (B : Finset Circle) (D : Finset ℝ) (p : ℂ)
    (hsize : 4*D.card+2 < 3*B.card) (hp : p ≠ 0) (hnorm : ‖p‖ ≠ 1)
    (hB : ∀ z ∈ B, dist p (z : ℂ) ∈ D)
    (hpair : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → dist (x : ℂ) (y : ℂ) ∈ D) :
    ∃ (T V : Finset Circle) (H : Subgroup Circle) (q : ℂ),
      (H : Set Circle) = T ∧ V.card = B.card ∧ V ⊆ T ∧ distanceSet T ⊆ D ∧
      q ≠ 0 ∧ ‖q‖ ≠ 1 ∧ ∀ z ∈ V, dist q (z : ℂ) ∈ D := by
  have hsub : distanceSet B ⊆ D := by
    intro d hd
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hu,hv,hne⟩ := Finset.mem_offDiag.mp huv
    exact hpair u hu v hv hne
  let T := B / B
  have hdist : distinctDistances B ≤ D.card := Finset.card_le_card hsub
  obtain ⟨H,hH⟩ := large_circle_is_group_orbit B (by omega)
  have hmem (z : Circle) : z ∈ T ↔ z ∈ H := by change z ∈ (↑T : Set Circle) ↔ _; rw [←hH]; rfl
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  let V := B.image (· / b)
  have hV : V.card = B.card := Finset.card_image_of_injective _ (div_left_injective ..)
  have hVT : V ⊆ T := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_div.mpr ⟨x,hx,b,hb,rfl⟩
  refine ⟨T,V,H,p/(b:ℂ),hH,hV,hVT,?_,div_ne_zero hp (Circle.coe_ne_zero b),
    by simpa [norm_div,Circle.norm_coe] using hnorm, ?_⟩
  · intro d hd
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hxy
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_div.mp ((hmem _).mpr (H.div_mem ((hmem _).mp hx) ((hmem _).mp hy)))
    change dist (x : ℂ) (y : ℂ) ∈ D
    rw [chord_from_quotient he.symm]
    apply hpair u hu v hv
    rintro rfl
    exact hne (div_eq_one.mp (by simpa using he.symm))
  · intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    simpa [Circle.coe_div,rotate_dist] using hB u hu

lemma polygon_bound_of_descent (hbase : H3) (hdesc : H4) (n : ℕ) (hn : 7 ≤ n) :
    ∀ (T : Finset Circle) (H : Subgroup Circle), (H : Set Circle) = T → T.card = n →
      ∀ q : ℂ, q ≠ 0 → ‖q‖ ≠ 1 →
      2*(T.filter (fun z : Circle => dist q (z : ℂ) ∈ distanceSet T)).card ≤ T.card := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T H hHT hc q hq hnorm
    by_cases he : Even T.card
    · by_cases hs : T.card ≤ 31
      · exact hbase T H hHT (by omega) hs (Or.inl he) q hq hnorm
      · obtain ⟨m,hm⟩ := he
        have hM : T.card = 2*m := by omega
        by_cases heven : Even m
        · by_contra! hfail
          obtain ⟨V,G,p,hGV,hV,hp,hp1,hbad⟩ := hdesc m (by omega) heven T H hHT hM q hq hnorm hfail
          exact (not_le_of_gt hbad) (ih m (by omega) (by omega) V G hGV hV p hp hp1)
        · have h16 := signed_polygon_at_most_sixteen T H hHT m (Nat.not_even_iff_odd.mp heven) hM q hq hnorm
          omega
    · by_cases hs : T.card = 7
      · exact hbase T H hHT (by omega) (by omega) (Or.inr hs) q hq hnorm
      · have h4 := odd_polygon_at_most_four T H hHT (Nat.not_even_iff_odd.mp he) q hq hnorm
        omega

lemma forbid_rich_circle (h : H3) (hdesc : H4) (A B : Finset ℝ²) (c p : ℝ²) (r : ℝ)
    (hBA : B ⊆ A) (hcard : 2 < B.card) (hsize : 4 * distinctDistances A + 2 < 3 * B.card)
    (hfar : 3 < distinctDistances A) (hC : ∀ x ∈ B, dist x c = r)
    (hp : p ∈ A) (hpc : p ≠ c) (hpr : dist p c ≠ r) : False := by
  have hsub : ¬ B ⊆ {c} := by
    intro h; have hh : B.card ≤ 1 := (Finset.card_le_card h).trans_eq (Finset.card_singleton c); omega
  obtain ⟨x,hx,hxc⟩ := Finset.not_subset.mp hsub
  have hr : 0 < r := (dist_pos.mpr (show x ≠ c by simpa using hxc)).trans_eq (hC x hx)
  let E := Complex.orthonormalBasisOneI.repr.symm
  let F (x : ℝ²) := E (x-c) / (r : ℂ)
  have hdist (x y : ℝ²) : dist (F x) (F y) = dist x y / r := by
    rw [dist_eq_norm]; dsimp only [F]
    rw [←sub_div,norm_div,←map_sub,E.norm_map,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      show (x-c)-(y-c) = x-y by abel,dist_eq_norm]
  have hFc : F c = 0 := by simp [F]
  have hnorm (x : ℝ²) : ‖F x‖ = dist x c / r := by rw [←dist_zero_right,← hFc,hdist]
  have hinj : Function.Injective F := by
    intro x y h
    have hxy := hdist x y
    rw [h,dist_self] at hxy
    exact dist_eq_zero.mp ((div_eq_zero_iff.mp hxy.symm).resolve_right hr.ne')
  let G (x : B) : Circle := ⟨F x.1, mem_sphere_zero_iff_norm.mpr (by rw [hnorm,hC _ x.2,div_self hr.ne'])⟩
  let S := B.attach.image G
  let D := (distanceSet A).image (· / r)
  have hG : Function.Injective G := by
    intro u v h
    exact Subtype.ext (hinj (congrArg ((↑) : Circle → ℂ) h))
  have hSc : S.card = B.card := by dsimp [S]; rw [Finset.card_image_of_injective _ hG,Finset.card_attach]
  have hDc : D.card = distinctDistances A := by
    apply Finset.card_image_of_injective
    exact fun _ _ h => (div_left_inj' hr.ne').mp h
  obtain ⟨T,V,H,q,hHT,hV,hVT,hTD,hq,hnq,hVq⟩ := transfer_rich_circle S D (F p) (by omega)
    (by intro he; exact hpc (hinj (he.trans hFc.symm)))
    (by rw [hnorm]; exact fun he => hpr ((div_eq_one_iff_eq hr.ne').mp he)) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      change dist (F p) (F u.1) ∈ D
      rw [hdist]
      refine Finset.mem_image.mpr ⟨_, dist_mem hp (hBA u.2) ?_, rfl⟩
      intro he; exact hpr (he ▸ hC u.1 u.2)) (by
      intro z hz w hw hzw
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      change dist (F u.1) (F v.1) ∈ D
      rw [hdist]
      refine Finset.mem_image.mpr ⟨_, dist_mem (hBA u.2) (hBA v.2) ?_,rfl⟩
      intro h; exact hzw (congrArg G (Subtype.ext h)))
  have hm := Finset.card_le_card hVT
  have h7 : 7 ≤ T.card := by omega
  have hinc := polygon_bound_of_descent h hdesc T.card h7 T H hHT rfl q hq hnq
  let isChord (z : Circle) := dist q (z : ℂ) ∈ distanceSet T
  have hgood := Finset.card_le_card (Finset.filter_subset_filter isChord hVT)
  have hcnt := Finset.card_filter_add_card_filter_not (s := V) isChord
  let Fbad := V.filter (fun z => ¬ isChord z)
  have hmap (z : Circle) (hz : z ∈ Fbad) : dist q (z : ℂ) ∈ D \ distanceSet T := by
    obtain ⟨hz,hb⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_sdiff.mpr ⟨hVq z hz,hb⟩
  have hbad : Fbad.card ≤ 2 * (D \ distanceSet T).card := by
    by_contra! hneg
    obtain ⟨d, _, hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap (by
      simpa [Nat.mul_comm] using hneg : (D \ distanceSet T).card * 2 < Fbad.card)
    exact (not_lt_of_ge (circle_fibers Fbad q hq d)) hd
  have hdiff := Finset.card_sdiff_of_subset hTD
  have hDle := Finset.card_le_card hTD
  have hTcard := (Finset.card_le_card_div_self (s := T)).trans (circle_quotient_card T)
  have hdist : (distanceSet T).card = distinctDistances T := rfl
  change 2*(T.filter isChord).card ≤ T.card at hinc
  change (V.filter isChord).card + Fbad.card = V.card at hcnt
  omega

lemma distanceSet_mono {A B : Finset ℝ²} (h : B ⊆ A) : distanceSet B ⊆ distanceSet A := by
  intro d hd
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hxy
  exact dist_mem (h hx) (h hy) hne

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos1082.erdos_1082.parts.i := by
  intro hsmall hsparse hregular hdesc Astart hstart
  suffices hall : ∀ n : ℕ, ∀ A : Finset ℝ², A.card = n → NonTrilinear (A : Set ℝ²) →
      A.card / 2 ≤ distinctDistances A from hall _ _ rfl hstart
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hAn hA
    by_contra! hbad
    have hmin {B : Finset ℝ²} (hBA : B ⊆ A) (hBn : B.card < n) : B.card / 2 ≤ distinctDistances B :=
      ih B.card hBn B rfl (Set.Triplewise.mono (Finset.coe_subset.mpr hBA) hA)
    have heven : A.card = 2 * distinctDistances A + 2 := by
      by_contra he
      have hlt : 2 * distinctDistances A + 2 < A.card := by omega
      obtain ⟨B,hBA,hBc⟩ := Finset.exists_subset_card_eq hlt.le
      have hbd := hmin hBA (by omega)
      have hm : distinctDistances B ≤ distinctDistances A := Finset.card_le_card (distanceSet_mono hBA)
      omega
    have heavy : ∃ d ∈ distanceSet A, A.card + 2 ≤ distanceMultiplicity A d := by
      by_contra! h
      exact (not_le_of_gt hbad) (small_distance_multiplicities A (fun d hd => by have := h d hd; omega))
    by_cases hlow : distinctDistances A ≤ 3
    · exact (not_le_of_gt hbad) (hsmall A hA hlow)
    by_cases hthin : ∀ (c : ℝ²) (r : ℝ), 3 * (A.filter (fun z => dist z c = r)).card ≤ 4 * distinctDistances A + 2
    · obtain ⟨x,hx,y,hy,d,hd,hmissing⟩ := hsparse A hA heven heavy hthin
      let B := (A.erase x).erase y
      have hBA : B ⊆ A := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hx' := Finset.card_erase_add_one hx
      have hy' : B.card + 1 = (A.erase x).card := Finset.card_erase_add_one hy
      have hbd := hmin hBA (by omega)
      have hsub := distanceSet_mono hBA
      have hne : distanceSet B ≠ distanceSet A := by intro he; exact hmissing (he ▸ hd)
      have hlt : distinctDistances B < distinctDistances A := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
      omega
    push Not at hthin
    obtain ⟨c,r,hlarge⟩ := hthin
    let B := A.filter (fun z => dist z c = r)
    have hBA : B ⊆ A := Finset.filter_subset _ _
    have hC (x) (hx : x ∈ B) := (Finset.mem_filter.mp hx).2
    change 4 * distinctDistances A + 2 < 3 * B.card at hlarge
    by_cases hex : ∃ p ∈ A, p ≠ c ∧ dist p c ≠ r
    · obtain ⟨p,hp,hpc,hpr⟩ := hex
      exact (forbid_rich_circle hregular hdesc A B c p r hBA (by omega) hlarge (by omega) hC hp hpc hpr).elim
    · apply (not_le_of_gt hbad)
      apply all_but_one_concyclic A c r hA c
      intro x hx
      by_contra hr
      exact hex ⟨x,Finset.mem_of_mem_erase hx,Finset.ne_of_mem_erase hx,hr⟩

end OMA.R_Erdos1082_erdos_1082_parts_i_R1
