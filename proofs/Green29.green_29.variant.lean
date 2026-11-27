import FormalConjectures.GreensOpenProblems.«29»

/-! A density increment proof of the approximate-group lemma. For a dense
subset B of A, many translates overlap B in a dense subset. Either their
actions almost preserve BA, or one overlap gives a smaller product set.
Iterating the latter alternative costs a fixed amount of product-set size. -/

open Finset
open scoped Pointwise
namespace Green29Proof

variable {G : Type*} [Group G] [DecidableEq G]

omit [DecidableEq G] in
private lemma inv_mem_A {A : Finset G} {K : ℝ} (hA : IsApproximateSubgroup K (A : Set G))
    {x : G} (hx : x ∈ A) : x⁻¹ ∈ A := by
  change x⁻¹ ∈ (A : Set G)
  rw [← hA.inv_eq_self]
  simpa using hx

private lemma overlap_sum {A B : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) (hB : B ⊆ A) :
    ∑ g ∈ A*A, (B ∩ g • B).card = B.card ^ 2 := by
  simp_rw [card_inter_smul, ← card_mul_inv_eq_convolution_inv]
  rw [← card_eq_sum_card_fiberwise, card_product, sq]
  intro p hp
  obtain ⟨hx,hy⟩ := mem_product.mp hp
  exact mul_mem_mul (hB hx) (inv_mem_A hA (hB hy))

private lemma popular {A B : Finset G} {K t : ℝ} (hK : 1 ≤ K)
    (ht : 0 < t) (hA : IsApproximateSubgroup K (A : Set G)) (hB : B ⊆ A)
    (hsize : t * A.card ≤ B.card) :
    ∃ S : Finset G, t^2/2 * A.card ≤ S.card ∧
      ∀ g ∈ S, t^2/(2*K) * A.card ≤ (B ∩ g • B).card := by
  classical
  let T := A*A
  let q := t^2/(2*K) * A.card
  let f (g : G) : ℝ := (B ∩ g • B).card
  let S := T.filter fun g => q ≤ f g
  refine ⟨S,?_,fun g hg => (mem_filter.mp hg).2⟩
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr (show A.Nonempty from ⟨1,hA.one_mem⟩)
  have hT : (T.card : ℝ) ≤ K * A.card := hA.card_mul_self_le
  have hsum : ∑ g ∈ T, f g = (B.card : ℝ)^2 := by dsimp [T,f]; exact_mod_cast overlap_sum hA hB
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsplit : (B.card : ℝ)^2 ≤ S.card * (A.card : ℝ) + T.card * q := by
    rw [← hsum, ← sum_filter_add_sum_filter_not T (fun g => q ≤ f g)]
    apply add_le_add
    · calc
        _ ≤ ∑ _g ∈ S, (A.card : ℝ) := sum_le_sum fun g _ =>
          by dsimp [f]; exact_mod_cast card_le_card ((inter_subset_left (s₂ := g • B)).trans hB)
        _ = _ := by simp
    · calc
        _ ≤ ∑ _g ∈ T.filter (fun g => ¬q ≤ f g), q := sum_le_sum fun g hg =>
          (lt_of_not_ge (mem_filter.mp hg).2).le
        _ = ((T.filter (fun g => ¬q ≤ f g)).card : ℝ) * q := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le T _) hq
  have hq' : K * (A.card : ℝ) * q = t^2/2 * (A.card : ℝ)^2 := by
    dsimp [q]; field_simp
  have hb2 := mul_self_le_mul_self (by positivity : 0 ≤ t * (A.card : ℝ)) hsize
  have hright := mul_le_mul_of_nonneg_right hT hq
  rw [hq'] at hright
  apply le_of_mul_le_mul_right (a := (A.card : ℝ)) _ hpos
  nlinarith

private def loss (D : Finset G) (w : G) : ℕ := (D \ w • D).card

private lemma loss_mul (D : Finset G) (g h : G) : loss D (g*h) ≤ loss D g + loss D h := by
  have sub : D \ (g*h) • D ⊆ (D \ g • D) ∪ g • (D \ h • D) := by
    rw [mul_smul,smul_finset_sdiff]
    intro x hx
    simp only [mem_sdiff,mem_union] at *
    tauto
  exact (card_le_card sub).trans ((card_union_le ..).trans (by simp [loss]))

private lemma loss_pow {D S : Finset G} {r : ℝ}
    (h : ∀ g ∈ S, (loss D g : ℝ) ≤ r) :
    ∀ (k : ℕ) (w : G), w ∈ S^k → (loss D w : ℝ) ≤ k*r := by
  intro k
  induction k with
  | zero => intro w hw; simp only [pow_zero,mem_one] at hw; subst w; simp [loss]
  | succ k ih =>
    intro w hw
    rw [pow_succ] at hw
    obtain ⟨g,hg,z,hz,rfl⟩ := mem_mul.mp hw
    have hh : (loss D (g*z):ℝ) ≤ loss D g + (loss D z : ℝ) := by exact_mod_cast loss_mul D g z
    push_cast
    linarith [ih g hg,h z hz]

private lemma finish {A B S : Finset G} {K : ℝ} (hA : IsApproximateSubgroup K (A : Set G))
    (hB : B ⊆ A) (hne : B.Nonempty)
    (hs : ∀ g ∈ S, ((B*A).card : ℝ) - A.card/16 ≤ ((B ∩ g • B)*A).card) :
    S ^ 8 ⊆ A ^ 4 := by
  let D := B*A
  have hD : A.card ≤ D.card := by
    obtain ⟨b,hb⟩ := hne
    have sub : b • A ⊆ D := by
      intro z hz
      obtain ⟨a,ha,rfl⟩ := mem_smul_finset.mp hz
      exact mul_mem_mul hb ha
    simpa using card_le_card sub
  have hloss (g : G) (hg : g ∈ S) : (loss D g : ℝ) ≤ A.card/16 := by
    have sub : (B ∩ g • B)*A ⊆ D ∩ g • D := by
      apply subset_inter
      · exact mul_subset_mul_right inter_subset_left
      · change _ ⊆ g • (B*A)
        rw [← smul_mul_assoc]
        exact mul_subset_mul_right inter_subset_right
    have eq := card_sdiff_add_card_inter D (g • D)
    change loss D g + _ = _ at eq
    have h1 : (((B ∩ g • B)*A).card : ℝ) ≤ (D ∩ g • D).card := by exact_mod_cast card_le_card sub
    have h2 : (loss D g : ℝ) + (D ∩ g • D).card = D.card := by exact_mod_cast eq
    have hs' : (D.card : ℝ) - A.card/16 ≤ ((B ∩ g • B)*A).card := hs g hg
    linarith
  intro w hw
  have hh := loss_pow (D := D) (S := S) hloss 8 w hw
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr (show A.Nonempty from ⟨1,hA.one_mem⟩)
  have hlt : loss D w < D.card := by
    have hD' : (A.card : ℝ) ≤ D.card := by exact_mod_cast hD
    exact_mod_cast (show (loss D w : ℝ) < D.card by norm_num at hh; linarith)
  have hi : (D ∩ w • D).Nonempty := by
    apply card_pos.mp
    have h := card_sdiff_add_card_inter D (w • D)
    change loss D w + _ = _ at h
    omega
  obtain ⟨z,hz⟩ := hi
  obtain ⟨x,hx,hxz⟩ := mem_smul_finset.mp (mem_inter.mp hz).2
  obtain ⟨a,ha,b,hb,hab⟩ := mem_mul.mp (mem_inter.mp hz).1
  obtain ⟨c,hc,d,hd,hcd⟩ := mem_mul.mp hx
  have eq : w = (a*b)*(d⁻¹*c⁻¹) := by
    change w*x = z at hxz
    rw [← mul_inv_rev, hcd, hab, ← hxz]; simp
  rw [eq,show 4 = 2+2 by decide,pow_add,sq]
  exact mul_mem_mul (mul_mem_mul (hB ha) hb) (mul_mem_mul (inv_mem_A hA hd) (inv_mem_A hA (hB hc)))


/-- At budget m, the product BA has size at most m |A| / 16. Failing the
almost-period condition at a popular translate permits reducing this budget
by one, with the new relative density still bounded solely in terms of K,t. -/
private lemma descent (K : ℝ) (hK : 1 ≤ K) (m : ℕ) :
    ∀ (t : ℝ), 0 < t → ∃ c : ℝ, 0 < c ∧
      ∀ {G : Type*} [Group G] [DecidableEq G] (A B : Finset G),
        IsApproximateSubgroup K (A : Set G) → B ⊆ A →
        t * A.card ≤ B.card → ((B*A).card : ℝ) ≤ m*A.card/16 →
        ∃ S : Finset G, c * A.card ≤ S.card ∧ S^8 ⊆ A^4 := by
  induction m with
  | zero =>
    intro t ht
    refine ⟨1,one_pos,?_⟩
    intro G _ _ A B hA hB hsize hbudget
    have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr (show A.Nonempty from ⟨1,hA.one_mem⟩)
    have hb : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos ht hpos).trans_le hsize)
    have hd : 0 < ((B*A).card : ℝ) := by
      exact_mod_cast card_pos.mpr (hb.mul (show A.Nonempty from ⟨1,hA.one_mem⟩))
    simp only [Nat.cast_zero,zero_mul,zero_div] at hbudget
    linarith
  | succ m ih =>
    intro t ht
    have ht' : 0 < t^2/(2*K) := by positivity
    obtain ⟨c,hc,ih⟩ := ih _ ht'
    refine ⟨min (t^2/2) c, lt_min (by positivity) hc, ?_⟩
    intro G _ _ A B hA hB hsize hbudget
    obtain ⟨S,hS,hpop⟩ := popular hK ht hA hB hsize
    have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr (show A.Nonempty from ⟨1,hA.one_mem⟩)
    have hb : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos ht hpos).trans_le hsize)
    by_cases h : ∀ g ∈ S, ((B*A).card : ℝ) - A.card/16 ≤ ((B ∩ g • B)*A).card
    · exact ⟨S,(mul_le_mul_of_nonneg_right (min_le_left ..) hpos.le).trans hS,finish hA hB hb h⟩
    push Not at h
    obtain ⟨g,hg,hsmall⟩ := h
    have hbudget' : (((B ∩ g • B)*A).card : ℝ) ≤ m*A.card/16 := by
      push_cast at hbudget; linarith
    obtain ⟨S',hs',hp'⟩ := ih A (B ∩ g • B) hA (inter_subset_left.trans hB) (hpop g hg) hbudget'
    exact ⟨S',(mul_le_mul_of_nonneg_right (min_le_right ..) hpos.le).trans hs',hp'⟩

end Green29Proof

open Green29Proof in
theorem OMA.solution : type_of% @Green29.green_29.variant := by
  intro K hK
  obtain ⟨m,hm⟩ := exists_nat_ge (16*K)
  obtain ⟨c,hc,h⟩ := descent K hK m 1 one_pos
  refine ⟨c,hc,?_⟩
  intro G _ _ A hA
  apply h A A hA (Finset.Subset.rfl) (by simp)
  have := hA.card_mul_self_le
  nlinarith [mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg A.card : (0:ℝ) ≤ A.card)]
