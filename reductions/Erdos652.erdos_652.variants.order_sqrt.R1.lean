import FormalConjectures.ErdosProblems.«652»

/-! # The order of the kth pinned distance count

Two finite geometric inputs suffice: an incidence bound at arbitrarily large sizes for
each fixed number of centers, and a rectangular circle-grid construction. The incidence
bound counts the zero distance; the definition of the admissible constants excludes it.
Credit: @JaviSoto. -/

namespace OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1

open Filter Finset Erdos652
open scoped EuclideanGeometry Classical

/-- A restricted version of Mathialagan's pinned incidence bound: the centers are in the
point set, and only arbitrarily large sizes are required for each fixed k. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∃ᶠ n : ℕ in atTop,
    ∀ P Q : Finset ℝ², P ⊆ Q → P.card = k → Q.card = n →
      ∃ p ∈ P, c * Real.sqrt ((k : ℝ) * n) ≤ ((Q.image fun q => dist q p).card : ℝ)

/-- A rectangular circle grid of height k*m supplies enough points while keeping the
number of radii at each of its k centers linear in k*m. -/
def H2 : Prop :=
  ∀ k n m : ℕ, k ≤ n → n ≤ m * (k * m) →
    ∃ pts : Finset ℝ², pts.card = n ∧ k ≤
      (pts.filter fun p => distinctDistancesFrom pts p ≤ k + 3*k*m).card

open Filter

private lemma all_distances_le_twice (Q : Finset ℝ²) (hQ : 2 ≤ Q.card) {p : ℝ²} (hp : p ∈ Q) :
    (Q.image fun q => dist q p).card ≤ 2 * distinctDistancesFrom Q p := by
  classical
  let D := (Q.erase p).image fun q => dist q p
  have hd : distinctDistancesFrom Q p = D.card := by
    unfold distinctDistancesFrom
    apply congrArg Finset.card
    ext d
    simp only [D, Finset.mem_image, Finset.mem_erase]
  have hpos : 0 < D.card := Finset.card_pos.mpr
    ((Finset.erase_nonempty hp).mpr (Finset.one_lt_card_iff_nontrivial.mp hQ) |>.image _)
  have he : Q.image (fun q => dist q p) = insert 0 D := by
    calc
      _ = (insert p (Q.erase p)).image (fun q => dist q p) := by rw [insert_erase hp]
      _ = _ := by rw [image_insert, dist_self]
  rw [hd, he]
  have := Finset.card_insert_le 0 D
  omega

private lemma admissible_lower {c : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h : ∃ᶠ n : ℕ in atTop, ∀ P Q : Finset ℝ², P ⊆ Q → P.card = k → Q.card = n →
      ∃ p ∈ P, c * Real.sqrt ((k : ℝ) * n) ≤ ((Q.image fun q => dist q p).card : ℝ))
    {a : ℝ} (ha : AdmissibleConstant k a) : c / 2 * Real.sqrt k ≤ a := by
  classical
  obtain ⟨n, hinc, ⟨Q, hcard, hgood⟩, hn⟩ := ((h.and_eventually
    (ha.2.and (eventually_ge_atTop 2))).exists)
  obtain ⟨P, hsub, hP⟩ := Finset.exists_subset_card_eq hgood
  have hPQ : P ⊆ Q := hsub.trans (Finset.filter_subset _ _)
  obtain ⟨p, hp, hlow⟩ := hinc P Q hPQ hP hcard
  have hpQ := hPQ hp
  have hu := (Finset.mem_filter.mp (hsub hp)).2
  have hd : ((Q.image fun q => dist q p).card : ℝ) ≤
      2 * (distinctDistancesFrom Q p : ℝ) := by
    exact_mod_cast all_distances_le_twice Q (by omega) hpQ
  rw [Real.sqrt_mul (by positivity : 0 ≤ (k : ℝ))] at hlow
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  by_contra! hbad
  have hcontra := mul_lt_mul_of_pos_right hbad hs
  linarith only [hlow.trans hd, hu, hcontra]

/-- Choose the grid width one above the integer square root of n/k. -/
private lemma admissible_of_rectangle (rect : H2)
    (k : ℕ) (hk : 2 ≤ k) : Erdos652.AdmissibleConstant k (8 * Real.sqrt k) := by
  classical
  have hkpos : 0 < k := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hkpos
  refine ⟨by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop k] with n hkn
  let d := (n / k).sqrt
  let m := d + 1
  have hdlt : (n / k).sqrt < m := Nat.lt_succ_self _
  have hlarge : n < m * m * k := (Nat.div_lt_iff_lt_mul hkpos).mp (Nat.sqrt_lt.mp hdlt)
  have hsize : n ≤ m * (k * m) := by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlarge.le
  obtain ⟨pts, hpts, hgood⟩ := rect k n m hkn hsize
  refine ⟨pts, hpts, hgood.trans (card_le_card ?_)⟩
  intro p hp
  obtain ⟨hpp, hcount⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨hpp, ?_⟩
  have hdsq : d*d*k ≤ n := (Nat.mul_le_mul_right k (Nat.sqrt_le (n/k))).trans (Nat.div_mul_le_self n k)
  have hdsqr : (d : ℝ)*(d : ℝ)*(k : ℝ) ≤ n := by exact_mod_cast hdsq
  have hdroot : (d : ℝ) * Real.sqrt k ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hkr.le, sq]
    exact hdsqr
  have hdprod : (k : ℝ)*d ≤ Real.sqrt k * Real.sqrt n := by
    calc (k : ℝ)*d = (Real.sqrt k * Real.sqrt k) * d :=
           congrArg (fun x : ℝ => x * d) (Real.mul_self_sqrt hkr.le).symm
         _ = Real.sqrt k * ((d : ℝ) * Real.sqrt k) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hdroot (Real.sqrt_nonneg _)
  have hknr : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hkprod : (k : ℝ) ≤ Real.sqrt k * Real.sqrt n := by
    calc (k : ℝ) = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hkr.le).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hknr) (Real.sqrt_nonneg _)
  have hreal : (distinctDistancesFrom pts p : ℝ) ≤ k + 3*(k:ℝ)*((d:ℝ)+1) := by
    exact_mod_cast hcount
  linarith

theorem main : H1 → H2 → type_of% @Erdos652.erdos_652.variants.order_sqrt := by
  rintro ⟨c, hc, hinc⟩ rect
  refine ⟨c / 2, 8, by positivity, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hu := admissible_of_rectangle rect k hk
  change c / 2 * Real.sqrt k ≤ sInf {a : ℝ | AdmissibleConstant k a} ∧
    sInf {a : ℝ | AdmissibleConstant k a} ≤ 8 * Real.sqrt k
  constructor
  · exact le_csInf ⟨_, hu⟩ fun a ha => admissible_lower hk (hinc k hk) ha
  · exact csInf_le ⟨0, fun a ha => ha.1.le⟩ hu

end OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1
