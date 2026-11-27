import FormalConjectures.ErdosProblems.«604»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # A reduction of the average pinned-distance conjecture

For a collinear pin set, choosing its line as the horizontal axis sends each
target (u,v) to (u,u²+v²). This identifies at most two targets. The squared
distances from a pin on the axis become level sets of one linear functional.
The Szemerédi–Trotter theorem therefore supplies the estimate in H1.

For H2, draw the positive-radius circles about the proposed pins that hit A.
Two circles meet in at most two points. Two distinct targets lie on at most
two circles in this family by the bisector condition. Theorem 8 of Székely,
Crossing Numbers and Hard Erdős Problems in Discrete Geometry (1997),
DOI 10.1017/S0963548397002976, supplies the incidence bound in this case.
For either estimate, two distinct pins distinguish targets up to reflection,
which also covers bounded pin-set sizes.

H3 is the remaining open geometric step. Its small-subset conditions exclude
rich lines and rich subsets in general position, including rich circles. The
last condition counts ordered isosceles triangles at each apex. The proof below
handles a pin with few such triangles using Cauchy–Schwarz, and passes from the
single-pin conclusion to the average by applying it to subsets.
-/

-- Credit: @NicholasWierenga
open Filter
open scoped EuclideanGeometry Finset

namespace OMA.R_Erdos604_erdos_604_variants_average_R2

lemma distances_mono {B A : Finset ℝ²} (h : B ⊆ A) (x : ℝ²) :
    distinctDistancesFrom B x ≤ distinctDistancesFrom A x := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let : DecidableEq ℝ := Classical.decEq _
  exact Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset_erase x h))

/-- If every subset of at least half the points has a pin reaching a fixed threshold,
at least half the original points reach that threshold. -/
lemma half_pins (A : Finset ℝ²) (t : ℝ)
    (hp : ∀ B ⊆ A, #A ≤ 2 * #B → ∃ x ∈ B, t ≤ (distinctDistancesFrom B x : ℝ)) :
    #A ≤ 2 * #(A.filter fun x => t ≤ (distinctDistancesFrom A x : ℝ)) := by
  classical
  let G := A.filter fun x => t ≤ (distinctDistancesFrom A x : ℝ)
  let B := A \ G
  have hB : B ⊆ A := Finset.sdiff_subset
  have hcard : #B = #A - #G := Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
  change #A ≤ 2 * #G
  by_contra! hf
  obtain ⟨x, hx, ht⟩ := hp B hB (by omega)
  have hg : x ∈ G := Finset.mem_filter.mpr
    ⟨hB hx, ht.trans (by exact_mod_cast distances_mono hB x)⟩
  exact (Finset.mem_sdiff.mp hx).2 hg

/-- The uniform sharp bound for a single pin implies the average bound. -/
theorem uniform_pin_to_average
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n →
      ∃ x ∈ A, c * (n : ℝ) / Real.sqrt (Real.log n) ≤ (distinctDistancesFrom A x : ℝ)) :
    type_of% @Erdos604.erdos_604.variants.average := by
  classical
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨c / 4, by positivity, eventually_atTop.2 ⟨2 * (N + 2), ?_⟩⟩
  intro n hn A hA
  let t : ℝ := c * ((n : ℝ) / 2) / Real.sqrt (Real.log n)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hmany := half_pins A t (by
    intro B hBA hsize
    have hBN : N ≤ #B := by omega
    have hBpos : (1 : ℝ) < #B := by exact_mod_cast (show 1 < #B by omega)
    have hsB : 0 < Real.sqrt (Real.log (#B : ℝ)) := Real.sqrt_pos.2 (Real.log_pos hBpos)
    have hsubset : (#B : ℝ) ≤ n := by
      exact_mod_cast (hA ▸ Finset.card_le_card hBA)
    have hs : Real.sqrt (Real.log (#B : ℝ)) ≤ Real.sqrt (Real.log n) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hsubset)
    have hhalf : (n : ℝ) ≤ 2 * (#B : ℝ) := by exact_mod_cast (hA ▸ hsize : n ≤ 2 * #B)
    obtain ⟨x, hx, hdx⟩ := hN #B hBN B rfl
    refine ⟨x, hx, ?_⟩
    calc
      t ≤ c * (#B : ℝ) / Real.sqrt (Real.log n) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hc.le) (by positivity)
      _ ≤ c * (#B : ℝ) / Real.sqrt (Real.log (#B : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hsB hs
      _ ≤ _ := hdx)
  let G := A.filter fun x => t ≤ (distinctDistancesFrom A x : ℝ)
  have hG : (n : ℝ) ≤ 2 * (#G : ℝ) := by exact_mod_cast (hA ▸ hmany : n ≤ 2 * #G)
  have hsum : (#G : ℝ) * t ≤ ∑ x ∈ A, (distinctDistancesFrom A x : ℝ) := calc
    _ = ∑ _x ∈ G, t := by simp
    _ ≤ ∑ x ∈ G, (distinctDistancesFrom A x : ℝ) :=
      Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
  push_cast
  calc
    c / 4 * (n : ℝ) ^ 2 / Real.sqrt (Real.log n) = ((n : ℝ) / 2) * t := by dsimp [t]; ring
    _ ≤ (#G : ℝ) * t := mul_le_mul_of_nonneg_right (by linarith) ht
    _ ≤ _ := hsum

/-- If a subset has at least `|A| / log |A|` points, a pinned bound at the
geometric mean of the two sizes gives a pin at the required scale. -/
theorem rich_subset_pin (c : ℝ) (hc : 0 < c)
    (A B : Finset ℝ²) (hA : 2 ≤ A.card) (hBA : B ⊆ A)
    (hlarge : (A.card : ℝ) ≤ (B.card : ℝ) * Real.log (A.card : ℝ))
    (hproj : 2 ≤ B.card → ∃ x ∈ B, c * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) ≤
      (distinctDistancesFrom A x : ℝ)) :
    ∃ x ∈ A, c * (A.card : ℝ) / Real.sqrt (Real.log (A.card : ℝ)) ≤
      (distinctDistancesFrom A x : ℝ) := by
  have hn : 2 ≤ (A.card : ℝ) := by exact_mod_cast hA
  have hn1 : 1 < (A.card : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hn0 : 0 ≤ (A.card : ℝ) := by positivity
  have hl : 0 < Real.log (A.card : ℝ) := Real.log_pos hn1
  have hB : 2 ≤ B.card := by
    by_contra! hlt
    have hb1 : (B.card : ℝ) ≤ 1 := by
      exact_mod_cast (show B.card ≤ 1 by omega)
    have hb_log : (B.card : ℝ) * Real.log (A.card : ℝ) ≤ Real.log (A.card : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 hl.le
    have hlog_lt := Real.log_lt_sub_one_of_pos (lt_trans zero_lt_one hn1) hn1.ne'
    linarith
  have hratio : (A.card : ℝ) / Real.log (A.card : ℝ) ≤ (B.card : ℝ) :=
    (div_le_iff₀ hl).2 hlarge
  have hsq : ((A.card : ℝ) * (A.card : ℝ)) / Real.log (A.card : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hratio hn0
  have hroot := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_div (mul_nonneg hn0 hn0), Real.sqrt_mul_self hn0] at hroot
  obtain ⟨x, hx, hxd⟩ := hproj hB
  refine ⟨x, hBA hx, ?_⟩
  rw [mul_div_assoc]
  exact (mul_le_mul_of_nonneg_left hroot hc.le).trans hxd

section Collisions

open scoped Classical

variable {X Y : Type*}

private theorem card_filter_eq_sum_ones (s : Finset X) (p : X → Prop)
    [DecidablePred p] : (s.filter p).card = ∑ x ∈ s, if p x then (1 : ℕ) else 0 := by
  simpa only [Nat.cast_id] using Finset.natCast_card_filter (R := ℕ) p s

private theorem square_card_le_card_image_mul_equal_pairs (B : Finset X) (f : X → Y) :
    B.card ^ 2 ≤ (B.image f).card *
      ((B ×ˢ B).filter fun p => f p.1 = f p.2).card := by
  classical
  let fiberSize := fun r : Y => (B.filter fun x => f x = r).card
  have hfirst : B.card = ∑ r ∈ B.image f, fiberSize r :=
    Finset.card_eq_sum_card_image f B
  have hmaps : (B : Set X).MapsTo f (B.image f) :=
    fun _ hx => Finset.mem_image_of_mem f (Finset.mem_coe.mp hx)
  have hsecond : (∑ r ∈ B.image f, fiberSize r ^ 2) =
      ((B ×ˢ B).filter fun p => f p.1 = f p.2).card := by
    calc
      (∑ r ∈ B.image f, fiberSize r ^ 2) =
          ∑ r ∈ B.image f, ∑ u ∈ B.filter (fun u => f u = r), fiberSize (f u) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [pow_two]
        exact (Finset.sum_const_nat fun u hu =>
          congrArg (fiberSize) (Finset.mem_filter.mp hu).2).symm
      _ = ∑ u ∈ B, fiberSize (f u) := Finset.sum_fiberwise_of_maps_to hmaps _
      _ = ((B ×ˢ B).filter fun p => f p.1 = f p.2).card := by
        simp only [fiberSize, card_filter_eq_sum_ones]
        simpa only [eq_comm] using
          (Finset.sum_product B B (fun p => if f p.1 = f p.2 then (1 : ℕ) else 0)).symm
  calc
    B.card ^ 2 = (∑ r ∈ B.image f, fiberSize r) ^ 2 := congrArg (· ^ 2) hfirst
    _ ≤ (B.image f).card * (∑ r ∈ B.image f, fiberSize r ^ 2) :=
      sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [hsecond]

private theorem card_equal_pairs (B : Finset X) (f : X → Y) :
    ((B ×ˢ B).filter fun p => f p.1 = f p.2).card =
      B.card + (B.offDiag.filter fun p => f p.1 = f p.2).card := by
  classical
  have heq : (B ×ˢ B).filter (fun p => f p.1 = f p.2) =
      B.diag ∪ B.offDiag.filter (fun p => f p.1 = f p.2) := by
    ext ⟨u, v⟩
    by_cases h : u = v
    · subst v
      simp
    · simp [h]
  rw [heq, Finset.card_union_of_disjoint, Finset.diag_card]
  refine Finset.disjoint_left.mpr fun p hdiag hoff => ?_
  exact (Finset.mem_offDiag.mp (Finset.mem_filter.mp hoff).1).2.2
    (Finset.mem_diag.mp hdiag).2

variable [MetricSpace X]


private theorem pin_collision_inequality (A : Finset X) (x : X) (hx : x ∈ A) :
    (A.card - 1) ^ 2 ≤ distinctDistancesFrom A x * (A.card - 1 + (A.offDiag.filter fun p => dist x p.1 = dist x p.2).card) := by
  classical
  let B := A.erase x
  let f := fun y : X => dist y x
  have hB : B.card = A.card - 1 := Finset.card_erase_of_mem hx
  have hD : (B.image f).card = distinctDistancesFrom A x := rfl
  have hsub : (B.offDiag.filter fun p => f p.1 = f p.2) ⊆
      A.offDiag.filter (fun p => dist x p.1 = dist x p.2) := by
    intro p hp
    obtain ⟨hpair, heq⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.offDiag_mono (Finset.erase_subset x A) hpair, ?_⟩
    simpa only [f, dist_comm x] using heq
  have henergy := square_card_le_card_image_mul_equal_pairs B f
  rw [card_equal_pairs, hB, hD] at henergy
  exact henergy.trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_left (Finset.card_le_card hsub) _))


/-- A pin with few equal-distance pairs sees at least the square-root logarithmic bound. -/
theorem pin_of_low_collisions (A : Finset X) (x : X)
    (hN : 1 ≤ Real.sqrt (Real.log (#A : ℝ))) (hn : 2 ≤ #A) (hx : x ∈ A)
    (hcoll : ((A.offDiag.filter fun p => dist x p.1 = dist x p.2).card : ℝ) ≤
      ((#A : ℝ) - 1) * Real.sqrt (Real.log (#A : ℝ))) :
    (1 / 4 : ℝ) * (#A : ℝ) / Real.sqrt (Real.log (#A : ℝ)) ≤
      (distinctDistancesFrom A x : ℝ) := by
  classical
  let n : ℝ := #A
  let s : ℝ := Real.sqrt (Real.log n)
  let d : ℝ := distinctDistancesFrom A x
  let k : ℝ := (A.offDiag.filter fun p => dist x p.1 = dist x p.2).card
  change 1 ≤ s at hN
  change k ≤ (n - 1) * s at hcoll
  change (1 / 4 : ℝ) * n / s ≤ d
  have hcard : 2 ≤ n := by dsimp [n]; exact_mod_cast hn
  have hprev : 0 < n - 1 := by linarith
  have hs : 0 < s := zero_lt_one.trans_le hN
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hNat := pin_collision_inequality A x hx
  have henergy := (Nat.cast_le (α := ℝ)).2 hNat
  push_cast [Nat.cast_sub (show 1 ≤ #A by omega)] at henergy
  change (n - 1) ^ 2 ≤ d * (n - 1 + k) at henergy
  have hsum : n - 1 + k ≤ (n - 1) * (2 * s) := by
    have hscale := mul_le_mul_of_nonneg_left hN hprev.le
    nlinarith
  have hmul := henergy.trans (mul_le_mul_of_nonneg_left hsum hd)
  have hcancel : n - 1 ≤ d * (2 * s) := by
    apply le_of_mul_le_mul_left _ hprev
    calc
      (n - 1) * (n - 1) = (n - 1) ^ 2 := by ring
      _ ≤ d * ((n - 1) * (2 * s)) := hmul
      _ = _ := by ring
  apply (div_le_iff₀ hs).2
  nlinarith

end Collisions

open scoped Classical

/-- The finite projection estimate for collinear pins. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A B : Finset ℝ²), B ⊆ A → 2 ≤ #B →
    Collinear ℝ (B : Set ℝ²) →
    ∃ x ∈ B, c * Real.sqrt ((#A : ℝ) * (#B : ℝ)) ≤ (distinctDistancesFrom A x : ℝ)

/-- The finite incidence estimate when each pair of targets has at most two
equidistant pins in B. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A B : Finset ℝ²), B ⊆ A → 2 ≤ #B →
    (∀ y ∈ A, ∀ z ∈ A, y ≠ z → #(B.filter fun x => dist x y = dist x z) ≤ 2) →
    ∃ x ∈ B, c * Real.sqrt ((#A : ℝ) * (#B : ℝ)) ≤ (distinctDistancesFrom A x : ℝ)

/-- A single pin for configurations with small line and bisector-sparse
subsets and many isosceles triangles at every apex. -/
def H3 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n →
    (∀ B ⊆ A, Collinear ℝ (B : Set ℝ²) → (#B : ℝ) * Real.log n < n) →
    (∀ B ⊆ A, (∀ y ∈ A, ∀ z ∈ A, y ≠ z →
      #(B.filter fun x => dist x y = dist x z) ≤ 2) → (#B : ℝ) * Real.log n < n) →
    (∀ x ∈ A, ((n : ℝ) - 1) * Real.sqrt (Real.log n) <
      (#(A.offDiag.filter fun p => dist x p.1 = dist x p.2) : ℝ)) →
    ∃ x ∈ A, c * (n : ℝ) / Real.sqrt (Real.log n) ≤ (distinctDistancesFrom A x : ℝ)

/-- The three steps give a sharp pin on every sufficiently large set. -/
lemma find_pin (h₁ : H1) (h₂ : H2) (h₃ : H3) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n →
      ∃ x ∈ A, c * (n : ℝ) / Real.sqrt (Real.log n) ≤ (distinctDistancesFrom A x : ℝ) := by
  classical
  obtain ⟨a, ha, hline⟩ := h₁
  obtain ⟨b, hb, hbis⟩ := h₂
  obtain ⟨c, hc, hcore⟩ := h₃
  let k := min (min a b) (min c (1 / 4 : ℝ))
  refine ⟨k, lt_min (lt_min ha hb) (lt_min hc (by norm_num)), ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hcore, hlog, eventually_ge_atTop (2 : ℕ)] with n hC hl hn
  intro A hA
  subst n
  have take_pin (u : ℝ) (hku : k ≤ u)
      (hp : ∃ x ∈ A, u * (#A : ℝ) / Real.sqrt (Real.log #A) ≤ (distinctDistancesFrom A x : ℝ)) :
      ∃ x ∈ A, k * (#A : ℝ) / Real.sqrt (Real.log #A) ≤ (distinctDistancesFrom A x : ℝ) := by
    obtain ⟨x, hx, hd⟩ := hp
    refine ⟨x, hx, le_trans ?_ hd⟩
    gcongr
  by_cases hL : ∀ B ⊆ A, Collinear ℝ (B : Set ℝ²) → (#B : ℝ) * Real.log #A < #A
  · by_cases hB : ∀ B ⊆ A, (∀ y ∈ A, ∀ z ∈ A, y ≠ z →
        #(B.filter fun x => dist x y = dist x z) ≤ 2) → (#B : ℝ) * Real.log #A < #A
    · by_cases hE : ∀ x ∈ A, ((#A : ℝ) - 1) * Real.sqrt (Real.log #A) <
          (#(A.offDiag.filter fun p => dist x p.1 = dist x p.2) : ℝ)
      · exact take_pin c ((min_le_right _ _).trans (min_le_left _ _)) (hC A rfl hL hB hE)
      · push Not at hE
        obtain ⟨x, hx, hlow⟩ := hE
        have hs : 1 ≤ Real.sqrt (Real.log #A) := by
          simpa using (Real.sqrt_le_sqrt hl)
        apply take_pin (1/4) ((min_le_right _ _).trans (min_le_right _ _))
        exact ⟨x, hx, pin_of_low_collisions A x hs hn hx hlow⟩
    · push Not at hB
      obtain ⟨B, hBA, hf, hsize⟩ := hB
      exact take_pin b ((min_le_left _ _).trans (min_le_right _ _))
        (rich_subset_pin b hb A B hn hBA hsize (fun htwo => hbis A B hBA htwo hf))
  · push Not at hL
    obtain ⟨B, hBA, hf, hsize⟩ := hL
    exact take_pin a ((min_le_left _ _).trans (min_le_left _ _))
      (rich_subset_pin a ha A B hn hBA hsize (fun htwo => hline A B hBA htwo hf))

theorem main : H1 → H2 → H3 → type_of% @Erdos604.erdos_604.variants.average := by
  intro h₁ h₂ h₃
  exact uniform_pin_to_average (find_pin h₁ h₂ h₃)

end OMA.R_Erdos604_erdos_604_variants_average_R2
