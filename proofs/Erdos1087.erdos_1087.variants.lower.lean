import FormalConjectures.ErdosProblems.«1087»

/-!
# Erdős 1087: the lower bound `n^3 log n ≪ f(n)`

Following the lattice idea of Erdős and Purdy. In the grid `[0, 8m)²` parametrise isosceles
triangles with apex `P`: for `Q` in the central square `[2m, 4m)²`, a primitive
direction `w = (a, t)` with `0 ≤ a < t ≤ m` and `gcd(a, t) = 1`, and `1 ≤ g, j ≤ m / t`, put
`Q' = Q + 2 g w` and `P = Q + g w + j w⊥`, so that `|PQ| = |PQ'|`. Together with any fourth
grid point `X` this gives a degenerate four-element set, and every such set arises from at most
`4^4` parameter choices (the map to `(P, Q, Q', X)` is injective because `w` is primitive).
The number of parameters is `4 m² · Σ_{t ≤ m} φ(t) ⌊m/t⌋² · (64 m² - 3)`, and
`Σ_{t ≤ m} φ(t) ⌊m/t⌋² ≥ m² log₄ m / 48` follows from `Σ_{d ≤ Y} φ(d) ⌊Y/d⌋ = Y (Y + 1) / 2`
on the blocks `(4^(j-1), 4^j]`. Padding the grid with far-away points gives every `n`.
-/

open Finset
open scoped EuclideanGeometry

namespace OMAv6c
open Erdos1087
open scoped Classical

noncomputable def pt (z : ℤ × ℤ) : ℝ² := !₂[(z.1 : ℝ), (z.2 : ℝ)]

lemma dist_pt (z w : ℤ × ℤ) :
    dist (pt z) (pt w) = Real.sqrt ((((z.1 - w.1 : ℤ) : ℝ)) ^ 2 + (((z.2 - w.2 : ℤ) : ℝ)) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [pt, Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma pt_inj : Function.Injective pt := by
  intro z w h
  have h0 := congrArg (fun p : ℝ² => p 0) h
  have h1 := congrArg (fun p : ℝ² => p 1) h
  simp [pt] at h0 h1
  exact Prod.ext h0 h1

lemma repeated_of_iso {p q r x : ℝ²} (hpq : p ≠ q) (hpr : p ≠ r) (hpx : p ≠ x) (hqr : q ≠ r)
    (hqx : q ≠ x) (hrx : r ≠ x) (hd : dist p q = dist p r) :
    ({p, q, r, x} : Finset ℝ²).card = 4 ∧ HasRepeatedDistance {p, q, r, x} := by
  have hcard : ({p, q, r, x} : Finset ℝ²).card = 4 := by
    rw [card_insert_of_notMem (by simp [hpq, hpr, hpx]), card_insert_of_notMem (by simp [hqr, hqx]),
      card_insert_of_notMem (by simp [hrx]), card_singleton]
  refine ⟨hcard, ?_⟩
  unfold HasRepeatedDistance distinctDistances distanceSet
  rw [hcard]
  have hsub : ({p, q, r, x} : Finset ℝ²).offDiag.image (fun pair : ℝ² × ℝ² => dist pair.1 pair.2)
      ⊆ {dist p q, dist q r, dist p x, dist q x, dist r x} := by
    intro d hd'
    simp only [mem_image, mem_offDiag, mem_insert, mem_singleton] at hd'
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩ := hd'
    dsimp only at ha hb hab ⊢
    simp only [mem_insert, mem_singleton]
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp_all [dist_comm]
  have h5 : ({dist p q, dist q r, dist p x, dist q x, dist r x} : Finset ℝ).card ≤ 5 := by
    refine (card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    simp
  have := (card_le_card hsub).trans h5
  have h42 : Nat.choose 4 2 = 6 := by decide
  rw [h42]
  omega


def cP (Q : ℤ × ℤ) (t a g j : ℕ) : ℤ × ℤ :=
  (Q.1 + (g : ℤ) * a - (j : ℤ) * t, Q.2 + (g : ℤ) * t + (j : ℤ) * a)

def cR (Q : ℤ × ℤ) (t a g : ℕ) : ℤ × ℤ :=
  (Q.1 + 2 * (g : ℤ) * a, Q.2 + 2 * (g : ℤ) * t)

lemma iso_dist (Q : ℤ × ℤ) (t a g j : ℕ) :
    dist (pt (cP Q t a g j)) (pt Q) = dist (pt (cP Q t a g j)) (pt (cR Q t a g)) := by
  rw [dist_pt, dist_pt]
  congr 1
  simp only [cP, cR]
  push_cast
  ring

def grid (m : ℕ) : Finset (ℤ × ℤ) := Ico (0 : ℤ) (8 * m) ×ˢ Ico (0 : ℤ) (8 * m)

def Qs (m : ℕ) : Finset (ℤ × ℤ) := Ico (2 * (m : ℤ)) (4 * m) ×ˢ Ico (2 * (m : ℤ)) (4 * m)

def U (m : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ × ℕ) :=
  (Ioc 0 m).sigma fun t => ((range t).filter fun a => t.Coprime a) ×ˢ (Ioc 0 (m / t) ×ˢ Ioc 0 (m / t))

noncomputable def tri (c : (ℤ × ℤ) × (Σ _ : ℕ, ℕ × ℕ × ℕ)) : Finset ℝ² :=
  {pt (cP c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2), pt c.1, pt (cR c.1 c.2.1 c.2.2.1 c.2.2.2.1)}

noncomputable def params (m : ℕ) : Finset (((ℤ × ℤ) × (Σ _ : ℕ, ℕ × ℕ × ℕ)) × ℝ²) :=
  ((Qs m ×ˢ U m) ×ˢ (grid m).image pt).filter fun x => x.2 ∉ tri x.1

noncomputable def quad (x : ((ℤ × ℤ) × (Σ _ : ℕ, ℕ × ℕ × ℕ)) × ℝ²) : Finset ℝ² :=
  {pt (cP x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2), pt x.1.1,
    pt (cR x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1), x.2}

lemma mem_params {m : ℕ} {Q : ℤ × ℤ} {t a g j : ℕ} {X : ℝ²} :
    ((Q, ⟨t, (a, g, j)⟩), X) ∈ params m ↔
      (2 * (m : ℤ) ≤ Q.1 ∧ Q.1 < 4 * m ∧ 2 * (m : ℤ) ≤ Q.2 ∧ Q.2 < 4 * m) ∧
      (0 < t ∧ t ≤ m ∧ a < t ∧ t.Coprime a ∧ 0 < g ∧ g ≤ m / t ∧ 0 < j ∧ j ≤ m / t) ∧
      X ∈ (grid m).image pt ∧ X ∉ tri (Q, ⟨t, (a, g, j)⟩) := by
  simp only [params, Qs, U, mem_filter, mem_product, mem_sigma, mem_Ico, mem_Ioc, mem_range]
  tauto


lemma bounds_of {m t g : ℕ} (ht : 0 < t) (hg : g ≤ m / t) : g * t ≤ m :=
  (Nat.mul_le_mul_right t hg).trans (Nat.div_mul_le_self m t)

lemma quad_mem {m : ℕ} {x : ((ℤ × ℤ) × (Σ _ : ℕ, ℕ × ℕ × ℕ)) × ℝ²} (hx : x ∈ params m) :
    quad x ∈ (((grid m).image pt).powersetCard 4).filter HasRepeatedDistance := by
  obtain ⟨⟨Q, ⟨t, a, g, j⟩⟩, X⟩ := x
  rw [mem_params] at hx
  obtain ⟨⟨hq1, hq2, hq3, hq4⟩, ⟨ht0, htm, hat, _, hg0, hg, hj0, hj⟩, hX, hXn⟩ := hx
  have hgt := bounds_of ht0 hg
  have hjt := bounds_of ht0 hj
  have hga : g * a ≤ g * t := Nat.mul_le_mul_left g hat.le
  have hja : j * a ≤ j * t := Nat.mul_le_mul_left j hat.le
  have hgt' : (g : ℤ) * t ≤ m := by exact_mod_cast hgt
  have hjt' : (j : ℤ) * t ≤ m := by exact_mod_cast hjt
  have hga' : (g : ℤ) * a ≤ (g : ℤ) * t := by exact_mod_cast hga
  have hja' : (j : ℤ) * a ≤ (j : ℤ) * t := by exact_mod_cast hja
  have hpos1 : (0 : ℤ) < (g : ℤ) * t := by positivity
  have hpos2 : (0 : ℤ) < (j : ℤ) * t := by positivity
  have hnn1 : (0 : ℤ) ≤ (g : ℤ) * a := by positivity
  have hnn2 : (0 : ℤ) ≤ (j : ℤ) * a := by positivity
  simp only [tri, mem_insert, mem_singleton, not_or] at hXn
  obtain ⟨hXP, hXQ, hXR⟩ := hXn
  have hPQ : pt (cP Q t a g j) ≠ pt Q := by
    intro h
    have := congrArg Prod.snd (pt_inj h)
    simp only [cP] at this
    linarith
  have hPR : pt (cP Q t a g j) ≠ pt (cR Q t a g) := by
    intro h
    have := congrArg Prod.fst (pt_inj h)
    simp only [cP, cR] at this
    linarith
  have hQR : pt Q ≠ pt (cR Q t a g) := by
    intro h
    have := congrArg Prod.snd (pt_inj h)
    simp only [cR] at this
    linarith
  obtain ⟨hcard, hrep⟩ := repeated_of_iso hPQ hPR (Ne.symm hXP) hQR (Ne.symm hXQ) (Ne.symm hXR)
    (iso_dist Q t a g j)
  rw [mem_filter, mem_powersetCard]
  refine ⟨⟨?_, hcard⟩, hrep⟩
  intro y hy
  simp only [quad, mem_insert, mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · refine mem_image.mpr ⟨_, ?_, rfl⟩
    simp only [grid, mem_product, mem_Ico, cP]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · refine mem_image.mpr ⟨_, ?_, rfl⟩
    simp only [grid, mem_product, mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · refine mem_image.mpr ⟨_, ?_, rfl⟩
    simp only [grid, mem_product, mem_Ico, cR]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · exact hX


noncomputable def ι (x : ((ℤ × ℤ) × (Σ _ : ℕ, ℕ × ℕ × ℕ)) × ℝ²) : ℝ² × ℝ² × ℝ² × ℝ² :=
  (pt (cP x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2), pt x.1.1,
    pt (cR x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1), x.2)

lemma ι_injOn (m : ℕ) : Set.InjOn ι (params m : Set _) := by
  rintro ⟨⟨Q, ⟨t, a, g, j⟩⟩, X⟩ hx ⟨⟨Q', ⟨t', a', g', j'⟩⟩, X'⟩ hy h
  rw [mem_coe, mem_params] at hx hy
  obtain ⟨_, ⟨ht0, _, _, hcop, hg0, _, _, _⟩, _, _⟩ := hx
  obtain ⟨_, ⟨ht0', _, _, hcop', hg0', _, _, _⟩, _, _⟩ := hy
  simp only [ι, Prod.mk.injEq] at h
  obtain ⟨hP, hQ, hR, hX⟩ := h
  have hQ' := pt_inj hQ
  subst hQ' hX
  have hR' := pt_inj hR
  simp only [cR, Prod.mk.injEq] at hR'
  obtain ⟨h1, h2⟩ := hR'
  have e1 : g * a = g' * a' := by
    have : (g : ℤ) * a = (g' : ℤ) * a' := by linarith
    exact_mod_cast this
  have e2 : g * t = g' * t' := by
    have : (g : ℤ) * t = (g' : ℤ) * t' := by linarith
    exact_mod_cast this
  have hgg : g = g' := by
    have k1 : Nat.gcd (g * a) (g * t) = g := by
      rw [Nat.gcd_mul_left, Nat.gcd_comm, hcop, mul_one]
    have k2 : Nat.gcd (g' * a') (g' * t') = g' := by
      rw [Nat.gcd_mul_left, Nat.gcd_comm, hcop', mul_one]
    rw [← k1, ← k2, e1, e2]
  subst hgg
  have haa : a = a' := Nat.eq_of_mul_eq_mul_left hg0 e1
  have htt : t = t' := Nat.eq_of_mul_eq_mul_left hg0 e2
  subst haa htt
  have hP' := pt_inj hP
  simp only [cP, Prod.mk.injEq] at hP'
  have e3 : j * t = j' * t := by
    have : (j : ℤ) * t = (j' : ℤ) * t := by linarith [hP'.1]
    exact_mod_cast this
  have hjj : j = j' := Nat.eq_of_mul_eq_mul_right ht0 e3
  subst hjj
  rfl

lemma fiber_le (m : ℕ) (S : Finset ℝ²) :
    ((params m).filter fun x => quad x = S).card ≤ 256 := by
  rcases Finset.eq_empty_or_nonempty ((params m).filter fun x => quad x = S) with h | ⟨x0, hx0⟩
  · rw [h]; simp
  have hx0' := mem_filter.mp hx0
  have hS : S.card = 4 := by
    have := quad_mem hx0'.1
    rw [mem_filter, mem_powersetCard] at this
    rw [← hx0'.2]; exact this.1.2
  have hmaps : ∀ x ∈ (params m).filter (fun x => quad x = S), ι x ∈ S ×ˢ S ×ˢ S ×ˢ S := by
    intro x hx
    rw [mem_filter] at hx
    rw [← hx.2]
    simp [ι, quad, mem_product]
  have := Finset.card_le_card_of_injOn ι hmaps
    ((ι_injOn m).mono (by intro x hx; exact (mem_filter.mp hx).1))
  simp only [card_product, hS] at this
  simpa using this


lemma card_grid (m : ℕ) : ((grid m).image pt).card = (8 * m) * (8 * m) := by
  rw [card_image_of_injective _ pt_inj, grid, card_product, Int.card_Ico]
  have : (8 * (m : ℤ) - 0).toNat = 8 * m := by omega
  rw [this]

lemma card_Qs (m : ℕ) : (Qs m).card = (2 * m) * (2 * m) := by
  rw [Qs, card_product, Int.card_Ico]
  have : (4 * (m : ℤ) - 2 * m).toNat = 2 * m := by omega
  rw [this]

lemma card_U (m : ℕ) : (U m).card = ∑ t ∈ Ioc 0 m, Nat.totient t * ((m / t) * (m / t)) := by
  rw [U, card_sigma]
  apply Finset.sum_congr rfl
  intro t _
  rw [card_product, card_product, Nat.card_Ioc, Nat.totient_eq_card_coprime]
  simp

lemma card_params (m : ℕ) :
    (Qs m ×ˢ U m).card * (((grid m).image pt).card - 3) ≤ (params m).card := by
  rw [params, card_filter, sum_product]
  rw [← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro c _
  rw [← card_filter]
  have h1 : ((grid m).image pt).filter (fun X => X ∉ tri c) = (grid m).image pt \ tri c := by
    ext X; simp [mem_sdiff]
  rw [h1]
  have h2 : (tri c).card ≤ 3 := by
    unfold tri
    refine (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans ?_))
    simp
  have h3 := Finset.le_card_sdiff (tri c) ((grid m).image pt)
  omega

lemma main_count (m : ℕ) :
    (Qs m ×ˢ U m).card * (((grid m).image pt).card - 3) ≤
      256 * degenerateCount ((grid m).image pt) := by
  refine (card_params m).trans ?_
  refine (Finset.card_le_mul_card_image (f := quad) (params m) 256 ?_).trans ?_
  · intro S _
    exact fiber_le m S
  · apply Nat.mul_le_mul_left
    unfold degenerateCount
    apply card_le_card
    intro S hS
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hS
    have := quad_mem hx
    rw [mem_filter] at this ⊢
    exact this

lemma sum_totient_floor (Y : ℕ) :
    ∑ d ∈ Ioc 0 Y, Nat.totient d * (Y / d) = ∑ t ∈ Ioc 0 Y, t := by
  have h1 : ∑ t ∈ Ioc 0 Y, t = ∑ t ∈ Ioc 0 Y, ∑ d ∈ t.divisors, Nat.totient d :=
    Finset.sum_congr rfl fun t _ => (Nat.sum_totient t).symm
  rw [h1]
  rw [Finset.sum_comm' (t' := Ioc 0 Y) (s' := fun d => (Ioc 0 Y).filter (fun t => d ∣ t))]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_const, smul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
  · intro t d
    simp only [mem_Ioc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h0, hY⟩, hd, ht⟩
      exact ⟨⟨⟨h0, hY⟩, hd⟩, Nat.pos_of_dvd_of_pos hd h0, (Nat.le_of_dvd h0 hd).trans hY⟩
    · rintro ⟨⟨⟨h0, hY⟩, hd⟩, _, _⟩
      exact ⟨⟨h0, hY⟩, hd, by omega⟩

lemma two_mul_sum_id (Y : ℕ) : 2 * ∑ t ∈ Ioc 0 Y, t = Y * (Y + 1) := by
  induction Y with
  | zero => simp
  | succ k ih =>
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le k) (Nat.le_succ k), Nat.Ioc_succ_singleton,
      sum_singleton, mul_add, ih]
    ring

/-- For `Y = 4 Z`, the totients on `(Z, 4 Z]` add up to at least `Y² / 12`. -/
lemma block_totient (Z : ℕ) :
    (4 * Z) * (4 * Z) ≤ 12 * ∑ d ∈ Ioc Z (4 * Z), Nat.totient d := by
  set Y := 4 * Z with hY
  have hsplit := Finset.sum_Ioc_consecutive (fun d => Nat.totient d * (Y / d))
    (Nat.zero_le Z) (show Z ≤ Y by omega)
  have htot := sum_totient_floor Y
  have hid := two_mul_sum_id Y
  have hsmall : ∑ d ∈ Ioc 0 Z, Nat.totient d * (Y / d) ≤ Z * Y := by
    calc ∑ d ∈ Ioc 0 Z, Nat.totient d * (Y / d) ≤ ∑ d ∈ Ioc 0 Z, Y := by
          apply Finset.sum_le_sum
          intro d _
          calc Nat.totient d * (Y / d) ≤ d * (Y / d) :=
                Nat.mul_le_mul_right _ (Nat.totient_le d)
            _ ≤ Y := Nat.mul_div_le Y d
      _ = Z * Y := by simp
  have hlarge : ∑ d ∈ Ioc Z Y, Nat.totient d * (Y / d) ≤ 3 * ∑ d ∈ Ioc Z Y, Nat.totient d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [mem_Ioc] at hd
    have : Y / d ≤ 3 := by
      have : Y / d < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    calc Nat.totient d * (Y / d) ≤ Nat.totient d * 3 := Nat.mul_le_mul_left _ this
      _ = 3 * Nat.totient d := by ring
  nlinarith


lemma block_weighted (m Z : ℕ) (hZ : 4 * Z ≤ m) (hZ0 : 0 < Z) :
    m * m ≤ 48 * ∑ t ∈ Ioc Z (4 * Z), Nat.totient t * ((m / t) * (m / t)) := by
  set Y := 4 * Z with hY
  set q := m / Y with hq
  have hb := block_totient Z
  have hmono : ∀ t ∈ Ioc Z Y, q ≤ m / t := by
    intro t ht
    rw [mem_Ioc] at ht
    exact Nat.div_le_div_left ht.2 (by omega)
  have h1 : (∑ t ∈ Ioc Z Y, Nat.totient t) * (q * q) ≤
      ∑ t ∈ Ioc Z Y, Nat.totient t * ((m / t) * (m / t)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t ht
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (hmono t ht) (hmono t ht))
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).mpr hZ
  have h2 : m ≤ 2 * (Y * q) := by
    have := Nat.div_add_mod m Y
    have := Nat.mod_lt m (show Y > 0 by omega)
    nlinarith
  have h3 : m * m ≤ 4 * (Y * Y) * (q * q) := by nlinarith
  have hb' : Y * Y ≤ 12 * ∑ d ∈ Ioc Z Y, Nat.totient d := hb
  have h4 := Nat.mul_le_mul_right (q * q) hb'
  calc m * m ≤ 4 * (Y * Y) * (q * q) := h3
    _ = 4 * (Y * Y * (q * q)) := by ring
    _ ≤ 4 * (12 * (∑ d ∈ Ioc Z Y, Nat.totient d) * (q * q)) := Nat.mul_le_mul_left _ h4
    _ = 48 * ((∑ d ∈ Ioc Z Y, Nat.totient d) * (q * q)) := by ring
    _ ≤ 48 * ∑ t ∈ Ioc Z Y, Nat.totient t * ((m / t) * (m / t)) := Nat.mul_le_mul_left _ h1

lemma weighted_log (m : ℕ) (hm : 0 < m) :
    Nat.log 4 m * (m * m) ≤ 48 * ∑ t ∈ Ioc 0 m, Nat.totient t * ((m / t) * (m / t)) := by
  have key : ∀ j : ℕ, 4 ^ j ≤ m →
      j * (m * m) ≤ 48 * ∑ t ∈ Ioc 0 (4 ^ j), Nat.totient t * ((m / t) * (m / t)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' : 4 ^ j ≤ m := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)) hj
      have h1 := ih hj'
      have hpow : 4 ^ (j + 1) = 4 * 4 ^ j := by ring
      have h2 := block_weighted m (4 ^ j) (by rw [← hpow]; exact hj) (by positivity)
      rw [hpow, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (4 ^ j)) (by omega), mul_add]
      nlinarith
  have hJ : 4 ^ Nat.log 4 m ≤ m := Nat.pow_log_le_self 4 hm.ne'
  have h := key _ hJ
  have hsub : ∑ t ∈ Ioc 0 (4 ^ Nat.log 4 m), Nat.totient t * ((m / t) * (m / t)) ≤
      ∑ t ∈ Ioc 0 m, Nat.totient t * ((m / t) * (m / t)) :=
    Finset.sum_le_sum_of_subset (Finset.Ioc_subset_Ioc_right hJ)
  omega


lemma deg_mono {A B : Finset ℝ²} (h : A ⊆ B) : degenerateCount A ≤ degenerateCount B := by
  unfold degenerateCount
  exact card_le_card (filter_subset_filter _ (powersetCard_mono h))

lemma grid_bound (m : ℕ) (hm : 1 ≤ m) :
    4 * 61 * (Nat.log 4 m * (m * m * (m * m) * (m * m))) ≤
      12288 * degenerateCount ((grid m).image pt) := by
  have h1 := main_count m
  rw [card_product, card_Qs, card_U, card_grid] at h1
  have h2 := weighted_log m (by omega)
  set W := ∑ t ∈ Ioc 0 m, Nat.totient t * ((m / t) * (m / t)) with hW
  set D := degenerateCount ((grid m).image pt)
  have h3 : 61 * (m * m) ≤ 8 * m * (8 * m) - 3 := by
    have : 1 ≤ m * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e : 8 * m * (8 * m) = 64 * (m * m) := by ring
    rw [e]
    omega
  have h4 : 2 * m * (2 * m) * W * (61 * (m * m)) ≤ 256 * D :=
    (Nat.mul_le_mul_left _ h3).trans h1
  have h5 : Nat.log 4 m * (m * m) * (4 * (m * m) * (61 * (m * m))) ≤
      48 * W * (4 * (m * m) * (61 * (m * m))) := Nat.mul_le_mul_right _ h2
  have h6 : 2 * m * (2 * m) * W * (61 * (m * m)) = W * (4 * (m * m) * (61 * (m * m))) := by ring
  nlinarith


lemma exists_superset (m n : ℕ) (h : (8 * m) * (8 * m) ≤ n) :
    ∃ P : Finset ℝ², P.card = n ∧ (grid m).image pt ⊆ P := by
  set E : Finset ℝ² := (range (n - (8 * m) * (8 * m))).image fun i : ℕ => pt (-1 - (i : ℤ), 0)
  have hEinj : Set.InjOn (fun i : ℕ => pt (-1 - (i : ℤ), 0)) (range (n - (8 * m) * (8 * m)) : Set ℕ) := by
    intro i _ j _ hij
    have := congrArg Prod.fst (pt_inj hij)
    simp only at this
    omega
  have hE : E.card = n - (8 * m) * (8 * m) := by
    rw [card_image_of_injOn hEinj, card_range]
  have hdisj : Disjoint ((grid m).image pt) E := by
    rw [Finset.disjoint_left]
    intro X hX hXE
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
    obtain ⟨i, _, hi⟩ := mem_image.mp hXE
    have := congrArg Prod.fst (pt_inj hi)
    simp only [grid, mem_product, mem_Ico] at hz
    simp only at this
    omega
  refine ⟨(grid m).image pt ∪ E, ?_, subset_union_left⟩
  rw [card_union_of_disjoint hdisj, card_grid, hE]
  omega

lemma main_lower :
    (fun n : ℕ ↦ (n : ℝ) ^ 3 * Real.log n) =O[Filter.atTop] fun n : ℕ ↦ (f n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound (1024 ^ 3 * 13 * 51) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 20)] with n hn
  set s := Nat.sqrt n with hs
  set m := s / 8 with hm
  have hs1 : s * s ≤ n := Nat.sqrt_le n
  have hs2 : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hs3 : 1024 ≤ s := by
    rw [hs]; exact Nat.le_sqrt'.mpr (by norm_num at hn ⊢; omega)
  have hm1 : 8 * m ≤ s := Nat.mul_div_le s 8
  have hm2 : s < 8 * m + 8 := by omega
  have hm4 : 4 ≤ m := by omega
  have hgrid : (8 * m) * (8 * m) ≤ n := le_trans (Nat.mul_le_mul hm1 hm1) hs1
  have hn256 : n ≤ 256 * (m * m) := by nlinarith
  obtain ⟨P, hP, hsub⟩ := exists_superset m n hgrid
  have hfP : degenerateCount ((grid m).image pt) ≤ f n := by
    have := degenerateCount_le_f P
    rw [hP] at this
    exact (deg_mono hsub).trans this
  have hgb := grid_bound m (by omega)
  set L := Nat.log 4 m with hL
  have hL1 : 1 ≤ L := Nat.log_pos (by norm_num) hm4
  have hmL : m < 4 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  -- real-number estimates
  have hn0 : (0 : ℝ) < n := by
    have : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
    exact_mod_cast this
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog4 : Real.log 4 < 1.4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hlogm : Real.log m < (L + 1) * Real.log 4 := by
    have h := Real.log_lt_log hmR (show (m : ℝ) < (4 : ℝ) ^ (L + 1) by exact_mod_cast hmL)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogn : Real.log n ≤ Real.log 256 + 2 * Real.log m := by
    have h := Real.log_le_log hn0 (show (n : ℝ) ≤ 256 * ((m : ℝ) * m) by exact_mod_cast hn256)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hmR.ne' hmR.ne'] at h
    linarith
  have hlog256 : Real.log 256 = 4 * Real.log 4 := by
    rw [show (256 : ℝ) = 4 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hlogn' : Real.log n ≤ 13 * L := by
    have : Real.log n ≤ (2 * L + 6) * Real.log 4 := by nlinarith
    nlinarith
  have hlognn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hn))
  have hn3 : (n : ℝ) ^ 3 ≤ (256 : ℝ) ^ 3 * ((m : ℝ) * m) ^ 3 := by
    have : (n : ℝ) ≤ 256 * ((m : ℝ) * m) := by exact_mod_cast hn256
    have h0 : (0 : ℝ) ≤ n := hn0.le
    calc (n : ℝ) ^ 3 ≤ (256 * ((m : ℝ) * m)) ^ 3 := pow_le_pow_left₀ h0 this 3
      _ = (256 : ℝ) ^ 3 * ((m : ℝ) * m) ^ 3 := by ring
  have hgbR : 244 * ((L : ℝ) * ((m : ℝ) * m * (m * m) * (m * m))) ≤
      12288 * (degenerateCount ((grid m).image pt) : ℝ) := by
    have := hgb
    norm_num at this
    exact_mod_cast this
  have hfR : (degenerateCount ((grid m).image pt) : ℝ) ≤ f n := by exact_mod_cast hfP
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hm6 : 0 ≤ ((m : ℝ) * m) ^ 3 := by positivity
  calc (n : ℝ) ^ 3 * Real.log n ≤ (256 : ℝ) ^ 3 * ((m : ℝ) * m) ^ 3 * (13 * L) :=
        mul_le_mul hn3 hlogn' hlognn (by positivity)
    _ = 256 ^ 3 * 13 / 244 * (244 * ((L : ℝ) * ((m : ℝ) * m * (m * m) * (m * m)))) := by ring
    _ ≤ 256 ^ 3 * 13 / 244 * (12288 * (degenerateCount ((grid m).image pt) : ℝ)) :=
        mul_le_mul_of_nonneg_left hgbR (by norm_num)
    _ ≤ 256 ^ 3 * 13 / 244 * (12288 * (f n : ℝ)) := by gcongr
    _ ≤ 1024 ^ 3 * 13 * 51 * (f n : ℝ) := by
        have : (0 : ℝ) ≤ f n := by positivity
        nlinarith

end OMAv6c

theorem OMA.solution : type_of% @Erdos1087.erdos_1087.variants.lower :=
  OMAv6c.main_lower
