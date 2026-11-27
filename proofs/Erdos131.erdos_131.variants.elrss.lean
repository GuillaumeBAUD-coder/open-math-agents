import FormalConjectures.ErdosProblems.«131»
import Mathlib.Combinatorics.Additive.SubsetSum

/-!
# The Erdős–Lev–Rauzy–Sándor–Sárközy bound for non-dividing sets

Reducing modulo the largest member produces a zero-sum-free set in a cyclic group.
We follow the greedy subgroup decomposition of J. E. Olson, “Sums of sets of group
elements” (Acta Arithmetica 28, 1975). For cyclic groups a direct packing of the
remaining generators, their negatives, and zero on translation-boundary levels
supplies the one-step growth estimate. The numerical recurrence is verified by
inequalities for large sizes and a kernel computation for the small sizes.
-/

/- Packing translates in levels of the translation boundary. -/

namespace OMA.Olson131Packing
open Finset

private abbrev level {G : Type*} (H : Finset G) (d : G → ℕ) (t : ℕ) :=
  H.filter (fun g => d g ≤ t)

private theorem level_mono {G : Type*} (H : Finset G) (d : G → ℕ) {s t : ℕ} (hst : s ≤ t) :
    level H d s ⊆ level H d t := fun _ h => mem_filter.mpr
      ⟨(mem_filter.mp h).1, (mem_filter.mp h).2.trans hst⟩

/-- If the boundary crosses a level, it takes a value at most one
generator increment above that level. -/
theorem interpolate {G : Type*} [AddCommGroup G] (d : G → ℕ) (a : ℕ)
    (hzero : d 0 = 0) (htriangle : ∀ x y, d (x+y) ≤ d x + d y)
    (hneg : ∀ x, d (-x) = d x) (R : Finset G) (hR : ∀ r ∈ R, d r ≤ a)
    {t : ℕ} {g : G} (hg : g ∈ AddSubgroup.closure (R : Set G)) (ht : t < d g) :
    ∃ u ∈ AddSubgroup.closure (R : Set G), t < d u ∧ d u ≤ t+a := by
  classical
  by_contra! hgap
  have hlow : ∀ v, ∀ hv : v ∈ AddSubgroup.closure (R : Set G), d v ≤ t := by
    intro v hv
    induction hv using AddSubgroup.closure_induction_left with
    | zero => omega
    | add_left x hx y hy ih =>
      have hmem := (AddSubgroup.closure (R : Set G)).add_mem (AddSubgroup.subset_closure hx) hy
      have hdx := hR x hx
      have htr := htriangle x y
      specialize hgap (x+y) hmem
      omega
    | neg_add_cancel x hx y hy ih =>
      have hmem := (AddSubgroup.closure (R : Set G)).add_mem
        ((AddSubgroup.closure (R : Set G)).neg_mem (AddSubgroup.subset_closure hx)) hy
      have hdx := hR x hx
      have htr := htriangle (-x) y
      rw [hneg] at htr
      specialize hgap (-x+y) hmem
      omega
  exact (hlow g hg).not_gt ht

private theorem pack_at_steps {G : Type*} [AddCommGroup G] [DecidableEq G]
    (H C : Finset G) (d : G → ℕ) (a t : ℕ)
    (hCH : C ⊆ H) (hclosed : ∀ x ∈ H, ∀ y ∈ H, x+y ∈ H)
    (hC : ∀ g ∈ C, d g ≤ a) (htriangle : ∀ x y, d (x+y) ≤ d x + d y)
    (hneg : ∀ x, d (-x) = d x)
    (hgap : ∀ v ≤ t, ∃ u ∈ H, v < d u ∧ d u ≤ v+a) :
    ∀ j : ℕ, (3*j+1)*a ≤ t →
      (j+1)*C.card ≤ (level H d ((3*j+1)*a)).card := by
  classical
  intro j
  induction j with
  | zero =>
    intro h
    simp only [Nat.mul_zero, Nat.zero_add, one_mul]
    exact card_le_card (fun g hg => mem_filter.mpr ⟨hCH hg, hC g hg⟩)
  | succ j ih =>
    intro ht
    have hc1 : (3*(j+1)+1)*a = (3*j+1)*a + 3*a := by ring
    rw [hc1] at ht ⊢
    specialize ih (by omega)
    obtain ⟨u, hu, hlo, hhi⟩ := hgap ((3*j+1)*a + a) (by omega)
    let U := C.image (fun z => u+z)
    have hsub : U ⊆ level H d ((3*j+1)*a + 3*a) := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      have := hC z hz
      have := htriangle u z
      exact mem_filter.mpr ⟨hclosed u hu z (hCH hz), by omega⟩
    have hd : Disjoint (level H d ((3*j+1)*a)) U := by
      apply disjoint_left.mpr
      intro x hx hxU
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hxU
      have hb := (mem_filter.mp hx).2
      have hc := hC z hz
      have hrev := htriangle (u+z) (-z)
      rw [add_neg_cancel_right, hneg] at hrev
      omega
    have hlevels := level_mono H d (Nat.le_add_right ((3*j+1)*a) (3*a))
    have htotal := card_le_card (union_subset hlevels hsub)
    rw [card_union_of_disjoint hd] at htotal
    have hcard : U.card = C.card := card_image_of_injective _ (add_right_injective _)
    rw [hcard] at htotal
    nlinarith

/-- A set of at least eight generator increments' worth of low-boundary
points forces more than k² intersections. -/
theorem packing_contradiction {G : Type*} [AddCommGroup G] [DecidableEq G]
    (H C : Finset G) (d : G → ℕ) (a k : ℕ)
    (hk : 0 < k) (hsize : 2*k ≤ H.card) (ha : 2*a ≤ k) (hbig : 8*a < C.card)
    (hCH : C ⊆ H) (hclosed : ∀ x ∈ H, ∀ y ∈ H, x+y ∈ H)
    (hC : ∀ g ∈ C, d g ≤ a) (hz : 0 ∈ H) (hd0 : d 0 = 0)
    (htriangle : ∀ x y, d (x+y) ≤ d x + d y) (hneg : ∀ x, d (-x) = d x)
    (hinter : ∀ t : ℕ, (∃ g ∈ H, t < d g) → ∃ u ∈ H, t < d u ∧ d u ≤ t+a)
    (hsum : ∑ j ∈ range k, (level H d j).card = k^2) : False := by
  classical
  have all_low (t : ℕ) (h : ¬∃ g ∈ H, t < d g) : level H d t = H := by
    apply filter_true_of_mem
    intro g hg
    exact le_of_not_gt (fun hgt => h ⟨g,hg,hgt⟩)
  by_cases haz : a = 0
  · subst a
    have h0 : ¬∃ g ∈ H, 0 < d g := by
      intro hi
      obtain ⟨u, _, hu, hb⟩ := hinter 0 hi
      omega
    have hforall (t : ℕ) : level H d t = H := all_low t (fun ⟨v,hv,hvt⟩ =>
      h0 ⟨v,hv,by omega⟩)
    simp only [hforall, sum_const, card_range, nsmul_eq_mul] at hsum
    nlinarith [Nat.mul_le_mul_left k hsize]
  have haPos : 0 < a := by omega
  have hone (t : ℕ) : 1 ≤ (level H d t).card := card_pos.mpr ⟨0, mem_filter.mpr ⟨hz,by omega⟩⟩
  have hwide (t : ℕ) (hat : a ≤ t) : 4*a ≤ (level H d t).card := by
    have h : C ⊆ level H d t := fun g hg => mem_filter.mpr ⟨hCH hg, (hC g hg).trans hat⟩
    have := card_le_card h
    omega
  have hlevel (t : ℕ) (hat : a ≤ t) (htk : t < k) : 2*t+1 ≤ (level H d t).card := by
    by_cases hhigh : ∃ g ∈ H, t < d g
    · let j := (t-a)/(3*a)
      have hdiv := Nat.div_add_mod (t-a) (3*a)
      have hrem := Nat.mod_lt (t-a) (show 0 < 3*a by omega)
      have hjn : (3*j+1)*a ≤ t ∧ t < (3*j+1)*a + 3*a := by
        dsimp [j]
        ring_nf at * -- normalize the products involving the quotient
        omega
      have hgap : ∀ v ≤ t, ∃ u ∈ H, v < d u ∧ d u ≤ v+a := by
        intro v hv
        obtain ⟨g,hg,hgt⟩ := hhigh
        exact hinter v ⟨g,hg,by omega⟩
      have hpack := pack_at_steps H C d a t hCH hclosed hC htriangle hneg hgap j hjn.1
      have hm := card_le_card (level_mono H d hjn.1)
      have hw := Nat.mul_le_mul_left (j+1) hbig.le
      nlinarith [Nat.zero_le (j*a)]
    · rw [all_low t hhigh]
      omega
  have hfirst : (2*a)^2 < ∑ j ∈ range (2*a), (level H d j).card := by
    rw [two_mul, sum_range_add]
    have h1 := sum_le_sum (s := range a) (g := fun i => (level H d i).card)
      (fun i _ => hone i)
    have h2 := sum_le_sum (s := range a) (g := fun i => (level H d (a+i)).card)
      (fun i _ => hwide (a+i) (by omega))
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h1 h2
    nlinarith
  have hstrong (n : ℕ) (hn : 2*a ≤ n) (hnk : n ≤ k) :
      n^2 < ∑ j ∈ range n, (level H d j).card := by
    induction n, hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      rw [sum_range_succ]
      have := ih (by omega)
      have := hlevel n (by omega) (by omega)
      nlinarith
  exact (hstrong k ha le_rfl).ne hsum.symm

end OMA.Olson131Packing

/- Translation boundaries in a finite cyclic group. -/

namespace OMA.Olson131Boundary
open Finset Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private abbrev shift (x : G) (B : Finset G) := B.image (fun y => x+y)

abbrev delta (B : Finset G) (x : G) := (shift x B \ B).card

private theorem shift_card (x : G) (B : Finset G) : (shift x B).card = B.card :=
  card_image_of_injective _ (add_right_injective _)

private theorem shift_mem {x z : G} {B : Finset G} : z ∈ shift x B ↔ z-x ∈ B := by
  constructor
  · rintro hz
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hz
    simpa using hb
  · exact fun h => mem_image.mpr ⟨z-x,h,by abel⟩

private theorem shift_shift (x y : G) (B : Finset G) :
    shift x (shift y B) = shift (x+y) B := by
  simp only [shift, image_image, Function.comp_def, add_assoc]

private theorem shift_sdiff (x : G) (A B : Finset G) :
    shift x (A \ B) = shift x A \ shift x B := image_sdiff _ _ (add_right_injective _)

theorem delta_zero (B : Finset G) : delta B 0 = 0 := by simp [delta, shift]

theorem delta_neg (B : Finset G) (x : G) : delta B (-x) = delta B x := by
  rw [delta, ← shift_card x, shift_sdiff, shift_shift]
  simp only [add_neg_cancel, shift, zero_add, image_id']
  exact card_sdiff_comm (shift_card x B).symm

theorem delta_add (B : Finset G) (x y : G) : delta B (x+y) ≤ delta B x + delta B y := by
  have hsub : shift (x+y) B \ B ⊆ (shift x B \ B) ∪ shift x (shift y B \ B) := by
    rw [shift_sdiff, shift_shift]
    intro g hg
    obtain ⟨hm, hn⟩ := mem_sdiff.mp hg
    by_cases h : g ∈ shift x B
    · exact mem_union_left _ (mem_sdiff.mpr ⟨h,hn⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hm,h⟩)
  exact (card_le_card hsub).trans <| (card_union_le _ _).trans_eq (by rw [shift_card])

theorem delta_union (B : Finset G) (x : G) :
    (B ∪ shift x B).card = B.card + delta B x := by
  rw [union_comm, ← card_sdiff_add_card, add_comm]

private theorem shift_group [Fintype G] (H : AddSubgroup G) {x : G} (hx : x ∈ H) :
    shift x (H : Set G).toFinset = (H : Set G).toFinset := by
  ext g
  simp only [shift_mem, Set.mem_toFinset, SetLike.mem_coe]
  exact ⟨fun h => by simpa using H.add_mem h hx, fun h => H.sub_mem h hx⟩

theorem delta_compl [Fintype G] (H : AddSubgroup G) (B : Finset G) (hB : (B : Set G) ⊆ H)
    {x : G} (hx : x ∈ H) : delta ((H : Set G).toFinset \ B) x = delta B x := by
  let K := (H : Set G).toFinset
  have hs : B ⊆ K := fun _ h => Set.mem_toFinset.mpr (hB h)
  have hsets : (K \ shift x B) \ (K \ B) = B \ shift x B := by
    ext g
    simp only [mem_sdiff]
    constructor
    · rintro ⟨⟨hk, hn⟩, h⟩
      exact ⟨by by_contra hm; exact h ⟨hk,hm⟩, hn⟩
    · rintro ⟨hb,hn⟩
      exact ⟨⟨hs hb,hn⟩,fun h => h.2 hb⟩
  rw [delta, shift_sdiff, shift_group H hx]
  exact (congrArg card hsets).trans (card_sdiff_comm (shift_card x B).symm)

/-- Counting a difference by its two endpoints, and then by its boundary
level, gives the same number of ordered pairs of elements of B. -/
theorem level_sum [Fintype G] (H : AddSubgroup G) (B : Finset G) (hB : (B : Set G) ⊆ H) :
    ∑ j ∈ range B.card, (((H : Set G).toFinset).filter (fun g => delta B g ≤ j)).card =
      B.card ^ 2 := by
  classical
  let K := (H : Set G).toFinset
  have hsize (g : G) :
      B.card - delta B g = (B.filter (fun y => y-g ∈ B)).card := by
    have hdiff := card_sdiff_add_card_inter (shift g B) B
    rw [shift_card] at hdiff
    have he : B ∩ shift g B = B.filter (fun y => y-g ∈ B) := by
      ext y; simp only [mem_inter, mem_filter, shift_mem]
    change B.card - (shift g B \ B).card = _
    rw [← he, inter_comm]
    omega
  have hswap (y : G) (hy : y ∈ B) : (K.filter (fun g => y-g ∈ B)).card = B.card := by
    have he : K.filter (fun g => y-g ∈ B) = B.image (fun z => y-z) := by
      ext g
      constructor
      · intro hg
        exact mem_image.mpr ⟨y-g, (mem_filter.mp hg).2, by abel⟩
      · intro hg
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hg
        exact mem_filter.mpr ⟨Set.mem_toFinset.mpr (H.sub_mem (hB hy) (hB hz)),by simpa using hz⟩
    rw [he, card_image_of_injective _ sub_right_injective]
  have htime (g : G) : ((range B.card).filter (fun j => delta B g ≤ j)).card =
      B.card - delta B g := by
    have he : (range B.card).filter (fun j => delta B g ≤ j) = Ico (delta B g) B.card := by
      ext j; simp [and_comm]
    rw [he, Nat.card_Ico]
  calc
    _ = ∑ g ∈ K, (B.card - delta B g) := by
      simp only [Finset.card_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro g _
      simpa only [Finset.card_filter] using htime g
    _ = ∑ y ∈ B, B.card := by
      simp_rw [hsize, Finset.card_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro y hy
      simpa only [Finset.card_filter] using hswap y hy
    _ = _ := by simp [pow_two]

/-- A nonzero residue equal to its negative is uniquely determined by
the modulus: its canonical representative is half the modulus. -/
private theorem antisym_union {m : ℕ} [NeZero m] (R : Finset (ZMod m))
    (hn : (0 : ZMod m) ∉ R) (ha : ∀ x ∈ R, ∀ y ∈ R, x+y=0 → x=y) :
    2 * R.card ≤ (insert 0 (R ∪ R.image Neg.neg)).card := by
  classical
  have hfix {x : ZMod m} (hx : x ∈ R ∩ R.image Neg.neg) : 2*x.val = m := by
    obtain ⟨hxR,hxn⟩ := mem_inter.mp hx
    obtain ⟨y,hy,hxy⟩ := mem_image.mp hxn
    have h := ha x hxR y hy (by rw [← hxy]; abel)
    have hf : -x = x := h ▸ hxy
    exact (x.neg_eq_self_iff.mp hf).resolve_left (fun he => hn (he ▸ hxR))
  have hone : (R ∩ R.image Neg.neg).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    have hxv := hfix hx
    have hyv := hfix hy
    exact ZMod.val_injective m (by omega)
  have hzero : (0 : ZMod m) ∉ R ∪ R.image Neg.neg := by simpa using hn
  have hc := card_union_add_card_inter R (R.image Neg.neg)
  rw [card_image_of_injective _ neg_injective] at hc
  rw [card_insert_of_notMem hzero]
  omega

/-- The finite cyclic translation bound used by the greedy peeling in
the non-dividing-set estimate. Antisymmetry makes the generator ball
large enough to prove the bound by packing translates. -/
theorem cyclic_boundary (m : ℕ) (hm : 0 < m) (B R : Finset (ZMod m))
    (hr : R.Nonempty) (hz : 0 ∈ B)
    (hb : (B : Set (ZMod m)) ⊆ AddSubgroup.closure (R : Set (ZMod m)))
    (havoid : ∀ r ∈ R, -r ∉ B) (hanti : ∀ x ∈ R, ∀ y ∈ R, x+y=0 → x=y) :
    ∃ x ∈ R, 4*B.card + min (2*(B.card+1)) R.card ≤
      4*(B ∪ B.image (fun y => x+y)).card := by
  classical
  let _ : NeZero m := ⟨hm.ne'⟩
  let H := AddSubgroup.closure (R : Set (ZMod m))
  let K := (H : Set (ZMod m)).toFinset
  let a := R.sup (delta B)
  have hBK : B ⊆ K := fun _ h => Set.mem_toFinset.mpr (hb h)
  have hR (r : ZMod m) (h : r ∈ R) : r ∈ H := AddSubgroup.subset_closure h
  have hdmax (r : ZMod m) (h : r ∈ R) : delta B r ≤ a := le_sup h
  obtain ⟨r,hr',heq⟩ := exists_mem_eq_sup R hr (delta B)
  refine ⟨r,hr',?_⟩
  change 4*B.card + min (2*(B.card+1)) R.card ≤ 4*(B ∪ shift r B).card
  rw [delta_union, ← heq]
  change 4*B.card + min (2*(B.card+1)) R.card ≤ 4*(B.card+a)
  by_contra! hbad
  have hnegK : R.image Neg.neg ⊆ K \ B := by
    intro z hz'
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz'
    exact mem_sdiff.mpr ⟨Set.mem_toFinset.mpr (H.neg_mem (hR y hy)), havoid y hy⟩
  have hkc := card_le_card hnegK
  rw [card_image_of_injective _ neg_injective, card_sdiff_of_subset hBK] at hkc
  let X := if 2*B.card ≤ K.card then B else K \ B
  have hX : X ⊆ K := by dsimp [X]; split <;> first | exact hBK | exact sdiff_subset
  have hXB : ∀ x ∈ H, delta X x = delta B x := by
    intro x hx
    dsimp [X]; split
    · rfl
    · exact delta_compl H B hb hx
  have hbpos := card_pos.mpr (show B.Nonempty from ⟨0,hz⟩)
  have hrpos := card_pos.mpr hr
  have hXsize : 0 < X.card ∧ 2*a ≤ X.card ∧ 2*X.card ≤ K.card := by
    dsimp [X]; split
    · omega
    · rw [card_sdiff_of_subset hBK]; omega
  let C := insert 0 (R ∪ R.image Neg.neg)
  have hnR : (0 : ZMod m) ∉ R := fun h => havoid 0 h (by simpa using hz)
  have hCsize := antisym_union R hnR hanti
  have hC : ∀ z ∈ C, delta X z ≤ a ∧ z ∈ K := by
    intro z h
    rcases mem_insert.mp h with rfl | h
    · exact ⟨by simp [delta_zero], Set.mem_toFinset.mpr H.zero_mem⟩
    · rcases mem_union.mp h with hrz | hneg
      · exact ⟨(hXB z (hR z hrz)).le.trans (hdmax z hrz), Set.mem_toFinset.mpr (hR z hrz)⟩
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp hneg
        rw [delta_neg, hXB y (hR y hy)]
        exact ⟨hdmax y hy, Set.mem_toFinset.mpr (H.neg_mem (hR y hy))⟩
  have hD (y : ZMod m) (hy : y ∈ R) : delta X y ≤ a := (hXB y (hR y hy)).le.trans (hdmax y hy)
  apply OMA.Olson131Packing.packing_contradiction K C (delta X) a X.card
    hXsize.1 hXsize.2.2 hXsize.2.1 (by change 8*a < (insert 0 (R ∪ R.image Neg.neg)).card; omega)
    (fun z h => (hC z h).2)
    (fun x hx y hy => Set.mem_toFinset.mpr (H.add_mem (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)))
    (fun z h => (hC z h).1) (Set.mem_toFinset.mpr H.zero_mem) (delta_zero X)
    (delta_add X) (delta_neg X)
  · intro t ⟨g,hg,hgt⟩
    obtain ⟨u,hu,hlo,hhi⟩ := OMA.Olson131Packing.interpolate (delta X) a (delta_zero X)
      (delta_add X) (delta_neg X) R hD (Set.mem_toFinset.mp hg) hgt
    exact ⟨u, Set.mem_toFinset.mpr hu,hlo,hhi⟩
  · exact level_sum H X (fun z h => Set.mem_toFinset.mp (hX h))

end OMA.Olson131Boundary

/- The scalar recurrence in Olson's zero-sum-free estimate. -/

namespace OMA.Olson131Numeric

private def b (s : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => b s i + (min (2 * (b s i + 1)) (s - i) + 3) / 4

private theorem b_step (s i : ℕ) :
    4 * b s i + min (2 * (b s i + 1)) (s - i) ≤ 4 * b s (i + 1) := by
  rw [b]
  omega

private theorem b_mono (s : ℕ) : Monotone (b s) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [b]
  omega

private theorem early_triangle (s : ℕ) (hs : 400 ≤ s) (i : ℕ) (hi : i ≤ s / 20) :
    i * (i + 1) ≤ 2 * b s i := by
  induction i with
  | zero => simp
  | succ i ih =>
    specialize ih (by omega)
    have hstep := b_step s i
    by_cases small : i ≤ 3
    · have h0 : b s 0 = 1 := rfl
      have h1 := b_step s 0
      have h2 := b_step s 1
      have h3 := b_step s 2
      have h4 := b_step s 3
      interval_cases i <;> simp only [Nat.reduceAdd, Nat.reduceMul] at * <;> omega
    · have hsq : 4 * (i + 1) ≤ 2 * (b s i + 1) := by
        nlinarith [Nat.zero_le ((i - 4) * (i + 1)), Nat.sub_add_cancel (show 4 ≤ i by omega)]
      have hlim : 4 * (i + 1) ≤ s - i := by omega
      have hincr : b s i + (i + 1) ≤ b s (i+1) := by omega
      nlinarith

private theorem after_threshold (s j p : ℕ) (hstart : s ≤ 2 * b s j)
    (hjp : j ≤ p) (hps : p ≤ s) :
    (s - j)^2 ≤ 8 * b s p + (s - p)^2 := by
  induction p, hjp using Nat.le_induction with
  | base => omega
  | succ p hp ih =>
    specialize ih (by omega)
    have hm := b_mono s hp
    have hstep := b_step s p
    rw [min_eq_right (by omega)] at hstep
    have he : s - p = (s - (p+1)) + 1 := by omega
    rw [he] at ih hstep
    nlinarith

private theorem large (s p : ℕ) (hs : 400 ≤ s) (hp : p < s) :
    s ^ 2 ≤ 9 * b s p + 2 * (s - p - 1) ^ 2 := by
  let j := s / 20
  have hjs : j ≤ s := by dsimp [j]; omega
  have hj : 20 ≤ j := by dsimp [j]; omega
  have hlo : 20*j ≤ s := by dsimp [j]; omega
  have hhi : s < 20*(j+1) := by dsimp [j]; omega
  have hstart : s ≤ 2 * b s j := by
    have ht := early_triangle s hs j (by rfl)
    nlinarith [Nat.mul_le_mul_right (j+1) hj]
  let r := s - p - 1
  have hr : p + r + 1 = s := by dsimp [r]; omega
  change s ^ 2 ≤ 9 * b s p + 2 * r ^ 2
  by_cases hjp : j ≤ p
  · have hafter := after_threshold s j p hstart hjp hp.le
    have hpr : s - p = r + 1 := by omega
    rw [hpr] at hafter
    have hw : (s-j) + j = s := Nat.sub_add_cancel hjs
    have hlinear : 19*s ≤ 20*(s-j) := by omega
    have hsq := Nat.mul_self_le_mul_self hlinear
    nlinarith [sq_nonneg ((r : ℤ)-2), Nat.mul_self_le_mul_self hs]
  · have hlin : 3*s ≤ 4*r := by omega
    nlinarith [Nat.mul_self_le_mul_self hlin]

private def check (s : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | k + 1, i, y => decide (s^2 ≤ 9*y + 2*(s-i-1)^2) &&
      check s k (i+1) (y + (min (2*(y+1)) (s-i)+3)/4)

private theorem check_sound (s k i : ℕ) (h : check s k i (b s i) = true)
    (p : ℕ) (hl : i ≤ p) (hu : p < i + k) :
    s ^ 2 ≤ 9 * b s p + 2 * (s - p - 1) ^ 2 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases eq_or_lt_of_le hl with rfl | hlt
    · exact h.1
    · exact ih (i+1) h.2 hlt (by omega)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem small_check : ∀ s : Fin 400, check s s 0 1 = true := by decide +kernel

/-- For the recurrence used by the greedy ordering, the accumulated
prefix growth and the doubled tail cover the required quadratic budget. -/
theorem numerical : ∀ s p : ℕ, p < s → s ^ 2 ≤ 9 *
    (Nat.rec (motive := fun _ => ℕ) 1 (fun i y : ℕ =>
      y + (min (2 * (y + 1)) (s - i) + 3) / 4) p) + 2 * (s-p-1)^2 := by
  intro s p hp
  have eq_b : ∀ i : ℕ, Nat.rec (motive := fun _ => ℕ) 1 (fun i y : ℕ =>
      y + (min (2 * (y+1)) (s-i) + 3) / 4) i = b s i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => simp only [b, ih]
  rw [eq_b]
  by_cases hs : 400 ≤ s
  · exact large s p hs hp
  · exact check_sound s s 0 (small_check ⟨s, by omega⟩) p (Nat.zero_le _) (by omega)

end OMA.Olson131Numeric

/- Reduction of the non-dividing-set estimate to cyclic subset sums. -/

namespace OMA.NonDividing131

open Finset Erdos131

/-- The only shared value of the two displayed families of subset sums of
disjoint parts is the sum of the whole first part. This yields the additive
lower bound without the general Kemperman--Scherk theorem. -/
theorem add_card_subsetSum {G : Type*} [AddCommGroup G] [DecidableEq G]
    {P Q : Finset G} (hd : Disjoint P Q)
    (hz : ∀ T ⊆ P ∪ Q, T.Nonempty → ∑ t ∈ T, t ≠ 0) :
    P.subsetSum.card + Q.subsetSum.card ≤ (P ∪ Q).subsetSum.card + 1 := by
  classical
  let a := ∑ x ∈ P, x
  let U := P.subsetSum.erase a
  let V := Q.subsetSum.image (fun y => a + y)
  have hU : U ⊆ (P ∪ Q).subsetSum :=
    (erase_subset _ _).trans (subsetSum_mono subset_union_left)
  have hV : V ⊆ (P ∪ Q).subsetSum := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hy
    exact mem_subsetSum_iff.mpr ⟨P ∪ T, union_subset_union_right hT,
      sum_union (hd.mono_right hT)⟩
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨hne, hzP⟩ := mem_erase.mp hzU
    obtain ⟨W, hW, hsumW⟩ := mem_subsetSum_iff.mp hzP
    obtain ⟨y, hy, hsum⟩ := mem_image.mp hzV
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hy
    have hrem : (P \ W).Nonempty := by
      by_contra! hempty
      have heq := subset_antisymm hW (sdiff_eq_empty_iff_subset.mp hempty)
      exact hne (hsumW.symm.trans (by rw [heq]))
    apply hz ((P \ W) ∪ T) (union_subset_union sdiff_subset hT) (hrem.mono subset_union_left)
    rw [sum_union (hd.mono sdiff_subset hT)]
    change (∑ x ∈ P, x) + ∑ x ∈ T, x = z at hsum
    have heq := sum_sdiff hW (f := id)
    change (∑ x ∈ P \ W, x) + ∑ x ∈ W, x = ∑ x ∈ P, x at heq
    rw [← heq, add_right_comm, hsumW] at hsum
    exact add_right_cancel (hsum.trans (zero_add z).symm)
  have hUV := card_le_card (union_subset hU hV)
  have ha : a ∈ P.subsetSum := mem_subsetSum_iff.mpr ⟨P, Subset.rfl, rfl⟩
  have hc := card_erase_add_one ha
  have hvc : V.card = Q.subsetSum.card := card_image_of_injective _ (add_right_injective a)
  rw [card_union_of_disjoint hdis, hvc] at hUV
  change U.card + 1 = P.subsetSum.card at hc
  omega

/-- A residue outside the subgroup of a set doubles the number of its subset sums. -/
theorem double_card_subsetSum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R : Finset G) (x : G) (hx : x ∉ AddSubgroup.closure (R : Set G)) :
    2 * R.subsetSum.card ≤ (insert x R).subsetSum.card := by
  classical
  let H := AddSubgroup.closure (R : Set G)
  have hsub {y} (hy : y ∈ R.subsetSum) : y ∈ H := by
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hy
    exact H.sum_mem fun t ht => AddSubgroup.subset_closure (hT ht)
  have hnot : x ∉ R := fun h => hx (AddSubgroup.subset_closure h)
  let B := R.subsetSum.image (fun y => x + y)
  have hB : B ⊆ (insert x R).subsetSum := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hz
    exact mem_subsetSum_iff.mpr ⟨insert x T, insert_subset_insert _ hT,
      sum_insert (fun h => hnot (hT h))⟩
  have hd : Disjoint R.subsetSum B := by
    apply Finset.disjoint_left.mpr
    intro y hy hyB
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hyB
    simpa using hx (show x ∈ H by simpa using H.sub_mem (hsub hy) (hsub hz))
  have hbound := card_le_card (union_subset (subsetSum_mono (subset_insert x R)) hB)
  have hc : B.card = R.subsetSum.card := card_image_of_injective _ (add_right_injective x)
  rwa [card_union_of_disjoint hd, hc, ← two_mul] at hbound

private theorem subsetSum_insert_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    {P : Finset G} {x : G} (hx : x ∉ P) :
    (insert x P).subsetSum = P.subsetSum ∪ P.subsetSum.image (fun y => x + y) := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp ha
    by_cases hm : x ∈ T
    · apply mem_union_right
      refine mem_image.mpr ⟨∑ y ∈ T.erase x, y, mem_subsetSum_iff.mpr ⟨_, ?_, rfl⟩, ?_⟩
      · intro y hy
        exact (mem_insert.mp (hT (mem_of_mem_erase hy))).resolve_left (ne_of_mem_erase hy)
      · simpa [add_comm] using sum_erase_add T (fun a => a) hm
    · apply mem_union_left
      exact mem_subsetSum_iff.mpr ⟨T, fun y hy =>
        (mem_insert.mp (hT hy)).resolve_left (fun h => hm (h ▸ hy)), rfl⟩
  · intro ha
    rcases mem_union.mp ha with hp | hi
    · exact subsetSum_mono (subset_insert _ _) hp
    · obtain ⟨z, hz, rfl⟩ := mem_image.mp hi
      obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hz
      exact mem_subsetSum_iff.mpr ⟨insert x T, insert_subset_insert _ hT,
        sum_insert (fun h => hx (hT h))⟩

private abbrev growth131 (s p : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 1 (fun i y : ℕ =>
    y + (min (2 * (y + 1)) (s - i) + 3) / 4) p

/- The finite-group increment isolated in Olson (1975), Lemma 3.1.
Here B lies in the group generated by R and avoids its negatives;
this specializes the lemma without assuming B consists of subset sums. -/
private abbrev boundary131 : Prop := ∀ m : ℕ, 0 < m → ∀ B R : Finset (ZMod m),
    R.Nonempty → (0 : ZMod m) ∈ B →
    (B : Set (ZMod m)) ⊆ AddSubgroup.closure (R : Set (ZMod m)) →
    (∀ r ∈ R, -r ∉ B) → (∀ x ∈ R, ∀ y ∈ R, x + y = 0 → x = y) →
    ∃ x ∈ R, 4 * B.card + min (2 * (B.card + 1)) R.card ≤
      4 * (B ∪ B.image (fun y => x + y)).card

private abbrev numeric131 : Prop := ∀ s p : ℕ, p < s →
    s ^ 2 ≤ 9 * growth131 s p + 2 * (s - p - 1) ^ 2

/-- Follow the greedy arrangement only while the remaining elements generate
the preceding ones. The first pivot that shrinks the generated subgroup
contributes two disjoint translates of all subset sums of the tail. -/
theorem olson_from_boundary (hboundary : boundary131) (hnum : numeric131)
    {m : ℕ} (hm : 0 < m) (S : Finset (ZMod m))
    (hzero : ∀ T ⊆ S, T.Nonempty → ∑ t ∈ T, t ≠ 0) :
    S.card ^ 2 ≤ 9 * (S.subsetSum.card - 1) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases he : S = ∅
    · simp [he]
    have search : ∀ R : Finset (ZMod m), ∀ P : Finset (ZMod m),
        Disjoint P R → P ∪ R = S → R.Nonempty →
        (P : Set (ZMod m)) ⊆ AddSubgroup.closure (R : Set (ZMod m)) →
        growth131 S.card P.card ≤ P.subsetSum.card →
        S.card ^ 2 ≤ 9 * (S.subsetSum.card - 1) := by
      intro R
      induction R using Finset.strongInductionOn with
      | _ R shrinks =>
        intro P hd hpart hr hgen hbudget
        have hsumgen : (P.subsetSum : Set (ZMod m)) ⊆ AddSubgroup.closure (R : Set (ZMod m)) := by
          intro a ha
          obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp ha
          exact AddSubgroup.sum_mem _ (fun t ht => hgen (hT ht))
        have hav : ∀ r ∈ R, -r ∉ P.subsetSum := by
          intro r hr' hrmem
          obtain ⟨T, hT, hsum⟩ := mem_subsetSum_iff.mp hrmem
          have hrT : r ∉ T := fun h => (Finset.disjoint_left.mp hd) (hT h) hr'
          apply hzero (insert r T) (hpart ▸ insert_subset
            (mem_union_right P hr') (hT.trans subset_union_left)) (insert_nonempty _ _)
          rw [sum_insert hrT, hsum, add_neg_cancel]
        have hanti : ∀ x ∈ R, ∀ y ∈ R, x + y = 0 → x = y := by
          intro x hx y hy hsum
          by_contra hxy
          apply hzero {x, y} (hpart ▸ insert_subset (mem_union_right P hx)
            (singleton_subset_iff.mpr (mem_union_right P hy))) (insert_nonempty _ _)
          simpa [hxy] using hsum
        obtain ⟨x, hx, hinc⟩ := hboundary m hm P.subsetSum R hr (by simp) hsumgen hav hanti
        let V := R.erase x
        have hV : V ⊂ R := erase_ssubset hx
        have hxP : x ∉ P := fun h => Finset.disjoint_left.mp hd h hx
        have hins : insert x V = R := insert_erase hx
        have hsum : P.card + R.card = S.card := by rw [← hpart, card_union_of_disjoint hd]
        have hVcard : V.card + 1 = R.card := card_erase_add_one hx
        by_cases hdrop : x ∈ AddSubgroup.closure (V : Set (ZMod m))
        · have hgenV : AddSubgroup.closure (R : Set (ZMod m)) ≤
                AddSubgroup.closure (V : Set (ZMod m)) := by
            apply (AddSubgroup.closure_le _).mpr
            intro a ha
            by_cases h : a = x
            · simpa [h] using hdrop
            · exact AddSubgroup.subset_closure (mem_erase.mpr ⟨h, ha⟩ : a ∈ V)
          have hnewpart : insert x P ∪ V = S := by rw [← hpart, ← hins, insert_union, union_insert]
          have hdnew : Disjoint (insert x P) V := by
            rw [disjoint_insert_left]
            exact ⟨notMem_erase x R, hd.mono_right (erase_subset _ _)⟩
          have hrg : (↑(insert x P) : Set (ZMod m)) ⊆
              AddSubgroup.closure (V : Set (ZMod m)) := by
            intro a ha
            rcases mem_insert.mp ha with rfl | ha
            · exact hdrop
            · exact hgenV (hgen ha)
          have hnonempty : V.Nonempty := by
            by_contra! hv
            rw [hv] at hdrop
            have hx0 : x = 0 := by simpa using hdrop
            exact hav x hx (by simp [hx0])
          apply shrinks V hV (insert x P) hdnew hnewpart hnonempty hrg
          rw [card_insert_of_notMem hxP]
          change growth131 S.card P.card + (min (2 * (growth131 S.card P.card + 1))
            (S.card - P.card) + 3) / 4 ≤ (insert x P).subsetSum.card
          rw [← subsetSum_insert_eq hxP] at hinc
          have hmin : min (2 * (growth131 S.card P.card + 1)) (S.card - P.card) ≤
              min (2 * (P.subsetSum.card + 1)) R.card := by
            apply min_le_min <;> omega
          omega
        · have hvS : V ⊂ S := hV.trans_le (hpart ▸ subset_union_right)
          have hsmall := ih V hvS (fun T hT => hzero T (hT.trans hvS.le))
          have hdbl := double_card_subsetSum V x hdrop
          have hadd := add_card_subsetSum hd (hpart ▸ hzero)
          rw [hins] at hdbl
          rw [hpart] at hadd
          have hpos := card_pos.mpr V.subsetSum_nonempty
          have hposS := card_pos.mpr S.subsetSum_nonempty
          have hnum' := hnum S.card P.card (by have := card_pos.mpr hr; omega)
          have hrnum : S.card - P.card - 1 = V.card := by omega
          rw [hrnum] at hnum'
          omega
    exact search S ∅ (by simp) (by simp) (Finset.nonempty_iff_ne_empty.mpr he)
      (by simp) (by simp [subsetSum])

/-- A non-dividing set, with its maximum deleted, embeds as a zero-sum-free
set in the cyclic group of that order. -/
theorem residues_of_max {A : Finset ℕ} (hne : A.Nonempty) (hnd : NonDividing A) :
    let m := A.max' hne
    let R := (A.erase m).image (fun a : ℕ => (a : ZMod m))
    R.card + 1 = A.card ∧
      ∀ T ⊆ R, T.Nonempty → ∑ t ∈ T, t ≠ 0 := by
  classical
  let m := A.max' hne
  have hm : m ∈ A := A.max'_mem hne
  have hlt {a : ℕ} (ha : a ∈ A.erase m) : a < m := by
    obtain ⟨hneq, hmem⟩ := mem_erase.mp ha
    exact lt_of_le_of_ne (A.le_max' _ hmem) hneq
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod m)) (A.erase m : Set ℕ) := by
    intro a ha b hb hab
    simpa only [ZMod.val_natCast_of_lt (hlt ha), ZMod.val_natCast_of_lt (hlt hb)] using
      congrArg ZMod.val hab
  refine ⟨?_, ?_⟩
  · rw [card_image_of_injOn hinj, card_erase_add_one hm]
  · intro T hT hneT hzero
    obtain ⟨S, hS, rfl⟩ := subset_image_iff.mp hT
    have hneS : S.Nonempty := by simpa using hneT
    rw [sum_image (hinj.mono hS)] at hzero
    exact hnd m hm S hS hneS <| (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hzero)

/-- The ELRSS estimate from Olson's cyclic zero-sum bound; no imported
Erdős conjecture or variant is used. -/
theorem elrss_of_olson
    (hOlson : ∀ m : ℕ, 0 < m → ∀ R : Finset (ZMod m),
      (∀ T ⊆ R, T.Nonempty → ∑ t ∈ T, t ≠ 0) → R.card ^ 2 < 9 * m)
    (N : ℕ) : (F N : ℝ) < 3 * Real.sqrt N + 1 := by
  classical
  obtain ⟨A, hAN, hnd, hA⟩ := exists_card_eq_F N
  by_cases hne : A.Nonempty
  · let m := A.max' hne
    have hm := mem_Icc.mp (hAN (A.max'_mem hne))
    obtain ⟨hc, hz⟩ := residues_of_max hne hnd
    let R := (A.erase m).image (fun a : ℕ => (a : ZMod m))
    have hs : R.card ^ 2 < 9 * N := (hOlson m hm.1 R hz).trans_le (by gcongr; exact hm.2)
    have hs' : (R.card : ℝ) ^ 2 < 9 * (N : ℝ) := by exact_mod_cast hs
    have hc' : (F N : ℝ) = R.card + 1 := by exact_mod_cast (hc.trans hA).symm
    rw [hc']
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity), Real.sqrt_nonneg (N : ℝ)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hA
    simp only [card_empty] at hA
    rw [← hA, Nat.cast_zero]
    positivity

/-- Reduction of Erdős 131 to a one-step group boundary bound and a
one-dimensional numerical recurrence. -/
theorem elrss_of_boundary (hb : boundary131) (hn : numeric131)
    (N : ℕ) : (F N : ℝ) < 3 * Real.sqrt N + 1 := by
  apply elrss_of_olson _ N
  intro m hm R hz
  let _ : NeZero m := ⟨hm.ne'⟩
  have hbound := olson_from_boundary hb hn hm R hz
  have hcard : R.subsetSum.card ≤ m := by simpa [ZMod.card] using card_le_univ R.subsetSum
  have := card_pos.mpr R.subsetSum_nonempty
  omega

end OMA.NonDividing131

theorem OMA.solution : type_of% @Erdos131.erdos_131.variants.elrss :=
  OMA.NonDividing131.elrss_of_boundary OMA.Olson131Boundary.cyclic_boundary
    OMA.Olson131Numeric.numerical
