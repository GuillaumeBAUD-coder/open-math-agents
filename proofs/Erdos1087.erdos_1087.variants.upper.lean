import FormalConjectures.ErdosProblems.«1087»

-- Problem: Erdős Problem 1087 — upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1087.lean:98 (declaration Erdos1087.erdos_1087.variants.upper)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics Finset
open scoped EuclideanGeometry

namespace OMA1087

open Erdos1087

lemma two_circles (P : Finset ℝ²) {c₁ c₂ : ℝ²} (hc : c₁ ≠ c₂) (r₁ r₂ : ℝ) :
    #(P.filter (fun p => dist p c₁ = r₁ ∧ dist p c₂ = r₂)) ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.1 h
  simp only [Finset.mem_filter] at ha hb hc'
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two finrank_euclideanSpace_fin
    hc hab ha.2.1 hb.2.1 hc'.2.1 ha.2.2 hb.2.2 hc'.2.2 with h1 | h1
  · exact hac h1.symm
  · exact hbc h1.symm

lemma card_filter_prod {α β : Type*} (Y : Finset β) (X : Finset α) (q : β → α → Prop)
    [∀ b a, Decidable (q b a)] :
    #((Y ×ˢ X).filter (fun p => q p.1 p.2)) = ∑ y ∈ Y, #(X.filter (fun x => q y x)) := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.card_filter]

lemma kst {α β : Type*} [DecidableEq α] (X : Finset α) (Y : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] (k : ℕ)
    (h : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → #(Y.filter (fun y => R x y ∧ R x' y)) ≤ k) :
    (∑ y ∈ Y, #(X.filter (fun x => R x y))) ^ 2 ≤
      #Y * (∑ y ∈ Y, #(X.filter (fun x => R x y)) + #X * #X * k) := by
  refine (sq_sum_le_card_mul_sum_sq).trans (Nat.mul_le_mul_left _ ?_)
  have key : ∑ y ∈ Y, #(X.filter (fun x => R x y)) ^ 2
      = ∑ x ∈ X, ∑ x' ∈ X, #(Y.filter (fun y => R x y ∧ R x' y)) := by
    simp only [Finset.card_filter, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : R x y <;> by_cases h2 : R x' y <;> simp [h1, h2]
  have hswap : ∑ y ∈ Y, #(X.filter (fun x => R x y)) = ∑ x ∈ X, #(Y.filter (fun y => R x y)) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [key, hswap]
  have hx : ∀ x ∈ X, ∑ x' ∈ X, #(Y.filter (fun y => R x y ∧ R x' y)) ≤
      #(Y.filter (fun y => R x y)) + #X * k := by
    intro x hxX
    rw [← Finset.add_sum_erase X _ hxX]
    refine Nat.add_le_add (le_of_eq (by simp)) ?_
    calc ∑ x' ∈ X.erase x, #(Y.filter (fun y => R x y ∧ R x' y))
        ≤ ∑ x' ∈ X.erase x, k := by
          refine Finset.sum_le_sum (fun x' hx' => ?_)
          exact h x hxX x' (Finset.mem_of_mem_erase hx') (Finset.ne_of_mem_erase hx').symm
      _ ≤ #X * k := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_erase_le)
  calc ∑ x ∈ X, ∑ x' ∈ X, #(Y.filter (fun y => R x y ∧ R x' y))
      ≤ ∑ x ∈ X, (#(Y.filter (fun y => R x y)) + #X * k) := Finset.sum_le_sum hx
    _ = ∑ x ∈ X, #(Y.filter (fun y => R x y)) + #X * #X * k := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_assoc]

lemma arith1 (I n : ℕ) (h : I ^ 2 ≤ n ^ 2 * (I + n * n * (2 * n))) : I ^ 2 ≤ 9 * n ^ 5 := by
  by_contra hc
  push Not at hc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp at h; simp [h] at hc
  have h4 : n ^ 4 ≤ n ^ 5 := Nat.pow_le_pow_right hn (by norm_num)
  have hI : 3 * n ^ 2 < I := by
    have : (3 * n ^ 2) ^ 2 < I ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  nlinarith

lemma arith2 (m n : ℕ) (h : m ^ 2 ≤ n * (m + n * n * 2)) : m ^ 2 ≤ 9 * n ^ 3 := by
  by_contra hc
  push Not at hc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp at h; simp [h] at hc
  have h4 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by norm_num)
  have hm : 3 * n < m := by
    have : (3 * n) ^ 2 < m ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  nlinarith

/-- Isosceles triples `((y, z), x)` with `y ≠ z` and `|xy| = |xz|`. -/
noncomputable def isoS (P : Finset ℝ²) : Finset ((ℝ² × ℝ²) × ℝ²) :=
  (((P ×ˢ P).filter (fun yz => yz.1 ≠ yz.2)) ×ˢ P).filter
    (fun t => dist t.2 t.1.1 = dist t.2 t.1.2)

/-- Pairs of pairs `((z, w), (x, y))` with `|xy| = |zw|`. -/
noncomputable def eqS (P : Finset ℝ²) : Finset ((ℝ² × ℝ²) × (ℝ² × ℝ²)) :=
  ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter (fun t => dist t.2.1 t.2.2 = dist t.1.1 t.1.2)

lemma iso_bound (P : Finset ℝ²) : #(isoS P) ^ 2 ≤ 9 * #P ^ 5 := by
  classical
  apply arith1
  set Y := (P ×ˢ P).filter (fun yz : ℝ² × ℝ² => yz.1 ≠ yz.2) with hY
  have hcard : #(isoS P) = ∑ yz ∈ Y, #(P.filter (fun x => dist x yz.1 = dist x yz.2)) := by
    rw [isoS]
    exact card_filter_prod Y P (fun yz x => dist x yz.1 = dist x yz.2)
  have hYc : #Y ≤ #P ^ 2 := by
    rw [sq, ← Finset.card_product]; exact Finset.card_filter_le _ _
  have hk := kst P Y (fun x yz => dist x yz.1 = dist x yz.2) (2 * #P) (by
    intro x _ x' _ hxx'
    calc #(Y.filter (fun yz => dist x yz.1 = dist x yz.2 ∧ dist x' yz.1 = dist x' yz.2))
        ≤ #((P ×ˢ P).filter (fun yz : ℝ² × ℝ² =>
            dist yz.2 x = dist yz.1 x ∧ dist yz.2 x' = dist yz.1 x')) := by
          refine Finset.card_le_card (fun yz hyz => ?_)
          simp only [hY, Finset.mem_filter] at hyz ⊢
          refine ⟨hyz.1.1, ?_, ?_⟩
          · rw [dist_comm yz.2, dist_comm yz.1]; exact hyz.2.1.symm
          · rw [dist_comm yz.2, dist_comm yz.1]; exact hyz.2.2.symm
      _ = ∑ y ∈ P, #(P.filter (fun z => dist z x = dist y x ∧ dist z x' = dist y x')) :=
          card_filter_prod P P (fun y z => dist z x = dist y x ∧ dist z x' = dist y x')
      _ ≤ ∑ y ∈ P, 2 := Finset.sum_le_sum (fun y _ => two_circles P hxx' _ _)
      _ = 2 * #P := by rw [Finset.sum_const, smul_eq_mul, mul_comm])
  rw [hcard]
  calc _ ≤ #Y * (∑ yz ∈ Y, #(P.filter (fun x => dist x yz.1 = dist x yz.2)) + #P * #P * (2 * #P)) := hk
    _ ≤ #P ^ 2 * (∑ yz ∈ Y, #(P.filter (fun x => dist x yz.1 = dist x yz.2)) + #P * #P * (2 * #P)) :=
        Nat.mul_le_mul_right _ hYc

lemma eq_bound (P : Finset ℝ²) : #(eqS P) ^ 2 ≤ 9 * #P ^ 7 := by
  classical
  have hcard : #(eqS P) = ∑ zw ∈ P ×ˢ P,
      #((P ×ˢ P).filter (fun xy : ℝ² × ℝ² => dist xy.1 xy.2 = dist zw.1 zw.2)) := by
    rw [eqS]
    exact card_filter_prod (P ×ˢ P) (P ×ˢ P)
      (fun zw xy => dist xy.1 xy.2 = dist zw.1 zw.2)
  have hm : ∀ d : ℝ, #((P ×ˢ P).filter (fun xy : ℝ² × ℝ² => dist xy.1 xy.2 = d)) ^ 2
      ≤ 9 * #P ^ 3 := by
    intro d
    apply arith2
    have he : #((P ×ˢ P).filter (fun xy : ℝ² × ℝ² => dist xy.1 xy.2 = d)) =
        ∑ y ∈ P, #(P.filter (fun x => dist y x = d)) :=
      card_filter_prod P P (fun y x => dist y x = d)
    rw [he]
    exact kst P P (fun x y => dist y x = d) 2 (fun x _ x' _ hxx' => two_circles P hxx' d d)
  rw [hcard]
  refine (sq_sum_le_card_mul_sum_sq).trans ?_
  calc #(P ×ˢ P) * ∑ zw ∈ P ×ˢ P,
        #((P ×ˢ P).filter (fun xy : ℝ² × ℝ² => dist xy.1 xy.2 = dist zw.1 zw.2)) ^ 2
      ≤ #(P ×ˢ P) * ∑ zw ∈ P ×ˢ P, 9 * #P ^ 3 :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun zw _ => hm _))
    _ = 9 * #P ^ 7 := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_product]; ring

/-- A repeated distance in a set gives two different pairs at the same distance. -/
lemma exists_pairs {S : Finset ℝ²} (h : HasRepeatedDistance S) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, a ≠ b ∧ c ≠ d ∧ s(a, b) ≠ s(c, d) ∧
      dist a b = dist c d := by
  classical
  by_contra hcon
  push Not at hcon
  apply (lt_irrefl (S.card.choose 2))
  refine lt_of_le_of_lt ?_ h
  rw [← Sym2.card_image_offDiag]
  unfold distinctDistances distanceSet
  let g : Sym2 ℝ² → ℝ := Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro e he
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := he
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨(a, b), hab, by simp [g]⟩
  · intro e₁ he₁ e₂ he₂ heq
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at he₁ he₂
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := he₁
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := he₂
    simp only [Finset.mem_offDiag] at hab hcd
    simp only [g, Function.uncurry_apply_pair, Sym2.lift_mk] at heq
    by_contra hne
    exact hcon a hab.1 b hab.2.1 c hcd.1 d hcd.2.1 hab.2.2 hcd.2.2 hne heq

lemma eq_insert4 {S : Finset ℝ²} (hS : #S = 4) {x y z w : ℝ²} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) (hw : w ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) : ({x, y, z, w} : Finset ℝ²) = S := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  · rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hzw]
    · simp [hyz, hyw]
    · simp [hxy, hxz, hxw]

lemma iso_case {S : Finset ℝ²} (hS : #S = 4) {x y z : ℝ²} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) (hyz : y ≠ z) (hd : dist x y = dist x z) :
    ∃ w ∈ S, ({x, y, z, w} : Finset ℝ²) = S := by
  classical
  have hxy : x ≠ y := by
    rintro rfl
    rw [dist_self] at hd
    exact hyz (dist_eq_zero.1 hd.symm)
  have hxz : x ≠ z := by
    rintro rfl
    rw [dist_self] at hd
    exact hyz (dist_eq_zero.1 hd).symm
  have hlt : #({x, y, z} : Finset ℝ²) < #S := by
    rw [hS]
    exact lt_of_le_of_lt Finset.card_le_three (by norm_num)
  obtain ⟨w, hwS, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  exact ⟨w, hwS, eq_insert4 hS hx hy hz hwS hxy hxz (Ne.symm hw.1) hyz (Ne.symm hw.2.1)
    (Ne.symm hw.2.2)⟩

lemma degenerate_le (P : Finset ℝ²) : degenerateCount P ≤ #(isoS P) * #P + #(eqS P) := by
  classical
  unfold degenerateCount
  let g1 : ((ℝ² × ℝ²) × ℝ²) × ℝ² → Finset ℝ² := fun t => {t.1.2, t.1.1.1, t.1.1.2, t.2}
  let g2 : (ℝ² × ℝ²) × (ℝ² × ℝ²) → Finset ℝ² := fun t => {t.2.1, t.2.2, t.1.1, t.1.2}
  have hsub : (P.powersetCard 4).filter HasRepeatedDistance ⊆
      ((isoS P ×ˢ P).image g1) ∪ ((eqS P).image g2) := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hSP, hS4⟩, hrep⟩ := hS
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hne, hdist⟩ := exists_pairs hrep
    have hiso : ∀ x y z, x ∈ S → y ∈ S → z ∈ S → y ≠ z → dist x y = dist x z →
        S ∈ ((isoS P ×ˢ P).image g1) ∪ ((eqS P).image g2) := by
      intro x y z hx hy hz hyz hxyz
      obtain ⟨w, hw, hSeq⟩ := iso_case hS4 hx hy hz hyz hxyz
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨(((y, z), x), w), ?_, hSeq⟩)
      simp [isoS, hSP hx, hSP hy, hSP hz, hSP hw, hyz, hxyz]
    by_cases hac : a = c
    · subst hac
      have hbd : b ≠ d := by rintro rfl; exact hne rfl
      exact hiso a b d ha hb hd hbd hdist
    by_cases had : a = d
    · subst had
      have hbc : b ≠ c := by rintro rfl; exact hne Sym2.eq_swap
      exact hiso a b c ha hb hc hbc (by rw [hdist, dist_comm])
    by_cases hbc : b = c
    · subst hbc
      exact hiso b a d hb ha hd had (by rw [dist_comm, hdist])
    by_cases hbd : b = d
    · subst hbd
      exact hiso b a c hb ha hc hac (by rw [dist_comm, hdist, dist_comm])
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨((c, d), (a, b)), ?_, ?_⟩)
    · simp [eqS, hSP ha, hSP hb, hSP hc, hSP hd, hdist]
    · exact eq_insert4 hS4 ha hb hc hd hab hac had hbc hbd hcd
  calc #((P.powersetCard 4).filter HasRepeatedDistance)
      ≤ #(((isoS P ×ˢ P).image g1) ∪ ((eqS P).image g2)) := Finset.card_le_card hsub
    _ ≤ #((isoS P ×ˢ P).image g1) + #((eqS P).image g2) := Finset.card_union_le _ _
    _ ≤ #(isoS P ×ˢ P) + #(eqS P) := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = #(isoS P) * #P + #(eqS P) := by rw [Finset.card_product]

lemma degenerate_sq (P : Finset ℝ²) : degenerateCount P ^ 2 ≤ 36 * #P ^ 7 := by
  have h1 := degenerate_le P
  have h2 := iso_bound P
  have h3 := eq_bound P
  set D := degenerateCount P
  set I := #(isoS P)
  set E := #(eqS P)
  set n := #P
  have h4 : (I * n) ^ 2 ≤ 9 * n ^ 7 := by
    calc (I * n) ^ 2 = I ^ 2 * n ^ 2 := by ring
      _ ≤ 9 * n ^ 5 * n ^ 2 := Nat.mul_le_mul_right _ h2
      _ = 9 * n ^ 7 := by ring
  have h5 : D ^ 2 ≤ (I * n + E) ^ 2 := Nat.pow_le_pow_left h1 2
  have h6 : (I * n + E) ^ 2 ≤ 2 * ((I * n) ^ 2 + E ^ 2) := by
    zify
    nlinarith [sq_nonneg ((I : ℤ) * (n : ℤ) - (E : ℤ))]
  omega

theorem f_sq (n : ℕ) : f n ^ 2 ≤ 36 * n ^ 7 := by
  have : f n ≤ Nat.sqrt (36 * n ^ 7) := by
    unfold f
    apply csSup_le'
    rintro m ⟨P, hP, rfl⟩
    rw [Nat.le_sqrt']
    have := degenerate_sq P
    rw [hP] at this
    exact this
  calc f n ^ 2 ≤ Nat.sqrt (36 * n ^ 7) ^ 2 := Nat.pow_le_pow_left this 2
    _ ≤ 36 * n ^ 7 := Nat.sqrt_le' _

end OMA1087

theorem OMA.solution : type_of% @Erdos1087.erdos_1087.variants.upper := by
  refine Asymptotics.IsBigO.of_bound 6 (Filter.Eventually.of_forall (fun n => ?_))
  have h := OMA1087.f_sq n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow : ((n : ℝ) ^ (7 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    norm_num
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (7 / 2 : ℝ) := Real.rpow_nonneg hn _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hpos]
  have hR : ((Erdos1087.f n : ℕ) : ℝ) ^ 2 ≤ (6 * (n : ℝ) ^ (7 / 2 : ℝ)) ^ 2 := by
    rw [mul_pow, hpow]
    exact_mod_cast (by norm_num [h] : Erdos1087.f n ^ 2 ≤ 36 * n ^ 7)
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num)).1 hR
