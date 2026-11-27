import OMAReductions.R_Erdos107_erdos_107_R1
import Mathlib.Tactic

/-!
# Proof of H2 for Erdos Problem 107 (Erdos-Szekeres 1960 lower bound)
-/

open Finset EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace Erdos107H2Helper

/- ## Part 1: Planar general-position ordering and 4-point convex independence -/

private lemma planar_coordinates (X : Finset ℝ²) :
    ∃ x y : ℝ² →ₗ[ℝ] ℝ, Set.InjOn x (X : Set ℝ²) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  let bad := (X ×ˢ X).image fun uv : ℝ² × ℝ² =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : ℝ² →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : ℝ² →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : ℝ²) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

private lemma orient_ne_in_image (X : Finset ℝ²)
    (hX : NonTrilinear (X : Set ℝ²))
    (x y : ℝ² →ₗ[ℝ] ℝ) (hjoint : ∀ p q, x p = x q → y p = y q → p = q) :
    ∀ a ∈ X.image (x.prod y), ∀ b ∈ X.image (x.prod y), ∀ c ∈ X.image (x.prod y),
      a.1 < b.1 → b.1 < c.1 → (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0 := by
  intro u hu v hv w hw hab hbc he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hw
  change x a < x b at hab
  change x b < x c at hbc
  change (x b - x a) * (y c - y b) - (y b - y a) * (x c - x b) = 0 at he
  have hnab : a ≠ b := fun h => hab.ne (congrArg x h)
  have hnbc : b ≠ c := fun h => hbc.ne (congrArg x h)
  have hnac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg x h)
  apply hX ha hb hc hnab hnbc hnac
  let r := (x b - x a) / (x c - x b)
  have hden := sub_ne_zero.mpr hbc.ne'
  have hxb : x b - x a = r * (x c - x b) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hden]
  have hyb : y b - y a = r * (y c - y b) := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    linarith only [he]
  have hdiff : b - a = r • (c - b) := by
    apply hjoint
    · simpa only [map_sub, map_smul, smul_eq_mul] using hxb
    · simpa only [map_sub, map_smul, smul_eq_mul] using hyb
  apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set ℝ²) by simp)).mpr
  refine ⟨c - b, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨-r, ?_⟩
    change _ = (-r) • (c - b) + b
    rw [neg_smul, ← hdiff]
    abel
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

private lemma enumerate_gp {N : ℕ} (P : Finset ℝ²) (size : P.card = N)
    (gp : NonTrilinear (P : Set ℝ²)) :
    ∃ (x y : ℝ² →ₗ[ℝ] ℝ) (p : Fin N ↪ ℝ²), (∀ i, p i ∈ P) ∧
      StrictMono (fun i => x (p i)) ∧
      ∀ i j k, i < j → j < k →
        (x (p j) - x (p i)) * (y (p k) - y (p i)) -
        (y (p j) - y (p i)) * (x (p k) - x (p i)) ≠ 0 := by
  obtain ⟨x, y, hx, hxy⟩ := planar_coordinates P
  let keys := P.image x
  have num : keys.card = N := (card_image_of_injOn hx).trans size
  let key := keys.orderIsoOfFin num
  have pre (i : Fin N) : ∃ v ∈ P, x v = (key i).val := mem_image.mp (key i).property
  choose pt member rep using pre
  have mono : StrictMono (fun i => x (pt i)) := by
    intro i j lt
    dsimp only
    rw [rep, rep]
    exact key.strictMono lt
  let p : Fin N ↪ ℝ² := ⟨pt, fun i j eq => mono.injective (congrArg x eq)⟩
  refine ⟨x, y, p, member, mono, ?_⟩
  intro i j k hij hjk
  have nonzero := orient_ne_in_image P gp x y hxy
    _ (mem_image_of_mem (x.prod y) (member i)) _ (mem_image_of_mem (x.prod y) (member j))
    _ (mem_image_of_mem (x.prod y) (member k)) (mono hij) (mono hjk)
  change (x (p j) - x (p i)) * (y (p k) - y (p j)) -
    (y (p j) - y (p i)) * (x (p k) - x (p j)) ≠ 0 at nonzero
  intro h
  apply nonzero
  linarith only [h]

private lemma boundary_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E →ₗ[ℝ] ℝ) (S : Set E) (u v : E) (hne : u ≠ v) (tie : F u = F v)
    (above : ∀ t ∈ S, t ≠ u → t ≠ v → F u < F t) :
    u ∉ convexHull ℝ (S \ {u}) := by
  let T := {t : E | F u < F t ∨ t = v}
  have cv : Convex ℝ T := by
    intro p hp q hq α β hα hβ hsum
    change F u < F p ∨ p = v at hp
    change F u < F q ∨ q = v at hq
    change F u < F (α • p + β • q) ∨ α • p + β • q = v
    rcases eq_or_lt_of_le hα with he | hα'
    · have ht : β = 1 := by linarith
      simpa [← he, ht] using hq
    rcases eq_or_lt_of_le hβ with he | hβ'
    · have ht : α = 1 := by linarith
      simpa [← he, ht] using hp
    have iden : α * F u + β * F u = F u := by rw [← add_mul, hsum, one_mul]
    simp only [map_add, map_smul, smul_eq_mul]
    rcases hp with hp | rfl <;> rcases hq with hq | rfl
    · exact Or.inl (by linarith [mul_lt_mul_of_pos_left hp hα', mul_lt_mul_of_pos_left hq hβ'])
    · exact Or.inl (by rw [← tie]; linarith [mul_lt_mul_of_pos_left hp hα'])
    · exact Or.inl (by rw [← tie]; linarith [mul_lt_mul_of_pos_left hq hβ'])
    · exact Or.inr (by rw [← add_smul, hsum, one_smul])
  have sub : S \ {u} ⊆ T := by
    intro t ht
    by_cases h : t = v
    · exact Or.inr h
    · exact Or.inl (above t ht.1 ht.2 h)
  intro h
  exact (convexHull_min sub cv h).elim (lt_irrefl _) hne

private lemma edge_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y : E →ₗ[ℝ] ℝ) (D : E → E → E → ℝ)
    (deq : ∀ a b c, D a b c = (x b - x a) * (y c - y a) - (y b - y a) * (x c - x a))
    (S : Set E) (u v p q : E)
    (cover : ∀ t ∈ S, t = u ∨ t = v ∨ t = p ∨ t = q) (hne : u ≠ v)
    (hp : D u v p ≠ 0) (hq : D u v q ≠ 0)
    (same : 0 < D u v p ↔ 0 < D u v q) :
    u ∉ convexHull ℝ (S \ {u}) ∧ v ∉ convexHull ℝ (S \ {v}) := by
  let L : E →ₗ[ℝ] ℝ := (x v - x u) • y - (y v - y u) • x
  have val (t : E) : L t - L u = D u v t := by simp [L, deq]; ring
  have tie : L u = L v := by have h := val v; simp [deq] at h; linarith
  have oneSide : ∃ F : E →ₗ[ℝ] ℝ, F u = F v ∧ F u < F p ∧ F u < F q := by
    by_cases pos : 0 < D u v p
    · exact ⟨L, tie, by linarith [val p], by linarith [val q, same.mp pos]⟩
    · have hn := lt_of_le_of_ne (le_of_not_gt pos) hp
      have hn' := lt_of_le_of_ne (le_of_not_gt (fun h => pos (same.mpr h))) hq
      refine ⟨-L, by simp [tie], ?_, ?_⟩
      · simp only [LinearMap.neg_apply, neg_lt_neg_iff]
        linarith [val p]
      · simp only [LinearMap.neg_apply, neg_lt_neg_iff]
        linarith [val q]
  obtain ⟨F, he, hp', hq'⟩ := oneSide
  have side (t : E) (ht : t ∈ S) (nu : t ≠ u) (nv : t ≠ v) : F u < F t := by
    rcases cover t ht with h | h | h | h
    · exact (nu h).elim
    · exact (nv h).elim
    · simpa only [h] using hp'
    · simpa only [h] using hq'
  exact ⟨boundary_extreme F S u v hne he side,
    boundary_extreme F S v u hne.symm he.symm (fun t ht nv nu => he ▸ side t ht nu nv)⟩

private lemma convex_of_signs (x y : ℝ² →ₗ[ℝ] ℝ) (D : ℝ² → ℝ² → ℝ² → ℝ)
    (deq : ∀ a b c, D a b c = (x b - x a) * (y c - y a) - (y b - y a) * (x c - x a))
    (a b c d : ℝ²) (hab : a ≠ b) (hcd : c ≠ d)
    (hA : D a b c ≠ 0) (hB : D a b d ≠ 0)
    (hC : D a c d ≠ 0) (hE : D b c d ≠ 0)
    (left : 0 < D a b c ↔ 0 < D a b d)
    (right : 0 < D a c d ↔ 0 < D b c d) :
    ConvexIndep ({a, b, c, d} : Set ℝ²) := by
  let S : Set ℝ² := {a, b, c, d}
  have cover (t : ℝ²) (ht : t ∈ S) : t = a ∨ t = b ∨ t = c ∨ t = d := by simpa [S] using ht
  have ab := edge_extreme x y D deq S a b c d cover hab hA hB left
  have cyc (t : ℝ²) : D c d t = D t c d := by simp only [deq]; ring
  have cd := edge_extreme x y D deq S c d a b
    (fun t ht => by rcases cover t ht with h | h | h | h <;> tauto)
    hcd (by rwa [cyc]) (by rwa [cyc]) (by simpa only [cyc] using right)
  intro t ht
  rcases cover t ht with rfl | rfl | rfl | rfl
  exacts [ab.1, ab.2, cd.1, cd.2]

private lemma convexIndep_of_four_large (S : Finset ℝ²) (large : 4 ≤ S.card)
    (four : ∀ Q ⊆ S, Q.card = 4 → ConvexIndep (Q : Set ℝ²)) :
    ConvexIndep (S : Set ℝ²) := by
  intro p hp hull
  rw [convexHull_eq_union] at hull
  simp only [Set.mem_iUnion, exists_prop] at hull
  obtain ⟨T, sub, indep, contains⟩ := hull
  have bound : T.card ≤ 3 := by
    have h := indep.card_le_finrank_succ
    have d := (vectorSpan ℝ (Set.range ((↑) : T → ℝ²))).finrank_le
    rw [finrank_euclideanSpace_fin] at d
    simp only [Fintype.card_coe] at h
    omega
  have inside : insert p T ⊆ S := insert_subset hp (fun x hx => (sub hx).1)
  obtain ⟨Q, hQ, hQS, size⟩ := exists_subsuperset_card_eq inside
    ((card_insert_le p T).trans (by omega : T.card + 1 ≤ 4)) large
  apply four Q hQS size p (hQ (mem_insert_self ..))
  apply convexHull_mono _ contains
  intro y hy
  exact ⟨hQ (mem_insert_of_mem hy), (sub hy).2⟩

private lemma convexIndep_of_four (S : Finset ℝ²) (gp : NonTrilinear (S : Set ℝ²))
    (four : ∀ Q ⊆ S, Q.card = 4 → ConvexIndep (Q : Set ℝ²)) :
    ConvexIndep (S : Set ℝ²) := by
  by_cases large : 4 ≤ S.card
  · exact convexIndep_of_four_large S large four
  intro p hp hull
  let T := S.erase p
  have few : T.card ≤ 2 := by dsimp [T]; rw [card_erase_of_mem hp]; omega
  have inHull : p ∈ convexHull ℝ (T : Set ℝ²) := by simpa only [T, coe_erase] using hull
  have outside : p ∉ T := notMem_erase _ _
  by_cases empty : T.card = 0
  · rw [card_eq_zero.mp empty] at inHull
    simp only [coe_empty, convexHull_empty, Set.mem_empty_iff_false] at inHull
  by_cases one : T.card = 1
  · obtain ⟨b, eq⟩ := card_eq_one.mp one
    rw [eq, coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at inHull
    exact outside (by simp [eq, inHull])
  obtain ⟨b, c, bc, eq⟩ := card_eq_two.mp (show T.card = 2 by omega)
  have hb : b ∈ T := by simp [eq]
  have hc : c ∈ T := by simp [eq]
  have pb : p ≠ b := fun e => outside (e ▸ hb)
  have pc : p ≠ c := fun e => outside (e ▸ hc)
  have general := gp hp (mem_of_mem_erase hb) (mem_of_mem_erase hc) pb bc pc
  apply general
  have span : p ∈ affineSpan ℝ ({b, c} : Set ℝ²) := by
    apply convexHull_subset_affineSpan
    simpa only [eq, coe_insert, coe_singleton] using inHull
  exact (collinear_insert_iff_of_mem_affineSpan span).mpr (collinear_pair ℝ b c)

private lemma polygon_of_ordered_four {N n : ℕ} {P : Set ℝ²} (p : Fin N ↪ ℝ²)
    (T : Finset (Fin N)) (size : T.card = n) (inside : ∀ i ∈ T, p i ∈ P)
    (gp : NonTrilinear P)
    (four : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a < b → b < c → c < d →
      ConvexIndep ({p a, p b, p c, p d} : Set ℝ²)) : HasConvexNGon n P := by
  refine ⟨T.map p, by simpa only [card_map] using size, ?_,
    convexIndep_of_four (T.map p) (Set.Triplewise.mono ?_ gp) ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    exact inside i hi
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    exact inside i hi
  · intro Q sub hQ
    let R := T.filter (fun i => p i ∈ Q)
    have imageR : R.map p = Q := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
        exact (mem_filter.mp hi).2
      · intro hx
        obtain ⟨i, hi, rfl⟩ := mem_map.mp (sub hx)
        exact mem_map.mpr ⟨i, mem_filter.mpr ⟨hi, hx⟩, rfl⟩
    have sizeR : R.card = 4 := (card_map (s := R) p).symm.trans ((congrArg card imageR).trans hQ)
    let e := R.orderEmbOfFin sizeR
    have member (i : Fin 4) : e i ∈ T := (mem_filter.mp (R.orderEmbOfFin_mem sizeR i)).1
    have corners := four _ (member 0) _ (member 1) _ (member 2) _ (member 3)
      (e.strictMono (by decide : (0 : Fin 4) < 1)) (e.strictMono (by decide : (1 : Fin 4) < 2))
      (e.strictMono (by decide : (2 : Fin 4) < 3))
    have listR : R = {e 0, e 1, e 2, e 3} := by
      calc
        R = univ.map e.toEmbedding := (R.map_orderEmbOfFin_univ sizeR).symm
        _ = _ := by
          rw [show (univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
          simp
    have points : (Q : Set ℝ²) = {p (e 0), p (e 1), p (e 2), p (e 3)} := by
      calc
        (Q : Set ℝ²) = (R.map p : Set ℝ²) := congrArg (fun U : Finset ℝ² => (U : Set ℝ²)) imageR.symm
        _ = (({e 0, e 1, e 2, e 3} : Finset (Fin N)).map p : Set ℝ²) :=
          congrArg (fun U : Finset (Fin N) => (U.map p : Set ℝ²)) listR
        _ = _ := by simp
    exact points.symm ▸ corners

/- ## Part 2: 3-uniform Ramsey theorem and nonemptiness of `Erdos107.cardSet n` -/

private lemma ramsey2 :
    ∀ s a b : ℕ, a + b = s →
      ∃ R : ℕ, ∀ (S : Finset ℕ) (f : ℕ → ℕ → Bool), R ≤ S.card →
        (∃ A ⊆ S, A.card = a ∧ ∀ x ∈ A, ∀ y ∈ A, x < y → f x y = true) ∨
        (∃ B ⊆ S, B.card = b ∧ ∀ x ∈ B, ∀ y ∈ B, x < y → f x y = false) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro a b hs
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨0, fun S _ _ => Or.inl ⟨∅, Finset.empty_subset S, rfl, by simp⟩⟩
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact ⟨0, fun S _ _ => Or.inr ⟨∅, Finset.empty_subset S, rfl, by simp⟩⟩
    obtain ⟨R1, hR1⟩ := ih (a - 1 + b) (by omega) (a - 1) b rfl
    obtain ⟨R2, hR2⟩ := ih (a + (b - 1)) (by omega) a (b - 1) rfl
    refine ⟨R1 + R2 + 1, fun S f hS => ?_⟩
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    let v : ℕ := S.min' hSne
    have hv_mem : v ∈ S := S.min'_mem hSne
    let S' : Finset ℕ := S.erase v
    have hv_lt : ∀ u ∈ S', v < u := fun u hu =>
      lt_of_le_of_ne (S.min'_le u (Finset.mem_of_mem_erase hu)) (Finset.ne_of_mem_erase hu).symm
    let St : Finset ℕ := S'.filter (fun u => f v u = true)
    let Sf : Finset ℕ := S'.filter (fun u => ¬ f v u = true)
    have hcard_split : St.card + Sf.card = S.card - 1 := by
      have h1 : St.card + Sf.card = S'.card := by
        have hs := Finset.sum_filter_add_sum_filter_not S' (fun u => f v u = true) (fun _ => 1)
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
        exact hs
      have h2 : S'.card + 1 = S.card := Finset.card_erase_add_one hv_mem
      omega
    rcases Nat.le_or_le R1 St.card with hSt | hSt
    · rcases hR1 St f hSt with ⟨A', hA'sub, hA'card, hA'mono⟩ | ⟨B, hBsub, hBcard, hBmono⟩
      · left
        have hA'S' : A' ⊆ S' := hA'sub.trans (Finset.filter_subset _ _)
        have hv_not : v ∉ A' := fun hvA => (Finset.ne_of_mem_erase (hA'S' hvA)) rfl
        refine ⟨insert v A', Finset.insert_subset hv_mem (hA'S'.trans (S.erase_subset v)),
          by rw [Finset.card_insert_of_notMem hv_not, hA'card]; omega, ?_⟩
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_irrefl _ hxy).elim
          · exact (Finset.mem_filter.mp (hA'sub hy')).2
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_asymm hxy (hv_lt x (hA'S' hx'))).elim
          · exact hA'mono x hx' y hy' hxy
      · exact Or.inr ⟨B, hBsub.trans ((Finset.filter_subset _ _).trans (S.erase_subset v)),
          hBcard, hBmono⟩
    · have hSf : R2 ≤ Sf.card := by omega
      rcases hR2 Sf f hSf with ⟨A, hAsub, hAcard, hAmono⟩ | ⟨B', hB'sub, hB'card, hB'mono⟩
      · exact Or.inl ⟨A, hAsub.trans ((Finset.filter_subset _ _).trans (S.erase_subset v)),
          hAcard, hAmono⟩
      · right
        have hB'S' : B' ⊆ S' := hB'sub.trans (Finset.filter_subset _ _)
        have hv_not : v ∉ B' := fun hvB => (Finset.ne_of_mem_erase (hB'S' hvB)) rfl
        refine ⟨insert v B', Finset.insert_subset hv_mem (hB'S'.trans (S.erase_subset v)),
          by rw [Finset.card_insert_of_notMem hv_not, hB'card]; omega, ?_⟩
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_irrefl _ hxy).elim
          · exact Bool.eq_false_iff.mpr (Finset.mem_filter.mp (hB'sub hy')).2
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_asymm hxy (hv_lt x (hB'S' hx'))).elim
          · exact hB'mono x hx' y hy' hxy

private lemma ramsey3 :
    ∀ s a b : ℕ, a + b = s →
      ∃ R : ℕ, ∀ (S : Finset ℕ) (g : ℕ → ℕ → ℕ → Bool), R ≤ S.card →
        (∃ A ⊆ S, A.card = a ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x < y → y < z → g x y z = true) ∨
        (∃ B ⊆ S, B.card = b ∧ ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x < y → y < z → g x y z = false) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro a b hs
    by_cases ha2 : a ≤ 2
    · refine ⟨a, fun S _ hS => ?_⟩
      obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hS
      refine Or.inl ⟨A, hAS, hAcard, fun x hx y hy z hz hxy hyz => ?_⟩
      exfalso
      have hsub : ({x, y, z} : Finset ℕ) ⊆ A := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({x, y, z} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
      have hle := Finset.card_le_card hsub
      omega
    by_cases hb2 : b ≤ 2
    · refine ⟨b, fun S _ hS => ?_⟩
      obtain ⟨B, hBS, hBcard⟩ := Finset.exists_subset_card_eq hS
      refine Or.inr ⟨B, hBS, hBcard, fun x hx y hy z hz hxy hyz => ?_⟩
      exfalso
      have hsub : ({x, y, z} : Finset ℕ) ⊆ B := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({x, y, z} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
      have hle := Finset.card_le_card hsub
      omega
    obtain ⟨M1, hM1⟩ := ih (a - 1 + b) (by omega) (a - 1) b rfl
    obtain ⟨M2, hM2⟩ := ih (a + (b - 1)) (by omega) a (b - 1) rfl
    obtain ⟨M, hM⟩ := ramsey2 (M1 + M2) M1 M2 rfl
    refine ⟨M + 1, fun S g hS => ?_⟩
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    let v : ℕ := S.min' hSne
    have hv_mem : v ∈ S := S.min'_mem hSne
    let S' : Finset ℕ := S.erase v
    have hv_lt : ∀ u ∈ S', v < u := fun u hu =>
      lt_of_le_of_ne (S.min'_le u (Finset.mem_of_mem_erase hu)) (Finset.ne_of_mem_erase hu).symm
    have hS'card : M ≤ S'.card := by
      have h2 : S'.card + 1 = S.card := Finset.card_erase_add_one hv_mem
      omega
    rcases hM S' (fun x y => g v x y) hS'card with
      ⟨U, hUS', hUcard, hUt⟩ | ⟨U, hUS', hUcard, hUf⟩
    · rcases hM1 U g (by omega) with ⟨A', hA'U, hA'card, hA'⟩ | ⟨B, hBU, hBcard, hB⟩
      · left
        have hA'S' : A' ⊆ S' := hA'U.trans hUS'
        have hv_not : v ∉ A' := fun hvA => (Finset.ne_of_mem_erase (hA'S' hvA)) rfl
        refine ⟨insert v A', Finset.insert_subset hv_mem (hA'S'.trans (S.erase_subset v)),
          by rw [Finset.card_insert_of_notMem hv_not, hA'card]; omega, ?_⟩
        intro x hx y hy z hz hxy hyz
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_irrefl _ hxy).elim
          · rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact (lt_irrefl _ (hxy.trans hyz)).elim
            · exact hUt y (hA'U hy') z (hA'U hz') hyz
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_asymm hxy (hv_lt x (hA'S' hx'))).elim
          · rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact (lt_asymm (hxy.trans hyz) (hv_lt x (hA'S' hx'))).elim
            · exact hA' x hx' y hy' z hz' hxy hyz
      · exact Or.inr ⟨B, (hBU.trans hUS').trans (S.erase_subset v), hBcard, hB⟩
    · rcases hM2 U g (by omega) with ⟨A, hAU, hAcard, hA⟩ | ⟨B', hB'U, hB'card, hB'⟩
      · exact Or.inl ⟨A, (hAU.trans hUS').trans (S.erase_subset v), hAcard, hA⟩
      · right
        have hB'S' : B' ⊆ S' := hB'U.trans hUS'
        have hv_not : v ∉ B' := fun hvB => (Finset.ne_of_mem_erase (hB'S' hvB)) rfl
        refine ⟨insert v B', Finset.insert_subset hv_mem (hB'S'.trans (S.erase_subset v)),
          by rw [Finset.card_insert_of_notMem hv_not, hB'card]; omega, ?_⟩
        intro x hx y hy z hz hxy hyz
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_irrefl _ hxy).elim
          · rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact (lt_irrefl _ (hxy.trans hyz)).elim
            · exact hUf y (hB'U hy') z (hB'U hz') hyz
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact (lt_asymm hxy (hv_lt x (hB'S' hx'))).elim
          · rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact (lt_asymm (hxy.trans hyz) (hv_lt x (hB'S' hx'))).elim
            · exact hB' x hx' y hy' z hz' hxy hyz

private lemma cardSet_nonempty {n : ℕ} (_hn : 3 ≤ n) : (Erdos107.cardSet n).Nonempty := by
  obtain ⟨R, hR⟩ := ramsey3 (n + n) n n rfl
  refine ⟨R, fun P hP gp => ?_⟩
  obtain ⟨x, y, p, mem, _mon, nonzero⟩ := enumerate_gp P hP gp
  let D (a b c : ℝ²) : ℝ := (x b - x a) * (y c - y a) - (y b - y a) * (x c - x a)
  let g (i j k : ℕ) : Bool :=
    if h : i < R ∧ j < R ∧ k < R then
      decide (0 < D (p ⟨i, h.1⟩) (p ⟨j, h.2.1⟩) (p ⟨k, h.2.2⟩))
    else false
  have liftSub (W : Finset ℕ) (hWR : W ⊆ Finset.range R) (hWcard : W.card = n) (val : Bool)
      (hmono : ∀ u ∈ W, ∀ v ∈ W, ∀ w ∈ W, u < v → v < w → g u v w = val) :
      HasConvexNGon n (P : Set ℝ²) := by
    let T : Finset (Fin R) := Finset.univ.filter (fun i : Fin R => i.val ∈ W)
    have hT_img : T.image Fin.val = W := by
      ext u
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hu
        exact ⟨⟨u, Finset.mem_range.mp (hWR hu)⟩, hu, rfl⟩
    have hT_card : T.card = n := by
      have hc := Finset.card_image_of_injective T Fin.val_injective
      rw [hT_img] at hc
      exact hc.symm.trans hWcard
    refine polygon_of_ordered_four p T hT_card (fun i _ => mem i) gp ?_
    intro a ha b hb c hc d hd hab hbc hcd
    have haW : a.val ∈ W := (Finset.mem_filter.mp ha).2
    have hbW : b.val ∈ W := (Finset.mem_filter.mp hb).2
    have hcW : c.val ∈ W := (Finset.mem_filter.mp hc).2
    have hdW : d.val ∈ W := (Finset.mem_filter.mp hd).2
    have hcol : ∀ u v w : Fin R, u.val ∈ W → v.val ∈ W → w.val ∈ W → u < v → v < w →
        decide (0 < D (p u) (p v) (p w)) = val := by
      intro u v w huW hvW hwW huv hvw
      have hg := hmono u.val huW v.val hvW w.val hwW huv hvw
      have hlt : u.val < R ∧ v.val < R ∧ w.val < R := ⟨u.isLt, v.isLt, w.isLt⟩
      simpa only [g, dif_pos hlt] using hg
    have h1 := hcol a b c haW hbW hcW hab hbc
    have h2 := hcol a b d haW hbW hdW hab (hbc.trans hcd)
    have h3 := hcol a c d haW hcW hdW (hab.trans hbc) hcd
    have h4 := hcol b c d hbW hcW hdW hbc hcd
    exact convex_of_signs x y D (fun _ _ _ => rfl) (p a) (p b) (p c) (p d)
      (p.injective.ne hab.ne) (p.injective.ne hcd.ne)
      (nonzero a b c hab hbc) (nonzero a b d hab (hbc.trans hcd))
      (nonzero a c d (hab.trans hbc) hcd) (nonzero b c d hbc hcd)
      (decide_eq_decide.mp (h1.trans h2.symm))
      (decide_eq_decide.mp (h3.trans h4.symm))
  rcases hR (Finset.range R) g (by simp) with ⟨A, hA, hAc, hAm⟩ | ⟨B, hB, hBc, hBm⟩
  · exact liftSub A hA hAc true hAm
  · exact liftSub B hB hBc false hBm

/- ## Part 3: Converse 4-point lemma via Cramer identity -/

private noncomputable def orient2d (a b c : ℝ²) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

private lemma between_sign {u v w a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (eq : c * v = a * u + b * w) (same : 0 < u ↔ 0 < w) : 0 < u ↔ 0 < v := by
  by_cases h : 0 < u
  · have hw := same.mp h
    have hv : 0 < v := by
      by_contra! hv
      linarith [mul_nonpos_of_nonneg_of_nonpos hc.le hv, mul_pos ha h, mul_pos hb hw]
    simp [h, hv]
  · have hw : w ≤ 0 := le_of_not_gt fun hw => h (same.mpr hw)
    have hv : ¬ 0 < v := by
      intro hv
      linarith [mul_pos hc hv, mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h),
        mul_nonpos_of_nonneg_of_nonpos hb.le hw]
    simp [h, hv]

private lemma signotope2d (a b c d : ℝ²)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0) :
    let A := 0 < orient2d a b c
    let B := 0 < orient2d a b d
    let C := 0 < orient2d a c d
    let E := 0 < orient2d b c d
    ((A ↔ C) → (A ↔ B)) ∧ ((A ↔ E) → (A ↔ B)) ∧
      ((A ↔ E) → (A ↔ C)) ∧ ((B ↔ E) → (B ↔ C)) := by
  dsimp only
  refine ⟨between_sign (a := d 0 - a 0) (b := b 0 - a 0) (c := c 0 - a 0)
      (by linarith) (by linarith) (by linarith) ?_,
    between_sign (a := d 0 - b 0) (b := b 0 - a 0) (c := c 0 - b 0)
      (by linarith) (by linarith) (by linarith) ?_,
    between_sign (a := d 0 - c 0) (b := c 0 - a 0) (c := c 0 - b 0)
      (by linarith) (by linarith) (by linarith) ?_,
    between_sign (a := d 0 - c 0) (b := d 0 - a 0) (c := d 0 - b 0)
      (by linarith) (by linarith) (by linarith) ?_⟩
  all_goals simp only [orient2d]; ring

private lemma mem_convexHull_of_pos_cramer {S : Set ℝ²} {p q₁ q₂ q₃ : ℝ²}
    (hq₁ : q₁ ∈ S \ {p}) (hq₂ : q₂ ∈ S \ {p}) (hq₃ : q₃ ∈ S \ {p})
    {w₀ w₁ w₂ w₃ : ℝ} (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₃ : 0 < w₃)
    (hsum : w₁ + w₂ + w₃ = w₀)
    (hc0 : w₀ * p 0 = w₁ * q₁ 0 + w₂ * q₂ 0 + w₃ * q₃ 0)
    (hc1 : w₀ * p 1 = w₁ * q₁ 1 + w₂ * q₂ 1 + w₃ * q₃ 1) :
    p ∈ convexHull ℝ (S \ {p}) := by
  have hK : Convex ℝ (convexHull ℝ (S \ {p})) := convex_convexHull ℝ (S \ {p})
  have hm₂₃_mem : (w₂ / (w₂ + w₃)) • q₂ + (w₃ / (w₂ + w₃)) • q₃ ∈ convexHull ℝ (S \ {p}) := by
    refine hK (subset_convexHull ℝ _ hq₂) (subset_convexHull ℝ _ hq₃)
      (by positivity) (by positivity) ?_
    have h23 : w₂ + w₃ ≠ 0 := by linarith
    field_simp
  have hp_comb_mem :
      (w₁ / w₀) • q₁ + ((w₂ + w₃) / w₀) • ((w₂ / (w₂ + w₃)) • q₂ + (w₃ / (w₂ + w₃)) • q₃) ∈
        convexHull ℝ (S \ {p}) := by
    refine hK (subset_convexHull ℝ _ hq₁) hm₂₃_mem (by positivity) (by positivity) ?_
    have h0 : w₀ ≠ 0 := hw₀.ne'
    field_simp
    linarith
  suffices hp_eq :
      p = (w₁ / w₀) • q₁ + ((w₂ + w₃) / w₀) • ((w₂ / (w₂ + w₃)) • q₂ + (w₃ / (w₂ + w₃)) • q₃) by
    rwa [← hp_eq] at hp_comb_mem
  have h0 : w₀ ≠ 0 := hw₀.ne'
  have h23 : w₂ + w₃ ≠ 0 := by linarith
  apply PiLp.ext
  intro i
  fin_cases i
  · change p 0 = (w₁ / w₀) * q₁ 0 + ((w₂ + w₃) / w₀) * ((w₂ / (w₂ + w₃)) * q₂ 0 + (w₃ / (w₂ + w₃)) * q₃ 0)
    field_simp
    linarith
  · change p 1 = (w₁ / w₀) * q₁ 1 + ((w₂ + w₃) / w₀) * ((w₂ / (w₂ + w₃)) * q₂ 1 + (w₃ / (w₂ + w₃)) * q₃ 1)
    field_simp
    linarith

private lemma signs_of_convexIndep {S : Set ℝ²} (hS : ConvexIndep S)
    {a b c d : ℝ²} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (hA : orient2d a b c ≠ 0) (hB : orient2d a b d ≠ 0)
    (hC : orient2d a c d ≠ 0) (hE : orient2d b c d ≠ 0) :
    (0 < orient2d a b c ↔ 0 < orient2d a b d) ∧
    (0 < orient2d a c d ↔ 0 < orient2d b c d) := by
  let d₀ := orient2d b c d
  let d₁ := orient2d a c d
  let d₂ := orient2d a b d
  let d₃ := orient2d a b c
  have hsum_id : d₀ - d₁ + d₂ - d₃ = 0 := by
    simp only [d₀, d₁, d₂, d₃, orient2d]; ring
  have hvec0 : d₀ * a 0 - d₁ * b 0 + d₂ * c 0 - d₃ * d 0 = 0 := by
    simp only [d₀, d₁, d₂, d₃, orient2d]; ring
  have hvec1 : d₀ * a 1 - d₁ * b 1 + d₂ * c 1 - d₃ * d 1 = 0 := by
    simp only [d₀, d₁, d₂, d₃, orient2d]; ring
  have hsig := signotope2d a b c d hab hbc hcd
  change ((0 < d₃ ↔ 0 < d₁) → (0 < d₃ ↔ 0 < d₂)) ∧
    ((0 < d₃ ↔ 0 < d₀) → (0 < d₃ ↔ 0 < d₂)) ∧
    ((0 < d₃ ↔ 0 < d₀) → (0 < d₃ ↔ 0 < d₁)) ∧
    ((0 < d₂ ↔ 0 < d₀) → (0 < d₂ ↔ 0 < d₁)) at hsig
  have hne_ab : a ≠ b := fun h => hab.ne (congrArg (fun p : ℝ² => p 0) h)
  have hne_ac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg (fun p : ℝ² => p 0) h)
  have hne_ad : a ≠ d := fun h => ((hab.trans hbc).trans hcd).ne (congrArg (fun p : ℝ² => p 0) h)
  have hne_bc : b ≠ c := fun h => hbc.ne (congrArg (fun p : ℝ² => p 0) h)
  have hne_bd : b ≠ d := fun h => (hbc.trans hcd).ne (congrArg (fun p : ℝ² => p 0) h)
  have hne_cd : c ≠ d := fun h => hcd.ne (congrArg (fun p : ℝ² => p 0) h)
  have hd₀_nz : d₀ ≠ 0 := hE
  have hd₁_nz : d₁ ≠ 0 := hC
  have hd₂_nz : d₂ ≠ 0 := hB
  have hd₃_nz : d₃ ≠ 0 := hA
  have hleft : 0 < d₃ ↔ 0 < d₂ := by
    by_contra hdiff
    by_cases h3 : 0 < d₃
    · have h2_not : ¬ 0 < d₂ := fun h2 => hdiff (iff_of_true h3 h2)
      have h1_not : ¬ 0 < d₁ := fun h1 => h2_not ((hsig.1 (iff_of_true h3 h1)).mp h3)
      have h0_not : ¬ 0 < d₀ := fun h0 => h2_not ((hsig.2.1 (iff_of_true h3 h0)).mp h3)
      have hd₂_neg : d₂ < 0 := lt_of_le_of_ne (le_of_not_gt h2_not) hd₂_nz
      have hd₁_neg : d₁ < 0 := lt_of_le_of_ne (le_of_not_gt h1_not) hd₁_nz
      have hd₀_neg : d₀ < 0 := lt_of_le_of_ne (le_of_not_gt h0_not) hd₀_nz
      exact hS b hb (mem_convexHull_of_pos_cramer
        ⟨ha, hne_ab⟩ ⟨hc, hne_bc.symm⟩ ⟨hd, hne_bd.symm⟩
        (w₀ := -d₁) (w₁ := -d₀) (w₂ := -d₂) (w₃ := d₃)
        (by linarith) (by linarith) (by linarith) h3
        (by linarith) (by linarith) (by linarith))
    · have h2 : 0 < d₂ := by
        by_contra h2_not
        exact hdiff (iff_of_false h3 h2_not)
      have h1 : 0 < d₁ := by
        by_contra h1_not
        exact h3 ((hsig.1 (iff_of_false h3 h1_not)).mpr h2)
      have h0 : 0 < d₀ := by
        by_contra h0_not
        exact h3 ((hsig.2.1 (iff_of_false h3 h0_not)).mpr h2)
      have hd₃_neg : d₃ < 0 := lt_of_le_of_ne (le_of_not_gt h3) hd₃_nz
      exact hS b hb (mem_convexHull_of_pos_cramer
        ⟨ha, hne_ab⟩ ⟨hc, hne_bc.symm⟩ ⟨hd, hne_bd.symm⟩
        (w₀ := d₁) (w₁ := d₀) (w₂ := d₂) (w₃ := -d₃)
        h1 h0 h2 (by linarith)
        (by linarith) (by linarith) (by linarith))
  refine ⟨hleft, ?_⟩
  by_contra hright
  by_cases h2 : 0 < d₂
  · have h3 : 0 < d₃ := hleft.mpr h2
    have h0_not : ¬ 0 < d₀ := by
      intro h0
      have h1 : 0 < d₁ := (hsig.2.2.2 (iff_of_true h2 h0)).mp h2
      exact hright (iff_of_true h1 h0)
    have h1 : 0 < d₁ := by
      by_contra h1_not
      exact hright (iff_of_false h1_not h0_not)
    have hd₀_neg : d₀ < 0 := lt_of_le_of_ne (le_of_not_gt h0_not) hd₀_nz
    exact hS c hc (mem_convexHull_of_pos_cramer
      ⟨ha, hne_ac⟩ ⟨hb, hne_bc⟩ ⟨hd, hne_cd.symm⟩
      (w₀ := d₂) (w₁ := -d₀) (w₂ := d₁) (w₃ := d₃)
      h2 (by linarith) h1 h3
      (by linarith) (by linarith) (by linarith))
  · have h3_not : ¬ 0 < d₃ := fun h3 => h2 (hleft.mp h3)
    have h0 : 0 < d₀ := by
      by_contra h0_not
      have h1_not : ¬ 0 < d₁ := fun h1 => h2 ((hsig.2.2.2 (iff_of_false h2 h0_not)).mpr h1)
      exact hright (iff_of_false h1_not h0_not)
    have h1_not : ¬ 0 < d₁ := fun h1 => hright (iff_of_true h1 h0)
    have hd₂_neg : d₂ < 0 := lt_of_le_of_ne (le_of_not_gt h2) hd₂_nz
    have hd₁_neg : d₁ < 0 := lt_of_le_of_ne (le_of_not_gt h1_not) hd₁_nz
    have hd₃_neg : d₃ < 0 := lt_of_le_of_ne (le_of_not_gt h3_not) hd₃_nz
    exact hS c hc (mem_convexHull_of_pos_cramer
      ⟨ha, hne_ac⟩ ⟨hb, hne_bc⟩ ⟨hd, hne_cd.symm⟩
      (w₀ := -d₂) (w₁ := d₀) (w₂ := -d₁) (w₃ := -d₃)
      (by linarith) h0 (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith))

/- ## Part 4: Explicit `2 ^ m` point construction and exact 4-line sign law -/

private noncomputable def xIn {m : ℕ} (S : Finset (Fin m)) : ℝ :=
  ∑ i ∈ S, (4 : ℝ) ^ (i : ℕ)

private noncomputable def dyIn {m : ℕ} (S : Finset (Fin m)) : ℝ :=
  ∑ i ∈ S, (16 : ℝ) ^ (i : ℕ)

private noncomputable def esM (m : ℕ) : ℝ :=
  (64 : ℝ) ^ (m + 2)

private noncomputable def esX {m : ℕ} (S : Finset (Fin m)) : ℝ :=
  (S.card : ℝ) * esM m + xIn S

private noncomputable def esY {m : ℕ} (S : Finset (Fin m)) : ℝ :=
  -((S.card : ℝ) ^ 2) * (esM m) ^ 2 + dyIn S

private noncomputable def esPt {m : ℕ} (S : Finset (Fin m)) : ℝ² :=
  !₂[esX S, esY S]

private lemma esPt_zero {m : ℕ} (S : Finset (Fin m)) : esPt S 0 = esX S := by
  simp [esPt]

private lemma esPt_one {m : ℕ} (S : Finset (Fin m)) : esPt S 1 = esY S := by
  simp [esPt]

private def diffSet {m : ℕ} (A B : Finset (Fin m)) : Finset (Fin m) :=
  (A \ B) ∪ (B \ A)

private lemma diffSet_nonempty {m : ℕ} {A B : Finset (Fin m)} (hne : A ≠ B) :
    (diffSet A B).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  apply hne
  ext u
  have hu : u ∉ diffSet A B := by simp [hemp]
  simp only [diffSet, Finset.mem_union, Finset.mem_sdiff] at hu
  tauto

private def maxDiff {m : ℕ} {A B : Finset (Fin m)} (hne : A ≠ B) : Fin m :=
  (diffSet A B).max' (diffSet_nonempty hne)

private lemma maxDiff_mem_iff {m : ℕ} {A B : Finset (Fin m)} (hne : A ≠ B) :
    (maxDiff hne ∈ A ∧ maxDiff hne ∉ B) ∨ (maxDiff hne ∉ A ∧ maxDiff hne ∈ B) := by
  have hm := (diffSet A B).max'_mem (diffSet_nonempty hne)
  change maxDiff hne ∈ diffSet A B at hm
  simp only [diffSet, Finset.mem_union, Finset.mem_sdiff] at hm
  tauto

private lemma eq_above_maxDiff {m : ℕ} {A B : Finset (Fin m)} (hne : A ≠ B)
    {u : Fin m} (hu : maxDiff hne < u) : u ∈ A ↔ u ∈ B := by
  have hnot : u ∉ diffSet A B := by
    intro hmem
    exact not_le_of_gt hu ((diffSet A B).le_max' u hmem)
  simp only [diffSet, Finset.mem_union, Finset.mem_sdiff] at hnot
  tauto

private lemma geom_sum_range_eq (b : ℝ) (k : ℕ) :
    (b - 1) * ∑ j ∈ Finset.range k, b ^ j = b ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private lemma fin_geom_sum_le {m : ℕ} (b : ℝ) (hb : 2 ≤ b) (k : ℕ) (T : Finset (Fin m))
    (hT : ∀ u ∈ T, (u : ℕ) < k) :
    0 ≤ ∑ u ∈ T, b ^ (u : ℕ) ∧ ∑ u ∈ T, b ^ (u : ℕ) ≤ (b ^ k - 1) / (b - 1) := by
  have hb0 : 0 ≤ b := by linarith
  have hb1 : 0 < b - 1 := by linarith
  refine ⟨Finset.sum_nonneg (fun u _ => pow_nonneg hb0 _), ?_⟩
  have hsub : T.image Fin.val ⊆ Finset.range k := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hT u hu)
  have himg : ∑ u ∈ T, b ^ (u : ℕ) = ∑ j ∈ T.image Fin.val, b ^ j :=
    (Finset.sum_image (fun _ _ _ _ h => Fin.ext h)).symm
  rw [himg, le_div_iff₀ hb1, mul_comm]
  calc
    (b - 1) * ∑ j ∈ T.image Fin.val, b ^ j
      ≤ (b - 1) * ∑ j ∈ Finset.range k, b ^ j :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hb0 _)) hb1.le
    _ = b ^ k - 1 := geom_sum_range_eq b k

private lemma sum_diff_at_maxDiff {m : ℕ} {A B : Finset (Fin m)} (hne : A ≠ B) (f : Fin m → ℝ)
    (hiA : maxDiff hne ∉ A) (hiB : maxDiff hne ∈ B) :
    ∑ u ∈ B, f u - ∑ u ∈ A, f u =
      f (maxDiff hne) +
        (∑ u ∈ B.filter (fun u => u < maxDiff hne), f u -
         ∑ u ∈ A.filter (fun u => u < maxDiff hne), f u) := by
  let i := maxDiff hne
  have splitSet (S : Finset (Fin m)) :
      ∑ u ∈ S, f u =
        (∑ u ∈ S.filter (fun u => u < i), f u) +
        ((∑ u ∈ (S.filter (fun u => ¬ u < i)).filter (fun u => u = i), f u) +
         (∑ u ∈ (S.filter (fun u => ¬ u < i)).filter (fun u => ¬ u = i), f u)) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun u => u < i) f]
    congr 1
    exact (Finset.sum_filter_add_sum_filter_not (S.filter (fun u => ¬ u < i)) (fun u => u = i) f).symm
  have hgt_eq :
      (B.filter (fun u => ¬ u < i)).filter (fun u => ¬ u = i) =
      (A.filter (fun u => ¬ u < i)).filter (fun u => ¬ u = i) := by
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨huB, hnlt⟩, hne_i⟩
      have hgt : i < u := lt_of_le_of_ne (not_lt.mp hnlt) (Ne.symm hne_i)
      exact ⟨⟨(eq_above_maxDiff hne hgt).mpr huB, hnlt⟩, hne_i⟩
    · rintro ⟨⟨huA, hnlt⟩, hne_i⟩
      have hgt : i < u := lt_of_le_of_ne (not_lt.mp hnlt) (Ne.symm hne_i)
      exact ⟨⟨(eq_above_maxDiff hne hgt).mp huA, hnlt⟩, hne_i⟩
  have hBeq : (B.filter (fun u => ¬ u < i)).filter (fun u => u = i) = {i} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · rintro rfl; exact ⟨⟨hiB, lt_irrefl i⟩, rfl⟩
  have hAeq : (A.filter (fun u => ¬ u < i)).filter (fun u => u = i) = ∅ := by
    ext u
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨huA, _⟩, rfl⟩
    exact hiA huA
  rw [splitSet B, splitSet A, hgt_eq, hBeq, hAeq, Finset.sum_singleton, Finset.sum_empty]
  ring

private lemma xIn_dyIn_diff_bounds {m : ℕ} {A B : Finset (Fin m)} (hne : A ≠ B)
    (hiA : maxDiff hne ∉ A) (hiB : maxDiff hne ∈ B) :
    let i : ℕ := (maxDiff hne : ℕ)
    ((2 / 3 : ℝ) * (4 : ℝ) ^ i < xIn B - xIn A ∧ xIn B - xIn A < (4 / 3 : ℝ) * (4 : ℝ) ^ i) ∧
    ((14 / 15 : ℝ) * (16 : ℝ) ^ i < dyIn B - dyIn A ∧
      dyIn B - dyIn A < (16 / 15 : ℝ) * (16 : ℝ) ^ i) := by
  intro i
  have hx_eq := sum_diff_at_maxDiff hne (fun u => (4 : ℝ) ^ (u : ℕ)) hiA hiB
  have hy_eq := sum_diff_at_maxDiff hne (fun u => (16 : ℝ) ^ (u : ℕ)) hiA hiB
  have hlt_mem (S : Finset (Fin m)) : ∀ u ∈ S.filter (fun u => u < maxDiff hne), (u : ℕ) < i :=
    fun u hu => (Finset.mem_filter.mp hu).2
  obtain ⟨hxB0, hxB1⟩ := fin_geom_sum_le 4 (by norm_num) i _ (hlt_mem B)
  obtain ⟨hxA0, hxA1⟩ := fin_geom_sum_le 4 (by norm_num) i _ (hlt_mem A)
  obtain ⟨hyB0, hyB1⟩ := fin_geom_sum_le 16 (by norm_num) i _ (hlt_mem B)
  obtain ⟨hyA0, hyA1⟩ := fin_geom_sum_le 16 (by norm_num) i _ (hlt_mem A)
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ i := by positivity
  have h16pos : (0 : ℝ) < (16 : ℝ) ^ i := by positivity
  change ((2 / 3 : ℝ) * (4 : ℝ) ^ i < xIn B - xIn A ∧ xIn B - xIn A < (4 / 3 : ℝ) * (4 : ℝ) ^ i) ∧
    ((14 / 15 : ℝ) * (16 : ℝ) ^ i < dyIn B - dyIn A ∧ dyIn B - dyIn A < (16 / 15 : ℝ) * (16 : ℝ) ^ i)
  unfold xIn dyIn
  rw [hx_eq, hy_eq]
  change ((2 / 3 : ℝ) * (4 : ℝ) ^ i < (4 : ℝ) ^ i + _ ∧ (4 : ℝ) ^ i + _ < (4 / 3 : ℝ) * (4 : ℝ) ^ i) ∧
    ((14 / 15 : ℝ) * (16 : ℝ) ^ i < (16 : ℝ) ^ i + _ ∧ (16 : ℝ) ^ i + _ < (16 / 15 : ℝ) * (16 : ℝ) ^ i)
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private lemma xIn_dyIn_global_bounds {m : ℕ} (S : Finset (Fin m)) :
    (0 ≤ xIn S ∧ xIn S < (4 : ℝ) ^ m) ∧ (0 ≤ dyIn S ∧ dyIn S < (16 : ℝ) ^ m) := by
  obtain ⟨hx0, hx1⟩ := fin_geom_sum_le 4 (by norm_num) m S (fun u _ => u.isLt)
  obtain ⟨hy0, hy1⟩ := fin_geom_sum_le 16 (by norm_num) m S (fun u _ => u.isLt)
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have h16pos : (0 : ℝ) < (16 : ℝ) ^ m := by positivity
  unfold xIn dyIn
  exact ⟨⟨hx0, by linarith⟩, ⟨hy0, by linarith⟩⟩

private lemma esM_large (m : ℕ) :
    (4 : ℝ) ^ m ≤ (16 : ℝ) ^ m ∧
    (2 * (m : ℝ) + 2) * (16 : ℝ) ^ m < esM m / 2 ∧
    (16 : ℝ) ^ m < esM m ∧
    4096 ≤ esM m := by
  have hm_pow : m + 1 ≤ 2 ^ m := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hm_4 : (m : ℝ) + 1 ≤ (4 : ℝ) ^ m := by
    have h1 : ((m + 1 : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hm_pow
    have h2 : (2 : ℝ) ^ m ≤ (4 : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    push_cast at h1
    linarith
  have h4_16 : (4 : ℝ) ^ m ≤ (16 : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have h1_64 : (1 : ℝ) ≤ (64 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have h16_pos : (0 : ℝ) < (16 : ℝ) ^ m := by positivity
  unfold esM
  have h64 : (4 : ℝ) ^ m * (16 : ℝ) ^ m = (64 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  have h64_m2 : (64 : ℝ) ^ (m + 2) = 4096 * (64 : ℝ) ^ m := by
    rw [pow_add]
    ring
  have hprod_le : (2 * (m : ℝ) + 2) * (16 : ℝ) ^ m ≤ 2 * (64 : ℝ) ^ m := by
    calc
      (2 * (m : ℝ) + 2) * (16 : ℝ) ^ m
        ≤ (2 * (4 : ℝ) ^ m) * (16 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right (by linarith) h16_pos.le
      _ = 2 * ((4 : ℝ) ^ m * (16 : ℝ) ^ m) := by ring
      _ = 2 * (64 : ℝ) ^ m := by rw [h64]
  have h16_le_64 : (16 : ℝ) ^ m ≤ (64 : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  exact ⟨h4_16, by linarith, by linarith, by linarith⟩

private lemma maxDiff_congr {m : ℕ} {A₁ B₁ A₂ B₂ : Finset (Fin m)}
    (hA : A₁ = A₂) (hB : B₁ = B₂) (h1 : A₁ ≠ B₁) (h2 : A₂ ≠ B₂) :
    maxDiff h1 = maxDiff h2 := by
  subst hA
  subst hB
  rfl

private lemma maxDiff_symm {m : ℕ} {A B : Finset (Fin m)} (hne : A ≠ B) :
    maxDiff (Ne.symm hne) = maxDiff hne := by
  have hd : diffSet B A = diffSet A B := Finset.union_comm _ _
  simp only [maxDiff, hd]

private lemma xIn_injective {m : ℕ} : Function.Injective (xIn (m := m)) := by
  intro A B heq
  by_contra hne
  rcases maxDiff_mem_iff hne with ⟨hiA, hiB⟩ | ⟨hiA, hiB⟩
  · have hiB' : maxDiff (Ne.symm hne) ∉ B := by rwa [maxDiff_symm]
    have hiA' : maxDiff (Ne.symm hne) ∈ A := by rwa [maxDiff_symm]
    have hpos := (xIn_dyIn_diff_bounds (Ne.symm hne) hiB' hiA').1.1
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (maxDiff (Ne.symm hne) : ℕ) := by positivity
    linarith
  · have hpos := (xIn_dyIn_diff_bounds hne hiA hiB).1.1
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (maxDiff hne : ℕ) := by positivity
    linarith

private lemma esX_lt_of_card_lt {m : ℕ} {A B : Finset (Fin m)} (hcard : A.card < B.card) :
    esX A < esX B := by
  have hcardR : (A.card : ℝ) + 1 ≤ (B.card : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hcard
  obtain ⟨⟨_, hxA⟩, _⟩ := xIn_dyIn_global_bounds A
  obtain ⟨⟨hxB0, _⟩, _⟩ := xIn_dyIn_global_bounds B
  obtain ⟨h4_16, _, h16_M, _⟩ := esM_large m
  have hM_pos : 0 < esM m := by linarith [show (0 : ℝ) < (16 : ℝ) ^ m by positivity]
  unfold esX
  nlinarith

private lemma esX_injective {m : ℕ} : Function.Injective (esX (m := m)) := by
  intro A B heq
  rcases lt_trichotomy A.card B.card with hlt | hcard_eq | hgt
  · exact (ne_of_lt (esX_lt_of_card_lt hlt) heq).elim
  · apply xIn_injective
    unfold esX at heq
    rw [hcard_eq] at heq
    linarith
  · exact (ne_of_gt (esX_lt_of_card_lt hgt) heq).elim

private lemma esPt_injective {m : ℕ} : Function.Injective (esPt (m := m)) := by
  intro A B heq
  apply esX_injective
  have h0 := congrArg (fun p : ℝ² => p 0) heq
  simpa only [esPt_zero] using h0

private lemma esX_lt_cases {m : ℕ} {A B : Finset (Fin m)} (hlt : esX A < esX B) :
    ∃ hne : A ≠ B,
      A.card < B.card ∨ (A.card = B.card ∧ maxDiff hne ∉ A ∧ maxDiff hne ∈ B) := by
  have hne : A ≠ B := fun h => hlt.ne (congrArg esX h)
  refine ⟨hne, ?_⟩
  rcases lt_trichotomy A.card B.card with hcard_lt | hcard_eq | hcard_gt
  · exact Or.inl hcard_lt
  · right
    refine ⟨hcard_eq, ?_⟩
    have hx_lt : xIn A < xIn B := by
      unfold esX at hlt
      rw [hcard_eq] at hlt
      linarith
    rcases maxDiff_mem_iff hne with ⟨hiA, hiB⟩ | ⟨hiA, hiB⟩
    · exfalso
      have hiB' : maxDiff (Ne.symm hne) ∉ B := by rwa [maxDiff_symm]
      have hiA' : maxDiff (Ne.symm hne) ∈ A := by rwa [maxDiff_symm]
      have hpos := (xIn_dyIn_diff_bounds (Ne.symm hne) hiB' hiA').1.1
      have h4 : (0 : ℝ) < (4 : ℝ) ^ (maxDiff (Ne.symm hne) : ℕ) := by positivity
      linarith
    · exact ⟨hiA, hiB⟩
  · exact (lt_asymm hlt (esX_lt_of_card_lt hcard_gt)).elim

private lemma orient_case4_lt_lt {m : ℕ} {A B C : Finset (Fin m)}
    (hAB : esX A < esX B) (hBC : esX B < esX C)
    (hcardAB : A.card < B.card) (hcardBC : B.card < C.card) :
    (esX B - esX A) * (esY C - esY B) - (esY B - esY A) * (esX C - esX B) < 0 := by
  obtain ⟨h4_16, hM_bound, h16_M, h4096_M⟩ := esM_large m
  have h16_pos : (0 : ℝ) < (16 : ℝ) ^ m := by positivity
  let M : ℝ := esM m
  have hM_pos : 0 < M := by dsimp [M]; linarith
  let dx₁ : ℝ := esX B - esX A
  let dy₁ : ℝ := esY B - esY A
  let dx₂ : ℝ := esX C - esX B
  let dy₂ : ℝ := esY C - esY B
  have hdx₁ : 0 < dx₁ := sub_pos.mpr hAB
  have hdx₂ : 0 < dx₂ := sub_pos.mpr hBC
  let d₁ : ℝ := (B.card : ℝ) - (A.card : ℝ)
  let s₁ : ℝ := (B.card : ℝ) + (A.card : ℝ)
  let d₂ : ℝ := (C.card : ℝ) - (B.card : ℝ)
  let s₂ : ℝ := (C.card : ℝ) + (B.card : ℝ)
  have hd₁ : 1 ≤ d₁ := by
    have : (A.card : ℝ) + 1 ≤ (B.card : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hcardAB
    dsimp [d₁]; linarith
  have hd₂ : 1 ≤ d₂ := by
    have : (B.card : ℝ) + 1 ≤ (C.card : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hcardBC
    dsimp [d₂]; linarith
  have hs₂_ge_s₁ : s₁ + 2 ≤ s₂ := by
    have : (A.card : ℝ) + 2 ≤ (C.card : ℝ) := by
      exact_mod_cast (show A.card + 2 ≤ C.card by omega)
    dsimp [s₁, s₂]; linarith
  have hs₂_le : s₂ ≤ 2 * (m : ℝ) := by
    have hcardC_le : C.card ≤ m := by
      have := Finset.card_le_univ C
      simpa using this
    have hB_le : (B.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show B.card ≤ m by omega)
    have hC_le : (C.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcardC_le
    dsimp [s₂]; linarith
  have hs₁_pos : 1 ≤ s₁ := by
    have : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
    dsimp [s₁]; linarith
  obtain ⟨⟨hxA0, hxA1⟩, ⟨hyA0, hyA1⟩⟩ := xIn_dyIn_global_bounds A
  obtain ⟨⟨hxB0, hxB1⟩, ⟨hyB0, hyB1⟩⟩ := xIn_dyIn_global_bounds B
  obtain ⟨⟨hxC0, hxC1⟩, ⟨hyC0, hyC1⟩⟩ := xIn_dyIn_global_bounds C
  have hdx₁_lo : d₁ * M - (16 : ℝ) ^ m < dx₁ := by dsimp [dx₁, esX, d₁, M]; linarith
  have hdx₂_hi : dx₂ < d₂ * M + (16 : ℝ) ^ m := by dsimp [dx₂, esX, d₂, M]; linarith
  have hdy₁_hi : -dy₁ < d₁ * s₁ * M ^ 2 + (16 : ℝ) ^ m := by
    have hsq : -((B.card : ℝ) ^ 2) * M ^ 2 - -((A.card : ℝ) ^ 2) * M ^ 2 = -(d₁ * s₁ * M ^ 2) := by
      dsimp [d₁, s₁]; ring
    dsimp [dy₁, esY, M]
    linarith
  have hdy₂_lo : d₂ * s₂ * M ^ 2 - (16 : ℝ) ^ m < -dy₂ := by
    have hsq : -((C.card : ℝ) ^ 2) * M ^ 2 - -((B.card : ℝ) ^ 2) * M ^ 2 = -(d₂ * s₂ * M ^ 2) := by
      dsimp [d₂, s₂]; ring
    dsimp [dy₂, esY, M]
    linarith
  have h16_lt_16M : (16 : ℝ) ^ m < (16 : ℝ) ^ m * M :=
    lt_mul_of_one_lt_right h16_pos (by dsimp [M]; linarith)
  have hM_gap : (2 * (m : ℝ) + 2) * ((16 : ℝ) ^ m * M) < (1 / 2) * M ^ 2 := by
    have hm := mul_lt_mul_of_pos_right hM_bound hM_pos
    dsimp [M] at hm ⊢
    linarith [show esM m / 2 * esM m = (1 / 2) * (esM m) ^ 2 by ring,
      show (2 * (m : ℝ) + 2) * (16 : ℝ) ^ m * esM m = (2 * (m : ℝ) + 2) * ((16 : ℝ) ^ m * esM m) by ring]
  have hsl₁ : -dy₁ < (s₁ + 1 / 2) * M * dx₁ := by
    have hle1 : (s₁ + 1 / 2) * ((16 : ℝ) ^ m * M) ≤ (2 * (m : ℝ) + 1) * ((16 : ℝ) ^ m * M) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_pos h16_pos hM_pos).le
    have hd1M : (1 / 2) * M ^ 2 ≤ (1 / 2) * d₁ * M ^ 2 := by
      have hM2 : 0 ≤ (1 / 2 : ℝ) * M ^ 2 := by positivity
      calc (1 / 2) * M ^ 2 = 1 * ((1 / 2) * M ^ 2) := by ring
        _ ≤ d₁ * ((1 / 2) * M ^ 2) := mul_le_mul_of_nonneg_right hd₁ hM2
        _ = (1 / 2) * d₁ * M ^ 2 := by ring
    have hstep1 : d₁ * s₁ * M ^ 2 + (16 : ℝ) ^ m < (s₁ + 1 / 2) * M * (d₁ * M - (16 : ℝ) ^ m) := by
      have hexp : (s₁ + 1 / 2) * M * (d₁ * M - (16 : ℝ) ^ m) =
          d₁ * s₁ * M ^ 2 + (1 / 2) * d₁ * M ^ 2 - (s₁ + 1 / 2) * ((16 : ℝ) ^ m * M) := by ring
      linarith
    have hpos_c1 : 0 < (s₁ + 1 / 2) * M := mul_pos (by linarith) hM_pos
    exact hdy₁_hi.trans (hstep1.trans (mul_lt_mul_of_pos_left hdx₁_lo hpos_c1))
  have hsl₂ : (s₂ - 1 / 2) * M * dx₂ < -dy₂ := by
    have hle2 : (s₂ - 1 / 2) * ((16 : ℝ) ^ m * M) ≤ (2 * (m : ℝ) + 1) * ((16 : ℝ) ^ m * M) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_pos h16_pos hM_pos).le
    have hd2M : (1 / 2) * M ^ 2 ≤ (1 / 2) * d₂ * M ^ 2 := by
      have hM2 : 0 ≤ (1 / 2 : ℝ) * M ^ 2 := by positivity
      calc (1 / 2) * M ^ 2 = 1 * ((1 / 2) * M ^ 2) := by ring
        _ ≤ d₂ * ((1 / 2) * M ^ 2) := mul_le_mul_of_nonneg_right hd₂ hM2
        _ = (1 / 2) * d₂ * M ^ 2 := by ring
    have hstep2 : (s₂ - 1 / 2) * M * (d₂ * M + (16 : ℝ) ^ m) < d₂ * s₂ * M ^ 2 - (16 : ℝ) ^ m := by
      have hexp : (s₂ - 1 / 2) * M * (d₂ * M + (16 : ℝ) ^ m) =
          d₂ * s₂ * M ^ 2 - (1 / 2) * d₂ * M ^ 2 + (s₂ - 1 / 2) * ((16 : ℝ) ^ m * M) := by ring
      linarith
    have hpos_c2 : 0 < (s₂ - 1 / 2) * M := mul_pos (by linarith) hM_pos
    exact (mul_lt_mul_of_pos_left hdx₂_hi hpos_c2).trans (hstep2.trans hdy₂_lo)
  have hsep : (s₁ + 1 / 2) * M < (s₂ - 1 / 2) * M := mul_lt_mul_of_pos_right (by linarith) hM_pos
  have hprod1 : (-dy₁) * dx₂ < ((s₁ + 1 / 2) * M * dx₁) * dx₂ := mul_lt_mul_of_pos_right hsl₁ hdx₂
  have hprod2 : ((s₁ + 1 / 2) * M * dx₁) * dx₂ < ((s₂ - 1 / 2) * M * dx₂) * dx₁ := by
    calc ((s₁ + 1 / 2) * M * dx₁) * dx₂
      _ = ((s₁ + 1 / 2) * M) * (dx₁ * dx₂) := by ring
      _ < ((s₂ - 1 / 2) * M) * (dx₁ * dx₂) := mul_lt_mul_of_pos_right hsep (mul_pos hdx₁ hdx₂)
      _ = ((s₂ - 1 / 2) * M * dx₂) * dx₁ := by ring
  have hprod3 : ((s₂ - 1 / 2) * M * dx₂) * dx₁ < (-dy₂) * dx₁ := mul_lt_mul_of_pos_right hsl₂ hdx₁
  linarith

private lemma orient_case1_eq_eq {m : ℕ} {A B C : Finset (Fin m)}
    (hAB : esX A < esX B) (hBC : esX B < esX C)
    (hcardAB_eq : A.card = B.card) (hcardBC_eq : B.card = C.card)
    (hneAB : A ≠ B) (hneBC : B ≠ C)
    (hiA : maxDiff hneAB ∉ A) (hiB : maxDiff hneAB ∈ B)
    (hjB : maxDiff hneBC ∉ B) (hjC : maxDiff hneBC ∈ C) :
    let dx₁ := esX B - esX A
    let dy₁ := esY B - esY A
    let dx₂ := esX C - esX B
    let dy₂ := esY C - esY B
    dx₁ * dy₂ - dy₁ * dx₂ ≠ 0 ∧
    (0 < dx₁ * dy₂ - dy₁ * dx₂ ↔ maxDiff hneAB < maxDiff hneBC) := by
  intro dx₁ dy₁ dx₂ dy₂
  have hdx₁ : 0 < dx₁ := sub_pos.mpr hAB
  have hdx₂ : 0 < dx₂ := sub_pos.mpr hBC
  let i := maxDiff hneAB
  let j := maxDiff hneBC
  have hij_ne : i ≠ j := by
    intro hij
    dsimp [i, j] at hij
    exact hjB (hij ▸ hiB)
  have hdx₁_eq : dx₁ = xIn B - xIn A := by dsimp [dx₁, esX]; rw [hcardAB_eq]; ring
  have hdy₁_eq : dy₁ = dyIn B - dyIn A := by dsimp [dy₁, esY]; rw [hcardAB_eq]; ring
  have hdx₂_eq : dx₂ = xIn C - xIn B := by dsimp [dx₂, esX]; rw [hcardBC_eq]; ring
  have hdy₂_eq : dy₂ = dyIn C - dyIn B := by dsimp [dy₂, esY]; rw [hcardBC_eq]; ring
  obtain ⟨⟨hx1_lo, hx1_hi⟩, ⟨hy1_lo, hy1_hi⟩⟩ := xIn_dyIn_diff_bounds hneAB hiA hiB
  obtain ⟨⟨hx2_lo, hx2_hi⟩, ⟨hy2_lo, hy2_hi⟩⟩ := xIn_dyIn_diff_bounds hneBC hjB hjC
  rw [← hdx₁_eq] at hx1_lo hx1_hi
  rw [← hdy₁_eq] at hy1_lo hy1_hi
  rw [← hdx₂_eq] at hx2_lo hx2_hi
  rw [← hdy₂_eq] at hy2_lo hy2_hi
  have h16i : (16 : ℝ) ^ (i : ℕ) = (4 : ℝ) ^ (i : ℕ) * (4 : ℝ) ^ (i : ℕ) := by
    rw [← mul_pow]; norm_num
  have h16j : (16 : ℝ) ^ (j : ℕ) = (4 : ℝ) ^ (j : ℕ) * (4 : ℝ) ^ (j : ℕ) := by
    rw [← mul_pow]; norm_num
  have h4i_pos : (0 : ℝ) < (4 : ℝ) ^ (i : ℕ) := by positivity
  have h4j_pos : (0 : ℝ) < (4 : ℝ) ^ (j : ℕ) := by positivity
  have hsl1_lo : (7 / 10 : ℝ) * (4 : ℝ) ^ (i : ℕ) * dx₁ < dy₁ := by
    calc (7 / 10 : ℝ) * (4 : ℝ) ^ (i : ℕ) * dx₁
      _ < (7 / 10 : ℝ) * (4 : ℝ) ^ (i : ℕ) * ((4 / 3 : ℝ) * (4 : ℝ) ^ (i : ℕ)) :=
          mul_lt_mul_of_pos_left hx1_hi (by positivity)
      _ = (14 / 15 : ℝ) * (16 : ℝ) ^ (i : ℕ) := by rw [h16i]; ring
      _ < dy₁ := hy1_lo
  have hsl1_hi : dy₁ < (8 / 5 : ℝ) * (4 : ℝ) ^ (i : ℕ) * dx₁ := by
    calc dy₁ < (16 / 15 : ℝ) * (16 : ℝ) ^ (i : ℕ) := hy1_hi
      _ = (8 / 5 : ℝ) * (4 : ℝ) ^ (i : ℕ) * ((2 / 3 : ℝ) * (4 : ℝ) ^ (i : ℕ)) := by rw [h16i]; ring
      _ < (8 / 5 : ℝ) * (4 : ℝ) ^ (i : ℕ) * dx₁ := mul_lt_mul_of_pos_left hx1_lo (by positivity)
  have hsl2_lo : (7 / 10 : ℝ) * (4 : ℝ) ^ (j : ℕ) * dx₂ < dy₂ := by
    calc (7 / 10 : ℝ) * (4 : ℝ) ^ (j : ℕ) * dx₂
      _ < (7 / 10 : ℝ) * (4 : ℝ) ^ (j : ℕ) * ((4 / 3 : ℝ) * (4 : ℝ) ^ (j : ℕ)) :=
          mul_lt_mul_of_pos_left hx2_hi (by positivity)
      _ = (14 / 15 : ℝ) * (16 : ℝ) ^ (j : ℕ) := by rw [h16j]; ring
      _ < dy₂ := hy2_lo
  have hsl2_hi : dy₂ < (8 / 5 : ℝ) * (4 : ℝ) ^ (j : ℕ) * dx₂ := by
    calc dy₂ < (16 / 15 : ℝ) * (16 : ℝ) ^ (j : ℕ) := hy2_hi
      _ = (8 / 5 : ℝ) * (4 : ℝ) ^ (j : ℕ) * ((2 / 3 : ℝ) * (4 : ℝ) ^ (j : ℕ)) := by rw [h16j]; ring
      _ < (8 / 5 : ℝ) * (4 : ℝ) ^ (j : ℕ) * dx₂ := mul_lt_mul_of_pos_left hx2_lo (by positivity)
  have hdx12_pos : 0 < dx₁ * dx₂ := mul_pos hdx₁ hdx₂
  rcases lt_or_gt_of_ne hij_ne with hij_lt | hij_gt
  · have hpow_ij : (8 / 5 : ℝ) * (4 : ℝ) ^ (i : ℕ) < (7 / 10 : ℝ) * (4 : ℝ) ^ (j : ℕ) := by
      have hstep : 4 * (4 : ℝ) ^ (i : ℕ) ≤ (4 : ℝ) ^ (j : ℕ) := by
        calc 4 * (4 : ℝ) ^ (i : ℕ) = (4 : ℝ) ^ ((i : ℕ) + 1) := by ring
          _ ≤ (4 : ℝ) ^ (j : ℕ) := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hij_lt)
      linarith
    have hpos : 0 < dx₁ * dy₂ - dy₁ * dx₂ := by
      have h1 := mul_lt_mul_of_pos_right hsl1_hi hdx₂
      have h2 := mul_lt_mul_of_pos_right hpow_ij hdx12_pos
      have h3 := mul_lt_mul_of_pos_left hsl2_lo hdx₁
      linarith [show ((8 / 5 : ℝ) * (4 : ℝ) ^ (i : ℕ) * dx₁) * dx₂ = (8 / 5 : ℝ) * (4 : ℝ) ^ (i : ℕ) * (dx₁ * dx₂) by ring,
        show dx₁ * ((7 / 10 : ℝ) * (4 : ℝ) ^ (j : ℕ) * dx₂) = (7 / 10 : ℝ) * (4 : ℝ) ^ (j : ℕ) * (dx₁ * dx₂) by ring]
    exact ⟨hpos.ne', iff_of_true hpos hij_lt⟩
  · have hpow_ji : (8 / 5 : ℝ) * (4 : ℝ) ^ (j : ℕ) < (7 / 10 : ℝ) * (4 : ℝ) ^ (i : ℕ) := by
      have hstep : 4 * (4 : ℝ) ^ (j : ℕ) ≤ (4 : ℝ) ^ (i : ℕ) := by
        calc 4 * (4 : ℝ) ^ (j : ℕ) = (4 : ℝ) ^ ((j : ℕ) + 1) := by ring
          _ ≤ (4 : ℝ) ^ (i : ℕ) := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hij_gt)
      linarith
    have hneg : dx₁ * dy₂ - dy₁ * dx₂ < 0 := by
      have h1 := mul_lt_mul_of_pos_left hsl2_hi hdx₁
      have h2 := mul_lt_mul_of_pos_right hpow_ji hdx12_pos
      have h3 := mul_lt_mul_of_pos_right hsl1_lo hdx₂
      linarith [show dx₁ * ((8 / 5 : ℝ) * (4 : ℝ) ^ (j : ℕ) * dx₂) = (8 / 5 : ℝ) * (4 : ℝ) ^ (j : ℕ) * (dx₁ * dx₂) by ring,
        show ((7 / 10 : ℝ) * (4 : ℝ) ^ (i : ℕ) * dx₁) * dx₂ = (7 / 10 : ℝ) * (4 : ℝ) ^ (i : ℕ) * (dx₁ * dx₂) by ring]
    exact ⟨hneg.ne, iff_of_false (not_lt_of_gt hneg) (not_lt_of_gt hij_gt)⟩

private lemma orient2d_esPt_law {m : ℕ} {A B C : Finset (Fin m)}
    (hAB : esX A < esX B) (hBC : esX B < esX C) :
    let hneAB : A ≠ B := fun h => hAB.ne (congrArg esX h)
    let hneBC : B ≠ C := fun h => hBC.ne (congrArg esX h)
    orient2d (esPt A) (esPt B) (esPt C) ≠ 0 ∧
    (0 < orient2d (esPt A) (esPt B) (esPt C) ↔
      (A.card = B.card ∧ B.card = C.card ∧ maxDiff hneAB < maxDiff hneBC) ∨
      (A.card < B.card ∧ B.card = C.card)) := by
  intro hneAB hneBC
  obtain ⟨_, hAB_cases⟩ := esX_lt_cases hAB
  obtain ⟨_, hBC_cases⟩ := esX_lt_cases hBC
  let dx₁ := esX B - esX A
  let dy₁ := esY B - esY A
  let dx₂ := esX C - esX B
  let dy₂ := esY C - esY B
  have hdx₁ : 0 < dx₁ := sub_pos.mpr hAB
  have hdx₂ : 0 < dx₂ := sub_pos.mpr hBC
  have horient_eq : orient2d (esPt A) (esPt B) (esPt C) = dx₁ * dy₂ - dy₁ * dx₂ := by
    simp only [orient2d, esPt_zero, esPt_one, dx₁, dy₁, dx₂, dy₂]
    ring
  rw [horient_eq]
  obtain ⟨_, _, h16_M, h4096_M⟩ := esM_large m
  have dy_neg_of_card_lt {P Q : Finset (Fin m)} (hpq : P.card < Q.card) : esY Q - esY P < 0 := by
    have hcardR : (P.card : ℝ) + 1 ≤ (Q.card : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hpq
    have hsq_diff : 1 ≤ (Q.card : ℝ) ^ 2 - (P.card : ℝ) ^ 2 := by
      have hp0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    obtain ⟨_, ⟨hyP0, _⟩⟩ := xIn_dyIn_global_bounds P
    obtain ⟨_, ⟨_, hyQ1⟩⟩ := xIn_dyIn_global_bounds Q
    unfold esY
    nlinarith
  rcases hAB_cases with hcardAB | ⟨hcardAB_eq, hiA, hiB⟩
  · rcases hBC_cases with hcardBC | ⟨hcardBC_eq, hjB, hjC⟩
    · have hneg := orient_case4_lt_lt hAB hBC hcardAB hcardBC
      change dx₁ * dy₂ - dy₁ * dx₂ < 0 at hneg
      refine ⟨hneg.ne, iff_of_false (not_lt_of_gt hneg) ?_⟩
      rintro (⟨h1, _, _⟩ | ⟨_, h2⟩) <;> omega
    · have hdy₁ : dy₁ < 0 := dy_neg_of_card_lt hcardAB
      have hdy₂_eq : dy₂ = dyIn C - dyIn B := by dsimp [dy₂, esY]; rw [hcardBC_eq]; ring
      have hdy₂ : 0 < dy₂ := by
        rw [hdy₂_eq]
        have h16j : (0 : ℝ) < (16 : ℝ) ^ (maxDiff hneBC : ℕ) := by positivity
        linarith [(xIn_dyIn_diff_bounds hneBC hjB hjC).2.1]
      have hpos : 0 < dx₁ * dy₂ - dy₁ * dx₂ := by nlinarith
      exact ⟨hpos.ne', iff_of_true hpos (Or.inr ⟨hcardAB, hcardBC_eq⟩)⟩
  · rcases hBC_cases with hcardBC | ⟨hcardBC_eq, hjB, hjC⟩
    · have hdy₁_eq : dy₁ = dyIn B - dyIn A := by dsimp [dy₁, esY]; rw [hcardAB_eq]; ring
      have hdy₁ : 0 < dy₁ := by
        rw [hdy₁_eq]
        have h16i : (0 : ℝ) < (16 : ℝ) ^ (maxDiff hneAB : ℕ) := by positivity
        linarith [(xIn_dyIn_diff_bounds hneAB hiA hiB).2.1]
      have hdy₂ : dy₂ < 0 := dy_neg_of_card_lt hcardBC
      have hneg : dx₁ * dy₂ - dy₁ * dx₂ < 0 := by nlinarith
      refine ⟨hneg.ne, iff_of_false (not_lt_of_gt hneg) ?_⟩
      rintro (⟨_, h2, _⟩ | ⟨h1, _⟩) <;> omega
    · obtain ⟨hnz, hiff⟩ := orient_case1_eq_eq hAB hBC hcardAB_eq hcardBC_eq hneAB hneBC hiA hiB hjB hjC
      refine ⟨hnz, hiff.trans ?_⟩
      constructor
      · intro hlt; exact Or.inl ⟨hcardAB_eq, hcardBC_eq, hlt⟩
      · rintro (⟨_, _, hlt⟩ | ⟨hcard_lt, _⟩)
        · exact hlt
        · omega

private noncomputable def esPts (m : ℕ) : Finset ℝ² :=
  Finset.univ.image (esPt (m := m))

private lemma esPts_card (m : ℕ) : (esPts m).card = 2 ^ m := by
  unfold esPts
  rw [Finset.card_image_of_injective _ esPt_injective, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

private lemma orient2d_zero_of_collinear {a b c : ℝ²}
    (hcol : Collinear ℝ ({a, b, c} : Set ℝ²)) : orient2d a b c = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (show a ∈ ({a, b, c} : Set ℝ²) by simp)).mp hcol
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  have hb0 : b 0 = rb * v 0 + a 0 := by
    have := congrArg (fun p : ℝ² => p 0) hrb
    simpa [vadd_eq_add] using this
  have hb1 : b 1 = rb * v 1 + a 1 := by
    have := congrArg (fun p : ℝ² => p 1) hrb
    simpa [vadd_eq_add] using this
  have hc0 : c 0 = rc * v 0 + a 0 := by
    have := congrArg (fun p : ℝ² => p 0) hrc
    simpa [vadd_eq_add] using this
  have hc1 : c 1 = rc * v 1 + a 1 := by
    have := congrArg (fun p : ℝ² => p 1) hrc
    simpa [vadd_eq_add] using this
  unfold orient2d
  rw [hb0, hb1, hc0, hc1]
  ring

private lemma esPts_nonTrilinear (m : ℕ) : NonTrilinear (esPts m : Set ℝ²) := by
  intro p hp q hq r hr hpq hqr hpr hcol
  have hz : orient2d p q r = 0 := orient2d_zero_of_collinear hcol
  obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨B, -, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hr
  have hAB : esX A ≠ esX B := fun h => hpq (congrArg esPt (esX_injective h))
  have hBC : esX B ≠ esX C := fun h => hqr (congrArg esPt (esX_injective h))
  have hAC : esX A ≠ esX C := fun h => hpr (congrArg esPt (esX_injective h))
  have hperm {U V W : Finset (Fin m)} (h1 : esX U < esX V) (h2 : esX V < esX W)
      (heq : orient2d (esPt U) (esPt V) (esPt W) = orient2d (esPt A) (esPt B) (esPt C) ∨
             orient2d (esPt U) (esPt V) (esPt W) = -orient2d (esPt A) (esPt B) (esPt C)) : False := by
    have hnz := (orient2d_esPt_law h1 h2).1
    apply hnz
    rcases heq with h | h <;> linarith
  rcases lt_or_gt_of_ne hAB with hab | hba <;>
    rcases lt_or_gt_of_ne hBC with hbc | hcb <;>
    rcases lt_or_gt_of_ne hAC with hac | hca
  · exact hperm hab hbc (Or.inl rfl)
  · linarith
  · exact hperm hac hcb (Or.inr (by unfold orient2d; ring))
  · exact hperm hca hab (Or.inl (by unfold orient2d; ring))
  · exact hperm hba hac (Or.inr (by unfold orient2d; ring))
  · exact hperm hbc hca (Or.inl (by unfold orient2d; ring))
  · linarith
  · exact hperm hcb hba (Or.inr (by unfold orient2d; ring))

/- ## Part 5: Upper/lower chain combinatorics and `¬ HasConvexNGon n (esPts (n - 2))` -/

private lemma chain_monochromatic {r : ℕ} (hr : 4 ≤ r) (col : Fin r → Fin r → Fin r → Bool)
    (hquad : ∀ a b c d : Fin r, a < b → b < c → c < d →
      col a b c = col a b d ∧ col a c d = col b c d)
    (val : Bool) :
    let first : Fin r := ⟨0, by omega⟩
    let last : Fin r := ⟨r - 1, by omega⟩
    let mid : Finset (Fin r) := Finset.univ.filter (fun t => first < t ∧ t < last)
    let C : Finset (Fin r) := insert first (insert last (mid.filter (fun t => col first t last = val)))
    ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a < b → b < c → col a b c = val := by
  intro first last mid C a ha b hb c hc hab hbc
  have hfirst_le (x : Fin r) : first ≤ x := Nat.zero_le x.val
  have hle_last (x : Fin r) : x ≤ last := by
    change x.val ≤ r - 1
    omega
  have hb_gt_first : first < b := lt_of_le_of_lt (hfirst_le a) hab
  have hb_lt_last : b < last := lt_of_lt_of_le hbc (hle_last c)
  have hb_mid : col first b last = val := by
    rcases Finset.mem_insert.mp hb with rfl | hb1
    · exact (lt_irrefl _ hb_gt_first).elim
    · rcases Finset.mem_insert.mp hb1 with rfl | hb2
      · exact (lt_irrefl _ hb_lt_last).elim
      · exact (Finset.mem_filter.mp hb2).2
  rcases eq_or_lt_of_le (hfirst_le a) with ha_eq | ha_gt
  · subst ha_eq
    rcases eq_or_lt_of_le (hle_last c) with hc_eq | hc_lt
    · subst hc_eq
      exact hb_mid
    · exact (hquad first b c last hab hbc hc_lt).1.trans hb_mid
  · rcases eq_or_lt_of_le (hle_last c) with hc_eq | hc_lt
    · subst hc_eq
      exact (hquad first a b last ha_gt hab hbc).2.symm.trans hb_mid
    · have h1 : col first b c = val :=
        (hquad first b c last (ha_gt.trans hab) hbc hc_lt).1.trans hb_mid
      exact (hquad first a b c ha_gt hab hbc).2.symm.trans h1

private lemma strictAnti_of_consec {t : ℕ} {α : Type*} [Preorder α] (f : Fin t → α)
    (hconsec : ∀ j : ℕ, (hj : j + 1 < t) → f ⟨j + 1, hj⟩ < f ⟨j, by omega⟩) :
    ∀ i j : Fin t, i < j → f j < f i := by
  intro i j hij
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j.val = i.val + (d + 1) := ⟨j.val - i.val - 1, by omega⟩
  have hgen : ∀ d : ℕ, (h : i.val + (d + 1) < t) → f ⟨i.val + (d + 1), h⟩ < f i := by
    intro d
    induction d with
    | zero =>
      intro h
      simpa using hconsec i.val h
    | succ d ih =>
      intro h
      have hstep := hconsec (i.val + (d + 1)) (by omega)
      have hprev := ih (by omega)
      exact lt_trans (by simpa [Nat.add_assoc] using hstep) hprev
  have hj_eq : j = ⟨i.val + (d + 1), hd ▸ j.isLt⟩ := Fin.ext hd
  rw [hj_eq]
  exact hgen d (hd ▸ j.isLt)

private lemma strictMono_of_consec {t : ℕ} {α : Type*} [Preorder α] (f : Fin t → α)
    (hconsec : ∀ j : ℕ, (hj : j + 1 < t) → f ⟨j, by omega⟩ < f ⟨j + 1, hj⟩) :
    ∀ i j : Fin t, i < j → f i < f j := by
  intro i j hij
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j.val = i.val + (d + 1) := ⟨j.val - i.val - 1, by omega⟩
  have hgen : ∀ d : ℕ, (h : i.val + (d + 1) < t) → f i < f ⟨i.val + (d + 1), h⟩ := by
    intro d
    induction d with
    | zero =>
      intro h
      simpa using hconsec i.val h
    | succ d ih =>
      intro h
      have hprev := ih (by omega)
      have hstep := hconsec (i.val + (d + 1)) (by omega)
      exact lt_trans hprev (by simpa [Nat.add_assoc] using hstep)
  have hj_eq : j = ⟨i.val + (d + 1), hd ▸ j.isLt⟩ := Fin.ext hd
  rw [hj_eq]
  exact hgen d (hd ▸ j.isLt)

private lemma cap_card_le_in_group {m r k : ℕ} (F : Fin r → Finset (Fin m))
    (hmonoX : StrictMono (fun u => esX (F u)))
    (W : Finset (Fin r)) (hW_card : ∀ u ∈ W, (F u).card = k)
    (hcap : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a < b → b < c →
      ¬ (0 < orient2d (esPt (F a)) (esPt (F b)) (esPt (F c)))) :
    W.card ≤ k + 1 := by
  rcases Nat.eq_zero_or_pos W.card with hw0 | hw_pos
  · omega
  obtain ⟨t, hwt⟩ : ∃ t : ℕ, W.card = t + 1 := ⟨W.card - 1, by omega⟩
  let e : Fin (t + 1) ↪o Fin r := W.orderEmbOfFin hwt
  have he_mem (s : Fin (t + 1)) : e s ∈ W := W.orderEmbOfFin_mem hwt s
  have hne_step (j : Fin t) : F (e j.castSucc) ≠ F (e j.succ) := by
    have hlt : esX (F (e j.castSucc)) < esX (F (e j.succ)) :=
      hmonoX (e.strictMono Fin.castSucc_lt_succ)
    exact fun h => hlt.ne (congrArg esX h)
  let idx (j : Fin t) : Fin m := maxDiff (hne_step j)
  have hidx_mem (j : Fin t) : idx j ∉ F (e j.castSucc) ∧ idx j ∈ F (e j.succ) := by
    have hlt : esX (F (e j.castSucc)) < esX (F (e j.succ)) :=
      hmonoX (e.strictMono Fin.castSucc_lt_succ)
    obtain ⟨_, hcases⟩ := esX_lt_cases hlt
    rcases hcases with hcard_lt | ⟨_, hiA, hiB⟩
    · have h1 := hW_card _ (he_mem j.castSucc)
      have h2 := hW_card _ (he_mem j.succ)
      omega
    · exact ⟨hiA, hiB⟩
  have hconsec : ∀ j : ℕ, (hj : j + 1 < t) → idx ⟨j + 1, hj⟩ < idx ⟨j, by omega⟩ := by
    intro j hj
    let j0 : Fin t := ⟨j, by omega⟩
    let j1 : Fin t := ⟨j + 1, hj⟩
    have he01 : e j0.castSucc < e j0.succ := e.strictMono Fin.castSucc_lt_succ
    have he12 : e j1.castSucc < e j1.succ := e.strictMono Fin.castSucc_lt_succ
    have hmid_eq : j0.succ = j1.castSucc := Fin.ext rfl
    have he12' : e j0.succ < e j1.succ := hmid_eq ▸ he12
    have hnot_pos := hcap _ (he_mem j0.castSucc) _ (he_mem j0.succ) _ (he_mem j1.succ) he01 he12'
    have hlaw := (orient2d_esPt_law (hmonoX he01) (hmonoX he12')).2
    have hnot_lt : ¬ (idx j0 < idx j1) := by
      intro hlt_idx
      apply hnot_pos
      rw [hlaw]
      left
      refine ⟨(hW_card _ (he_mem j0.castSucc)).trans (hW_card _ (he_mem j0.succ)).symm,
        (hW_card _ (he_mem j0.succ)).trans (hW_card _ (he_mem j1.succ)).symm, ?_⟩
      have hc1 : maxDiff (fun h => (hmonoX he01).ne (congrArg esX h)) = idx j0 := rfl
      have hc2 : maxDiff (fun h => (hmonoX he12').ne (congrArg esX h)) = idx j1 :=
        maxDiff_congr (congrArg (fun x => F (e x)) hmid_eq) rfl _ _
      rw [hc1, hc2]
      exact hlt_idx
    have hne_idx : idx j0 ≠ idx j1 := by
      intro heq_idx
      have hin0 : idx j0 ∈ F (e j0.succ) := (hidx_mem j0).2
      have hnot1 : idx j1 ∉ F (e j1.castSucc) := (hidx_mem j1).1
      rw [heq_idx, hmid_eq] at hin0
      exact hnot1 hin0
    exact lt_of_le_of_ne (not_lt.mp hnot_lt) hne_idx.symm
  have hanti : ∀ j₁ j₂ : Fin t, j₁ < j₂ → idx j₂ < idx j₁ :=
    strictAnti_of_consec idx hconsec
  have hinj : Function.Injective idx := by
    intro j₁ j₂ heq
    rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
    · exact (ne_of_gt (hanti j₁ j₂ hlt) heq).elim
    · rfl
    · exact (ne_of_lt (hanti j₂ j₁ hgt) heq).elim
  have hstay : ∀ (j : Fin t) (s : ℕ) (hs : s ≤ t), j.val + 1 ≤ s →
      idx j ∈ F (e ⟨s, Nat.lt_succ_of_le hs⟩) := by
    intro j s
    induction s with
    | zero => intro _ h; omega
    | succ s ih =>
      intro hs hle
      rcases eq_or_lt_of_le hle with heq | hlt
      · have hfin : (⟨s + 1, Nat.lt_succ_of_le hs⟩ : Fin (t + 1)) = j.succ := Fin.ext heq.symm
        rw [hfin]
        exact (hidx_mem j).2
      · have hprev : idx j ∈ F (e ⟨s, by omega⟩) := ih (by omega) (by omega)
        let j' : Fin t := ⟨s, by omega⟩
        have hjj' : j < j' := by
          change j.val < s
          omega
        have hidx_gt : idx j' < idx j := hanti j j' hjj'
        have heq_mem := eq_above_maxDiff (hne_step j') hidx_gt
        have hcast_eq : (⟨s, by omega⟩ : Fin (t + 1)) = j'.castSucc := Fin.ext rfl
        have hsucc_eq : (⟨s + 1, Nat.lt_succ_of_le hs⟩ : Fin (t + 1)) = j'.succ := Fin.ext rfl
        rw [hsucc_eq]
        rw [hcast_eq] at hprev
        exact heq_mem.mp hprev
  have hsub : Finset.univ.image idx ⊆ F (e ⟨t, Nat.lt_succ_self t⟩) := by
    intro u hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu
    exact hstay j t le_rfl (Nat.succ_le_of_lt j.isLt)
  have ht_le : t ≤ k := by
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      hW_card _ (he_mem ⟨t, Nat.lt_succ_self t⟩)] at hc1
    exact hc1
  omega

private lemma cup_card_le_in_group {m r k : ℕ} (F : Fin r → Finset (Fin m))
    (hmonoX : StrictMono (fun u => esX (F u)))
    (W : Finset (Fin r)) (hW_card : ∀ u ∈ W, (F u).card = k)
    (hcup : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a < b → b < c →
      0 < orient2d (esPt (F a)) (esPt (F b)) (esPt (F c))) :
    W.card ≤ m - k + 1 := by
  rcases Nat.eq_zero_or_pos W.card with hw0 | hw_pos
  · omega
  obtain ⟨t, hwt⟩ : ∃ t : ℕ, W.card = t + 1 := ⟨W.card - 1, by omega⟩
  let e : Fin (t + 1) ↪o Fin r := W.orderEmbOfFin hwt
  have he_mem (s : Fin (t + 1)) : e s ∈ W := W.orderEmbOfFin_mem hwt s
  have hne_step (j : Fin t) : F (e j.castSucc) ≠ F (e j.succ) := by
    have hlt : esX (F (e j.castSucc)) < esX (F (e j.succ)) :=
      hmonoX (e.strictMono Fin.castSucc_lt_succ)
    exact fun h => hlt.ne (congrArg esX h)
  let idx (j : Fin t) : Fin m := maxDiff (hne_step j)
  have hidx_mem (j : Fin t) : idx j ∉ F (e j.castSucc) ∧ idx j ∈ F (e j.succ) := by
    have hlt : esX (F (e j.castSucc)) < esX (F (e j.succ)) :=
      hmonoX (e.strictMono Fin.castSucc_lt_succ)
    obtain ⟨_, hcases⟩ := esX_lt_cases hlt
    rcases hcases with hcard_lt | ⟨_, hiA, hiB⟩
    · have h1 := hW_card _ (he_mem j.castSucc)
      have h2 := hW_card _ (he_mem j.succ)
      omega
    · exact ⟨hiA, hiB⟩
  have hconsec : ∀ j : ℕ, (hj : j + 1 < t) → idx ⟨j, by omega⟩ < idx ⟨j + 1, hj⟩ := by
    intro j hj
    let j0 : Fin t := ⟨j, by omega⟩
    let j1 : Fin t := ⟨j + 1, hj⟩
    have he01 : e j0.castSucc < e j0.succ := e.strictMono Fin.castSucc_lt_succ
    have he12 : e j1.castSucc < e j1.succ := e.strictMono Fin.castSucc_lt_succ
    have hmid_eq : j0.succ = j1.castSucc := Fin.ext rfl
    have he12' : e j0.succ < e j1.succ := hmid_eq ▸ he12
    have hpos := hcup _ (he_mem j0.castSucc) _ (he_mem j0.succ) _ (he_mem j1.succ) he01 he12'
    have hlaw := (orient2d_esPt_law (hmonoX he01) (hmonoX he12')).2
    rw [hlaw] at hpos
    rcases hpos with ⟨_, _, hlt_idx⟩ | ⟨hcard_lt, _⟩
    · have hc1 : maxDiff (fun h => (hmonoX he01).ne (congrArg esX h)) = idx j0 := rfl
      have hc2 : maxDiff (fun h => (hmonoX he12').ne (congrArg esX h)) = idx j1 :=
        maxDiff_congr (congrArg (fun x => F (e x)) hmid_eq) rfl _ _
      rwa [hc1, hc2] at hlt_idx
    · have h1 := hW_card _ (he_mem j0.castSucc)
      have h2 := hW_card _ (he_mem j0.succ)
      omega
  have hmono : ∀ j₁ j₂ : Fin t, j₁ < j₂ → idx j₁ < idx j₂ :=
    strictMono_of_consec idx hconsec
  have hinj : Function.Injective idx := by
    intro j₁ j₂ heq
    rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
    · exact (ne_of_lt (hmono j₁ j₂ hlt) heq).elim
    · rfl
    · exact (ne_of_gt (hmono j₂ j₁ hgt) heq).elim
  have hstay0 : ∀ (j : Fin t) (d : ℕ) (hd : d ≤ j.val),
      idx j ∉ F (e ⟨j.val - d, by omega⟩) := by
    intro j d
    induction d with
    | zero =>
      intro _
      have hfin : (⟨j.val - 0, by omega⟩ : Fin (t + 1)) = j.castSucc := Fin.ext (by simp)
      rw [hfin]
      exact (hidx_mem j).1
    | succ d ih =>
      intro hd
      have hprev : idx j ∉ F (e ⟨j.val - d, by omega⟩) := ih (by omega)
      let j' : Fin t := ⟨j.val - (d + 1), by omega⟩
      have hj'j : j' < j := by
        change j.val - (d + 1) < j.val
        omega
      have hidx_gt : idx j' < idx j := hmono j' j hj'j
      have heq_mem := eq_above_maxDiff (hne_step j') hidx_gt
      have hcast_eq : (⟨j.val - (d + 1), by omega⟩ : Fin (t + 1)) = j'.castSucc := Fin.ext rfl
      have hsucc_eq : (⟨j.val - d, by omega⟩ : Fin (t + 1)) = j'.succ := Fin.ext (by dsimp [j']; omega)
      rw [hcast_eq]
      rw [hsucc_eq] at hprev
      exact fun hmem => hprev (heq_mem.mp hmem)
  have hsub : Finset.univ.image idx ⊆ Finset.univ \ F (e ⟨0, Nat.zero_lt_succ t⟩) := by
    intro u hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    have h0 := hstay0 j j.val le_rfl
    simpa only [Nat.sub_self] using h0
  have ht_le : t ≤ m - k := by
    have hc1 := Finset.card_le_card hsub
    have hsdiff : (Finset.univ \ F (e ⟨0, Nat.zero_lt_succ t⟩)).card = m - k := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        hW_card _ (he_mem ⟨0, Nat.zero_lt_succ t⟩)]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hsdiff] at hc1
    exact hc1
  omega

private lemma not_hasConvexNGon_esPts {n : ℕ} (hn : 3 ≤ n) :
    ¬ HasConvexNGon n (esPts (n - 2) : Set ℝ²) := by
  by_cases hn3 : n = 3
  · subst hn3
    rintro ⟨S, hScard, hSsub, _⟩
    have hle : S.card ≤ (esPts 1).card := Finset.card_le_card (by exact_mod_cast hSsub)
    rw [esPts_card] at hle
    omega
  have hn4 : 4 ≤ n := by omega
  set m : ℕ := n - 2
  have hm2 : 2 ≤ m := by omega
  have hn_eq : n = m + 2 := by omega
  rintro ⟨S, hScard, hSsub, hSconv⟩
  let C : Finset (Finset (Fin m)) := Finset.univ.filter (fun A => esPt A ∈ S)
  have hC_img : C.image esPt = S := by
    ext p
    simp only [C, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨A, hA, rfl⟩; exact hA
    · intro hpS
      have hp_es : p ∈ esPts m := hSsub hpS
      obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hp_es
      exact ⟨A, hpS, rfl⟩
  have hC_card : C.card = n := by
    have hc := Finset.card_image_of_injective C esPt_injective
    rw [hC_img] at hc
    exact hc.symm.trans hScard
  let keys : Finset ℝ := C.image esX
  have hkeys_card : keys.card = n :=
    (Finset.card_image_of_injective C esX_injective).trans hC_card
  let keyIso := keys.orderIsoOfFin hkeys_card
  have hpre (i : Fin n) : ∃ A ∈ C, esX A = (keyIso i).val :=
    Finset.mem_image.mp (keyIso i).property
  choose F hFC hF_esX using hpre
  have hmonoX : StrictMono (fun i => esX (F i)) := by
    intro i j hij
    dsimp only
    rw [hF_esX, hF_esX]
    exact keyIso.strictMono hij
  have hF_in_S (i : Fin n) : esPt (F i) ∈ (S : Set ℝ²) :=
    (Finset.mem_filter.mp (hFC i)).2
  let col (a b c : Fin n) : Bool :=
    decide (0 < orient2d (esPt (F a)) (esPt (F b)) (esPt (F c)))
  have hquad : ∀ a b c d : Fin n, a < b → b < c → c < d →
      col a b c = col a b d ∧ col a c d = col b c d := by
    intro a b c d hab hbc hcd
    have hxa : (esPt (F a)) 0 < (esPt (F b)) 0 := by
      simpa only [esPt_zero] using hmonoX hab
    have hxb : (esPt (F b)) 0 < (esPt (F c)) 0 := by
      simpa only [esPt_zero] using hmonoX hbc
    have hxc : (esPt (F c)) 0 < (esPt (F d)) 0 := by
      simpa only [esPt_zero] using hmonoX hcd
    have hA := (orient2d_esPt_law (hmonoX hab) (hmonoX hbc)).1
    have hB := (orient2d_esPt_law (hmonoX hab) (hmonoX (hbc.trans hcd))).1
    have hC := (orient2d_esPt_law (hmonoX (hab.trans hbc)) (hmonoX hcd)).1
    have hE := (orient2d_esPt_law (hmonoX hbc) (hmonoX hcd)).1
    obtain ⟨hl, hr⟩ := signs_of_convexIndep hSconv
      (hF_in_S a) (hF_in_S b) (hF_in_S c) (hF_in_S d) hxa hxb hxc hA hB hC hE
    exact ⟨decide_eq_decide.mpr hl, decide_eq_decide.mpr hr⟩
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hfirst_lt_last : first < last := by
    change 0 < n - 1
    omega
  let mid : Finset (Fin n) := Finset.univ.filter (fun t => first < t ∧ t < last)
  let U : Finset (Fin n) := insert first (insert last (mid.filter (fun t => col first t last = false)))
  let L : Finset (Fin n) := insert first (insert last (mid.filter (fun t => col first t last = true)))
  have hmid_card : mid.card = n - 2 := by
    have hmid_eq : mid = (Finset.univ.erase first).erase last := by
      ext t
      have ht_lt : t.val < n := t.isLt
      simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase,
        Fin.lt_def, first, last]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun heq => ?_, fun heq => ?_⟩
        · subst heq; simp at h2
        · subst heq; simp at h1
      · rintro ⟨hne1, hne2⟩
        have h1 : t.val ≠ n - 1 := fun h => hne1 (Fin.ext h)
        have h2 : t.val ≠ 0 := fun h => hne2 (Fin.ext h)
        omega
    have hlast_mem : last ∈ Finset.univ.erase first :=
      Finset.mem_erase.mpr ⟨hfirst_lt_last.ne', Finset.mem_univ _⟩
    rw [hmid_eq, Finset.card_erase_of_mem hlast_mem,
      Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ, Fintype.card_fin]
    omega
  have hUL_sum : U.card + L.card = n + 2 := by
    have hfirst_not_U : first ∉ insert last (mid.filter (fun t => col first t last = false)) := by
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, mid]
      rintro (heq | ⟨⟨hlt, _⟩, _⟩)
      · exact hfirst_lt_last.ne heq
      · exact lt_irrefl _ hlt
    have hlast_not_U : last ∉ mid.filter (fun t => col first t last = false) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mid]
      rintro ⟨⟨_, hlt⟩, _⟩
      exact lt_irrefl _ hlt
    have hfirst_not_L : first ∉ insert last (mid.filter (fun t => col first t last = true)) := by
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, mid]
      rintro (heq | ⟨⟨hlt, _⟩, _⟩)
      · exact hfirst_lt_last.ne heq
      · exact lt_irrefl _ hlt
    have hlast_not_L : last ∉ mid.filter (fun t => col first t last = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mid]
      rintro ⟨⟨_, hlt⟩, _⟩
      exact lt_irrefl _ hlt
    have hU_c : U.card = 2 + (mid.filter (fun t => col first t last = false)).card := by
      dsimp [U]
      rw [Finset.card_insert_of_notMem hfirst_not_U, Finset.card_insert_of_notMem hlast_not_U]
      omega
    have hL_c : L.card = 2 + (mid.filter (fun t => col first t last = true)).card := by
      dsimp [L]
      rw [Finset.card_insert_of_notMem hfirst_not_L, Finset.card_insert_of_notMem hlast_not_L]
      omega
    have hfilt_eq : mid.filter (fun t => ¬ col first t last = false) =
        mid.filter (fun t => col first t last = true) := by
      ext t
      cases col first t last <;> simp
    have hsum := Finset.sum_filter_add_sum_filter_not mid (fun t => col first t last = false) (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hfilt_eq] at hsum
    omega
  have hU_cap : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a < b → b < c →
      ¬ (0 < orient2d (esPt (F a)) (esPt (F b)) (esPt (F c))) := by
    intro a ha b hb c hc hab hbc
    have hm_col := chain_monochromatic hn4 col hquad false a ha b hb c hc hab hbc
    exact of_decide_eq_false hm_col
  have hL_cup : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, a < b → b < c →
      0 < orient2d (esPt (F a)) (esPt (F b)) (esPt (F c)) := by
    intro a ha b hb c hc hab hbc
    have hm_col := chain_monochromatic hn4 col hquad true a ha b hb c hc hab hbc
    exact of_decide_eq_true hm_col
  have hcard_mono : ∀ u v : Fin n, u ≤ v → (F u).card ≤ (F v).card := by
    intro u v huv
    rcases eq_or_lt_of_le huv with rfl | hlt
    · exact le_rfl
    · obtain ⟨_, hcases⟩ := esX_lt_cases (hmonoX hlt)
      rcases hcases with hc | ⟨hc, _, _⟩ <;> omega
  let k₀ := (F first).card
  let k₁ := (F last).card
  have hk₀_le_k₁ : k₀ ≤ k₁ := hcard_mono first last (Nat.zero_le _)
  have hk₁_le_m : k₁ ≤ m := by
    have := Finset.card_le_univ (F last)
    simpa using this
  rcases eq_or_lt_of_le hk₀_le_k₁ with hk_eq | hk_lt
  · have hall_k₀ : ∀ u : Fin n, (F u).card = k₀ := by
      intro u
      have h1 : k₀ ≤ (F u).card := hcard_mono first u (Nat.zero_le _)
      have h2 : (F u).card ≤ k₁ := hcard_mono u last (by change u.val ≤ n - 1; omega)
      omega
    have hU_le : U.card ≤ k₀ + 1 :=
      cap_card_le_in_group F hmonoX U (fun u _ => hall_k₀ u) hU_cap
    have hL_le : L.card ≤ m - k₀ + 1 :=
      cup_card_le_in_group F hmonoX L (fun u _ => hall_k₀ u) hL_cup
    omega
  · let L0 := L.filter (fun u => (F u).card = k₀)
    let L1 := L.filter (fun u => ¬ (F u).card = k₀)
    have hL_split : L.card = L0.card + L1.card := by
      have hs := Finset.sum_filter_add_sum_filter_not L (fun u => (F u).card = k₀) (fun _ => 1)
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
      exact hs.symm
    have hL0_le : L0.card ≤ 1 := by
      by_contra hgt1
      obtain ⟨u₁, hu₁, u₂, hu₂, hne12⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hgt1)
      have hcheck {a b : Fin n} (ha : a ∈ L0) (hb : b ∈ L0) (hab : a < b) : False := by
        have haL := (Finset.mem_filter.mp ha).1
        have hbL := (Finset.mem_filter.mp hb).1
        have ha_k := (Finset.mem_filter.mp ha).2
        have hb_k := (Finset.mem_filter.mp hb).2
        have hb_lt_last : b < last := by
          have hle : b ≤ last := by change b.val ≤ n - 1; omega
          exact lt_of_le_of_ne hle (fun heq => by rw [heq] at hb_k; exact hk_lt.ne hb_k.symm)
        have hpos := hL_cup a haL b hbL last (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hab hb_lt_last
        have hlaw := (orient2d_esPt_law (hmonoX hab) (hmonoX hb_lt_last)).2
        rw [hlaw] at hpos
        rcases hpos with ⟨_, h2, _⟩ | ⟨h1, _⟩ <;> omega
      rcases lt_or_gt_of_ne hne12 with hlt | hgt
      · exact hcheck hu₁ hu₂ hlt
      · exact hcheck hu₂ hu₁ hgt
    have hL1_k₁ : ∀ u ∈ L1, (F u).card = k₁ := by
      intro u hu
      have huL := (Finset.mem_filter.mp hu).1
      have hne_k₀ := (Finset.mem_filter.mp hu).2
      have hge_k₀ : k₀ ≤ (F u).card := hcard_mono first u (Nat.zero_le _)
      have hgt_k₀ : k₀ < (F u).card := lt_of_le_of_ne hge_k₀ (Ne.symm hne_k₀)
      have hle_k₁ : (F u).card ≤ k₁ := hcard_mono u last (by change u.val ≤ n - 1; omega)
      rcases eq_or_lt_of_le hle_k₁ with heq | hlt_k₁
      · exact heq
      · exfalso
        have hu_gt_first : first < u :=
          lt_of_le_of_ne (Nat.zero_le _) (fun heq => hgt_k₀.ne (congrArg (fun x => (F x).card) heq))
        have hu_lt_last : u < last := by
          have hle : u ≤ last := by change u.val ≤ n - 1; omega
          exact lt_of_le_of_ne hle (fun heq => hlt_k₁.ne (congrArg (fun x => (F x).card) heq))
        have hpos := hL_cup first (Finset.mem_insert_self _ _) u huL
          last (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hu_gt_first hu_lt_last
        have hlaw := (orient2d_esPt_law (hmonoX hu_gt_first) (hmonoX hu_lt_last)).2
        rw [hlaw] at hpos
        rcases hpos with ⟨h1, _, _⟩ | ⟨_, h2⟩ <;> omega
    have hL1_le : L1.card ≤ m - k₁ + 1 :=
      cup_card_le_in_group F hmonoX L1 hL1_k₁
        (fun a ha b hb c hc => hL_cup a (Finset.mem_of_mem_filter a ha)
          b (Finset.mem_of_mem_filter b hb) c (Finset.mem_of_mem_filter c hc))
    let U0 := U.filter (fun u => (F u).card = k₀)
    let Upos := U.filter (fun u => ¬ (F u).card = k₀)
    have hU_split : U.card = U0.card + Upos.card := by
      have hs := Finset.sum_filter_add_sum_filter_not U (fun u => (F u).card = k₀) (fun _ => 1)
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
      exact hs.symm
    have hU0_le : U0.card ≤ k₀ + 1 :=
      cap_card_le_in_group F hmonoX U0 (fun u hu => (Finset.mem_filter.mp hu).2)
        (fun a ha b hb c hc => hU_cap a (Finset.mem_of_mem_filter a ha)
          b (Finset.mem_of_mem_filter b hb) c (Finset.mem_of_mem_filter c hc))
    have hUpos_inj : Set.InjOn (fun u : Fin n => (F u).card) (Upos : Set (Fin n)) := by
      intro u₁ hu₁ u₂ hu₂ hcard_eq
      by_contra hne12
      have hcheck {a b : Fin n} (ha : a ∈ Upos) (hb : b ∈ Upos) (hab : a < b)
          (heq_ab : (F a).card = (F b).card) : False := by
        have haU := (Finset.mem_filter.mp ha).1
        have hbU := (Finset.mem_filter.mp hb).1
        have hne_k₀ := (Finset.mem_filter.mp ha).2
        have hgt_k₀ : k₀ < (F a).card :=
          lt_of_le_of_ne (hcard_mono first a (Nat.zero_le _)) (Ne.symm hne_k₀)
        have ha_gt_first : first < a :=
          lt_of_le_of_ne (Nat.zero_le _) (fun heq => hgt_k₀.ne (congrArg (fun x => (F x).card) heq))
        have hnot_pos := hU_cap first (Finset.mem_insert_self _ _) a haU b hbU ha_gt_first hab
        have hlaw := (orient2d_esPt_law (hmonoX ha_gt_first) (hmonoX hab)).2
        exact hnot_pos (hlaw.mpr (Or.inr ⟨hgt_k₀, heq_ab⟩))
      rcases lt_or_gt_of_ne hne12 with hlt | hgt
      · exact hcheck hu₁ hu₂ hlt hcard_eq
      · exact hcheck hu₂ hu₁ hgt hcard_eq.symm
    have hUpos_sub : Upos.image (fun u => (F u).card) ⊆ Finset.Ioc k₀ k₁ := by
      intro c hc
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
      have hne_k₀ := (Finset.mem_filter.mp hu).2
      have hgt_k₀ : k₀ < (F u).card :=
        lt_of_le_of_ne (hcard_mono first u (Nat.zero_le _)) (Ne.symm hne_k₀)
      have hle_k₁ : (F u).card ≤ k₁ := hcard_mono u last (by change u.val ≤ n - 1; omega)
      exact Finset.mem_Ioc.mpr ⟨hgt_k₀, hle_k₁⟩
    have hUpos_le : Upos.card ≤ k₁ - k₀ := by
      have hc1 := Finset.card_le_card hUpos_sub
      rw [Finset.card_image_of_injOn hUpos_inj, Nat.card_Ioc] at hc1
      exact hc1
    omega

end Erdos107H2Helper

theorem prove_Erdos107_H2 : ∀ n ≥ 3, 2 ^ (n - 2) + 1 ≤ Erdos107.f n := by
  intro n hn
  refine le_csInf (Erdos107H2Helper.cardSet_nonempty hn) (fun N hN => ?_)
  by_contra hlt
  have hle : N ≤ (Erdos107H2Helper.esPts (n - 2)).card := by
    rw [Erdos107H2Helper.esPts_card]
    omega
  obtain ⟨pts, hpts_sub, hpts_card⟩ :=
    Finset.exists_subset_card_eq hle
  have hnontri : NonTrilinear (pts : Set ℝ²) :=
    Set.Triplewise.mono (by exact_mod_cast hpts_sub) (Erdos107H2Helper.esPts_nonTrilinear (n - 2))
  obtain ⟨S, hScard, hSsub, hSconv⟩ := hN pts hpts_card hnontri
  exact Erdos107H2Helper.not_hasConvexNGon_esPts hn
    ⟨S, hScard, hSsub.trans (by exact_mod_cast hpts_sub), hSconv⟩

theorem OMA.solution : OMA.R_Erdos107_erdos_107_R1.H2 :=
  prove_Erdos107_H2
