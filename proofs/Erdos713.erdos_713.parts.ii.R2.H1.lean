import OMAReductions.R_Erdos713_erdos_713_parts_ii_R2
import Mathlib

/-! Step Erdos713.erdos_713.parts.ii.R2.H1: hypothesis H1 of reduction Erdos713.erdos_713.parts.ii.R2.
Credit: @ivillar. The edge-deletion graph `avoid` and its edge count follow our earlier merged
proof proofs/Erdos713.erdos_713.parts.ii.R1.H2.R1.H1.lean. Let J be F with the vertex v of
degree at most one deleted. For an F-free host, delete the edges at vertices of degree < r; the
rest is J-free (a copy of J extends to F through a high-degree neighbour, or, when the image of
the neighbour u of v has low degree, u is a leaf and an edge avoiding the copy replaces u v).
So ex(n, F) <= ex(n, J) + 2 r n, which is o(n^alpha) for alpha > 1, contradicting minimality. -/

open SimpleGraph Finset Filter Asymptotics

namespace OMA713R2H1

open scoped Classical

/-- The graph `H` with every edge meeting `T` deleted. -/
def avoid {n : ℕ} (H : SimpleGraph (Fin n)) (T : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y := H.Adj x y ∧ x ∉ T ∧ y ∉ T
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => H.loopless.irrefl x h.1⟩

lemma card_edgeFinset_le_avoid {n : ℕ} (H : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    #H.edgeFinset ≤ #(avoid H T).edgeFinset + ∑ t ∈ T, H.degree t := by
  have hsub : H.edgeFinset ⊆ (avoid H T).edgeFinset ∪ T.biUnion (fun t => H.incidenceFinset t) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      by_cases hx : x ∈ T
      · apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        exact ⟨x, hx, by rw [mem_incidenceFinset, mem_incidenceSet]; exact he⟩
      · by_cases hy : y ∈ T
        · apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          refine ⟨y, hy, ?_⟩
          rw [mem_incidenceFinset, Sym2.eq_swap, mem_incidenceSet]
          exact he.symm
        · apply Finset.mem_union_left
          rw [mem_edgeFinset, mem_edgeSet]
          exact ⟨he, hx, hy⟩
  calc #H.edgeFinset ≤ #((avoid H T).edgeFinset ∪ T.biUnion (fun t => H.incidenceFinset t)) :=
        Finset.card_le_card hsub
    _ ≤ #(avoid H T).edgeFinset + #(T.biUnion (fun t => H.incidenceFinset t)) :=
        Finset.card_union_le _ _
    _ ≤ #(avoid H T).edgeFinset + ∑ t ∈ T, #(H.incidenceFinset t) := by
        gcongr
        exact Finset.card_biUnion_le
    _ = #(avoid H T).edgeFinset + ∑ t ∈ T, H.degree t := by
        congr 1
        exact Finset.sum_congr rfl fun t _ => card_incidenceFinset_eq_degree H t

lemma exists_adj_avoid {n : ℕ} (H : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (h : 0 < #(avoid H T).edgeFinset) : ∃ a b, H.Adj a b ∧ a ∉ T ∧ b ∉ T := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  induction x using Sym2.ind with
  | _ a b =>
    rw [mem_edgeFinset, mem_edgeSet] at hx
    exact ⟨a, b, hx⟩

/-- Deleting a vertex of degree at most one changes the extremal number by `O(n)`. -/
lemma key_bound {r : ℕ} (F : SimpleGraph (Fin r)) (v : Fin r) (hv : F.degree v < 2)
    {s : ℕ} (J : SimpleGraph (Fin s)) (e : J ≃g F.induce ({v}ᶜ : Set (Fin r))) (hsr : s < r)
    (n : ℕ) : extremalNumber n F ≤ extremalNumber n J + 2 * r * n := by
  have key : ∀ (G : SimpleGraph (Fin n)), F.Free G →
      #G.edgeFinset ≤ extremalNumber n J + 2 * r * n := by
    intro G hfree
    by_contra hbig
    have hbig' : extremalNumber n J + 2 * r * n < #G.edgeFinset := by omega
    -- the host has at least `r` vertices
    have hnr : r ≤ n := by
      by_contra hlt
      have h1 := G.card_edgeFinset_le_card_choose_two
      rw [Fintype.card_fin, Nat.choose_two_right] at h1
      have h2 : n * (n - 1) / 2 ≤ n * n := (Nat.div_le_self _ _).trans
        (Nat.mul_le_mul_left n (Nat.sub_le n 1))
      have h3 : n * n ≤ r * n := Nat.mul_le_mul_right n (by omega)
      have h4 : r * n ≤ 2 * r * n := by nlinarith
      omega
    have hdegle : ∀ x : Fin n, G.degree x ≤ n := fun x => by
      have := G.degree_lt_card_verts x
      rw [Fintype.card_fin] at this
      omega
    -- low-degree vertices
    set L : Finset (Fin n) := univ.filter (fun x => G.degree x < r) with hLdef
    have hL : #G.edgeFinset ≤ #(avoid G L).edgeFinset + r * n := by
      have h1 := card_edgeFinset_le_avoid G L
      have h2 : ∑ t ∈ L, G.degree t ≤ ∑ _t ∈ L, r :=
        Finset.sum_le_sum fun t ht => (Finset.mem_filter.mp ht).2.le
      have h3 : #L ≤ n := by
        have := Finset.card_le_univ L
        rwa [Fintype.card_fin] at this
      rw [Finset.sum_const, smul_eq_mul] at h2
      have h4 : #L * r ≤ r * n := by nlinarith
      omega
    have hJ : J ⊑ avoid G L := by
      by_contra hno
      have := card_edgeFinset_le_extremalNumber hno
      rw [Fintype.card_fin] at this
      have : r * n ≤ 2 * r * n := by nlinarith
      omega
    obtain ⟨f⟩ := hJ
    set S : Set (Fin r) := ({v}ᶜ : Set (Fin r)) with hSdef
    have memS : ∀ x : Fin r, x ≠ v → x ∈ S := fun x hx => Set.mem_compl_singleton_iff.mpr hx
    -- the vertex attached to `x ≠ v`
    let g : ∀ x : Fin r, x ≠ v → Fin n := fun x hx => f (e.symm ⟨x, memS x hx⟩)
    have hgadj : ∀ x y (hx : x ≠ v) (hy : y ≠ v), F.Adj x y → (avoid G L).Adj (g x hx) (g y hy) := by
      intro x y hx hy hxy
      apply f.toHom.map_adj
      rw [e.symm.map_adj_iff]
      simpa using hxy
    have hginj : ∀ x y (hx : x ≠ v) (hy : y ≠ v), g x hx = g y hy → x = y := by
      intro x y hx hy hxy
      have := e.symm.injective (f.injective hxy)
      simpa using congrArg Subtype.val this
    set T : Finset (Fin n) := univ.image (fun z => f z) with hTdef
    have hgT : ∀ x (hx : x ≠ v), g x hx ∈ T := fun x hx =>
      Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hTcard : #T < r := by
      calc #T ≤ #(univ : Finset (Fin s)) := Finset.card_image_le
        _ = s := by simp
        _ < r := hsr
    apply hfree
    by_cases hiso : ∀ y, ¬ F.Adj v y
    · -- `v` is isolated: any unused vertex will do
      obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := T) (t := univ) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
      let φ : Fin r → Fin n := fun x => if hx : x = v then w else g x hx
      have hmap : ∀ {x y : Fin r}, F.Adj x y → G.Adj (φ x) (φ y) := by
        intro x y hxy
        by_cases hx : x = v
        · exact absurd (hx ▸ hxy) (hiso y)
        by_cases hy : y = v
        · exact absurd (hy ▸ hxy.symm) (hiso x)
        simp only [φ, dif_neg hx, dif_neg hy]
        exact (hgadj x y hx hy hxy).1
      have hinj : Function.Injective φ := by
        intro x y hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · rw [hx, hy]
        · simp only [φ, dif_pos hx, dif_neg hy] at hxy
          exact absurd (hxy ▸ hgT y hy) hw
        · simp only [φ, dif_neg hx, dif_pos hy] at hxy
          exact absurd (hxy.symm ▸ hgT x hx) hw
        · simp only [φ, dif_neg hx, dif_neg hy] at hxy
          exact hginj x y hx hy hxy
      exact ⟨⟨⟨φ, hmap⟩, hinj⟩⟩
    push Not at hiso
    obtain ⟨u, hvu⟩ := hiso
    have huniq : ∀ y, F.Adj v y → y = u := by
      intro y hy
      have hle : #(F.neighborFinset v) ≤ 1 := by
        rw [card_neighborFinset_eq_degree]; omega
      exact Finset.card_le_one.mp hle y (by simpa using hy) u (by simpa using hvu)
    have huv : u ≠ v := fun h => F.loopless.irrefl v (h ▸ hvu)
    set u0 := g u huv with hu0def
    by_cases hu0 : u0 ∈ L
    · -- the image of `u` has low degree: `u` is a leaf attached only to `v`
      have honly : ∀ y, F.Adj u y → y = v := by
        intro y hy
        by_contra hyv
        have := (hgadj u y huv hyv hy).2.1
        exact this hu0
      set T' := T.erase u0 with hT'def
      have hT'card : #T' < r := (Finset.card_erase_le).trans_lt hTcard
      have h1 := card_edgeFinset_le_avoid G T'
      have h2 : ∑ t ∈ T', G.degree t ≤ ∑ _t ∈ T', n := Finset.sum_le_sum fun t _ => hdegle t
      rw [Finset.sum_const, smul_eq_mul] at h2
      have h3 : #T' * n ≤ r * n := Nat.mul_le_mul_right n hT'card.le
      have h4 : r * n ≤ 2 * r * n := by nlinarith
      obtain ⟨a, b, hab, haT, hbT⟩ := exists_adj_avoid G T' (by omega)
      have hab' : a ≠ b := G.ne_of_adj hab
      let φ : Fin r → Fin n := fun x => if hx : x = v then b else if x = u then a else g x hx
      have hgT' : ∀ x (hx : x ≠ v), x ≠ u → g x hx ∈ T' := by
        intro x hx hxu
        refine Finset.mem_erase.mpr ⟨fun h => hxu (hginj x u hx huv h), hgT x hx⟩
      have hmap : ∀ {x y : Fin r}, F.Adj x y → G.Adj (φ x) (φ y) := by
        intro x y hxy
        by_cases hx : x = v
        · subst hx
          have hy := huniq y hxy
          subst hy
          simp only [φ, dif_pos rfl, dif_neg huv]
          exact hab.symm
        by_cases hy : y = v
        · subst hy
          have hx' := huniq x hxy.symm
          subst hx'
          simp only [φ, dif_pos rfl, dif_neg huv]
          exact hab
        by_cases hxu : x = u
        · subst hxu
          exact absurd (honly y hxy) hy
        by_cases hyu : y = u
        · subst hyu
          exact absurd (honly x hxy.symm) hx
        simp only [φ, dif_neg hx, dif_neg hy, if_neg hxu, if_neg hyu]
        exact (hgadj x y hx hy hxy).1
      have hinj : Function.Injective φ := by
        intro x y hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · rw [hx, hy]
        · exfalso
          simp only [φ, dif_pos hx, dif_neg hy] at hxy
          by_cases hyu : y = u
          · simp only [if_pos hyu] at hxy; exact hab' hxy.symm
          · simp only [if_neg hyu] at hxy; exact hbT (hxy ▸ hgT' y hy hyu)
        · exfalso
          simp only [φ, dif_neg hx, dif_pos hy] at hxy
          by_cases hxu : x = u
          · simp only [if_pos hxu] at hxy; exact hab' hxy
          · simp only [if_neg hxu] at hxy; exact hbT (hxy.symm ▸ hgT' x hx hxu)
        · simp only [φ, dif_neg hx, dif_neg hy] at hxy
          by_cases hxu : x = u <;> by_cases hyu : y = u
          · rw [hxu, hyu]
          · exfalso
            simp only [if_pos hxu, if_neg hyu] at hxy
            exact haT (hxy ▸ hgT' y hy hyu)
          · exfalso
            simp only [if_neg hxu, if_pos hyu] at hxy
            exact haT (hxy.symm ▸ hgT' x hx hxu)
          · simp only [if_neg hxu, if_neg hyu] at hxy
            exact hginj x y hx hy hxy
      exact ⟨⟨⟨φ, hmap⟩, hinj⟩⟩
    · -- the image of `u` has degree at least `r`: attach `v` to an unused neighbour
      have hdeg : r ≤ G.degree u0 := by
        by_contra hlt
        exact hu0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      obtain ⟨w, hwN, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := T) (t := G.neighborFinset u0) (by rw [card_neighborFinset_eq_degree]; omega)
      have hwadj : G.Adj u0 w := (mem_neighborFinset G u0 w).mp hwN
      let φ : Fin r → Fin n := fun x => if hx : x = v then w else g x hx
      have hmap : ∀ {x y : Fin r}, F.Adj x y → G.Adj (φ x) (φ y) := by
        intro x y hxy
        by_cases hx : x = v
        · subst hx
          have hy := huniq y hxy
          subst hy
          simp only [φ, dif_pos rfl, dif_neg huv]
          exact hwadj.symm
        by_cases hy : y = v
        · subst hy
          have hx' := huniq x hxy.symm
          subst hx'
          simp only [φ, dif_pos rfl, dif_neg huv]
          exact hwadj
        simp only [φ, dif_neg hx, dif_neg hy]
        exact (hgadj x y hx hy hxy).1
      have hinj : Function.Injective φ := by
        intro x y hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · rw [hx, hy]
        · simp only [φ, dif_pos hx, dif_neg hy] at hxy
          exact absurd (hxy ▸ hgT y hy) hw
        · simp only [φ, dif_neg hx, dif_pos hy] at hxy
          exact absurd (hxy.symm ▸ hgT x hx) hw
        · simp only [φ, dif_neg hx, dif_neg hy] at hxy
          exact hginj x y hx hy hxy
      exact ⟨⟨⟨φ, hmap⟩, hinj⟩⟩
  have := (extremalNumber_le_iff (V := Fin n) F
    (extremalNumber n J + 2 * r * n)).mpr (fun H _ hH => by convert key H hH)
  rwa [Fintype.card_fin] at this

lemma lin_littleO (α : ℝ) (hα : 1 < α) :
    (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
  rw [isLittleO_iff]
  intro c hc
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (1 / c), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.norm_of_nonneg hn0.le, Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)]
  have hsplit : (n : ℝ) ^ α = n * (n : ℝ) ^ (α - 1) := by
    rw [Real.rpow_sub hn0, Real.rpow_one]
    field_simp
  rw [hsplit]
  have h1 : 1 ≤ c * (n : ℝ) ^ (α - 1) := by
    rw [div_le_iff₀ hc] at hn
    linarith
  nlinarith

theorem main_H1 : OMA.R_Erdos713_erdos_713_parts_ii_R2.H1 := by
  intro r F hv α hα hnot hmin
  obtain ⟨v, hv⟩ := hv
  let S : Set (Fin r) := ({v}ᶜ : Set (Fin r))
  let J := (F.induce S).overFin rfl
  let e : J ≃g F.induce S := ((F.induce S).overFinIso rfl).symm
  have hJF : J ⊑ F := ⟨(Copy.induce F S).comp e.toCopy⟩
  have hsr : Fintype.card S < r := by
    have := Fintype.card_subtype_lt (p := (· ∈ S)) (x := v) (by simp [S])
    simpa using this
  have hedge : #J.edgeFinset ≤ #F.edgeFinset := by
    obtain ⟨c⟩ := hJF
    have := Fintype.card_le_of_embedding c.mapEdgeSet
    simpa only [edgeFinset_card] using this
  have hJo := hmin (Fintype.card S) J hJF (by omega)
  apply hnot
  have hb : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop]
      (fun n : ℕ => (extremalNumber n J : ℝ) + 2 * r * (n : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Eventually.of_forall fun n => ?_
    have h := key_bound F v hv J e hsr n
    have h' : (extremalNumber n F : ℝ) ≤ (extremalNumber n J : ℝ) + 2 * r * (n : ℝ) := by
      exact_mod_cast h
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    exact h'
  have hs : (fun n : ℕ => (extremalNumber n J : ℝ) + 2 * r * (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ α) :=
    hJo.add ((lin_littleO α hα).const_mul_left (2 * r))
  exact hb.trans_isLittleO hs

end OMA713R2H1

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R2.H1 := OMA713R2H1.main_H1
