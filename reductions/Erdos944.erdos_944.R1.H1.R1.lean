import OMAReductions.R_Erdos944_erdos_944_R1

/-!
# The four-, six-, and eight-color witnesses in Erdős 944

The four-color graph follows Sections 2–7 of Liam Kruer and Jensen Kohlmeyer,
[Vertex-critical four-chromatic graphs with no small critical edge set](https://hexagonmath.org/2611.00772v1)
(CC BY 4.0). The independent Lean argument below checks their punctured coloring
and assembles the finite witness from the arithmetic and winding inputs.
The original full formal proof was [certified by Conjectures.io](https://conjectures.io/results/e7afff2c-bb07-4fa8-92b6-67a530aaad70).
The six- and eight-color cases are covered mathematically by Ema Skottová and
Raphael Steiner, [Critical edge sets in vertex-critical graphs](https://arxiv.org/abs/2508.08703).
-/

open scoped BigOperators
open Erdos944

namespace OMA.R_Erdos944_erdos_944_R1_H1_R1

/-- The two remaining higher-color cases of the Skottová–Steiner construction. -/
def H1 : Prop :=
  ∀ k ∈ ({6, 8} : Finset ℕ), ∀ r ≥ 2,
    ∃ (V : Type) (G : SimpleGraph V), Finite V ∧ G.IsErdos944 k r

/-- Cyclic arithmetic parameters, including the three-step detours and the deficit inequality. -/
def H2 : Prop :=
  ∀ r ≥ 2, ∃ t n : ℕ, r ≤ t ∧ 3 * t + 1 < n ∧ n % 3 = 1 ∧ (3 * t + 1) ∣ n ∧
    ∃ (a : ZMod (3 * t + 1) → (ZMod n)ˣ) (S J : Finset (ZMod n)),
    (∀ i s, s ∈ S →
      let d := (((a i)⁻¹ : (ZMod n)ˣ) : ZMod n) * s
      d.val = 1 ∨ d.val = n - 1 ∨ d.val % 3 = 2) ∧
    (∀ i j, i ≠ j → ∀ l : ℕ, 1 < l → l ≤ 3 * t + 1 → l % 3 = 1 →
      ((((a i)⁻¹ : (ZMod n)ˣ) : ZMod n) * ((a j : ZMod n) * l)).val % 3 = 2) ∧
    (∀ i, (a i : ZMod n) ∈ S) ∧
    (∀ i j, i ≠ j → (a i : ZMod n) ≠ a j ∧ (a i : ZMod n) ≠ -(a j : ZMod n)) ∧
    (∀ s ∈ S, -s ∈ S ∧ s + s ≠ 0) ∧ J ⊆ S ∧
    (∀ s ∈ S, s ∈ J ∨ -s ∈ J) ∧ (∀ s ∈ J, -s ∉ J) ∧
    (∀ s ∈ J, ∃ w : Fin r → Fin 3 → ZMod n,
      (∀ i, ∑ p, w i p = s) ∧
      (∀ i p, w i p ∈ S ∧ w i p ≠ s ∧ w i p ≠ -s) ∧
      (∀ i j, i ≠ j → ∀ p z, w i p ≠ w j z ∧ w i p ≠ -w j z)) ∧
    (∀ K : ZMod n,
      (∑ s ∈ J, (n - 3 * min (K * s).val (n - (K * s).val))) ≤ r →
        ∃ i, n > 3 * min (K * (a i : ZMod n)).val (n - (K * (a i : ZMod n)).val))

/-- The finite winding criterion for the core translations and filled chords. -/
def H3 : Prop :=
  ∀ {r t n : ℕ}, r ≤ t → 3 * t + 1 < n → n % 3 = 1 →
    ∀ (hq : (3 * t + 1) ∣ n) (a : ZMod (3 * t + 1) → (ZMod n)ˣ)
      (S J : Finset (ZMod n)) (G : SimpleGraph (ZMod n)),
    ((∀ i, (a i : ZMod n) ∈ S) ∧
    (∀ i j, i ≠ j → (a i : ZMod n) ≠ a j ∧ (a i : ZMod n) ≠ -(a j : ZMod n)) ∧
    (∀ s ∈ S, -s ∈ S ∧ s + s ≠ 0) ∧ J ⊆ S ∧
    (∀ s ∈ S, s ∈ J ∨ -s ∈ J) ∧ (∀ s ∈ J, -s ∉ J) ∧
    (∀ s ∈ J, ∃ w : Fin r → Fin 3 → ZMod n,
      (∀ i, ∑ p, w i p = s) ∧
      (∀ i p, w i p ∈ S ∧ w i p ≠ s ∧ w i p ≠ -s) ∧
      (∀ i j, i ≠ j → ∀ p z, w i p ≠ w j z ∧ w i p ≠ -w j z)) ∧
    (∀ K : ZMod n,
      (∑ s ∈ J, (n - 3 * min (K * s).val (n - (K * s).val))) ≤ r →
        ∃ i, n > 3 * min (K * (a i : ZMod n)).val (n - (K * (a i : ZMod n)).val))) →
    (∀ s ∈ S, ∀ x, G.Adj x (x + s)) →
    (∀ (b : ZMod n) (j l : ℕ), 1 < l → j + l ≤ 3 * t + 1 → l % 3 = 1 →
      let d := (a (ZMod.castHom hq (ZMod (3 * t + 1)) b) : ZMod n)
      G.Adj (b + d * j) (b + d * (↑(j + l) : ZMod n))) →
    ∀ D : Finset (Sym2 (ZMod n)), D.card ≤ r →
      ¬ (G.deleteEdges (D : Set _)).Colorable 3

theorem color_ne_of_normalDifference {n : ℕ} [NeZero n] (hn : n % 3 = 1)
    {x y : ZMod n} (hx : x ≠ 0) (hy : y ≠ 0) (h : ((y - x).val = 1 ∨ (y - x).val = n - 1 ∨ (y - x).val % 3 = 2)) :
    x.val % 3 ≠ y.val % 3 := by
  have hxpos : 0 < x.val := Nat.pos_of_ne_zero (fun hzero => hx ((ZMod.val_eq_zero _).mp hzero))
  have hypos : 0 < y.val := Nat.pos_of_ne_zero (fun hzero => hy ((ZMod.val_eq_zero _).mp hzero))
  have hxlt := x.val_lt
  have hylt := y.val_lt
  have hdlt := (y - x).val_lt
  have hxy : x + (y - x) = y := by abel
  by_cases hw : x.val + (y - x).val < n
  · have hval : y.val = x.val + (y - x).val := by
      calc
        y.val = (x + (y - x)).val := congrArg ZMod.val hxy.symm
        _ = _ := ZMod.val_add_of_lt hw
    rcases h with h | h | h <;> omega
  · have hval : y.val + n = x.val + (y - x).val := by
      calc
        _ = (x + (y - x)).val + n := congrArg (fun z : ZMod n => z.val + n) hxy.symm
        _ = _ := (ZMod.val_add_val_of_le (Nat.le_of_not_gt hw)).symm
    rcases h with h | h | h <;> omega

/-- A finite `(s+1)`-critical graph robust under at most `r` edge deletions
gives the finite witness used by the first reduction of Erdős 944. -/
theorem finite_witness {V : Type*} [Finite V] (G : SimpleGraph V) (s r : ℕ)
    (hG : G.IsErdos944 (s+1) r) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin (n+1))),
      (∀ v, ∃ c : {x : Fin (n+1) // x ≠ v} → Fin s,
        ∀ x y, H.Adj x.val y.val → c x ≠ c y) ∧
      ∀ D : Finset (Sym2 (Fin (n+1))), D.card ≤ r →
        ¬ (H.deleteEdges (D : Set _)).Colorable s := by
  classical
  obtain ⟨⟨hχ,hDelete⟩,hRobust⟩ := hG
  have : Nonempty V := by
    by_contra! hEmpty
    have hzero := (SimpleGraph.chromaticNumber_eq_zero_iff (G := G)).mpr hEmpty
    rw [hzero] at hχ
    push_cast at hχ
    have hpos := (ENat.natCast_lt_add_one_iff (m := 0) (n := (s : ℕ∞))).mpr (by simp)
    exact hpos.ne hχ
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.card V ≠ 0 from Nat.card_pos.ne')
  let e : Fin (n+1) ≃ V := (Finite.equivFinOfCardEq hn).symm
  let H := G.comap e
  refine ⟨n,H,?_,?_⟩
  · intro v
    let T := (⊤ : G.Subgraph).deleteVerts ({e v} : Set V)
    have hv := hDelete (e v)
    change T.coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber at hv
    rw [SimpleGraph.chromaticNumber_congr (SimpleGraph.Subgraph.topIso (G := G)),hχ] at hv
    push_cast at hv
    have hc : T.coe.chromaticNumber ≤ (s : ℕ∞) :=
      (ENat.lt_add_one_iff (ENat.natCast_ne_top s)).mp hv
    obtain ⟨c⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp hc
    let f (x : {x : Fin (n+1) // x ≠ v}) : T.verts := ⟨e x.val, by
      have hx : e x.val ≠ e v := fun h => x.property (e.injective h)
      simp [T,hx]⟩
    refine ⟨fun x => c (f x),fun x y hxy => c.valid ?_⟩
    have h1 : e x.val ≠ e v := fun h => x.property (e.injective h)
    have h2 : e y.val ≠ e v := fun h => y.property (e.injective h)
    change G.Adj (e x.val) (e y.val) at hxy
    change T.Adj (e x.val) (e y.val)
    simpa [T,SimpleGraph.Subgraph.deleteVerts_adj,h1,h2] using hxy
  · intro D hD hc
    let E : Set (Sym2 V) := Sym2.map e '' (D : Set (Sym2 (Fin (n+1))))
    have hE : E.ncard ≤ r := by
      dsimp only [E]
      rw [Set.ncard_image_of_injective _ (Sym2.map.injective e.injective),Set.ncard_coe_finset]
      exact hD
    obtain ⟨c⟩ := hc
    have hcG : (G.deleteEdges E).Colorable s := by
      refine ⟨SimpleGraph.Coloring.mk (fun x => c (e.symm x)) ?_⟩
      intro x y hadj
      obtain ⟨hxy,hnot⟩ := SimpleGraph.deleteEdges_adj.mp hadj
      apply c.valid
      refine SimpleGraph.deleteEdges_adj.mpr ⟨?_,?_⟩
      · change G.Adj (e (e.symm x)) (e (e.symm y))
        simpa using hxy
      · intro hh
        apply hnot
        exact ⟨_,hh,by simp [Sym2.map_mk]⟩
    have hcrit : G.IsCriticalEdges E := by
      change (G.deleteEdges E).chromaticNumber < G.chromaticNumber
      rw [hχ]
      exact hcG.chromaticNumber_le.trans_lt (ENat.natCast_lt_add_one_iff.mpr le_rfl)
    exact (not_lt_of_ge hE) (hRobust E hcrit)

/-- The core and filled chords support the punctured coloring independently of the winding bound. -/
private theorem exists_augmented_with_punctured {n q : ℕ} [NeZero n]
    (hqn : q ∣ n) (hsmall : q < n) (a : ZMod q → (ZMod n)ˣ)
    (S : Finset (ZMod n)) (hn : n % 3 = 1)
    (hcore : ∀ i s, s ∈ S →
      let d := (((a i)⁻¹ : (ZMod n)ˣ) : ZMod n) * s
      d.val = 1 ∨ d.val = n - 1 ∨ d.val % 3 = 2)
    (hoff : ∀ i j : ZMod q, i ≠ j → ∀ l : ℕ, 1 < l → l ≤ q → l % 3 = 1 →
      ((((a i)⁻¹ : (ZMod n)ˣ) : ZMod n) * ((a j : ZMod n) * l)).val % 3 = 2)
    (hs : ∀ s ∈ S, s + s ≠ 0) :
    ∃ G : SimpleGraph (ZMod n), (∀ s ∈ S, ∀ x, G.Adj x (x + s)) ∧
      (∀ (b : ZMod n) (j l : ℕ), 1 < l → j + l ≤ q → l % 3 = 1 →
        let d := (a (ZMod.castHom hqn (ZMod q) b) : ZMod n)
        G.Adj (b + d * j) (b + d * (↑(j + l) : ZMod n))) ∧
      ∀ v : ZMod n, ∃ c : {x : ZMod n // x ≠ v} → Fin 3,
        ∀ x y, G.Adj x.val y.val → c x ≠ c y := by
  let projection : ZMod n →+* ZMod q := ZMod.castHom hqn _
  let coordinate (i : ZMod q) (v u : ZMod n) : ZMod n := ((a i)⁻¹ : (ZMod n)ˣ) * (u - v)
  let chord (x y : ZMod n) : Prop :=
    ∃ (b : ZMod n) (j l : ℕ), 1 < l ∧ j + l ≤ q ∧ l % 3 = 1 ∧
      x = b + (a (projection b) : ZMod n) * j ∧
      y = b + (a (projection b) : ZMod n) * (↑(j + l) : ZMod n)
  let G : SimpleGraph (ZMod n) :=
    { Adj := fun x y => x ≠ y ∧ (y - x ∈ S ∨ x - y ∈ S ∨ chord x y ∨ chord y x)
      symm := ⟨by
        intro x y h
        rcases h with ⟨hne, h | h | h | h⟩
        · exact ⟨hne.symm, Or.inr (Or.inl h)⟩
        · exact ⟨hne.symm, Or.inl h⟩
        · exact ⟨hne.symm, Or.inr (Or.inr (Or.inr h))⟩
        · exact ⟨hne.symm, Or.inr (Or.inr (Or.inl h))⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨G, ?_, ?_, ?_⟩
  · intro s hS x
    have hne : s ≠ 0 := fun h => hs s hS (by simp [h])
    refine ⟨fun h => hne (by linear_combination -h), Or.inl ?_⟩
    have he : x + s - x = s := by abel
    rwa [he]
  · intro b j l hl hjl hm
    let d : (ZMod n)ˣ := a (projection b)
    have hd : b + (d : ZMod n) * (↑(j + l) : ZMod n) -
        (b + (d : ZMod n) * j) = (d : ZMod n) * (l : ZMod n) := by push_cast; ring
    have hnz : (l : ZMod n) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt (by omega : l < n), ZMod.val_zero] at hv
      omega
    have hne : b + (d : ZMod n) * j ≠ b + (d : ZMod n) * (↑(j + l) : ZMod n) := by
      intro he
      apply hnz
      apply (Units.mul_right_eq_zero d).mp
      rw [← hd, he, sub_self]
    exact ⟨hne, Or.inr (Or.inr (Or.inl ⟨b, j, l, hl, hjl, hm, rfl, rfl⟩))⟩
  have hnonzero (i : ZMod q) (v u : ZMod n) (hu : u ≠ v) : coordinate i v u ≠ 0 := by
    exact fun hz => hu (sub_eq_zero.mp ((Units.mul_right_eq_zero _).mp hz))
  have hstep (i : ZMod q) (b v : ZMod n) (j : ℕ) :
      coordinate i v (b + (a i : ZMod n) * j) = coordinate i v b + (j : ZMod n) := by
    show (((a i)⁻¹ : (ZMod n)ˣ) : ZMod n) * (b + (a i : ZMod n) * j - v) =
      (((a i)⁻¹ : (ZMod n)ˣ) : ZMod n) * (b - v) + j
    rw [show b + (a i : ZMod n) * j - v = (b - v) + (a i : ZMod n) * j by abel,
      mul_add, ← mul_assoc, Units.inv_mul, one_mul]
  have ownColor {b v : ZMod n} (hi : projection b = projection v)
      {j l : ℕ} (hl : l % 3 = 1) (hjl : j + l ≤ q)
      (hy : b + (a (projection b) : ZMod n) * (↑(j + l) : ZMod n) ≠ v) :
      (coordinate (projection v) v (b + (a (projection b) : ZMod n) * j)).val % 3 ≠
        (coordinate (projection v) v
          (b + (a (projection b) : ZMod n) * (↑(j + l) : ZMod n))).val % 3 := by
    let z := coordinate (projection v) v b
    have hzproj : projection z = 0 := by
      simp only [z, coordinate, map_mul, map_sub, hi, sub_self, mul_zero]
    have hzdvd : q ∣ z.val := by
      have hzcast : (z.val : ZMod q) = 0 := by
        rw [← map_natCast (projection), ZMod.natCast_zmod_val, hzproj]
      simpa only [ZMod.natCast_eq_zero_iff] using hzcast
    have hzle : z.val + q ≤ n := by
      obtain ⟨i, hi⟩ := hzdvd
      obtain ⟨m, hm⟩ := hqn
      have hzlt := z.val_lt
      rw [hi, hm] at hzlt ⊢
      have him : i < m := Nat.lt_of_mul_lt_mul_left hzlt
      calc
        q * i + q = q * (i + 1) := by rw [Nat.mul_succ]
        _ ≤ q * m := Nat.mul_le_mul_left _ him
    rw [hi] at hy ⊢
    rw [hstep, hstep]
    have hycoord : z + (↑(j + l) : ZMod n) ≠ 0 := by
      simpa only [hstep] using hnonzero (projection v) v _ hy
    have hylt : z.val + (j + l) < n := by
      have hle : z.val + (j + l) ≤ n := by omega
      refine lt_of_le_of_ne hle ?_
      intro he
      apply hycoord
      calc
        _ = (↑(z.val + (j + l)) : ZMod n) := by simp
        _ = 0 := by rw [he, ZMod.natCast_self]
    have hxlt : z.val + j < n := by omega
    have hval (k : ℕ) (hk : z.val + k < n) : (z + (k : ZMod n)).val = z.val + k := by
      calc
        _ = (↑(z.val + k) : ZMod n).val := by simp
        _ = _ := ZMod.val_natCast_of_lt hk
    rw [hval _ hxlt, hval _ hylt]
    omega
  intro v
  let i := projection v
  have hcoord (x y : ZMod n) :
      coordinate i v y - coordinate i v x = ((a i)⁻¹ : (ZMod n)ˣ) * (y - x) := by
    simp only [coordinate, ← mul_sub]
    congr 1
    abel
  have hcoreColor (x y : {x : ZMod n // x ≠ v}) (h : y.val - x.val ∈ S) :
      (coordinate i v x.val).val % 3 ≠ (coordinate i v y.val).val % 3 := by
    apply color_ne_of_normalDifference hn (hnonzero i v _ x.property)
      (hnonzero i v _ y.property)
    rw [hcoord]
    exact hcore i _ h
  have hchordColor (x y : {x : ZMod n // x ≠ v}) (h : chord x.val y.val) :
      (coordinate i v x.val).val % 3 ≠ (coordinate i v y.val).val % 3 := by
    obtain ⟨b, j, l, hl, hjl, hmod, hx, hy⟩ := h
    by_cases hi : projection b = i
    · rw [hx, hy]
      exact ownColor hi hmod hjl (hy ▸ y.property)
    · apply color_ne_of_normalDifference hn (hnonzero i v _ x.property)
        (hnonzero i v _ y.property)
      rw [hcoord, hx, hy]
      have hdiff : b + (a (projection b) : ZMod n) * (↑(j + l) : ZMod n) -
          (b + (a (projection b) : ZMod n) * j) =
          (a (projection b) : ZMod n) * l := by push_cast; ring
      rw [hdiff]
      exact Or.inr (Or.inr (hoff i _ (Ne.symm hi) l hl (by omega) hmod))
  refine ⟨fun x => ⟨(coordinate i v x.val).val % 3, Nat.mod_lt _ (by decide)⟩, ?_⟩
  intro x y hadj hcolor
  have hval := congrArg Fin.val hcolor
  rcases hadj.2 with h | h | h | h
  · exact hcoreColor x y h hval
  · exact hcoreColor y x h hval.symm
  · exact hchordColor x y h hval
  · exact hchordColor y x h hval.symm


theorem main : H1 → H2 → H3 → OMA.R_Erdos944_erdos_944_R1.H1 := by
  intro hHigher hArithmetic hWinding s hs r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · obtain ⟨t, n, hrt, hsmall, hmod, hqn, a, S, J, hcore, hoff, hdata⟩ := hArithmetic r hr
    let : NeZero n := ⟨by omega⟩
    obtain ⟨G, hcoreAdj, hchordAdj, hpunctured⟩ :=
      exists_augmented_with_punctured hqn hsmall a S hmod hcore hoff
        (fun s hs => (hdata.2.2.1 s hs).2)
    have hrobust := hWinding hrt hsmall hmod hqn a S J G hdata hcoreAdj hchordAdj
    exact finite_witness G 3 r (DiracLarge.critical_of_deletion G 3 r 0 hpunctured hrobust)
  · obtain ⟨V, G, hV, hG⟩ := hHigher 6 (by simp) r hr
    let := hV
    exact finite_witness G 5 r hG
  · obtain ⟨V, G, hV, hG⟩ := hHigher 8 (by simp) r hr
    let := hV
    exact finite_witness G 7 r hG

end OMA.R_Erdos944_erdos_944_R1_H1_R1
