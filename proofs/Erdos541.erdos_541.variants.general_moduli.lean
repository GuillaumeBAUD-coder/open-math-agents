import FormalConjectures.ErdosProblems.«541»

/-
Graham's conjecture on equal-length zero sums in cyclic groups.

The proof follows Gao, Hamidoune and Wang (https://arxiv.org/abs/0902.4758).
It uses the Moser–Scherk sumset bound for the large-length case and
Savchev and Chen's normalization (https://arxiv.org/abs/math/0602568)
for the short-length case.
-/

open scoped Pointwise BigOperators

namespace Graham541

/-- The Moser–Scherk bound in the case of a unique representation of zero. -/
theorem card_add_ge_of_unique_zero {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (ha₀ : 0 ∈ A) (hb₀ : 0 ∈ B)
    (hu : ∀ a ∈ A, ∀ b ∈ B, a + b = 0 → b = 0) :
    A.card + B.card ≤ (A + B).card + 1 := by
  classical
  suffices aux : ∀ n : ℕ, ∀ A B : Finset G, B.card = n → 0 ∈ A → 0 ∈ B →
      (∀ a ∈ A, ∀ b ∈ B, a + b = 0 → b = 0) →
      A.card + B.card ≤ (A + B).card + 1 from aux B.card A B rfl ha₀ hb₀ hu
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A B hn ha₀ hb₀ hu
    by_cases hstable : ∀ e ∈ A, ∀ b ∈ B, b + e ∈ A
    · have hb_eq (b : G) (hb : b ∈ B) : b = 0 := by
        let Z := A.image (fun a => a + b)
        have hz : Z ⊆ A := by
          intro z hz
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
          simpa [add_comm] using hstable a ha b hb
        have hc : Z.card = A.card := Finset.card_image_of_injective _ (add_left_injective b)
        have hζ := Finset.eq_of_subset_of_card_le hz hc.ge
        obtain ⟨a, ha, hs⟩ := Finset.mem_image.mp (hζ.symm ▸ ha₀ : 0 ∈ Z)
        exact hu a ha b hb hs
      have hb : B = {0} := by
        ext x
        simp only [Finset.mem_singleton]
        exact ⟨hb_eq x, fun h => h ▸ hb₀⟩
      rw [hb]
      change A.card + 1 ≤ (A + 0).card + 1
      rw [add_zero]
    · push Not at hstable
      obtain ⟨e, he, b, hb, hbe⟩ := hstable
      let T := B.image (fun z => z + e)
      let A' := A ∪ T
      let B' := B.filter (fun z => z + e ∈ A)
      have ha' : 0 ∈ A' := Finset.mem_union.mpr (Or.inl ha₀)
      have hb' : 0 ∈ B' := Finset.mem_filter.mpr ⟨hb₀, by simpa using he⟩
      have hu' (x : G) (hx : x ∈ A') (y : G) (hy : y ∈ B') (hs : x + y = 0) :
          y = 0 := by
        obtain ⟨hyB, hyA⟩ := Finset.mem_filter.mp hy
        rcases Finset.mem_union.mp hx with hxA | hxT
        · exact hu x hxA y hyB hs
        · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hxT
          have hz₀ : z = 0 := hu (y + e) hyA z hz (by simpa [add_comm, add_left_comm, add_assoc] using hs)
          exact hu e he y hyB (by simpa [hz₀] using hs)
      have hI : B'.image (fun z => z + e) = A ∩ T := by
        ext z
        constructor
        · intro hz
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨hB, hA⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_inter.mpr ⟨hA, Finset.mem_image_of_mem _ hB⟩
        · intro hz
          obtain ⟨hA, hT⟩ := Finset.mem_inter.mp hz
          obtain ⟨x, hB, rfl⟩ := Finset.mem_image.mp hT
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hB, hA⟩)
      have hcards : A'.card + B'.card = A.card + B.card := by
        change (A ∪ T).card + B'.card = A.card + B.card
        rw [← Finset.card_image_of_injective B' (add_left_injective e), hI,
          Finset.card_union_add_card_inter, show T.card = B.card from
            Finset.card_image_of_injective B (add_left_injective e)]
      have hsum : A' + B' ⊆ A + B := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
        obtain ⟨hyB, hyA⟩ := Finset.mem_filter.mp hy
        rcases Finset.mem_union.mp hx with hxA | hxT
        · exact Finset.mem_add.mpr ⟨x, hxA, y, hyB, rfl⟩
        · obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hxT
          exact Finset.mem_add.mpr ⟨y + e, hyA, x, hxB, by abel⟩
      have hp : B'.card < n := by
        rw [← hn]
        exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨b, hb, hbe⟩)
      rw [← hcards]
      exact (ih B'.card hp A' B' rfl ha' hb' hu').trans
        (Nat.add_le_add_right (Finset.card_le_card hsum) _)

end Graham541

namespace Graham541

/-- A squarefree partition bounds the length of a shortest zero-sum subsequence. -/
theorem short_zero_sum_of_partition {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]
    (a : I → G) (t : ℕ) (label : I → Fin t) (hcard : Fintype.card G ≤ Fintype.card I)
    (hinj : ∀ i j, label i = label j → a i = a j → i = j) :
    ∃ S : Finset I, S.Nonempty ∧ S.card ≤ t ∧ (∑ i ∈ S, a i) = 0 := by
  classical
  by_contra! hn
  let good (k : ℕ) (S : Finset I) :=
    Set.InjOn label (S : Set I) ∧ ∀ i ∈ S, (label i).val < k
  let active (k : ℕ) := (Finset.univ : Finset I).filter (fun i => (label i).val < k)
  let block (k : ℕ) := (Finset.univ : Finset I).filter (fun i => (label i).val = k)
  let sums (k : ℕ) := (((Finset.univ : Finset I).powerset).filter (good k)).image
    (fun S => ∑ i ∈ S, a i)
  have hmem (k : ℕ) (s : G) :
      s ∈ sums k ↔ ∃ S : Finset I, good k S ∧ ∑ i ∈ S, a i = s := by
    simp only [sums, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
  have hzero (k : ℕ) : 0 ∈ sums k :=
    (hmem k 0).mpr ⟨∅, by simp [good], by simp⟩
  have hgood_next (k : ℕ) (S : Finset I) (hS : good k S) : good (k + 1) S :=
    ⟨hS.1, fun i hi => (hS.2 i hi).trans (Nat.lt_succ_self k)⟩
  have hnew (k : ℕ) (S : Finset I) (hS : good k S) (j : I) (hj : (label j).val = k) :
      j ∉ S ∧ good (k + 1) (insert j S) := by
    refine ⟨fun h => (hS.2 j h).ne hj, ⟨?_, ?_⟩⟩
    · intro i hi l hl h
      change i ∈ insert j S at hi
      change l ∈ insert j S at hl
      rcases Finset.mem_insert.mp hi with hij | hiS
      · rcases Finset.mem_insert.mp hl with hlj | hlS
        · exact hij.trans hlj.symm
        · rw [hij] at h
          have he := congrArg Fin.val h
          have hlk := hS.2 l hlS
          omega
      · rcases Finset.mem_insert.mp hl with hlj | hlS
        · rw [hlj] at h
          have he := congrArg Fin.val h
          have hik := hS.2 i hiS
          omega
        · exact hS.1 hiS hlS h
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · omega
      · exact (hgood_next k S hS).2 i hi
  have hsize {k : ℕ} {S : Finset I} (hS : good k S) : S.card ≤ t := by
    rw [← Finset.card_image_of_injOn hS.1]
    simpa using (Finset.card_le_univ (S.image label))
  have hcount (k : ℕ) (hk : k ≤ t) : (active k).card + 1 ≤ (sums k).card := by
    induction k with
    | zero => simpa [active] using Finset.card_pos.mpr ⟨0, hzero 0⟩
    | succ k ih =>
      have hkt : k < t := hk
      have hi := ih (Nat.le_of_lt hkt)
      let B := insert (0 : G) ((block k).image a)
      have hB₀ : 0 ∈ B := Finset.mem_insert_self _ _
      have hB (v : G) (hv : v ∈ B) (h : v ≠ 0) :
          ∃ j ∈ block k, a j = v := by
        rcases Finset.mem_insert.mp hv with h0 | hv
        · exact (h h0).elim
        · exact Finset.mem_image.mp hv
      have hcardB : B.card = (block k).card + 1 := by
        have hb_inj : Set.InjOn a (block k : Set I) := by
          intro u hu v hv huv
          have h₁ := (Finset.mem_filter.mp hu).2
          have h₂ := (Finset.mem_filter.mp hv).2
          exact hinj u v (Fin.ext (h₁.trans h₂.symm)) huv
        have hnot : (0 : G) ∉ (block k).image a := by
          intro h
          obtain ⟨j, hj, ha⟩ := Finset.mem_image.mp h
          exact hn {j} (by simp) (by simp; omega) (by simpa using ha)
        rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hb_inj]
      have hvalid (u : G) (hu : u ∈ sums k) (v : G) (hv : v ∈ B) (hv₀ : v ≠ 0) :
          ∃ S : Finset I, good (k + 1) S ∧ S.Nonempty ∧ ∑ i ∈ S, a i = u + v := by
        obtain ⟨X, hX, hXsum⟩ := (hmem k u).mp hu
        obtain ⟨j, hj, haj⟩ := hB v hv hv₀
        have ⟨hXj, hY⟩ := hnew k X hX j (Finset.mem_filter.mp hj).2
        exact ⟨insert j X, hY, ⟨j, Finset.mem_insert_self _ _⟩,
          by rw [Finset.sum_insert hXj, hXsum, haj, add_comm]⟩
      have hunique (u : G) (hu : u ∈ sums k) (v : G) (hv : v ∈ B) (hsum : u + v = 0) :
          v = 0 := by
        by_contra hne
        obtain ⟨Y, hY, hYne, hYsum⟩ := hvalid u hu v hv hne
        exact hn Y hYne (hsize hY) (hYsum.trans hsum)
      have hinc : sums k + B ⊆ sums (k + 1) := by
        intro z hz
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hz
        by_cases hv₀ : v = 0
        · obtain ⟨X, hX, hXsum⟩ := (hmem k u).mp hu
          exact (hmem _ _).mpr ⟨X, hgood_next k X hX, by simpa [hv₀] using hXsum⟩
        · obtain ⟨X, hX, _, hXsum⟩ := hvalid u hu v hv hv₀
          exact (hmem _ _).mpr ⟨X, hX, hXsum⟩
      have hsum := (card_add_ge_of_unique_zero (sums k) B (hzero k) hB₀ hunique).trans
        (Nat.add_le_add_right (Finset.card_le_card hinc) 1)
      have hActive : active (k + 1) = active k ∪ block k := by
        ext i
        simp [active, block]
        omega
      have hDisj : Disjoint (active k) (block k) := Finset.disjoint_left.mpr (by
        intro i hi hj
        have h₁ := (Finset.mem_filter.mp hi).2
        have h₂ := (Finset.mem_filter.mp hj).2
        omega)
      rw [hActive, Finset.card_union_of_disjoint hDisj]
      rw [hcardB] at hsum
      omega
  have hAll : active t = Finset.univ := by ext i; simp [active]
  have hBig := hcount t le_rfl
  rw [hAll, Finset.card_univ] at hBig
  have hSmall := Finset.card_le_univ (sums t)
  omega

end Graham541

namespace Graham541

/-- Moser–Scherk gives a zero-sum of length at most the largest multiplicity
whenever the sequence has at least as many entries as the group. -/
theorem short_zero_sum {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype I]
    (a : I → G) (t : ℕ) (hcard : Fintype.card G ≤ Fintype.card I)
    (hmult : ∀ v : G, ((Finset.univ : Finset I).filter (fun i => a i = v)).card ≤ t) :
    ∃ S : Finset I, S.Nonempty ∧ S.card ≤ t ∧ (∑ i ∈ S, a i) = 0 := by
  classical
  let fiber (v : G) := (Finset.univ : Finset I).filter (fun i => a i = v)
  let enc (v : G) : ↥(fiber v) ↪ Fin t :=
    (Fintype.equivFin ↥(fiber v)).toEmbedding.trans (Fin.castLEEmb (by
      simpa only [Fintype.card_coe] using hmult v))
  let val (i : I) (v : G) (h : a i = v) : Fin t :=
    enc v ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have val_eq (i : I) (v w : G) (hv : a i = v) (hw : v = w) :
      val i v hv = val i w (hv.trans hw) := by subst w; rfl
  let label (i : I) : Fin t := val i (a i) rfl
  apply short_zero_sum_of_partition a t label hcard
  intro i j hlabels hvalue
  have hsame : val i (a i) rfl = val j (a i) hvalue.symm := hlabels.trans
    (val_eq j (a j) (a i) rfl hvalue.symm)
  exact congrArg Subtype.val ((enc (a i)).injective hsame)

/-- Pad a subset by a prescribed number of copies of a single value. -/
theorem common_length_of_padding {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype I]
    (a : I → G) (r : ℕ)
    (huniform : ∀ S : Finset I, S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r)
    (v : G) (B : Finset I) (hB : ∀ i ∈ B, a i ≠ v)
    (k : ℕ) (hk : k ≤ ((Finset.univ : Finset I).filter (fun i => a i = v)).card)
    (hn : 0 < B.card + k) (hz : (∑ i ∈ B, a i) + k • v = 0) :
    B.card + k = r := by
  classical
  obtain ⟨D, hDC, hD⟩ := Finset.exists_subset_card_eq hk
  have hv (i : I) (hi : i ∈ D) : a i = v := (Finset.mem_filter.mp (hDC hi)).2
  have hd : Disjoint B D := Finset.disjoint_left.mpr (fun i hiB hiD =>
    hB i hiB (hv i hiD))
  have hsumD : (∑ i ∈ D, a i) = k • v := by
    calc
      (∑ i ∈ D, a i) = ∑ _i ∈ D, v := Finset.sum_congr rfl hv
      _ = _ := by simp [hD]
  have hcard : (B ∪ D).card = B.card + k := by rw [Finset.card_union_of_disjoint hd, hD]
  have hne : (B ∪ D).Nonempty := Finset.card_pos.mp (hcard.symm ▸ hn)
  exact hcard.symm.trans (huniform (B ∪ D) hne (by rw [Finset.sum_union hd, hsumD]; exact hz))

end Graham541

namespace Graham541

/-- A value occurring at least as often as the common large zero-sum length
has either full order or order exactly half the modulus. -/
theorem order_of_frequent_value {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (huniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r)
    (hlarge : p ≤ 2 * r) (v : ZMod p)
    (hv : r ≤ ((Finset.univ : Finset (Fin p)).filter (fun i => a i = v)).card) :
    addOrderOf v = p ∨ (addOrderOf v = r ∧ p = 2 * r) := by
  classical
  by_cases h : addOrderOf v = p
  · exact Or.inl h
  · right
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have hq : 0 < addOrderOf v := addOrderOf_pos v
    have hdiv : addOrderOf v ∣ p :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simp [nsmul_eq_mul])
    obtain ⟨d, hd⟩ := hdiv
    have htwo : 2 ≤ d := by
      by_contra! hl
      interval_cases d
      · simp at hd
        omega
      · simp at hd
        exact h hd.symm
    have hhalf : 2 * addOrderOf v ≤ p := by
      calc
        2 * addOrderOf v = addOrderOf v * 2 := Nat.mul_comm _ _
        _ ≤ addOrderOf v * d := Nat.mul_le_mul_left _ htwo
        _ = p := hd.symm
    have hqv : addOrderOf v ≤ ((Finset.univ : Finset (Fin p)).filter
        (fun i => a i = v)).card := (show addOrderOf v ≤ r by omega).trans hv
    have hz : (∑ i ∈ (∅ : Finset (Fin p)), a i) + addOrderOf v • v = 0 := by
      rw [Finset.sum_empty, zero_add]
      exact addOrderOf_nsmul_eq_zero v
    have hr : addOrderOf v = r := by
      simpa using common_length_of_padding a r huniform v ∅ (by simp) (addOrderOf v)
        hqv (by simpa using hq) hz
    exact ⟨hr, by omega⟩

end Graham541

namespace Graham541

/-- Some value occurs at least as often as the common length of the zero-sums. -/
theorem exists_frequent_value {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (huniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r) :
    ∃ v : ZMod p, r ≤ ((Finset.univ : Finset (Fin p)).filter (fun i => a i = v)).card := by
  classical
  let freq (v : ZMod p) := ((Finset.univ : Finset (Fin p)).filter (fun i => a i = v)).card
  obtain ⟨v, _, hmax⟩ := Finset.exists_max_image Finset.univ freq Finset.univ_nonempty
  obtain ⟨S, hS, hle, hz⟩ := short_zero_sum a (freq v) (by simp [ZMod.card])
    (fun x => hmax x (Finset.mem_univ x))
  exact ⟨v, (huniform S hS hz) ▸ hle⟩

theorem isUnit_of_full_addOrder {p : ℕ} [NeZero p] (v : ZMod p) (hv : addOrderOf v = p) :
    IsUnit v := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have horder := ZMod.addOrderOf_coe v.val (NeZero.ne p)
  rw [ZMod.natCast_zmod_val, hv] at horder
  have hpos : 0 < p.gcd v.val := Nat.gcd_pos_of_pos_left _ hp
  have hgcd : p.gcd v.val = 1 := by
    by_contra hne
    have hlt := Nat.div_lt_self hp (show 1 < p.gcd v.val by omega)
    omega
  have hc : v.val.Coprime p := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    exact hgcd
  simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime v.val p).mpr hc

/-- Multiplying by the inverse of a unit preserves the common-length hypothesis
and takes the selected repeated value to one. -/
theorem via_unit_normalization {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (huniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r)
    (v : ZMod p) (hv : IsUnit v)
    (hm : r ≤ ((Finset.univ : Finset (Fin p)).filter (fun i => a i = v)).card)
    (hsolve : ∀ b : Fin p → ZMod p,
      (∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, b i) = 0 → S.card = r) →
      r ≤ ((Finset.univ : Finset (Fin p)).filter (fun i => b i = 1)).card →
      (Set.range b).ncard ≤ 2) :
    (Set.range a).ncard ≤ 2 := by
  classical
  obtain ⟨u, rfl⟩ := hv
  let scale (x : ZMod p) := (↑u⁻¹ : ZMod p) * x
  have hinj : Function.Injective scale := by
    intro x y h
    have hh := congrArg (fun z : ZMod p => (u : ZMod p) * z) h
    simpa [scale, ← mul_assoc] using hh
  let b := scale ∘ a
  have hbu (S : Finset (Fin p)) (hS : S.Nonempty) (hs : (∑ i ∈ S, b i) = 0) :
      S.card = r := by
    apply huniform S hS
    apply hinj
    simpa [scale, b, Finset.mul_sum] using hs
  have hones : (Finset.univ.filter (fun i => b i = 1)) =
      Finset.univ.filter (fun i => a i = (u : ZMod p)) := by
    have hval : scale (u : ZMod p) = 1 := by simp [scale]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change scale (a i) = 1 ↔ _
    rw [← hval, hinj.eq_iff]
  have hb := hsolve b hbu (by rwa [hones])
  rwa [show Set.range b = scale '' Set.range a from Set.range_comp _ _,
    Set.ncard_image_of_injective _ hinj] at hb

end Graham541

namespace GrahamLarge541

private theorem sum_ones {p : ℕ} (a : Fin p → ZMod p) (B : Finset (Fin p))
    (hB : ∀ i ∈ B, a i = 1) : (∑ i ∈ B, a i) = (B.card : ZMod p) := by
  calc
    (∑ i ∈ B, a i) = ∑ _i ∈ B, (1 : ZMod p) := Finset.sum_congr rfl hB
    _ = (B.card : ZMod p) := by simp

private theorem pad {p : ℕ} (a : Fin p → ZMod p) (B O : Finset (Fin p))
    (hB : ∀ i ∈ B, a i ≠ 1) (hO : ∀ i ∈ O, a i = 1) (k : ℕ) (hk : k ≤ O.card) :
    ∃ T : Finset (Fin p), B ⊆ T ∧ T ⊆ B ∪ O ∧ T.card = B.card+k ∧
      (∑ i ∈ T, a i) = (∑ i ∈ B, a i) + (k : ZMod p) := by
  obtain ⟨D,hDO,hD⟩ := Finset.exists_subset_card_eq hk
  have hd : Disjoint B D := Finset.disjoint_left.mpr fun i hiB hiD => hB i hiB (hO i (hDO hiD))
  refine ⟨B ∪ D,Finset.subset_union_left,Finset.union_subset_union_right hDO,?_ ,?_⟩
  · rw [Finset.card_union_of_disjoint hd,hD]
  · rw [Finset.sum_union hd,sum_ones a D (fun i hi => hO i (hDO hi)),hD]

private theorem replacement_card {p r : ℕ} (a : Fin p → ZMod p)
    (hU : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r)
    (T A B : Finset (Fin p)) (hT : T.Nonempty) (hzero : (∑ i ∈ T,a i) = 0)
    (hA : A ⊆ T) (hBT : Disjoint B T) (hB : B.Nonempty)
    (hAB : (∑ i ∈ A,a i) = ∑ i ∈ B,a i) : A.card = B.card := by
  have hd : Disjoint (T \ A) B := Finset.disjoint_left.mpr fun i hi hiB =>
    Finset.disjoint_left.mp hBT hiB (Finset.mem_sdiff.mp hi).1
  have hn : (T \ A ∪ B).Nonempty :=
    hB.mono Finset.subset_union_right
  have hs : (∑ i ∈ T \ A ∪ B, a i) = 0 := by
    rw [Finset.sum_union hd, ← hAB, Finset.sum_sdiff hA,hzero]
  have hc := hU (T \ A ∪ B) hn hs
  rw [Finset.card_union_of_disjoint hd] at hc
  have hc' := Finset.card_sdiff_add_card_eq_card hA
  have ht := hU T hT hzero
  omega

private theorem cast_sum_vals {p : ℕ} [NeZero p] (a : Fin p → ZMod p) (B : Finset (Fin p)) :
    (((∑ i ∈ B,(a i).val : ℕ) : ZMod p)) = ∑ i ∈ B,a i := by
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => ZMod.natCast_zmod_val _


theorem card_range_le_two {p : ℕ} [NeZero p] (a : Fin p → ZMod p) (r : ℕ)
    (hr : 2 ≤ r) (hp : p ≤ 2*r)
    (hv : r ≤ (Finset.univ.filter (fun i => a i = 1)).card)
    (hU : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r) :
    (Set.range a).ncard ≤ 2 := by
  classical
  let O := Finset.univ.filter (fun i => a i = 1)
  let v := O.card
  let B := Finset.univ \ O
  let valSum (S : Finset (Fin p)) : ℕ := ∑ i ∈ S, (a i).val
  have hvp : v ≤ p := by simpa [v] using Finset.card_le_univ O
  change r ≤ v at hv
  have hrp : r ≤ p := hv.trans hvp
  have hhalf : p ≤ 2*v := by omega
  have hO (i : Fin p) : i ∈ O ↔ a i = 1 := by simp [O]
  have hB (i : Fin p) : i ∈ B ↔ a i ≠ 1 := by simp [B,hO]
  have hBcard : B.card = p-v := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  have hnonzero (i : Fin p) : a i ≠ 0 := by
    intro hi
    have h := hU {i} (Finset.singleton_nonempty _) (by simpa using hi)
    simp at h
    omega
  have hval₂ (i : Fin p) (hi : a i ≠ 1) : 2 ≤ (a i).val := by
    have h0 : (a i).val ≠ 0 := fun h => hnonzero i ((ZMod.val_eq_zero _).mp h)
    have h1 : (a i).val ≠ 1 := by
      intro h
      exact hi ((ZMod.natCast_zmod_val (a i)).symm.trans (by rw [h,Nat.cast_one]))
    omega
  have hinjVal (i j : Fin p) (he : (a i).val = (a j).val) : a i = a j :=
    (ZMod.natCast_zmod_val (a i)).symm.trans
      ((congrArg (fun n : ℕ => (n : ZMod p)) he).trans (ZMod.natCast_zmod_val (a j)))
  by_cases hpair : ∃ i j, a i ≠ 1 ∧ a j ≠ 1 ∧ a i ≠ a j
  swap
  · push Not at hpair
    by_cases hs : ∃ i, a i ≠ 1
    · obtain ⟨i,hi⟩ := hs
      have hsub : Set.range a ⊆ ({1,a i} : Set (ZMod p)) := by
        rintro _ ⟨j,rfl⟩
        by_cases hj : a j = 1
        · simp [hj]
        · simp [hpair j i hj hi]
      exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hi.symm)
    · push Not at hs
      have hsub : Set.range a ⊆ ({1} : Set (ZMod p)) := by
        rintro _ ⟨i,rfl⟩
        simp [hs i]
      exact (Set.ncard_le_ncard hsub).trans (by simp)
  exfalso
  obtain ⟨i₀,j₀,hi₀,hj₀,hneq⟩ := hpair
  have hfill (Q : Finset (Fin p)) (hQB : Q ⊆ B) (hQ : Q.Nonempty)
      (z : ℕ) (hsum : valSum Q = z) (hzlo : p-v ≤ z) (hzhi : z ≤ p) :
      ∃ T : Finset (Fin p), Q ⊆ T ∧ T ⊆ Q ∪ O ∧ T.Nonempty ∧
        T.card = Q.card+(p-z) ∧ (∑ i ∈ T,a i) = 0 := by
    obtain ⟨T,hQT,hT,hcard,hs⟩ := pad a Q O
      (fun i hi => (hB i).mp (hQB hi)) (fun i hi => (hO i).mp hi) (p-z) (by omega)
    refine ⟨T,hQT,hT,hQ.mono hQT,hcard,?_⟩
    have hcast : (z:ZMod p) = ∑ i ∈ Q,a i := by
      rw [← hsum]
      exact cast_sum_vals a Q
    rw [hs,← hcast,← Nat.cast_add,show z+(p-z)=p by omega,ZMod.natCast_self]
  have hfillPair (i j : Fin p) (hi : a i ≠ 1) (hj : a j ≠ 1) (hne : i ≠ j)
      (hlo : p-v ≤ (a i).val+(a j).val) (hhi : (a i).val+(a j).val ≤ p) :
      ∃ T : Finset (Fin p), ({i,j} : Finset (Fin p)) ⊆ T ∧
        T ⊆ {i,j} ∪ O ∧ T.Nonempty ∧ (∑ x ∈ T,a x)=0 ∧
        (a i).val+(a j).val=p-r+2 := by
    have hsub : ({i,j} : Finset (Fin p)) ⊆ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (hB _).mpr hi
      · obtain rfl := Finset.mem_singleton.mp hx
        exact (hB _).mpr hj
    obtain ⟨T,hsubT,hT,hneT,hcard,hs⟩ := hfill {i,j} hsub
      (Finset.insert_nonempty _ _) ((a i).val+(a j).val)
      (by simp [valSum,Finset.sum_pair hne]) hlo hhi
    have hc := hU T hneT hs
    simp only [Finset.card_pair hne] at hcard
    exact ⟨T,hsubT,hT,hneT,hs,by omega⟩
  have hhigh (i : Fin p) (hi : a i ≠ 1) (h : p-v ≤ (a i).val) : (a i).val = p-r+1 := by
    obtain ⟨T,_,_,hn,hcard,hs⟩ := hfill {i}
      (by simpa using (hB i).mpr hi) (Finset.singleton_nonempty _) ((a i).val)
      (by simp [valSum]) h (ZMod.val_lt _).le
    have hc := hU T hn hs
    simp only [Finset.card_singleton] at hcard
    omega
  have hsmall (i : Fin p) (hi : a i ≠ 1) : (a i).val < p-v := by
    by_contra! hlarge
    have hval := hhigh i hi hlarge
    obtain ⟨j,hj,hdiff⟩ : ∃ j, a j ≠ 1 ∧ a j ≠ a i := by
      by_cases h : a i = a i₀
      · exact ⟨j₀,hj₀,fun h' => hneq (h.symm.trans h'.symm)⟩
      · exact ⟨i₀,hi₀,Ne.symm h⟩
    have hjlt : (a j).val < p-v := by
      by_contra! h
      exact hdiff (hinjVal j i ((hhigh j hj h).trans hval.symm))
    have hne : i ≠ j := fun h => hdiff (h ▸ rfl)
    obtain ⟨_,_,_,_,_,hvalsum⟩ := hfillPair i j hi hj hne (by omega) (by omega)
    have hv₂ := hval₂ j hj
    omega
  have hcB : B.card ≤ valSum B := by
    have hh : (∑ _i ∈ B, (1:ℕ)) ≤ ∑ i ∈ B,(a i).val :=
      Finset.sum_le_sum fun i hi => (by have := hval₂ i ((hB i).mp hi); omega)
    simpa [valSum] using hh
  have hBp : 0 < p-v := by
    have hh := hsmall i₀ hi₀
    omega
  let F := B.powerset.filter fun E => p-v ≤ valSum E
  have hBF : B ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr le_rfl, hBcard ▸ hcB⟩
  obtain ⟨E,hEF,hmin⟩ := Finset.exists_min_image F Finset.card ⟨B,hBF⟩
  obtain ⟨hEB',hElo⟩ := Finset.mem_filter.mp hEF
  have hEB := Finset.mem_powerset.mp hEB'
  have hEn : E.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hElo
    simp [valSum] at hElo
    omega
  obtain ⟨x,hx⟩ := hEn
  have hxB := (hB x).mp (hEB hx)
  have hErase : valSum (E.erase x) < p-v := by
    by_contra! he
    have hm : E.erase x ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hEB),he⟩
    have hn := hmin (E.erase x) hm
    have hh := Finset.card_erase_add_one hx
    omega
  have hEhi : valSum E ≤ p := by
    have hh : valSum (E.erase x)+(a x).val = valSum E := by
      exact Finset.sum_erase_add E (fun i => (a i).val) hx
    have hval := hsmall x hxB
    omega
  obtain ⟨T,hET,_,hTn,_,hTz⟩ := hfill E hEB ⟨x,hx⟩ (valSum E) rfl hElo hEhi
  have hxT := hET hx
  have hTin (T : Finset (Fin p)) (hTn : T.Nonempty) (hTz : (∑ i ∈ T,a i)=0)
      (i : Fin p) (hiT : i ∈ T) (hi : a i ≠ 1) : (O \ T).card < (a i).val := by
    by_contra! h
    obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq h
    have hsum : (∑ j ∈ A, a j) = a i := by
      rw [sum_ones a A (fun j hj => (hO j).mp (Finset.mem_sdiff.mp (hA hj)).1),
        hcard,ZMod.natCast_zmod_val]
    have hd : Disjoint A T := Finset.disjoint_left.mpr
      (fun j hj hjT => (Finset.mem_sdiff.mp (hA hj)).2 hjT)
    have hAn : A.Nonempty := Finset.card_pos.mp (by have := hval₂ i hi; omega)
    have he := replacement_card a hU T {i} A hTn hTz (by simpa using hiT) hd hAn
      (by simpa using hsum.symm)
    simp only [Finset.card_singleton,hcard] at he
    have := hval₂ i hi
    omega
  have hTout (T : Finset (Fin p)) (hTn : T.Nonempty) (hTz : (∑ i ∈ T,a i)=0)
      (j : Fin p) (hjT : j ∉ T) (hj : a j ≠ 1) : (O ∩ T).card < (a j).val := by
    by_contra! h
    obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq h
    have hsum : (∑ i ∈ A,a i) = a j := by
      rw [sum_ones a A (fun i hi => (hO i).mp (Finset.mem_inter.mp (hA hi)).1),
        hcard,ZMod.natCast_zmod_val]
    have hd : Disjoint ({j} : Finset (Fin p)) T := Finset.disjoint_left.mpr
      (fun i hi hT => hjT (Finset.mem_singleton.mp hi ▸ hT))
    have he := replacement_card a hU T A {j} hTn hTz
      (fun i hi => (Finset.mem_inter.mp (hA hi)).2) hd (Finset.singleton_nonempty _)
      (by simpa using hsum)
    simp only [Finset.card_singleton,hcard] at he
    have := hval₂ j hj
    omega
  have hcross (T : Finset (Fin p)) (hTn : T.Nonempty) (hTz : (∑ i ∈ T,a i)=0)
      (i j : Fin p) (hiT : i ∈ T) (hjT : j ∉ T) (hi : a i ≠ 1) (hj : a j ≠ 1) :
      (a i).val+(a j).val=p-r+2 := by
    have hsum : (O \ T).card + (O ∩ T).card = v := Finset.card_sdiff_add_card_inter O T
    have hlo₁ := hTin T hTn hTz i hiT hi
    have hlo₂ := hTout T hTn hTz j hjT hj
    have hhi₁ := hsmall i hi
    have hhi₂ := hsmall j hj
    have hne : i ≠ j := fun h => hjT (h ▸ hiT)
    obtain ⟨_,_,_,_,_,hh⟩ := hfillPair i j hi hj hne (by omega) (by omega)
    exact hh
  let W := B \ T
  have hW : W.card+(O \ T).card = p-T.card := by
    have he₁ : (Finset.univ \ T) \ O = W := by
      ext i
      simp [W,B,and_comm]
    have he₂ : (Finset.univ \ T) ∩ O = O \ T := by
      ext i
      simp [and_comm]
    have h := Finset.card_sdiff_add_card_inter (Finset.univ \ T) O
    rw [he₁,he₂,Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ,Fintype.card_fin] at h
    exact h
  obtain ⟨y,hy,z,hz,hyz⟩ := Finset.one_lt_card.mp (show 1 < W.card by
    have hTcard := hU T hTn hTz
    have hlo := hTin T hTn hTz x hxT hxB
    have hhi := hsmall x hxB
    omega)
  obtain ⟨hyB,hyT⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨hzB,hzT⟩ := Finset.mem_sdiff.mp hz
  have hy1 := (hB y).mp hyB
  have hz1 := (hB z).mp hzB
  have hxy : x ≠ y := fun he => hyT (he ▸ hxT)
  have hxySum := hcross T hTn hTz x y hxT hyT hxB hy1
  obtain ⟨T',hxyT',hT',hT'n,hT'z,_⟩ :=
    hfillPair x y hxB hy1 hxy (by omega) (by omega)
  have hxT' : x ∈ T' := hxyT' (by simp)
  have hyT' : y ∈ T' := hxyT' (by simp)
  have hzT' : z ∉ T' := by
    intro hz'
    have hzx : z ≠ x := fun h => hzT (h.symm ▸ hxT)
    have h := hT' hz'
    simp [hzx,hyz.symm,hO,hz1] at h
  have hEq : (a x).val = (a y).val := by
    have h₁ := hcross T' hT'n hT'z x z hxT' hzT' hxB hz1
    have h₂ := hcross T' hT'n hT'z y z hyT' hzT' hy1 hz1
    omega
  have hall (i : Fin p) (hi : a i ≠ 1) : a i = a x := by
    apply hinjVal
    by_cases ht : i ∈ T
    · have h := hcross T hTn hTz i y ht hyT hi hy1
      omega
    · have h := hcross T hTn hTz x i hxT ht hxB hi
      omega
  exact hneq ((hall i₀ hi₀).trans (hall j₀ hj₀).symm)

end GrahamLarge541

namespace Graham541

theorem range_le_two_of_half_order {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (hr : 2 ≤ r) (hp : p = 2 * r) (v : ZMod p) (horder : addOrderOf v = r)
    (hmultiplicity : r ≤ (Finset.univ.filter (fun i => a i = v)).card)
    (huniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r) :
    (Set.range a).ncard ≤ 2 := by
  classical
  let H := AddSubgroup.zmultiples v
  have hrzero : r • v = 0 := by
    simpa only [horder] using addOrderOf_nsmul_eq_zero v
  have hHcard : Nat.card H = r := by
    rw [show H = AddSubgroup.zmultiples v from rfl, Nat.card_zmultiples, horder]
  have hH : H.index = 2 := by
    have hcard := H.index_mul_card
    rw [hHcard, Nat.card_zmod] at hcard
    exact mul_right_cancel₀ (by omega : r ≠ 0) (hcard.trans hp)
  have hpad (B : Finset (Fin p)) (hB : ∀ i ∈ B, a i ≠ v) (hBn : B.Nonempty)
      (hSum : (∑ i ∈ B, a i) ∈ H) : (∑ i ∈ B, a i) = B.card • v := by
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hSum
    let m := (z % (r : ℤ)).toNat
    have hm₀ : 0 ≤ z % (r : ℤ) := Int.emod_nonneg _ (by omega)
    have hm₁ : z % (r : ℤ) < r := Int.emod_lt_of_pos _ (by omega)
    have hm : m < r := by
      have hcast : (m : ℤ) = z % (r : ℤ) := Int.toNat_of_nonneg hm₀
      omega
    have hmSum : m • v = ∑ i ∈ B, a i := by
      have hmod := mod_addOrderOf_zsmul v z
      rw [horder] at hmod
      rw [← natCast_zsmul, show (m : ℤ) = z % (r : ℤ) from Int.toNat_of_nonneg hm₀,
        hmod, hz]
    have h0 : (∑ i ∈ B, a i) + (r - m) • v = 0 := by
      rw [← hmSum, ← add_nsmul, Nat.add_sub_of_le hm.le, hrzero]
    have hBpos := Finset.card_pos.mpr hBn
    have hlen := common_length_of_padding a r huniform v B hB (r - m)
      (by omega) (by omega) h0
    have heq : m = B.card := by omega
    simpa only [heq] using hmSum.symm
  have hOutside {i : Fin p} (hi : a i ≠ v) : a i ∉ H := by
    intro hin
    apply hi
    simpa using hpad {i} (by simpa using hi) (Finset.singleton_nonempty i) (by simpa)
  have hPairOff {i j : Fin p} (hi : a i ≠ v) (hj : a j ≠ v) :
      ∀ k ∈ ({i, j} : Finset (Fin p)), a k ≠ v := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · rw [Finset.mem_singleton.mp hk]
      exact hj
  have hPair {i j : Fin p} (hi : a i ≠ v) (hj : a j ≠ v) (hij : i ≠ j) :
      a i + a j = 2 • v := by
    have hmem : a i + a j ∈ H :=
      (H.add_mem_iff_of_index_two hH).mpr ⟨fun h => (hOutside hi h).elim,
        fun h => (hOutside hj h).elim⟩
    have hSum : (∑ k ∈ ({i, j} : Finset (Fin p)), a k) ∈ H := by
      simpa [hij] using hmem
    simpa [hij] using hpad {i, j} (hPairOff hi hj) (by simp) hSum
  have hEqual {i j : Fin p} (hi : a i ≠ v) (hj : a j ≠ v) : a i = a j := by
    by_contra hne
    have hij : i ≠ j := fun h => hne (congrArg a h)
    have hOthers (k : Fin p) (hki : k ≠ i) (hkj : k ≠ j) : a k = v := by
      by_contra hk
      exact hne (add_left_cancel ((hPair hk hi hki).trans (hPair hk hj hkj).symm))
    let B : Finset (Fin p) := {i, j}
    have hBcard : B.card = 2 := by simp [B, hij]
    have hBoff : ∀ k ∈ B, a k ≠ v := hPairOff hi hj
    let D := (Finset.univ : Finset (Fin p)) \ B
    have hDcard : D.card = p - 2 := by
      rw [show D = Finset.univ \ B from rfl, Finset.card_sdiff_of_subset
        (Finset.subset_univ B), hBcard, Finset.card_univ, Fintype.card_fin]
    have hDsub : D ⊆ Finset.univ.filter (fun k => a k = v) := by
      intro k hk
      have hnot : k ∉ B := (Finset.mem_sdiff.mp hk).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, hOthers k ?_ ?_⟩
      · exact fun he => hnot (by simp [B, he])
      · exact fun he => hnot (by simp [B, he])
    have hk : p - 2 ≤ (Finset.univ.filter (fun k => a k = v)).card :=
      hDcard ▸ Finset.card_le_card hDsub
    have hSum : (∑ k ∈ B, a k) = 2 • v := by
      simpa [B, hij] using hPair hi hj hij
    have hZero : (∑ k ∈ B, a k) + (p - 2) • v = 0 := by
      rw [hSum, ← add_nsmul, show 2 + (p - 2) = p by omega]
      calc
        p • v = (2 * r) • v := congrArg (fun n : ℕ => n • v) hp
        _ = 0 := by rw [two_mul, add_nsmul, hrzero, add_zero]
    have hlen := common_length_of_padding a r huniform v B hBoff (p - 2)
      hk (by omega) hZero
    omega
  by_cases he : ∃ i, a i ≠ v
  · obtain ⟨i, hi⟩ := he
    have hsub : Set.range a ⊆ ({v, a i} : Set (ZMod p)) := by
      rintro _ ⟨j, rfl⟩
      by_cases hj : a j = v
      · simp [hj]
      · simp [hEqual hj hi]
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_pair hi.symm).le
  · have hsub : Set.range a ⊆ ({v} : Set (ZMod p)) := by
      rintro _ ⟨j, rfl⟩
      exact Set.mem_singleton_iff.mpr (by_contra fun hj => he ⟨j, hj⟩)
    exact (Set.ncard_le_ncard hsub).trans (by simp)

end Graham541

namespace GrahamZeroSum

/-- A sequence has no nonempty zero-sum subsequence. -/
def Free {ι G : Type*} [AddCommMonoid G] (a : ι → G) : Prop :=
  ∀ S : Finset ι, S.Nonempty → ∑ i ∈ S, a i ≠ 0

private def initial (n : ℕ) (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < k.val

private theorem initial_subset {n : ℕ} {j k : Fin (n + 1)} (h : j ≤ k) :
    initial n j ⊆ initial n k := by
  intro i hi
  simp only [initial, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_lt_of_le hi h

private theorem prefix_injective {G : Type*} [AddCommGroup G] {n : ℕ}
    {a : Fin n → G} (h : Free a) :
    Function.Injective (fun j : Fin (n + 1) => ∑ i ∈ initial n j, a i) := by
  apply Function.Injective.of_lt_imp_ne
  intro j k hjk hs
  let S := initial n k \ initial n j
  have hsne : S.Nonempty := by
    have hjn : j.val < n := by omega
    refine ⟨⟨j.val, hjn⟩, ?_⟩
    simp [S, initial, show j.val < k.val from hjk]
  apply h S hsne
  have hsplit : (∑ i ∈ S, a i) + ∑ i ∈ initial n j, a i = ∑ i ∈ initial n k, a i :=
    Finset.sum_sdiff (initial_subset (le_of_lt hjk))
  exact add_right_cancel (hsplit.trans (hs.symm.trans (zero_add _).symm))

/-- Restriction and reindexing preserve the absence of nonempty zero sums. -/
theorem Free.reindex {ι κ G : Type*} [AddCommMonoid G] {a : ι → G} (h : Free a)
    (e : κ ↪ ι) : Free (a ∘ e) := by
  intro S hS hs
  apply h (S.map e) hS.map
  simpa [Finset.sum_map, Function.comp_def] using hs

/-- A sequence of length at least the order of its ambient group has a nonempty zero sum. -/
theorem exists_zero_sum {G : Type*} [Fintype G] [AddCommGroup G] {n : ℕ}
    (a : Fin n → G) (hn : Fintype.card G ≤ n) :
    ∃ S : Finset (Fin n), S.Nonempty ∧ ∑ i ∈ S, a i = 0 := by
  classical
  by_contra! h
  have hc := Fintype.card_le_of_injective _ (prefix_injective h)
  rw [Fintype.card_fin] at hc
  omega

private theorem prefix_total {G : Type*} [Fintype G] [AddCommGroup G] {n : ℕ}
    {a : Fin n → G} (h : Free a) (hn : n + 1 = Fintype.card G) :
    (∑ j : Fin (n + 1), ∑ i ∈ initial n j, a i) = ∑ g : G, g := by
  have hb := (Fintype.bijective_iff_injective_and_card
    (fun j : Fin (n + 1) => ∑ i ∈ initial n j, a i)).2
      ⟨prefix_injective h, by simpa using hn⟩
  exact (Equiv.ofBijective _ hb).sum_comp id

private theorem adjacent_eq {G : Type*} [Fintype G] [AddCommGroup G] {n : ℕ}
    {a : Fin n → G} (h : Free a) (hn : n + 1 = Fintype.card G)
    (k : ℕ) (hk : k + 1 < n) :
    a ⟨k, by omega⟩ = a ⟨k + 1, hk⟩ := by
  classical
  let u : Fin n := ⟨k, by omega⟩
  let v : Fin n := ⟨k + 1, hk⟩
  let e := Equiv.swap u v
  let j : Fin (n + 1) := ⟨k + 1, by omega⟩
  let j₀ : Fin (n + 1) := ⟨k, by omega⟩
  let P := fun i : Fin (n + 1) => ∑ l ∈ initial n i, a l
  let Q := fun i : Fin (n + 1) => ∑ l ∈ initial n i, a (e l)
  have ht : ∑ i, P i = ∑ i, Q i :=
    (prefix_total h hn).trans (prefix_total (h.reindex e.toEmbedding) hn).symm
  have ho (i : Fin (n + 1)) (hi : i ≠ j) : P i = Q i := by
    refine (Finset.sum_equiv e ?_ ?_).symm
    · intro l
      have huv : u ∈ initial n i ↔ v ∈ initial n i := by
        simp only [initial, Finset.mem_filter, Finset.mem_univ, true_and]
        have hij : i.val ≠ k + 1 := fun he => hi (Fin.ext he)
        change k < i.val ↔ k + 1 < i.val
        omega
      by_cases hu : l = u
      · simpa only [hu, e, Equiv.swap_apply_left] using huv
      by_cases hv : l = v
      · simpa only [hv, e, Equiv.swap_apply_right] using huv.symm
      rw [show e l = l from Equiv.swap_apply_of_ne_of_ne hu hv]
    · intro l _
      rfl
  have hterm : P j = Q j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at ht
    have hpq : ∑ i ∈ Finset.univ.erase j, P i = ∑ i ∈ Finset.univ.erase j, Q i :=
      Finset.sum_congr rfl fun i hi => ho i (Finset.ne_of_mem_erase hi)
    rwa [← hpq, add_right_inj] at ht
  have hinit : initial n j = insert u (initial n j₀) := by
    ext l
    simp only [initial, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    change l.val < k + 1 ↔ l = u ∨ l.val < k
    rw [Fin.ext_iff]
    change l.val < k + 1 ↔ l.val = k ∨ l.val < k
    omega
  have hu : u ∉ initial n j₀ := by simp [initial, u, j₀]
  have hrest := ho j₀ (by intro he; have := congrArg Fin.val he; simp [j₀, j] at this)
  dsimp only [P, Q] at hterm hrest
  rw [hinit, Finset.sum_insert hu, Finset.sum_insert hu,
    show e u = v from Equiv.swap_apply_left _ _, ← hrest] at hterm
  exact add_right_cancel hterm

/-- At the maximum zero-sum-free length, all terms are equal. -/
theorem Free.constant_fin {G : Type*} [Fintype G] [AddCommGroup G] {n : ℕ}
    {a : Fin n → G} (h : Free a) (hn : n + 1 = Fintype.card G) (i j : Fin n) :
    a i = a j := by
  have hstep : ∀ k (hk : k < n), a ⟨k, hk⟩ = a ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      exact (adjacent_eq h hn k hk).symm.trans (ih (by omega))
  exact (hstep i.val i.isLt).trans (hstep j.val j.isLt).symm

/-- The result holds on any finite index type. -/
theorem Free.constant {ι G : Type*} [Fintype ι] [Fintype G] [AddCommGroup G]
    {a : ι → G} (h : Free a) (hn : Fintype.card ι + 1 = Fintype.card G) (i j : ι) :
    a i = a j := by
  let e := Fintype.equivFin ι
  simpa [e] using (h.reindex e.symm.toEmbedding).constant_fin hn (e i) (e j)

/-- The prefix-sum pigeonhole argument on a general finite index type. -/
theorem exists_zero_sum_fintype {ι G : Type*} [Fintype ι] [Fintype G] [AddCommGroup G]
    (a : ι → G) (h : Fintype.card G ≤ Fintype.card ι) :
    ∃ S : Finset ι, S.Nonempty ∧ ∑ i ∈ S, a i = 0 := by
  let e := (Fintype.equivFin ι).symm.toEmbedding
  obtain ⟨S, hS, hz⟩ := exists_zero_sum (a ∘ e) h
  exact ⟨S.map e, hS.map, by simpa [Finset.sum_map, Function.comp_def] using hz⟩

private theorem card_range_le_pair {ι G : Type*} [Finite G] (a : ι → G) {x y : G}
    (h : ∀ i, a i = x ∨ a i = y) : (Set.range a).ncard ≤ 2 := by
  calc
    (Set.range a).ncard ≤ ({x, y} : Set G).ncard := by
      apply Set.ncard_le_ncard (ht := Set.toFinite _)
      rintro _ ⟨i, rfl⟩
      simpa using h i
    _ ≤ 2 := by simpa using Set.ncard_insert_le x ({y} : Set G)

private theorem erase_card {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq ι]
    (h : Fintype.card ι = Fintype.card G) (i : ι) :
    Fintype.card ↥(Finset.univ.erase i) + 1 = Fintype.card G := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, ← h]
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

private theorem zero_sum_on_erasure {ι G : Type*} [Fintype ι] [AddCommMonoid G]
    [DecidableEq ι] {a : ι → G} {i : ι} {S : Finset ↥(Finset.univ.erase i)}
    (hS : S.Nonempty) (hz : ∑ j ∈ S, a j.val = 0) :
    ∃ T : Finset ι, T.Nonempty ∧ i ∉ T ∧ ∑ j ∈ T, a j = 0 := by
  let e : ↥(Finset.univ.erase i) ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨S.map e, hS.map, ?_, by simpa [Finset.sum_map, e] using hz⟩
  intro hi
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
  have hji : j.val ≠ i := Finset.ne_of_mem_erase j.property
  exact hji hj

/-- When all nonempty zero sums have length one, the sequence has at most two values. -/
theorem range_le_two_of_length_one {ι G : Type*} [Fintype ι] [Fintype G] [AddCommGroup G]
    (a : ι → G) (hn : Fintype.card ι = Fintype.card G)
    (h : ∀ S : Finset ι, S.Nonempty → ∑ i ∈ S, a i = 0 → S.card = 1) :
    (Set.range a).ncard ≤ 2 := by
  classical
  obtain ⟨S, hS, hz⟩ := exists_zero_sum_fintype a hn.ge
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (h S hS hz)
  have hi : a i = 0 := by simpa using hz
  have huniq (j : ι) (hj : j ≠ i) : a j ≠ 0 := by
    intro hjz
    have hp : ∑ k ∈ ({j, i} : Finset ι), a k = 0 := by
      simp [Finset.sum_pair hj, hi, hjz]
    have hcard := h {j, i} (by simp) hp
    simp [hj] at hcard
  let I := Finset.univ.erase i
  have hf : Free (fun j : I => a j.val) := by
    intro U hU hu
    obtain ⟨T, hT, hni, ht⟩ := zero_sum_on_erasure hU hu
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (h T hT ht)
    exact huniq j (Ne.symm (by simpa using hni)) (by simpa using ht)
  by_cases hI : I.Nonempty
  · obtain ⟨j, hj⟩ := hI
    apply card_range_le_pair a (x := 0) (y := a j)
    intro k
    by_cases hki : k = i
    · exact Or.inl (hki ▸ hi)
    · have hk : k ∈ I := by simp [I, hki]
      exact Or.inr (hf.constant (erase_card hn i) ⟨k, hk⟩ ⟨j, hj⟩)
  · apply card_range_le_pair a (x := 0) (y := 0)
    intro j
    by_cases hj : j = i
    · exact Or.inl (hj ▸ hi)
    · exact (hI ⟨j, by simp [I, hj]⟩).elim

/-- When all nonempty zero sums use the entire sequence, the range has at most two values. -/
theorem range_le_two_of_full_length {ι G : Type*} [Fintype ι] [Fintype G] [AddCommGroup G]
    (a : ι → G) (hn : Fintype.card ι = Fintype.card G)
    (h : ∀ S : Finset ι, S.Nonempty → ∑ i ∈ S, a i = 0 → S.card = Fintype.card ι) :
    (Set.range a).ncard ≤ 2 := by
  classical
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.mp (hn ▸ Fintype.card_pos (α := G))
  let I := Finset.univ.erase i
  have hf : Free (fun j : I => a j.val) := by
    intro U hU hu
    obtain ⟨T, hT, hni, ht⟩ := zero_sum_on_erasure hU hu
    have hsub : T ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      exact fun he => hni (he ▸ Finset.mem_univ i)
    have hlt := Finset.card_lt_card hsub
    rw [Finset.card_univ, h T hT ht] at hlt
    omega
  by_cases hI : I.Nonempty
  · obtain ⟨j, hj⟩ := hI
    apply card_range_le_pair a (x := a i) (y := a j)
    intro k
    by_cases hki : k = i
    · exact Or.inl (congrArg a hki)
    · have hk : k ∈ I := by simp [I, hki]
      exact Or.inr (hf.constant (erase_card hn i) ⟨k, hk⟩ ⟨j, hj⟩)
  · apply card_range_le_pair a (x := a i) (y := a i)
    intro j
    by_cases hj : j = i
    · exact Or.inl (congrArg a hj)
    · exact (hI ⟨j, by simp [I, hj]⟩).elim

/-- The extreme common lengths in the all-moduli statement. -/
theorem zmod_endpoints (p : ℕ) (a : Fin p → ZMod p) {r : ℕ}
    (h : ∀ S : Finset (Fin p), S ≠ ∅ → ∑ i ∈ S, a i = 0 → S.card = r)
    (hr : r = 1 ∨ r = p) : (Set.range a).ncard ≤ 2 := by
  by_cases hp : p = 0
  · subst p
    simp
  have : NeZero p := ⟨hp⟩
  have hc : Fintype.card (Fin p) = Fintype.card (ZMod p) := by simp
  rcases hr with rfl | rfl
  · exact range_le_two_of_length_one a hc (fun s hs => h s hs.ne_empty)
  · exact range_le_two_of_full_length a hc (fun s hs hz => by
      simpa using h s hs.ne_empty hz)

end GrahamZeroSum

namespace Graham541

/-- The order of a frequent value determines which large-length construction applies. -/
theorem range_le_two_of_large_length {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (hr : 2 ≤ r) (hlarge : p ≤ 2*r)
    (huniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S,a i)=0 → S.card=r) :
    (Set.range a).ncard ≤ 2 := by
  obtain ⟨v,hv⟩ := exists_frequent_value a huniform
  rcases order_of_frequent_value a huniform hlarge v hv with horder | ⟨horder,hp⟩
  · exact via_unit_normalization a huniform v (isUnit_of_full_addOrder v horder) hv
      (fun b hb hones => GrahamLarge541.card_range_le_two b r hr hlarge hones hb)
  · exact range_le_two_of_half_order a hr hp v horder hv huniform

/-- It suffices to prove the case of a common length strictly between one and half the modulus. -/
theorem reduce_to_short
    (short : ∀ {p r : ℕ} [NeZero p] (a : Fin p → ZMod p),
      (∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S,a i)=0 → S.card=r) →
      2 ≤ r → 2*r < p → (Set.range a).ncard ≤ 2) :
    type_of% @Erdos541.erdos_541.variants.general_moduli := by
  intro p a ha
  by_cases hp : p = 0
  · subst p
    simp
  let _ : NeZero p := ⟨hp⟩
  obtain ⟨r,hr⟩ := ha
  by_cases hend : r = 1 ∨ r = p
  · exact GrahamZeroSum.zmod_endpoints p a hr hend
  have hU (S : Finset (Fin p)) (hS : S.Nonempty) (hz : (∑ i ∈ S,a i)=0) : S.card=r :=
    hr S hS.ne_empty hz
  have hr₂ : 2 ≤ r := by
    obtain ⟨S,hS,hz⟩ := GrahamZeroSum.exists_zero_sum_fintype a (by simp)
    have h := Finset.card_pos.mpr hS
    rw [hU S hS hz] at h
    omega
  by_cases hsmall : 2*r < p
  · exact short a hU hr₂ hsmall
  · exact range_le_two_of_large_length a hr₂ (by omega) hU

end Graham541

open scoped BigOperators

namespace GrahamNormalization

variable {ι G : Type*} [AddCommGroup G] [DecidableEq G]

/-- All subsums of an indexed sequence, including the empty sum. -/
def subsums (a : ι → G) (S : Finset ι) : Finset G :=
  S.powerset.image fun T => ∑ i ∈ T, a i

/-- A finite set of indices contains no nonempty zero sum. -/
def FreeOn (a : ι → G) (S : Finset ι) : Prop :=
  ∀ T ⊆ S, T.Nonempty → ∑ i ∈ T, a i ≠ 0

theorem mem_subsums {a : ι → G} {S : Finset ι} {x : G} :
    x ∈ subsums a S ↔ ∃ T ⊆ S, ∑ i ∈ T, a i = x := by
  simp only [subsums, Finset.mem_image, Finset.mem_powerset]

theorem zero_mem_subsums (a : ι → G) (S : Finset ι) : 0 ∈ subsums a S :=
  mem_subsums.mpr ⟨∅, Finset.empty_subset _, Finset.sum_empty⟩

theorem subsums_mono (a : ι → G) {S T : Finset ι} (h : S ⊆ T) :
    subsums a S ⊆ subsums a T := by
  intro _ hx
  obtain ⟨U, hU, hsum⟩ := mem_subsums.mp hx
  exact mem_subsums.mpr ⟨U, hU.trans h, hsum⟩

omit [DecidableEq G] in
theorem FreeOn.mono {a : ι → G} {S T : Finset ι} (hf : FreeOn a T) (h : S ⊆ T) :
    FreeOn a S := fun U hU => hf U (hU.trans h)

/-- In a zero-sum-free sequence each proper subset misses the full sum. -/
theorem FreeOn.total_not_mem {a : ι → G} {S T : Finset ι} (hf : FreeOn a T)
    (hst : S ⊂ T) : (∑ i ∈ T, a i) ∉ subsums a S := by
  classical
  intro h
  obtain ⟨U, hU, hsum⟩ := mem_subsums.mp h
  have hut : U ⊆ T := hU.trans hst.subset
  have hproper : T \ U ≠ ∅ := by
    intro he
    have htu : T ⊆ U := Finset.sdiff_eq_empty_iff_subset.mp he
    exact hst.not_ge (htu.trans hU)
  have hsplit : (∑ i ∈ T \ U, a i) + ∑ i ∈ U, a i = ∑ i ∈ T, a i :=
    Finset.sum_sdiff hut
  exact hf (T \ U) Finset.sdiff_subset (Finset.nonempty_iff_ne_empty.mpr hproper)
    (add_right_cancel (hsplit.trans (hsum.symm.trans (zero_add _).symm)))

/-- Translate a finite set by adding a fixed element. -/
def translate (B : Finset G) (g : G) : Finset G := B.image fun x => x + g

theorem mem_translate {B : Finset G} {g x : G} :
    x ∈ translate B g ↔ x - g ∈ B := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x - g, hx, sub_add_cancel _ _⟩

theorem card_translate (B : Finset G) (g : G) :
    (translate B g).card = B.card :=
  Finset.card_image_of_injective B (add_left_injective g)

variable [DecidableEq ι]

theorem subsums_insert {a : ι → G} {S : Finset ι} {i : ι} (hi : i ∉ S) :
    subsums a (insert i S) = subsums a S ∪ translate (subsums a S) (a i) := by
  ext x
  rw [Finset.mem_union, mem_translate, mem_subsums, mem_subsums, mem_subsums]
  constructor
  · rintro ⟨T, hT, hz⟩
    by_cases hit : i ∈ T
    · right
      refine ⟨T.erase i, ?_, ?_⟩
      · intro j hj
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hj))).resolve_left
          (Finset.ne_of_mem_erase hj)
      · apply eq_sub_of_add_eq
        rw [Finset.sum_erase_add _ _ hit, hz]
    · left
      exact ⟨T, fun j hj => (Finset.mem_insert.mp (hT hj)).resolve_left
        (fun h => hit (h ▸ hj)), hz⟩
  · rintro (⟨T, hT, hz⟩ | ⟨T, hT, hz⟩)
    · exact ⟨T, hT.trans (Finset.subset_insert _ _), hz⟩
    · refine ⟨insert i T, Finset.insert_subset_insert _ hT, ?_⟩
      rw [Finset.sum_insert (fun hit => hi (hT hit)), add_comm, hz, sub_add_cancel]

theorem FreeOn.subsums_card_lt_insert {a : ι → G} {S : Finset ι} {i : ι}
    (hf : FreeOn a (insert i S)) (hi : i ∉ S) :
    (subsums a S).card < (subsums a (insert i S)).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subsums_mono a (Finset.subset_insert _ _), ?_⟩
  have htotal := hf.total_not_mem (Finset.ssubset_insert hi)
  intro he
  apply htotal
  rw [he]
  exact mem_subsums.mpr ⟨_, Finset.Subset.rfl, rfl⟩

private def indicator (B : Finset G) (x : G) : ℤ := if x ∈ B then 1 else 0

private def point (x y : G) : ℤ := if x = y then 1 else 0

private theorem translate_boundary {a : ι → G} {S : Finset ι} {i : ι}
    (hf : FreeOn a (insert i S)) (hi : i ∉ S)
    (hone : (subsums a (insert i S)).card = (subsums a S).card + 1) :
    let B := subsums a S
    let T := ∑ j ∈ S, a j
    ∀ x, indicator B (x - a i) - indicator B x = point x (T + a i) - point x 0 := by
  dsimp only
  let B := subsums a S
  let b := a i
  let t := ∑ j ∈ S, a j
  let C := translate B b
  have hnew : (C \ B).card = 1 := by
    have hc := Finset.card_sdiff_add_card C B
    rw [Finset.union_comm, ← subsums_insert hi, hone] at hc
    change (C \ B).card + B.card = B.card + 1 at hc
    omega
  have hlose : (B \ C).card = 1 := by
    rw [← hnew]
    exact Finset.card_sdiff_comm (card_translate _ _).symm
  have htotal : t + b ∈ C \ B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_translate.mpr ?_, ?_⟩
    · simpa [t] using (mem_subsums.mpr ⟨S, Finset.Subset.rfl, rfl⟩ : t ∈ subsums a S)
    · simpa [t, b, Finset.sum_insert hi, add_comm] using
        hf.total_not_mem (Finset.ssubset_insert hi)
  have hz : 0 ∈ B \ C := by
    refine Finset.mem_sdiff.mpr ⟨zero_mem_subsums a S, ?_⟩
    intro hz
    obtain ⟨U, hU, hu⟩ := mem_subsums.mp (mem_translate.mp hz)
    apply hf (insert i U) (Finset.insert_subset_insert i hU) ⟨i, Finset.mem_insert_self _ _⟩
    rw [Finset.sum_insert (fun hui => hi (hU hui)), hu, zero_sub, add_neg_cancel]
  have hplus : C \ B = {t + b} := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hnew
    rw [hx, Finset.mem_singleton] at htotal
    rw [hx, htotal]
  have hminus : B \ C = {0} := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hlose
    simpa [hx] using congrArg (fun z => ({z} : Finset G))
      (show x = 0 by simpa [hx, eq_comm] using hz)
  intro x
  have hp : x = t + b ↔ x - b ∈ B ∧ x ∉ B := by
    rw [← Finset.mem_singleton, ← hplus, Finset.mem_sdiff, mem_translate]
  have hm : x = 0 ↔ x ∈ B ∧ x - b ∉ B := by
    rw [← Finset.mem_singleton, ← hminus, Finset.mem_sdiff, mem_translate]
  change indicator B (x - b) - indicator B x = point x (t + b) - point x 0
  simp only [indicator, point, hp, hm]
  by_cases hx : x ∈ B <;> by_cases hxb : x - b ∈ B <;> simp [hx, hxb]

/-- Two one-increment extensions of a nonempty zero-sum-free sequence have the same value. -/
theorem one_increment_unique {a : ι → G} {S : Finset ι} {i j : ι}
    (hS : S.Nonempty) (hi : i ∉ S) (hj : j ∉ S)
    (hfi : FreeOn a (insert i S)) (hfj : FreeOn a (insert j S))
    (hci : (subsums a (insert i S)).card = (subsums a S).card + 1)
    (hcj : (subsums a (insert j S)).card = (subsums a S).card + 1) : a i = a j := by
  let B := subsums a S
  let t := ∑ k ∈ S, a k
  let b := a i
  let c := a j
  have ht : t ≠ 0 := (hfi.mono (Finset.subset_insert _ _)) S Finset.Subset.rfl hS
  have hb (x : G) : indicator B (x - b) - indicator B x =
      point x (t + b) - point x 0 := translate_boundary hfi hi hci x
  have hc (x : G) : indicator B (x - c) - indicator B x =
      point x (t + c) - point x 0 := translate_boundary hfj hj hcj x
  have hcomm (x : G) : point x c + point x (t + b) = point x b + point x (t + c) := by
    have hb₁ := hb (x - c)
    have hc₁ := hc (x - b)
    have hb₀ := hb x
    have hc₀ := hc x
    rw [sub_sub, add_comm c b, ← sub_sub] at hb₁
    rw [show point (x - c) (t + b) = point x (t + b + c) by
          simp only [point, sub_eq_iff_eq_add],
        show point (x - c) 0 = point x c by simp [point, sub_eq_iff_eq_add]] at hb₁
    rw [show point (x - b) (t + c) = point x (t + b + c) by
          simp only [point, sub_eq_iff_eq_add, add_right_comm t c b],
        show point (x - b) 0 = point x b by simp [point, sub_eq_iff_eq_add]] at hc₁
    omega
  by_contra hbc
  have hnc : c ≠ t + c := fun he => ht (add_right_cancel (he.symm.trans (zero_add c).symm))
  have hp : 0 ≤ point c (t + b) := by unfold point; split <;> omega
  have hcb : c ≠ b := Ne.symm hbc
  have hsum : (1 : ℤ) + point c (t + b) = 0 + 0 := by
    simpa only [show point c c = 1 by simp [point], show point c b = 0 by simp [point, hcb],
      show point c (t + c) = 0 by simp [point, hnc]] using hcomm c
  omega

/-- The sole new subsum of a one-increment extension is its full sum. -/
theorem one_increment_subsums {a : ι → G} {S : Finset ι} {i : ι}
    (hi : i ∉ S) (hf : FreeOn a (insert i S))
    (hc : (subsums a (insert i S)).card = (subsums a S).card + 1) :
    subsums a (insert i S) = insert (∑ j ∈ insert i S, a j) (subsums a S) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset_iff.mpr
      ⟨mem_subsums.mpr ⟨_, Finset.Subset.rfl, rfl⟩,
       subsums_mono a (Finset.subset_insert _ _)⟩
  · rw [Finset.card_insert_of_notMem (hf.total_not_mem (Finset.ssubset_insert hi)), hc]

/-- Additional copies of a one-increment value also increase the count by one. -/
theorem one_increment_repeat {a : ι → G} {S : Finset ι} {i j : ι}
    (hi : i ∉ S) (hj : j ∉ insert i S) (heq : a i = a j)
    (hf : FreeOn a (insert j (insert i S)))
    (hc : (subsums a (insert i S)).card = (subsums a S).card + 1) :
    (subsums a (insert j (insert i S))).card = (subsums a (insert i S)).card + 1 := by
  let D := subsums a (insert i S)
  let t := ∑ k ∈ insert i S, a k
  have hd : D = insert t (subsums a S) :=
    one_increment_subsums hi (hf.mono (Finset.subset_insert _ _)) hc
  have hsub : translate (subsums a S) (a j) ⊆ D := by
    rw [← heq]
    change translate (subsums a S) (a i) ⊆ subsums a (insert i S)
    rw [subsums_insert hi]
    exact Finset.subset_union_right
  have htrans : translate D (a j) ⊆ insert (t + a j) D := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [hd, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hsub (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
  have htop : subsums a (insert j (insert i S)) ⊆ insert (t + a j) D := by
    rw [subsums_insert hj]
    exact Finset.union_subset (Finset.subset_insert _ _) htrans
  have hle := (Finset.card_le_card htop).trans (Finset.card_insert_le _ _)
  have hlt := hf.subsums_card_lt_insert hj
  change (subsums a (insert j (insert i S))).card ≤ D.card + 1 at hle
  change D.card < (subsums a (insert j (insert i S))).card at hlt
  exact le_antisymm hle (Nat.succ_le_of_lt hlt)

private theorem one_increment_after_tail {a : ι → G} {S T : Finset ι} {j : ι}
    (hd : Disjoint T S) (hj : j ∉ S ∪ T) (heq : ∀ i ∈ T, a i = a j)
    (hf : FreeOn a (insert j (S ∪ T)))
    (hc : (subsums a (insert j S)).card = (subsums a S).card + 1) :
    (subsums a (insert j (S ∪ T))).card = (subsums a (S ∪ T)).card + 1 := by
  induction T using Finset.induction_on generalizing S with
  | empty => simpa using hc
  | insert i T hi ih =>
    have hiS : i ∉ S := fun hs => Finset.disjoint_left.mp hd (Finset.mem_insert_self _ _) hs
    have hjS : j ∉ S := fun hs => hj (Finset.mem_union_left _ hs)
    have hji : j ≠ i := fun he => hj (Finset.mem_union_right _ (he ▸ Finset.mem_insert_self _ _))
    have haj := heq i (Finset.mem_insert_self _ _)
    have hci : (subsums a (insert i S)).card = (subsums a S).card + 1 := by
      rw [subsums_insert hiS, haj, ← subsums_insert hjS]
      exact hc
    have hrewrite : S ∪ insert i T = insert i S ∪ T := by
      rw [Finset.union_insert, Finset.insert_union]
    rw [hrewrite] at hf ⊢
    have hF : FreeOn a (insert j (insert i S)) :=
      hf.mono (Finset.insert_subset_insert _ Finset.subset_union_left)
    have hcc := one_increment_repeat hiS (by simp [hji, hjS]) haj hF hci
    refine ih ?_ ?_ ?_ hf hcc
    · apply Finset.disjoint_left.mpr
      intro l hlT hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hi hlT
      · exact Finset.disjoint_left.mp hd (Finset.mem_insert_of_mem hlT) hl
    · intro hj'
      exact hj (hrewrite.symm ▸ hj')
    · exact fun l hlT => heq l (Finset.mem_insert_of_mem hlT)

/-- From a seed with sufficiently many subsums, some remaining term can be appended last
with an increase of just one subsum. -/
theorem last_increment_one [Fintype G] {a : ι → G} {U S : Finset ι}
    (hf : FreeOn a U) (hU : Fintype.card G < 2 * U.card)
    (hSU : S ⊆ U) (hS : S.Nonempty) (hspread : 2 * S.card ≤ (subsums a S).card) :
    ∃ j ∈ U, j ∉ S ∧ (subsums a U).card = (subsums a (U.erase j)).card + 1 := by
  classical
  let C := U.powerset.filter fun T => S ⊆ T ∧ 2 * T.card ≤ (subsums a T).card
  have hC : C.Nonempty := ⟨S, by simp [C, hSU, hspread]⟩
  obtain ⟨B, hBC, hB⟩ := C.exists_max_image Finset.card hC
  have hspec := Finset.mem_filter.mp hBC
  have hBU : B ⊆ U := Finset.mem_powerset.mp hspec.1
  obtain ⟨hSB, hspreadB⟩ := hspec.2
  have hBU' : B ≠ U := by
    intro he
    have hcard := Finset.card_le_univ (subsums a U)
    rw [he] at hspreadB
    omega
  have hBne : (U \ B).Nonempty := Finset.nonempty_iff_ne_empty.mpr fun he =>
    hBU' (Finset.Subset.antisymm hBU (Finset.sdiff_eq_empty_iff_subset.mp he))
  have hinc (i : ι) (hi : i ∈ U \ B) :
      (subsums a (insert i B)).card = (subsums a B).card + 1 := by
    obtain ⟨hiU, hiB⟩ := Finset.mem_sdiff.mp hi
    have hisub : insert i B ⊆ U := Finset.insert_subset_iff.mpr ⟨hiU, hBU⟩
    have hF := hf.mono hisub
    have hlt := hF.subsums_card_lt_insert hiB
    by_contra he
    have hcard := Finset.card_insert_of_notMem hiB
    have hbig : 2 * (insert i B).card ≤ (subsums a (insert i B)).card := by omega
    have hmax := hB (insert i B) (by simp [C, hisub, hSB.trans (Finset.subset_insert _ _), hbig])
    omega
  obtain ⟨j, hj⟩ := hBne
  obtain ⟨hjU, hjB⟩ := Finset.mem_sdiff.mp hj
  let T := (U \ B).erase j
  have hd : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro i hi hiB
    exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hi)).2 hiB
  have hBT : B ∪ T = U.erase j := by
    ext i
    simp only [T, Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff]
    constructor
    · rintro (hi | hi)
      · exact ⟨fun he => hjB (he ▸ hi), hBU hi⟩
      · exact ⟨hi.1, hi.2.1⟩
    · intro hi
      by_cases hmem : i ∈ B
      · exact Or.inl hmem
      · exact Or.inr ⟨hi.1, hi.2, hmem⟩
  have hfull : insert j (B ∪ T) = U := by
    rw [hBT, Finset.insert_erase hjU]
  have hvalues (i : ι) (hi : i ∈ T) : a i = a j := by
    have hi' : i ∈ U \ B := Finset.mem_of_mem_erase hi
    obtain ⟨hiU, hiB⟩ := Finset.mem_sdiff.mp hi'
    exact one_increment_unique (hS.mono hSB) hiB hjB
      (hf.mono (Finset.insert_subset_iff.mpr ⟨hiU, hBU⟩))
      (hf.mono (Finset.insert_subset_iff.mpr ⟨hjU, hBU⟩)) (hinc i hi') (hinc j hj)
  have htail := one_increment_after_tail hd (by rw [hBT]; simp) hvalues
    (hfull.symm ▸ hf) (hinc j hj)
  rw [hfull, hBT] at htail
  exact ⟨j, hjU, fun hs => hjB (hSB hs), htail⟩

omit [DecidableEq ι] in
theorem subsums_congr {a b : ι → G} {S : Finset ι} (he : Set.EqOn a b S) :
    subsums a S = subsums b S := by
  unfold subsums
  refine Finset.image_congr ?_
  intro U hU
  exact Finset.sum_congr rfl fun i hi => he (Finset.mem_powerset.mp hU hi)

omit [DecidableEq ι] [DecidableEq G] in
theorem FreeOn.congr {a b : ι → G} {S : Finset ι} (hf : FreeOn a S)
    (he : Set.EqOn a b S) : FreeOn b S := by
  intro T hT hne
  have hsum : ∑ i ∈ T, a i = ∑ i ∈ T, b i :=
    Finset.sum_congr rfl fun i hi => he (hT hi)
  rw [← hsum]
  exact hf T hT hne

theorem FreeOn.insert_of_missing {a : ι → G} {S : Finset ι} {i : ι}
    (hf : FreeOn a S) (hmiss : -a i ∉ subsums a S) :
    FreeOn a (insert i S) := by
  intro T hT hne hz
  by_cases hit : i ∈ T
  · apply hmiss
    have hsub : T.erase i ⊆ S := by
      intro j hj
      exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hj))).resolve_left
        (Finset.ne_of_mem_erase hj)
    refine mem_subsums.mpr ⟨T.erase i, hsub, ?_⟩
    have hsplit := Finset.sum_erase_add T a hit
    rw [hz, ← eq_neg_iff_add_eq_zero] at hsplit
    exact hsplit
  · apply hf T (fun j hj => (Finset.mem_insert.mp (hT hj)).resolve_left
      (fun he => hit (he ▸ hj))) hne hz

/-- In an infinite pool of index labels, any finite zero-sum-free sequence extends
to one whose subsums exhaust the group. -/
theorem exists_saturated_extension [Infinite ι] [Fintype G]
    {a : ι → G} {S : Finset ι} (hf : FreeOn a S) :
    ∃ (b : ι → G) (T : Finset ι), S ⊆ T ∧ Set.EqOn a b S ∧
      FreeOn b T ∧ subsums b T = Finset.univ := by
  have extend (m : ℕ) (a : ι → G) (S : Finset ι) (hf : FreeOn a S)
      (hm : Fintype.card G - (subsums a S).card = m) :
      ∃ (b : ι → G) (T : Finset ι), S ⊆ T ∧ Set.EqOn a b S ∧
        FreeOn b T ∧ subsums b T = Finset.univ := by
    induction m using Nat.strong_induction_on generalizing a S with
    | h m ih =>
      by_cases hs : subsums a S = Finset.univ
      · exact ⟨a, S, Finset.Subset.rfl, fun _ _ => rfl, hf, hs⟩
      obtain ⟨x, _, hx⟩ := Finset.not_subset.mp (fun h =>
        hs (Finset.Subset.antisymm (Finset.subset_univ _) h))
      obtain ⟨i, hi⟩ := S.exists_notMem
      let a' := Function.update a i (-x)
      have he : Set.EqOn a a' S := by
        intro j hj
        change j ∈ S at hj
        have hj' : j ≠ i := fun he => hi (he ▸ hj)
        exact (Function.update_of_ne hj' _ _).symm
      have heD := subsums_congr he
      have hmiss : -a' i ∉ subsums a' S := by
        rw [← heD]
        simpa [a'] using hx
      have hf' := (hf.congr he).insert_of_missing hmiss
      have hlt := hf'.subsums_card_lt_insert hi
      have hbound := Finset.card_le_univ (subsums a' (insert i S))
      rw [← heD] at hlt
      have hl : Fintype.card G - (subsums a' (insert i S)).card < m := by omega
      obtain ⟨b, T, hT, heb, hb, hD⟩ := ih _ hl a' (insert i S) hf' rfl
      refine ⟨b, T, (Finset.subset_insert _ _).trans hT, ?_, hb, hD⟩
      exact fun j hj => (he hj).trans (heb (Finset.mem_insert_of_mem hj))
  exact extend _ a S hf rfl

/-- A subsequence is represented by a zero-free interval of integer coefficients,
with every coefficient up to its total realized as a subsum. -/
def Behaves (a : ι → G) (S : Finset ι) (g : G) : Prop :=
  ∃ w : ι → ℕ, (∀ j ∈ S, 0 < w j ∧ a j = w j • g) ∧
    (∑ j ∈ S, w j) < addOrderOf g ∧
    ∀ k ≤ ∑ j ∈ S, w j, ∃ U ⊆ S, ∑ j ∈ U, w j = k

omit [DecidableEq ι] [DecidableEq G] in
private theorem sum_eq_nsmul {a : ι → G} {w : ι → ℕ} {S U : Finset ι} {g : G}
    (hw : ∀ j ∈ S, 0 < w j ∧ a j = w j • g) (hU : U ⊆ S) :
    (∑ i ∈ U, a i) = (∑ i ∈ U, w i) • g := by
  rw [← Finset.sum_nsmul_assoc]
  exact Finset.sum_congr rfl fun j hj => (hw j (hU hj)).2

omit [DecidableEq ι] in
private theorem subsums_eq_coefficient_range {a : ι → G} {w : ι → ℕ} {S : Finset ι}
    {g : G} (hw : ∀ j ∈ S, 0 < w j ∧ a j = w j • g)
    (hfill : ∀ k ≤ ∑ j ∈ S, w j, ∃ U ⊆ S, ∑ j ∈ U, w j = k) :
    subsums a S = (Finset.range ((∑ j ∈ S, w j) + 1)).image (· • g) := by
  ext x
  rw [mem_subsums, Finset.mem_image]
  constructor
  · rintro ⟨U, hu, hsum⟩
    refine ⟨∑ j ∈ U, w j, Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), ?_⟩
    · exact Finset.sum_le_sum_of_subset hu
    · rwa [sum_eq_nsmul hw hu] at hsum
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨U, hu, hsum⟩ := hfill k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    exact ⟨U, hu, by rw [sum_eq_nsmul hw hu, hsum]⟩

omit [DecidableEq ι] [DecidableEq G] in
private theorem behaves_singleton [Fintype G] {a : ι → G} {i : ι} (ha : a i ≠ 0) :
    Behaves a {i} (a i) := by
  refine ⟨fun _ => 1, ?_, ?_, ?_⟩
  · simp
  · have hp := (addOrderOf_pos_iff.mpr (isOfFinAddOrder_of_finite (a i)))
    have hn : addOrderOf (a i) ≠ 1 := fun he => ha (AddMonoid.addOrderOf_eq_one_iff.mp he)
    simp only [Finset.sum_singleton]
    omega
  · intro k hk
    simp only [Finset.sum_singleton] at hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · exact ⟨∅, Finset.empty_subset _, by simp⟩
    · exact ⟨{i}, Finset.Subset.rfl, by simp⟩

private theorem behaves_insert {a : ι → G} {S : Finset ι} {i : ι}
    {g : G} {m : ℕ} (hi : i ∉ S) (hf : FreeOn a (insert i S))
    (hB : Behaves a S g) (hm : 0 < m)
    (hle : m ≤ (subsums a S).card) (ha : a i = m • g) :
    Behaves a (insert i S) g := by
  obtain ⟨w, hw, htotal, hfill⟩ := hB
  let q := ∑ k ∈ S, w k
  have hD := subsums_eq_coefficient_range hw hfill
  have hcard : (subsums a S).card ≤ q + 1 := by
    rw [hD]
    exact Finset.card_image_le.trans_eq (Finset.card_range _)
  have hmq : m ≤ q + 1 := hle.trans hcard
  have hmord : m ≤ addOrderOf g := by omega
  have hbigger : q + m < addOrderOf g := by
    by_contra! hb
    let k := addOrderOf g - m
    have hkm : k + m = addOrderOf g := Nat.sub_add_cancel hmord
    have hk : k ≤ q := by omega
    obtain ⟨U, hu, hsum⟩ := hfill k hk
    apply hf (insert i U) (Finset.insert_subset_insert _ hu) ⟨i, Finset.mem_insert_self _ _⟩
    rw [Finset.sum_insert (fun hiU => hi (hu hiU)), sum_eq_nsmul hw hu, hsum, ha,
      ← add_nsmul, add_comm m k, hkm, addOrderOf_nsmul_eq_zero]
  let w' := Function.update w i m
  have he (U : Finset ι) (hU : U ⊆ S) : ∑ k ∈ U, w' k = ∑ k ∈ U, w k := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≠ i := fun he => hi (he ▸ hU hj)
    exact Function.update_of_ne hj' _ _
  have hwi : w' i = m := Function.update_self _ _ _
  have htotal' : ∑ j ∈ insert i S, w' j = m + q := by
    rw [Finset.sum_insert hi, he S Finset.Subset.rfl, hwi]
  refine ⟨w', ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa [w'] using And.intro hm ha
    · simpa [w', show j ≠ i from fun re => hi (re ▸ hj)] using hw j hj
  · rw [htotal', add_comm]
    exact hbigger
  · intro k hk
    rw [htotal'] at hk
    by_cases hkq : k ≤ q
    · obtain ⟨U, hu, hsum⟩ := hfill k hkq
      exact ⟨U, hu.trans (Finset.subset_insert _ _), (he U hu).trans hsum⟩
    · have hkm : m ≤ k := by omega
      obtain ⟨U, hu, hsum⟩ := hfill (k - m) (by omega)
      refine ⟨insert i U, Finset.insert_subset_insert _ hu, ?_⟩
      rw [Finset.sum_insert (fun hiU => hi (hu hiU)), he U hu, hwi, hsum]
      omega

omit [DecidableEq ι] in
private theorem one_card_le_subsums (a : ι → G) (S : Finset ι) :
    1 ≤ (subsums a S).card := Finset.card_pos.mpr ⟨0, zero_mem_subsums a S⟩

private theorem behaves_disjoint_translate {a : ι → G} {S : Finset ι} {i : ι} {g : G}
    (hi : i ∉ S) (hf : FreeOn a (insert i S)) (hB : Behaves a S g)
    (hfail : ¬ Behaves a (insert i S) g) :
    Disjoint (subsums a S) (translate (subsums a S) (a i)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxt
  obtain ⟨w, hw, htotal, hfill⟩ := hB
  let q := ∑ j ∈ S, w j
  have hD := subsums_eq_coefficient_range hw hfill
  have hcard : (subsums a S).card = q + 1 := by
    rw [hD, Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl he
    apply nsmul_injOn_Iio_addOrderOf _ _ he
    · have := Finset.mem_range.mp hk
      exact Set.mem_Iio.mpr (by omega)
    · have := Finset.mem_range.mp hl
      exact Set.mem_Iio.mpr (by omega)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxt
  rw [hD, Finset.mem_image] at hx hy
  obtain ⟨k, hk, he⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hy
  have hk' : k ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl' : l ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hai : a i ≠ 0 := by
    simpa using hf {i} (by simp) (by simp)
  have hkl : k ≠ l := by
    intro h
    subst l
    exact hai (add_left_cancel (he.symm.trans (add_zero _).symm))
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · obtain ⟨U, hu, hsum⟩ := hfill (l - k) (by omega)
    apply hf (insert i U) (Finset.insert_subset_insert _ hu) ⟨i, Finset.mem_insert_self _ _⟩
    rw [Finset.sum_insert (fun hiU => hi (hu hiU)), sum_eq_nsmul hw hu, hsum]
    have hsub : l = k + (l - k) := by omega
    conv at he => rhs; lhs; rw [hsub, add_nsmul]
    rw [add_assoc] at he
    have hcancel := add_left_cancel (he.symm.trans (add_zero (k • g)).symm)
    simpa [add_comm] using hcancel
  · have hsub : k = l + (k - l) := by omega
    conv at he => lhs; rw [hsub, add_nsmul]
    have hai' : a i = (k - l) • g := (add_left_cancel he).symm
    apply hfail (behaves_insert hi hf ⟨w, hw, htotal, hfill⟩ (by omega) ?_ hai')
    rw [hcard]
    omega

private theorem max_behaves [Fintype G] {a : ι → G} {U : Finset ι} {g : G}
    (hf : FreeOn a U) (hg : ∃ i ∈ U, a i = g) :
    ∃ S ⊆ U, S.Nonempty ∧ Behaves a S g ∧
      (∀ T ⊆ U, Behaves a T g → T.card ≤ S.card) ∧
      ∀ i ∈ U, a i = g → i ∈ S := by
  classical
  let C := U.powerset.filter (fun S => Behaves a S g)
  obtain ⟨i, hi, rfl⟩ := hg
  have ha : a i ≠ 0 := by
    simpa using hf {i} (Finset.singleton_subset_iff.mpr hi) (by simp)
  have hsing := behaves_singleton ha
  have hC : C.Nonempty := ⟨{i}, by simp [C, Finset.singleton_subset_iff, hi, hsing]⟩
  obtain ⟨S, hs, hmax⟩ := C.exists_max_image Finset.card hC
  have hSU := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
  have hS := (Finset.mem_filter.mp hs).2
  have hcard (T : Finset ι) (hT : T ⊆ U) (hT' : Behaves a T (a i)) : T.card ≤ S.card :=
    hmax T (by simp [C, hT, hT'])
  have hsCard := hcard {i} (Finset.singleton_subset_iff.mpr hi) hsing
  have hne : S.Nonempty := Finset.card_pos.mp (by simpa using hsCard)
  refine ⟨S, hSU, hne, hS, hcard, ?_⟩
  intro j hj hja
  by_contra hjS
  have hjU : insert j S ⊆ U := Finset.insert_subset_iff.mpr ⟨hj, hSU⟩
  have hBeh := behaves_insert hjS (hf.mono hjU) hS Nat.zero_lt_one
    (one_card_le_subsums _ _) (by simpa using hja)
  have hc := hcard _ hjU hBeh
  rw [Finset.card_insert_of_notMem hjS] at hc
  omega

private theorem excluded_last [Fintype G] {a : ι → G} {U : Finset ι}
    (hf : FreeOn a U) (hD : subsums a U = Finset.univ)
    {j : ι} (hj : j ∈ U)
    (hinc : (subsums a U).card = (subsums a (U.erase j)).card + 1) :
    a j = -(∑ i ∈ U, a i) := by
  have hd : (Finset.univ \ subsums a (U.erase j)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (subsums a (U.erase j))), ← hD, hinc]
    omega
  have ht : (∑ i ∈ U, a i) ∈ Finset.univ \ subsums a (U.erase j) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hf.total_not_mem (Finset.erase_ssubset hj)⟩
  have hn : -a j ∈ Finset.univ \ subsums a (U.erase j) := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hz
    obtain ⟨T, hT, hsum⟩ := mem_subsums.mp hz
    have hjT : j ∉ T := fun he => Finset.notMem_erase j U (hT he)
    have hTU : insert j T ⊆ U :=
      Finset.insert_subset_iff.mpr ⟨hj, hT.trans (Finset.erase_subset _ _)⟩
    apply hf _ hTU ⟨j, Finset.mem_insert_self _ _⟩
    rw [Finset.sum_insert hjT, hsum, add_neg_cancel]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hd
  rw [hx, Finset.mem_singleton] at ht hn
  exact neg_eq_iff_eq_neg.mp (hn.trans ht.symm)

private theorem exists_excluded_behaves [Fintype G]
    {a : ι → G} {U : Finset ι} (hf : FreeOn a U)
    (hD : subsums a U = Finset.univ) (hU : Fintype.card G < 2 * U.card)
    {g : G} (hg : ∃ i ∈ U, a i = g) (hfail : ¬ Behaves a U g) :
    ∃ j ∈ U, a j = -(∑ i ∈ U, a i) ∧ a j ≠ g := by
  obtain ⟨S, hSU, _, hB, hmax, hall⟩ := max_behaves hf hg
  have hne : (U \ S).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hEq := Finset.Subset.antisymm hSU (Finset.sdiff_eq_empty_iff_subset.mp he)
    exact hfail (hEq ▸ hB)
  obtain ⟨i, hi⟩ := hne
  obtain ⟨hiU, hiS⟩ := Finset.mem_sdiff.mp hi
  have hSiU : insert i S ⊆ U := Finset.insert_subset_iff.mpr ⟨hiU, hSU⟩
  have hno : ¬ Behaves a (insert i S) g := by
    intro h
    have hc := hmax _ hSiU h
    rw [Finset.card_insert_of_notMem hiS] at hc
    omega
  have hdis := behaves_disjoint_translate hiS (hf.mono hSiU) hB hno
  have hcard : S.card + 1 ≤ (subsums a S).card := by
    obtain ⟨w, hw, htotal, hfill⟩ := hB
    have hD' := subsums_eq_coefficient_range hw hfill
    have hsum : S.card ≤ ∑ j ∈ S, w j := by
      simpa using (Finset.sum_le_sum fun j hj => (hw j hj).1 :
        (∑ _j ∈ S, (1 : ℕ)) ≤ ∑ j ∈ S, w j)
    rw [hD', Finset.card_image_of_injOn, Finset.card_range]
    · omega
    · intro k hk l hl he
      apply nsmul_injOn_Iio_addOrderOf _ _ he
      · have := Finset.mem_range.mp hk
        exact Set.mem_Iio.mpr (by omega)
      · have := Finset.mem_range.mp hl
        exact Set.mem_Iio.mpr (by omega)
  have hspread : 2 * (insert i S).card ≤ (subsums a (insert i S)).card := by
    rw [subsums_insert hiS, Finset.card_union_of_disjoint hdis, card_translate,
      Finset.card_insert_of_notMem hiS]
    omega
  obtain ⟨j, hjU, hjS, hinc⟩ := last_increment_one hf hU hSiU
    ⟨i, Finset.mem_insert_self _ _⟩ hspread
  exact ⟨j, hjU, excluded_last hf hD hjU hinc, fun he =>
    hjS (Finset.mem_insert_of_mem (hall j hjU he))⟩

/-- A long zero-sum-free sequence with all possible subsums has a normalized
positive-integer representation with sum below the order of the common base. -/
theorem saturated_behaves [Fintype G] {a : ι → G} {U : Finset ι}
    (hf : FreeOn a U) (hD : subsums a U = Finset.univ)
    (hU : Fintype.card G < 2 * U.card) : ∃ g, Behaves a U g := by
  classical
  have hne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hne
  by_cases hB : Behaves a U (a i)
  · exact ⟨a i, hB⟩
  obtain ⟨j, hj, ht, _⟩ := exists_excluded_behaves hf hD hU ⟨i, hi, rfl⟩ hB
  refine ⟨a j, ?_⟩
  by_contra! hn
  obtain ⟨k, _, hk, hkne⟩ := exists_excluded_behaves hf hD hU ⟨j, hj, rfl⟩ hn
  exact hkne (hk.trans ht.symm)

/-- Savchev–Chen normalization. A zero-sum-free subsequence longer than half the
order of its ambient group has positive integer weights summing to less than
the group order, with the weights interpreted relative to a generator. -/
theorem normalize_long [Fintype G] {a : ι → G} {S : Finset ι}
    (hf : FreeOn a S) (hS : Fintype.card G < 2 * S.card) :
    ∃ (g : G) (w : ι → ℕ), addOrderOf g = Fintype.card G ∧
      (∀ i ∈ S, 0 < w i ∧ a i = w i • g) ∧ (∑ i ∈ S, w i) < Fintype.card G := by
  classical
  let e : ι ↪ ι ⊕ ℕ := Function.Embedding.inl
  let a' : ι ⊕ ℕ → G := Sum.elim a (fun _ => 0)
  let S' := S.map e
  have hf' : FreeOn a' S' := by
    intro T hT ht hz
    have hm : T ∈ (S.map e).powersetCard T.card := Finset.mem_powersetCard.mpr ⟨hT, rfl⟩
    rw [Finset.powersetCard_map] at hm
    obtain ⟨U, hu, hue⟩ := Finset.mem_map.mp hm
    change U.map e = T at hue
    rw [← hue] at ht hz
    apply hf U (Finset.mem_powersetCard.mp hu).1 (Finset.map_nonempty.mp ht)
    simpa [a', e, Finset.sum_map] using hz
  obtain ⟨b, U, hsub, he, hb, hU⟩ := exists_saturated_extension hf'
  have hcard : S.card ≤ U.card := by simpa [S'] using Finset.card_le_card hsub
  obtain ⟨g, v, hv, htotal, _⟩ := saturated_behaves hb hU (by omega)
  have hsum : U.card ≤ ∑ i ∈ U, v i := by
    simpa using (Finset.sum_le_sum fun i hi => (hv i hi).1 :
      (∑ _i ∈ U, (1 : ℕ)) ≤ ∑ i ∈ U, v i)
  have hord : addOrderOf g = Fintype.card G := by
    obtain ⟨d, hd⟩ : addOrderOf g ∣ Fintype.card G := addOrderOf_dvd_card
    have hd' : d = 1 := by
      by_contra hne
      have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
      have hdpos : 0 < d := Nat.pos_of_ne_zero (fun he => by
        rw [he, mul_zero] at hd
        exact (ne_of_gt hpos) hd)
      have htw : addOrderOf g * 2 ≤ Fintype.card G := by
        rw [hd]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    simpa [hd'] using hd.symm
  let w : ι → ℕ := v ∘ e
  refine ⟨g, w, hord, ?_, ?_⟩
  · intro i hi
    have hi' : e i ∈ S' := Finset.mem_map_of_mem e hi
    have h := hv (e i) (hsub hi')
    exact ⟨h.1, (he hi').trans h.2⟩
  · have hle : (∑ i ∈ S, w i) ≤ ∑ i ∈ U, v i := by
      simpa [S', w, Function.comp_def, Finset.sum_map] using
        (Finset.sum_le_sum_of_subset (f := v) hsub)
    rw [← hord]
    exact hle.trans_lt htotal

/-- Normalization in the residue ring, by multiplying the sequence by a unit. -/
theorem normalize_zmod {p : ℕ} [NeZero p] {a : Fin p → ZMod p} {S : Finset (Fin p)}
    (hf : ∀ T ⊆ S, T.Nonempty → ∑ i ∈ T, a i ≠ 0) (hS : p < 2 * S.card) :
    ∃ u : (ZMod p)ˣ, (∑ i ∈ S, ((u : ZMod p) * a i).val) < p := by
  classical
  obtain ⟨g, w, hg, hw, htotal⟩ := normalize_long (show FreeOn a S from hf) (by simpa using hS)
  rw [ZMod.card] at hg htotal
  let f : Fin p → ZMod p := fun j => j.val • g
  have hinj : Function.Injective f := by
    intro k l he
    apply Fin.ext
    exact nsmul_injOn_Iio_addOrderOf (show k.val < addOrderOf g from hg.symm ▸ k.isLt)
      (show l.val < addOrderOf g from hg.symm ▸ l.isLt) he
  have hsurj := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp⟩).surjective
  obtain ⟨k, hk⟩ := hsurj 1
  have hik : (k.val : ZMod p) * g = 1 := by simpa [f, nsmul_eq_mul] using hk
  let v : (ZMod p)ˣ := ⟨g, k.val, by rwa [mul_comm], hik⟩
  refine ⟨v⁻¹, ?_⟩
  convert htotal using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hwi := (Finset.single_le_sum (f := w) (fun j hj => Nat.zero_le (w j)) hi).trans_lt htotal
  have hei := (hw i hi).2
  rw [hei, nsmul_eq_mul]
  have hunit : (↑v⁻¹ : ZMod p) * g = 1 := v.inv_mul
  rw [mul_left_comm, hunit, mul_one, ZMod.val_natCast_of_lt hwi]

end GrahamNormalization

namespace GrahamDeficits

/-- Accumulating deficits until their sum first exceeds the common zero-sum length
produces a positive complementary residue larger than the number of terms used. -/
theorem crossing {ι : Type*} [DecidableEq ι] {E : Finset ι} {d : ι → ℕ}
    {τ r p : ℕ} (hE : E.Nonempty) (hr : E.card + τ = r) (hp : 2 * r < p)
    (hlo : ∀ i ∈ E, τ + 3 ≤ d i) (hhi : ∀ i ∈ E, d i ≤ r - 1)
    (hpair : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → d i + d j ≤ r) :
    ∃ U ⊆ E, U.Nonempty ∧ r + 1 ≤ (∑ i ∈ U, d i) ∧
      (∑ i ∈ U, d i) < p ∧ U.card < p - (∑ i ∈ U, d i) := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := E.exists_max_image d hE
  have hfour : 4 ≤ E.card := by
    have h₁ := hlo i₀ hi₀
    have h₂ := hhi i₀ hi₀
    omega
  let k := (E.card + 3) / 3
  have hk : 1 ≤ k := by omega
  have hkhalf : 2 * k ≤ E.card := by omega
  have hcount : E.card + 1 ≤ 3 * k := by omega
  have hvsz : k - 1 ≤ (E.erase i₀).card := by
    rw [Finset.card_erase_of_mem hi₀]
    omega
  obtain ⟨V, hV, hVc⟩ := Finset.exists_subset_card_eq hvsz
  have hiV : i₀ ∉ V := fun he => Finset.notMem_erase _ _ (hV he)
  let W := insert i₀ V
  have hWE : W ⊆ E :=
    Finset.insert_subset_iff.mpr ⟨hi₀, hV.trans (Finset.erase_subset _ _)⟩
  have hWc : W.card = k := by
    rw [Finset.card_insert_of_notMem hiV, hVc]
    omega
  have hWsum : r + 1 ≤ ∑ i ∈ W, d i := by
    have h₀ := hlo i₀ hi₀
    have hVsum : 3 * V.card ≤ ∑ i ∈ V, d i := by
      simpa [Nat.mul_comm] using (Finset.sum_le_sum fun j hj =>
        (show 3 ≤ d j from (by omega : 3 ≤ τ + 3).trans
          (hlo j (Finset.mem_of_mem_erase (hV hj)))) :
        (∑ _j ∈ V, (3 : ℕ)) ≤ ∑ j ∈ V, d j)
    rw [Finset.sum_insert hiV]
    omega
  let C := E.powerset.filter fun U => i₀ ∈ U ∧ r + 1 ≤ ∑ i ∈ U, d i
  have hW : W ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hWE, Finset.mem_insert_self _ _, hWsum⟩
  obtain ⟨U, hU, hmin⟩ := C.exists_min_image Finset.card ⟨W, hW⟩
  have hUE : U ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
  obtain ⟨hiU, hUsum⟩ := (Finset.mem_filter.mp hU).2
  have hUc : U.card ≤ k := (hmin W hW).trans_eq hWc
  have hUne : (U.erase i₀).Nonempty := by
    by_contra hn
    have hz : U.erase i₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hsingle : U = {i₀} := by simpa [hz] using (Finset.insert_erase hiU).symm
    have hless := hhi i₀ hi₀
    rw [hsingle, Finset.sum_singleton] at hUsum
    omega
  obtain ⟨j, hj⟩ := hUne
  have hjU : j ∈ U := Finset.mem_of_mem_erase hj
  have hji : j ≠ i₀ := Finset.ne_of_mem_erase hj
  have hjE : j ∈ E := hUE hjU
  have hhalf : 2 * d j ≤ r := by
    have hm := hmax j hjE
    have hb := hpair i₀ hi₀ j hjE hji.symm
    omega
  have hcap : ∑ i ∈ U.erase j, d i ≤ r := by
    by_contra! hbad
    have hU' : U.erase j ∈ C := by
      simp [C, hji.symm, hiU, (Finset.erase_subset _ _).trans hUE, hbad]
    have hc := hmin _ hU'
    rw [Finset.card_erase_of_mem hjU] at hc
    have hpos : 0 < U.card := Finset.card_pos.mpr ⟨j, hjU⟩
    omega
  have hsum := Finset.sum_erase_add U d hjU
  refine ⟨U, hUE, ⟨i₀, hiU⟩, hUsum, ?_, ?_⟩ <;> omega

end GrahamDeficits

namespace GrahamShort541

/--
The first structural conclusions for a short zero-sum with normalized complement.
The coverage hypothesis is the conclusion of Gao–Hamidoune–Wang's Lemma 3.1(ii).
-/
theorem normalized_complement_structure {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (hr : 2 ≤ r) (hshort : 2 * r < p)
    (huniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r)
    (R : Finset (Fin p)) (hRne : R.Nonempty) (hRsum : (∑ i ∈ R, a i) = 0)
    (hvalues : 2 < (Set.range a).ncard)
    (hcover : ∀ k : ℕ, 2 ≤ k → k ≤ (∑ i ∈ Rᶜ, (a i).val) →
      ∃ U ⊆ Rᶜ, 2 ≤ U.card ∧ (∑ i ∈ U, (a i).val) = k) :
    (∃ i ∈ Rᶜ, a i ≠ 1) ∧ 2 ≤ (R.filter (fun i => a i ≠ 1)).card ∧
      ∀ i ∈ R, a i ≠ 1 → (∑ j ∈ Rᶜ, (a j).val) < (a i).val := by
  classical
  let C := Rᶜ
  let s := ∑ i ∈ C, (a i).val
  have hRcard := huniform R hRne hRsum
  have hCcard : C.card = p - r := by
    have h := Finset.card_compl_add_card R
    change C.card + R.card = Fintype.card (Fin p) at h
    simp only [Fintype.card_fin, hRcard] at h
    omega
  have hp₁ : 1 < p := by omega
  have hValPos (i : Fin p) : 0 < (a i).val := by
    by_contra! hval
    have hz : a i = 0 := (ZMod.val_eq_zero (a i)).mp (by omega)
    have hlen := huniform {i} (Finset.singleton_nonempty i) (by simpa using hz)
    simp only [Finset.card_singleton] at hlen
    omega
  have hValGeTwo {i : Fin p} (hi : a i ≠ 1) : 2 ≤ (a i).val := by
    have hne : (a i).val ≠ 1 := fun h => hi ((ZMod.val_eq_one hp₁ (a i)).mp h)
    have hp := hValPos i
    omega
  have hLarge (i : Fin p) (hi : i ∈ R) (hne : a i ≠ 1) : s < (a i).val := by
    by_contra! hle
    obtain ⟨U, hUC, hUcard, hUval⟩ := hcover (a i).val (hValGeTwo hne) hle
    have hUdisj : Disjoint (R.erase i) U := by
      refine Finset.disjoint_left.mpr fun j hjR hjU => ?_
      exact (Finset.mem_compl.mp (hUC hjU)) (Finset.mem_erase.mp hjR).2
    have hUsum : (∑ j ∈ U, a j) = a i := by
      calc
        _ = ∑ j ∈ U, ((a j).val : ZMod p) := by simp
        _ = ((∑ j ∈ U, (a j).val : ℕ) : ZMod p) := by rw [Nat.cast_sum]
        _ = _ := by rw [hUval, ZMod.natCast_zmod_val]
    have hNewSum : (∑ j ∈ R.erase i ∪ U, a j) = 0 := by
      rw [Finset.sum_union hUdisj, hUsum, Finset.sum_erase_add R a hi, hRsum]
    have hNewCard : (R.erase i ∪ U).card = (r - 1) + U.card := by
      rw [Finset.card_union_of_disjoint hUdisj, Finset.card_erase_of_mem hi, hRcard]
    have hNewNe : (R.erase i ∪ U).Nonempty := Finset.card_pos.mp (by omega)
    have hNewLen := huniform (R.erase i ∪ U) hNewNe hNewSum
    omega
  have hCnonOne : ∃ i ∈ C, a i ≠ 1 := by
    by_contra! hAll
    have hs : s = C.card := by
      unfold s
      rw [Finset.sum_congr rfl (fun i hi => (ZMod.val_eq_one hp₁ (a i)).mpr (hAll i hi))]
      simp
    have hOnes : C ⊆ Finset.univ.filter (fun i => a i = 1) := by
      intro i hi
      simp [hAll i hi]
    have hSame (i : Fin p) (hi : a i ≠ 1) : a i = ((p - r + 1 : ℕ) : ZMod p) := by
      have hiR : i ∈ R := by
        by_contra hir
        exact hi (hAll i (Finset.mem_compl.mpr hir))
      have hL := hLarge i hiR hi
      have hValLt := ZMod.val_lt (a i)
      let k := p - (a i).val
      have hk : k ≤ (Finset.univ.filter (fun i => a i = 1)).card :=
        (show k ≤ C.card by dsimp [k]; omega).trans (Finset.card_le_card hOnes)
      have hZero : (∑ j ∈ ({i} : Finset (Fin p)), a j) + k • (1 : ZMod p) = 0 := by
        simp only [Finset.sum_singleton, nsmul_one]
        calc
          _ = ((a i).val : ZMod p) + (k : ZMod p) := by rw [ZMod.natCast_zmod_val]
          _ = ((p : ℕ) : ZMod p) := by
            rw [← Nat.cast_add, show (a i).val + k = p by dsimp [k]; omega]
          _ = 0 := ZMod.natCast_self p
      have hlen := Graham541.common_length_of_padding a r huniform 1 {i}
        (by simpa using hi) k hk (by simp) hZero
      simp only [Finset.card_singleton] at hlen
      have hval : (a i).val = p - r + 1 := by dsimp [k] at hlen; omega
      rw [← hval, ZMod.natCast_zmod_val]
    let w : ZMod p := (p - r + 1 : ℕ)
    have hRange : Set.range a ⊆ ({1, w} : Set (ZMod p)) := by
      rintro _ ⟨i, rfl⟩
      by_cases hi : a i = 1
      · simp [hi]
      · simp [hSame i hi, w]
    have hPair : ({1, w} : Set (ZMod p)).ncard ≤ 2 := by
      simpa using
        Set.ncard_insert_le (1 : ZMod p) ({w} : Set (ZMod p))
    exact hvalues.not_ge ((Set.ncard_le_ncard hRange).trans hPair)
  have hRnonOne : ∃ i ∈ R, a i ≠ 1 := by
    by_contra! hAll
    have hs : (∑ i ∈ R, a i) = (r : ZMod p) := by
      rw [Finset.sum_congr rfl hAll, Finset.sum_const, hRcard, nsmul_one]
    have hz : (r : ZMod p) = 0 := hs.symm.trans hRsum
    have h := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at h
    omega
  have hCstrict : C.card < s := by
    obtain ⟨i, hi, hne⟩ := hCnonOne
    have hSum : (∑ _j ∈ C, (1 : ℕ)) < ∑ j ∈ C, (a j).val :=
      Finset.sum_lt_sum (fun j _ => by have h := hValPos j; omega)
        ⟨i, hi, by have h := hValGeTwo hne; omega⟩
    simpa [s] using hSum
  have hRtwo : 2 ≤ (R.filter (fun i => a i ≠ 1)).card := by
    by_contra! hFew
    have hAtMost : (R.filter (fun i => a i ≠ 1)).card ≤ 1 := by omega
    obtain ⟨i, hi, hne⟩ := hRnonOne
    have hiN : i ∈ R.filter (fun i => a i ≠ 1) := Finset.mem_filter.mpr ⟨hi, hne⟩
    have hRest : ∀ j ∈ R.erase i, a j = 1 := by
      intro j hj
      by_contra hnj
      have hjN : j ∈ R.filter (fun i => a i ≠ 1) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hj).2, hnj⟩
      exact (Finset.mem_erase.mp hj).1 (Finset.card_le_one_iff.mp hAtMost hjN hiN)
    have hSumRest : (∑ j ∈ R.erase i, a j) = ((r - 1 : ℕ) : ZMod p) := by
      rw [Finset.sum_congr rfl hRest, Finset.sum_const, Finset.card_erase_of_mem hi,
        hRcard, nsmul_one]
    have hsum : a i + ((r - 1 : ℕ) : ZMod p) = 0 := by
      rw [← hSumRest, Finset.add_sum_erase R a hi, hRsum]
    have hzero : ((p - (r - 1) : ℕ) : ZMod p) + ((r - 1 : ℕ) : ZMod p) = 0 := by
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
    have hiCast : a i = ((p - (r - 1) : ℕ) : ZMod p) :=
      add_right_cancel (hsum.trans hzero.symm)
    have hival : (a i).val = p - (r - 1) := by
      rw [hiCast, ZMod.val_natCast_of_lt (by omega)]
    have hbig := hLarge i hi hne
    omega
  exact ⟨hCnonOne, hRtwo, hLarge⟩

end GrahamShort541

namespace GrahamShort541

private def onesIn {I : Type*} (C : Finset I) (b : I → ℕ) : Finset I :=
  C.filter (fun i => b i = 1)

private def largerIn {I : Type*} (C : Finset I) (b : I → ℕ) : Finset I :=
  C.filter (fun i => b i ≠ 1)

private theorem ge_two_of_mem_larger {I : Type*} {C : Finset I} {b : I → ℕ}
    (hpos : ∀ i ∈ C, 0 < b i) {i : I} (hi : i ∈ largerIn C b) : 2 ≤ b i := by
  have h := Finset.mem_filter.mp hi
  have := hpos i h.1
  omega

private theorem split_totals {I : Type*} (C : Finset I) (b : I → ℕ)
    (hpos : ∀ i ∈ C, 0 < b i) :
    (∑ i ∈ C, b i) = (onesIn C b).card + (∑ i ∈ largerIn C b, b i) ∧
    (∑ i ∈ C, b i) + (onesIn C b).card =
      2 * C.card + ∑ i ∈ largerIn C b, (b i - 2) := by
  classical
  let O := onesIn C b
  let B := largerIn C b
  have hUnion : O ∪ B = C := by
    ext i
    simp only [O, B, onesIn, largerIn, Finset.mem_union, Finset.mem_filter]
    tauto
  have hDisj : Disjoint O B := Finset.disjoint_left.mpr (fun i hiO hiB =>
    (Finset.mem_filter.mp hiB).2 ((Finset.mem_filter.mp hiO).2))
  have hCard : C.card = O.card + B.card := by
    rw [← hUnion, Finset.card_union_of_disjoint hDisj]
  have hOne : (∑ i ∈ O, b i) = O.card := by
    calc
      _ = ∑ _i ∈ O, (1 : ℕ) := Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
      _ = _ := by simp
  have hSum : (∑ i ∈ C, b i) = O.card + ∑ i ∈ B, b i := by
    rw [← hUnion, Finset.sum_union hDisj, hOne]
  have hOther : (∑ i ∈ B, b i) = 2 * B.card + ∑ i ∈ B, (b i - 2) := by
    calc
      _ = ∑ i ∈ B, (2 + (b i - 2)) :=
        Finset.sum_congr rfl fun i hi => (Nat.add_sub_of_le (ge_two_of_mem_larger hpos hi)).symm
      _ = _ := by
        have hTwo : (∑ _i ∈ B, (2 : ℕ)) = 2 * B.card := by
          simp [Nat.mul_comm]
        rw [Finset.sum_add_distrib, hTwo]
  refine ⟨hSum, ?_⟩
  change (∑ i ∈ C, b i) + O.card = 2 * C.card + ∑ i ∈ B, (b i - 2)
  omega

private theorem excess_bound {I : Type*} (C : Finset I) (b : I → ℕ) (p gap : ℕ)
    (hpos : ∀ i ∈ C, 0 < b i) (hcard : p+1 ≤ 2*C.card)
    (hsum : (∑ i ∈ C, b i) + gap ≤ p) :
    (∑ i ∈ largerIn C b, (b i - 2)) + gap + 1 ≤ (onesIn C b).card := by
  have h := (split_totals C b hpos).2
  omega

private theorem value_le_ones {I : Type*} {C : Finset I} {b : I → ℕ}
    (hpos : ∀ i ∈ C, 0 < b i)
    (hbound : (∑ i ∈ largerIn C b, (b i - 2)) + 2 ≤ (onesIn C b).card)
    {i : I} (hi : i ∈ largerIn C b) : b i ≤ (onesIn C b).card := by
  have hi₂ := ge_two_of_mem_larger hpos hi
  have hiSum : b i - 2 ≤ ∑ j ∈ largerIn C b, (b j - 2) :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (b j - 2)) hi
  omega

/-- Every entry larger than one is bounded by the number of ones. -/
theorem entry_le_ones {I : Type*} (C : Finset I) (b : I → ℕ) (p : ℕ)
    (hpos : ∀ i ∈ C, 0 < b i) (hcard : p+1 ≤ 2*C.card)
    (hsum : (∑ i ∈ C, b i) + 2 ≤ p) {j : I} (hj : j ∈ C) (hbj : 2 ≤ b j) :
    b j ≤ (C.filter fun i => b i = 1).card := by
  have hbound := excess_bound C b p 2 hpos hcard hsum
  exact value_le_ones hpos (by omega) (Finset.mem_filter.mpr ⟨hj, by omega⟩)

private theorem pad_ones {I : Type*} (C : Finset I) (b : I → ℕ)
    {X : Finset I} (hX : X ⊆ largerIn C b) (d : ℕ) (hd : d ≤ (onesIn C b).card) :
    ∃ U ⊆ C, U.card = X.card + d ∧ (∑ i ∈ U, b i) = (∑ i ∈ X, b i) + d := by
  classical
  obtain ⟨D, hDO, hDcard⟩ := Finset.exists_subset_card_eq hd
  have hSumD : (∑ i ∈ D, b i) = d := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp (hDO hi)).2)]
    simp [hDcard]
  have hDisj : Disjoint X D := Finset.disjoint_left.mpr (fun i hiX hiD =>
    (Finset.mem_filter.mp (hX hiX)).2 ((Finset.mem_filter.mp (hDO hiD)).2))
  refine ⟨X ∪ D, ?_, ?_, ?_⟩
  · exact Finset.union_subset (fun _ hi => (Finset.mem_filter.mp (hX hi)).1)
      (fun _ hi => (Finset.mem_filter.mp (hDO hi)).1)
  · rw [Finset.card_union_of_disjoint hDisj, hDcard]
  · rw [Finset.sum_union hDisj, hSumD]

private theorem max_feasible_sum {I : Type*} (B : Finset I) (b : I → ℕ) (k : ℕ) :
    ∃ X ⊆ B, (∑ i ∈ X, b i) ≤ k ∧
      ∀ Y ⊆ B, (∑ i ∈ Y, b i) ≤ k → (∑ i ∈ Y, b i) ≤ ∑ i ∈ X, b i := by
  classical
  let eligible := B.powerset.filter (fun X => (∑ i ∈ X, b i) ≤ k)
  have hne : eligible.Nonempty := ⟨∅, by simp [eligible]⟩
  obtain ⟨X, hX, hmax⟩ := Finset.exists_max_image eligible (fun X => ∑ i ∈ X, b i) hne
  have ⟨hXB, hXk⟩ := Finset.mem_filter.mp hX
  refine ⟨X, Finset.mem_powerset.mp hXB, hXk, fun Y hY hYk => ?_⟩
  exact hmax Y (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hY, hYk⟩)

private theorem residual_lt {I : Type*} {B X : Finset I} {b : I → ℕ} {k : ℕ}
    (hX : X ⊆ B) (hXk : (∑ i ∈ X, b i) ≤ k)
    (hmax : ∀ Y ⊆ B, (∑ i ∈ Y, b i) ≤ k → (∑ i ∈ Y, b i) ≤ ∑ i ∈ X, b i)
    {i : I} (hiB : i ∈ B) (hiX : i ∉ X) (hiPos : 0 < b i) :
    k - (∑ j ∈ X, b j) < b i := by
  classical
  by_contra! hle
  have hInsertSum : (∑ j ∈ insert i X, b j) = b i + ∑ j ∈ X, b j :=
    Finset.sum_insert hiX
  have hmax' := hmax (insert i X) (Finset.insert_subset hiB hX) (by omega)
  omega

/-- Every target from two through the total has a realization using at least two entries. -/
theorem exists_long_realizing {I : Type*} (C : Finset I) (b : I → ℕ) (p k : ℕ)
    (hpos : ∀ i ∈ C, 0 < b i) (hcard : p+1 ≤ 2*C.card)
    (hsum : (∑ i ∈ C, b i) < p) (hk₂ : 2 ≤ k) (hk : k ≤ ∑ i ∈ C, b i) :
    ∃ U ⊆ C, 2 ≤ U.card ∧ (∑ i ∈ U, b i) = k := by
  classical
  let O := onesIn C b
  let B := largerIn C b
  have hTotal : (∑ i ∈ C, b i) = O.card + ∑ i ∈ B, b i := (split_totals C b hpos).1
  have hExcess : (∑ i ∈ B, (b i - 2)) + 2 ≤ O.card := by
    simpa [B, O, Nat.add_assoc] using excess_bound C b p 1 hpos hcard (by omega)
  obtain ⟨X, hX, hXk, hmax⟩ := max_feasible_sum B b k
  let d := k - ∑ i ∈ X, b i
  have hd : d ≤ O.card := by
    by_cases hXB : X = B
    · dsimp [d]
      rw [hXB]
      omega
    · obtain ⟨i, hiB, hiX⟩ := Finset.not_subset.mp
        (fun hBX => hXB (Finset.Subset.antisymm hX hBX))
      have hlt : d < b i := residual_lt hX hXk hmax hiB hiX
        (lt_of_lt_of_le (by decide) (ge_two_of_mem_larger hpos hiB))
      exact hlt.le.trans (value_le_ones hpos hExcess hiB)
  by_cases hlong : 2 ≤ X.card + d
  · obtain ⟨U, hUC, hUcard, hUsum⟩ := pad_ones C b hX d hd
    refine ⟨U, hUC, by omega, ?_⟩
    dsimp [d] at hUsum
    omega
  · have hXne : X.Nonempty := by
      by_contra hn
      have hXempty := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [hXempty, d] at hlong
      omega
    have hXcard : X.card = 1 := by have := Finset.card_pos.mpr hXne; omega
    obtain ⟨i, hXi⟩ := Finset.card_eq_one.mp hXcard
    have hiB := hX (show i ∈ X by simp [hXi])
    have hUpper : b i ≤ O.card := value_le_ones hpos hExcess hiB
    have hEq : (∑ j ∈ X, b j) = b i := by simp [hXi]
    have hkO : k ≤ O.card := by
      dsimp [d] at hlong
      omega
    obtain ⟨U, hUC, hUcard, hUsum⟩ := pad_ones C b (Finset.empty_subset B) k hkO
    simp only [Finset.card_empty, Finset.sum_empty, zero_add] at hUcard hUsum
    exact ⟨U, hUC, hUcard.symm ▸ hk₂, hUsum⟩

/-- An interior target has realizations of two different lengths. -/
theorem exists_two_lengths {I : Type*} (C : Finset I) (b : I → ℕ) (p k : ℕ)
    (hpos : ∀ i ∈ C, 0 < b i) (hcard : p+1 ≤ 2*C.card)
    (hsum : (∑ i ∈ C, b i) + 2 ≤ p) {j : I} (hj : j ∈ C) (hbj : 2 ≤ b j)
    (hjk : b j ≤ k) (hk : k + b j ≤ ∑ i ∈ C, b i) :
    ∃ U ⊆ C, ∃ V ⊆ C, (∑ i ∈ U, b i) = k ∧ (∑ i ∈ V, b i) = k ∧ U.card ≠ V.card := by
  classical
  let O := onesIn C b
  let B := largerIn C b
  have hTotal : (∑ i ∈ C, b i) = O.card + ∑ i ∈ B, b i := (split_totals C b hpos).1
  have hExcess : (∑ i ∈ B, (b i - 2)) + 3 ≤ O.card := by
    simpa [B, O, Nat.add_assoc] using excess_bound C b p 2 hpos hcard hsum
  have hjB : j ∈ B := Finset.mem_filter.mpr ⟨hj, by omega⟩
  obtain ⟨X, hX, hXk, hmax⟩ := max_feasible_sum B b k
  have hMaxSingle : b j ≤ ∑ i ∈ X, b i := by
    simpa only [Finset.sum_singleton] using
      hmax {j} (Finset.singleton_subset_iff.mpr hjB) (by simpa only [Finset.sum_singleton] using hjk)
  have hXne : X.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty] at hMaxSingle
    omega
  let d := k - ∑ i ∈ X, b i
  have hRemove : ∃ i ∈ X, d + b i ≤ O.card := by
    by_cases hXB : X = B
    · refine ⟨j, hXB.symm ▸ hjB, ?_⟩
      dsimp [d]
      rw [hXB] at hXk ⊢
      omega
    · obtain ⟨j', hj'B, hj'X⟩ := Finset.not_subset.mp
        (fun hBX => hXB (Finset.Subset.antisymm hX hBX))
      obtain ⟨i, hiX⟩ := hXne
      have hiB := hX hiX
      have hij' : i ≠ j' := fun h => hj'X (h ▸ hiX)
      have hi₂ := ge_two_of_mem_larger hpos hiB
      have hj'₂ := ge_two_of_mem_larger hpos hj'B
      have hPair : ({i, j'} : Finset I) ⊆ B :=
        Finset.insert_subset hiB (Finset.singleton_subset_iff.mpr hj'B)
      have hPairSum : (∑ u ∈ ({i, j'} : Finset I), (b u - 2)) ≤
          ∑ u ∈ B, (b u - 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hPair (fun _ _ _ => Nat.zero_le _)
      simp [hij'] at hPairSum
      have hlt : d < b j' := residual_lt hX hXk hmax hj'B hj'X (by omega)
      exact ⟨i, hiX, by omega⟩
  obtain ⟨i, hiX, hdi⟩ := hRemove
  have hi₂ := ge_two_of_mem_larger hpos (hX hiX)
  have hd : d ≤ O.card := by omega
  obtain ⟨U, hUC, hUcard, hUsum⟩ := pad_ones C b hX d hd
  have hErase : X.erase i ⊆ B := (Finset.erase_subset i X).trans hX
  obtain ⟨V, hVC, hVcard, hVsum⟩ := pad_ones C b hErase (d + b i) hdi
  have hEraseCard := Finset.card_erase_of_mem hiX
  have hEraseSum := Finset.sum_erase_add X b hiX
  have hXpos := Finset.card_pos.mpr hXne
  dsimp [d] at hUsum hVsum
  exact ⟨U, hUC, V, hVC, by omega, by omega, by omega⟩

end GrahamShort541

namespace GrahamShort541

theorem support_of_normalized_complement {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (uniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r)
    (hr : 2 ≤ r) (hshort : 2 * r < p) {R : Finset (Fin p)}
    (hRne : R.Nonempty) (hRzero : (∑ i ∈ R, a i) = 0)
    (hsmall : (∑ i ∈ Rᶜ, (a i).val) < p) : (Set.range a).ncard ≤ 2 := by
  classical
  by_contra! hlarge
  let C := Rᶜ
  let b (i : Fin p) := (a i).val
  let s := ∑ i ∈ C, b i
  have hRcard : R.card = r := uniform R hRne hRzero
  have hCcard : C.card = p - r := by simp [C, Finset.card_compl, hRcard]
  have hCsize : p + 1 ≤ 2 * C.card := by omega
  have hsmall' : s < p := hsmall
  have hb_lt (i : Fin p) : b i < p := ZMod.val_lt _
  have hpos (i : Fin p) : 0 < b i := by
    by_contra! hi
    have hz : a i = 0 := (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_le_zero hi)
    have h := uniform {i} (by simp) (by simpa using hz)
    simp at h
    omega
  have ha_eq (i : Fin p) : (b i : ZMod p) = a i := ZMod.natCast_zmod_val _
  have hval_one (i : Fin p) : b i = 1 ↔ a i = 1 := by
    constructor
    · intro hi
      simpa [hi] using (ha_eq i).symm
    · intro hi
      have h : 1 < p := by omega
      simpa only [b, hi, Nat.cast_one] using (ZMod.val_natCast_of_lt h)
  have hheavy (i : Fin p) (hi : a i ≠ 1) : 2 ≤ b i := by
    have := hpos i
    have := mt (hval_one i).mp hi
    omega
  have hsum_ge (U : Finset (Fin p)) : U.card ≤ ∑ i ∈ U, b i := by
    simpa using
      (Finset.sum_le_sum fun i (_ : i ∈ U) => Nat.succ_le_of_lt (hpos i) :
        (∑ _i ∈ U, (1 : ℕ)) ≤ ∑ i ∈ U, b i)
  have hs_lower : p - r ≤ s := by simpa only [s, hCcard] using hsum_ge C
  have hcover (k : ℕ) (hk : 2 ≤ k) (hks : k ≤ s) :
      ∃ U ⊆ C, 2 ≤ U.card ∧ (∑ i ∈ U, b i) = k :=
    exists_long_realizing C b p k (fun i _ => hpos i) hCsize hsmall' hk hks
  obtain ⟨⟨j, hj, hj₁⟩, hEsize, hsep⟩ :=
    normalized_complement_structure a hr hshort uniform R hRne hRzero hlarge hcover
  let m := b j
  let O := C.filter fun i => b i = 1
  let γ := O.card
  have hm : 2 ≤ m := hheavy j hj₁
  have hsum_erase : (∑ i ∈ C.erase j, b i) + m = s := Finset.sum_erase_add C b hj
  have hB_lower : p - r - 1 ≤ s - m := by
    have h := hsum_ge (C.erase j)
    rw [Finset.card_erase_of_mem hj, hCcard] at h
    omega
  let E := R.filter fun i => a i ≠ 1
  let T := R.filter fun i => a i = 1
  let τ := T.card
  change 2 ≤ E.card at hEsize
  have hEsub : E ⊆ R := Finset.filter_subset _ _
  have hEnonempty : E.Nonempty := Finset.card_pos.mp (by omega)
  have hseparate (i : Fin p) (hi : i ∈ E) : s < b i :=
    hsep i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  have hs_margin : s + 2 ≤ p := by
    obtain ⟨i, hi⟩ := hEnonempty
    have := hseparate i hi
    have := hb_lt i
    omega
  have hm_ones : m ≤ γ :=
    entry_le_ones C b p (fun i _ => hpos i) hCsize hs_margin hj hm
  have hTsum : (∑ i ∈ T, a i) = (τ : ZMod p) := by
    calc
      _ = ∑ _i ∈ T, (1 : ZMod p) := Finset.sum_congr rfl fun i hi =>
        (Finset.mem_filter.mp hi).2
      _ = _ := by simp [τ]
  have hETcard : E.card + τ = r := by
    rw [add_comm]
    exact (Finset.card_filter_add_card_filter_not (s := R) (fun i => a i = 1)).trans hRcard
  have hETsum : (∑ i ∈ E, a i) + (τ : ZMod p) = 0 := by
    have hpartition : (∑ i ∈ T, a i) + (∑ i ∈ E, a i) = ∑ i ∈ R, a i :=
      Finset.sum_filter_add_sum_filter_not R (fun i => a i = 1) a
    rw [hTsum, hRzero, add_comm] at hpartition
    exact hpartition
  have replace {X U : Finset (Fin p)} (hX : X ⊆ R) (hU : U ⊆ C) (hne : U.Nonempty)
      (heq : (∑ i ∈ X, a i) = ∑ i ∈ U, a i) : X.card = U.card := by
    have hd : Disjoint (R \ X) U := Finset.disjoint_left.mpr fun i hi hiU =>
      (Finset.mem_compl.mp (hU hiU)) (Finset.mem_sdiff.mp hi).1
    have hsum : (∑ i ∈ (R \ X) ∪ U, a i) = 0 := by
      rw [Finset.sum_union hd, ← heq, Finset.sum_sdiff hX, hRzero]
    have hc := uniform ((R \ X) ∪ U) (hne.mono Finset.subset_union_right) hsum
    rw [Finset.card_union_of_disjoint hd, Finset.card_sdiff_of_subset hX, hRcard] at hc
    have hXcard := Finset.card_le_card hX
    omega
  have from_ones {X : Finset (Fin p)} (hX : X ⊆ R) {k : ℕ} (hk : 0 < k)
      (hkγ : k ≤ γ) (hXsum : (∑ i ∈ X, a i) = (k : ZMod p)) : X.card = k := by
    obtain ⟨V, hVO, hVcard⟩ := Finset.exists_subset_card_eq hkγ
    have hVsum : (∑ i ∈ V, a i) = (k : ZMod p) := by
      calc
        _ = ∑ _i ∈ V, (1 : ZMod p) := Finset.sum_congr rfl fun i hi =>
          (hval_one i).mp (Finset.mem_filter.mp (hVO hi)).2
        _ = _ := by simp [hVcard]
    have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
    rw [← hVcard]
    exact replace hX (hVO.trans (Finset.filter_subset _ _)) hVne (hXsum.trans hVsum.symm)
  have hcast_sum (U : Finset (Fin p)) : (↑(∑ i ∈ U, b i) : ZMod p) = ∑ i ∈ U, a i := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => ha_eq i
  have forbidden {X : Finset (Fin p)} (hX : X ⊆ R) {k : ℕ} (hmk : m ≤ k)
      (hkB : k ≤ s - m) (heq : (∑ i ∈ X, a i) = (k : ZMod p)) : False := by
    have hk : k + m ≤ s := by omega
    obtain ⟨U, hU, V, hV, hUs, hVs, hUV⟩ :=
      exists_two_lengths C b p k (fun i _ => hpos i) hCsize hs_margin hj hm hmk hk
    have sum_ne {W : Finset (Fin p)} (hW : (∑ i ∈ W, b i) = k) : W.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hW
      omega
    have hUeq : (∑ i ∈ X, a i) = ∑ i ∈ U, a i := by rw [← hcast_sum U, hUs, heq]
    have hVeq : (∑ i ∈ X, a i) = ∑ i ∈ V, a i := by rw [← hcast_sum V, hVs, heq]
    exact hUV ((replace hX hU (sum_ne hUs) hUeq).symm.trans (replace hX hV (sum_ne hVs) hVeq))

  let d (i : Fin p) := p - b i
  have hdhi (i : Fin p) (hi : i ∈ E) : d i ≤ r - 1 := by
    have := hseparate i hi
    dsimp [d]
    omega
  have hdneg (i : Fin p) : a i = -(d i : ZMod p) := by
    dsimp only [d]
    rw [Nat.cast_sub (hb_lt i).le, ZMod.natCast_self, zero_sub, neg_neg, ha_eq]
  have hneg_sum {X : Finset (Fin p)} :
      (∑ i ∈ X, a i) = -(↑(∑ i ∈ X, d i) : ZMod p) := by
    rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hdneg i
  have residue {X : Finset (Fin p)} (h : (∑ i ∈ X, d i) ≤ p) :
      (∑ i ∈ X, a i) = (↑(p - ∑ i ∈ X, d i) : ZMod p) := by
    rw [hneg_sum, Nat.cast_sub h, ZMod.natCast_self, zero_sub]
  have pair_residue (i : Fin p) (hi : i ∈ E) (l : Fin p) (hl : l ∈ E) (hne : i ≠ l) :
      d i + d l ≤ r ∧ (∑ x ∈ ({i, l} : Finset (Fin p)), a x) =
        (↑(p - (d i + d l)) : ZMod p) := by
    let X : Finset (Fin p) := {i, l}
    let k := p - (d i + d l)
    have hXi : X ⊆ R := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hEsub hi
      · rw [Finset.mem_singleton.mp hx]
        exact hEsub hl
    have hXn : X.card = 2 := Finset.card_pair hne
    have hds : (∑ x ∈ X, d x) = d i + d l := by simp [X, hne]
    have hdi := hdhi i hi
    have hdl := hdhi l hl
    have hXsum : (∑ x ∈ X, a x) = (k : ZMod p) := by
      have hz : (∑ x ∈ X, d x) ≤ p := by omega
      simpa only [hds, k] using residue hz
    have hk : 3 ≤ k := by dsimp [k]; omega
    have hmk : m ≤ k := by
      by_contra! hlt
      have hcard := from_ones hXi (by omega : 0 < k) (by omega : k ≤ γ) hXsum
      omega
    have hlower : s - m < k := by
      by_contra! hle
      exact forbidden hXi hmk hle hXsum
    refine ⟨?_, hXsum⟩
    dsimp [k] at hlower
    omega
  have hlow (i : Fin p) (hi : i ∈ E) : τ + 3 ≤ d i := by
    have hτd : τ < d i := by
      by_contra! hle
      have count : d i ≤ ((Finset.univ : Finset (Fin p)).filter fun x => a x = 1).card :=
        hle.trans (Finset.card_le_card fun x hx => Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
      have hne (x : Fin p) (hx : x ∈ ({i} : Finset (Fin p))) : a x ≠ 1 := by
        rw [Finset.mem_singleton.mp hx]
        exact (Finset.mem_filter.mp hi).2
      have hz : (∑ x ∈ ({i} : Finset (Fin p)), a x) + d i • (1 : ZMod p) = 0 := by
        simp [hdneg i, nsmul_eq_mul]
      have hlen := Graham541.common_length_of_padding a r uniform 1 {i} hne (d i) count
        (by simp) hz
      rw [Finset.card_singleton] at hlen
      omega
    by_contra! hshort_d
    let X := E.erase i
    let k := d i - τ
    have hk : 0 < k := by dsimp [k]; omega
    have hk₂ : k ≤ 2 := by dsimp [k]; omega
    have hXsub : X ⊆ R := (Finset.erase_subset _ _).trans hEsub
    have heq : (∑ x ∈ X, a x) = (k : ZMod p) := by
      have he := Finset.sum_erase_add E a hi
      rw [hdneg i] at he
      dsimp only [k]
      rw [Nat.cast_sub hτd.le]
      apply add_right_cancel (b := -(d i : ZMod p) + (τ : ZMod p))
      calc
        (∑ x ∈ X, a x) + (-(d i : ZMod p) + (τ : ZMod p)) = 0 := by
          rw [← add_assoc, show (∑ x ∈ X, a x) + (-(d i : ZMod p)) = ∑ x ∈ E, a x from he,
            hETsum]
        _ = ((d i : ZMod p) - (τ : ZMod p)) + (-(d i : ZMod p) + (τ : ZMod p)) := by abel
    have hcard := from_ones hXsub hk (by omega : k ≤ γ) heq
    have hklt : k < p := by omega
    have hval : (∑ x ∈ X, a x).val = k := by rw [heq, ZMod.val_natCast_of_lt hklt]
    rcases (show X.card = 1 ∨ X.card = 2 by omega) with h1 | h2
    · obtain ⟨l, hl⟩ := Finset.card_eq_one.mp h1
      have hlE : l ∈ E := Finset.mem_of_mem_erase (show l ∈ X by simp [hl])
      have hbl := hseparate l hlE
      have hb : b l = k := by simpa only [hl, Finset.sum_singleton, b] using hval
      omega
    · obtain ⟨l, n, hln, hX⟩ := Finset.card_eq_two.mp h2
      have hlE : l ∈ E := Finset.mem_of_mem_erase (show l ∈ X by simp [hX])
      have hnE : n ∈ E := Finset.mem_of_mem_erase (show n ∈ X by simp [hX])
      obtain ⟨hle, hres⟩ := pair_residue l hlE n hnE hln
      have hp' : p - (d l + d n) < p := by
        have hlv := hb_lt l
        dsimp [d]
        omega
      have hresval : (∑ x ∈ X, a x).val = p - (d l + d n) := by
        rw [hX, hres, ZMod.val_natCast_of_lt hp']
      omega
  obtain ⟨X, hXE, _, hlarge_sum, hbelow, htoo_short⟩ :=
    GrahamDeficits.crossing hEnonempty hETcard hshort hlow hdhi
      (fun i hi l hl hne => (pair_residue i hi l hl hne).1)
  let k := p - ∑ i ∈ X, d i
  have hk : 0 < k := by dsimp [k]; omega
  have hkB : k ≤ s - m := by dsimp [k]; omega
  have hXR := hXE.trans hEsub
  have heq : (∑ i ∈ X, a i) = (k : ZMod p) := residue hbelow.le
  have hlt : k < m := by
    by_contra! hge
    exact forbidden hXR hge hkB heq
  have hcard := from_ones hXR hk (by omega : k ≤ γ) heq
  exact (Nat.ne_of_lt htoo_short) hcard

end GrahamShort541


namespace GrahamShort541

theorem support_of_short_length {p r : ℕ} [NeZero p] (a : Fin p → ZMod p)
    (uniform : ∀ S : Finset (Fin p), S.Nonempty → (∑ i ∈ S, a i) = 0 → S.card = r)
    (hr : 2 ≤ r) (hshort : 2 * r < p) : (Set.range a).ncard ≤ 2 := by
  classical
  obtain ⟨R, hRne, hRzero⟩ := GrahamZeroSum.exists_zero_sum_fintype a (by simp)
  have hRcard := uniform R hRne hRzero
  let C := Rᶜ
  have hCcard : C.card = p - r := by simp [C, Finset.card_compl, hRcard]
  have hCsize : p < 2 * C.card := by omega
  have free (U : Finset (Fin p)) (hU : U ⊆ C) (hUne : U.Nonempty) :
      (∑ i ∈ U, a i) ≠ 0 := by
    intro hUzero
    have hd : Disjoint R U := Finset.disjoint_left.mpr fun i hiR hiU =>
      Finset.mem_compl.mp (hU hiU) hiR
    have hzero : (∑ i ∈ R ∪ U, a i) = 0 := by rw [Finset.sum_union hd, hRzero, hUzero, add_zero]
    have hcard := uniform (R ∪ U) (hRne.mono Finset.subset_union_left) hzero
    rw [Finset.card_union_of_disjoint hd, hRcard] at hcard
    have := Finset.card_pos.mpr hUne
    omega
  obtain ⟨u, hu⟩ := GrahamNormalization.normalize_zmod free hCsize
  let scale (x : ZMod p) := (u : ZMod p) * x
  have hinj : Function.Injective scale := by
    intro x y h
    have hh := congrArg (fun z : ZMod p => (↑u⁻¹ : ZMod p) * z) h
    simpa [scale, ← mul_assoc] using hh
  let a' := scale ∘ a
  have uniform' (S : Finset (Fin p)) (hS : S.Nonempty) (hs : (∑ i ∈ S, a' i) = 0) :
      S.card = r := by
    apply uniform S hS
    apply hinj
    simpa [scale, a', Finset.mul_sum] using hs
  have hRzero' : (∑ i ∈ R, a' i) = 0 := by
    simp [a', scale, ← Finset.mul_sum, hRzero]
  have h := support_of_normalized_complement a' uniform' hr hshort hRne hRzero' hu
  rwa [show Set.range a' = scale '' Set.range a from Set.range_comp _ _,
    Set.ncard_image_of_injective _ hinj] at h

end GrahamShort541

/-- Graham's conjecture for arbitrary cyclic groups. The short-complement
argument follows Gao, Hamidoune and Wang with the Savchev–Chen normalization. -/
theorem OMA.solution : type_of% @Erdos541.erdos_541.variants.general_moduli :=
  Graham541.reduce_to_short GrahamShort541.support_of_short_length